"use strict";

import 'bufferutil';
import 'utf-8-validate';
import { createSecureContext, connect as tlsConnect } from 'tls';
import { connect as http2Connect } from 'http2';
import WebSocket from 'ws';
import { readFileSync, watch } from 'fs';
import { setPriority, cpus } from 'os';

process.env.UV_THREADPOOL_SIZE = String(cpus().length * 4);

// ---------- KONFİGÜRASYON ----------
const cfg = JSON.parse(readFileSync('cfg.json', 'utf8'));
const TOKEN = cfg.token;
const GUILD_ID = cfg.id;

const REQ_COUNT = 4;           // her API sürümü için HTTP/1.1 soket sayısı
const GW_COUNT = 3;            // 3 gateway bağlantısı
const USE_HTTP2 = true;        // HTTP/2 kullan
const USE_V7 = true;           // v7 API sürümünü de dene

const DISCORD_HOST = 'canary.discord.com';
const DISCORD_IPS = [
    '162.159.137.232',
    '162.159.136.232',
    '162.159.135.232',
    '162.159.138.232',
    '104.16.58.5',
    '104.16.59.5',
];

const UA = 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/131.0.0.0 Safari/537.36';
const SP = 'eyJicm93c2VyIjoiQ2hyb21lIiwiYnJvd3Nlcl91c2VyX2FnZW50IjoiQ2hyb21lIiwiY2xpZW50YnVpbGRfbnVtYmVyIjozNTU2MjR9';

const noop = () => {};
const guilds = new Map();

const tlsSessions = new Array(DISCORD_IPS.length).fill(null);
const sharedCtx = createSecureContext({
    minVersion: 'TLSv1.3',
    maxVersion: 'TLSv1.3',
    sessionTimeout: 86400,
});

let mfaToken = '';
let lastSeq = 0;
let gwGen = 0;
let succeeded = false;
let fireStartTime = 0;
let lastFireCode = '';
let lastFireTimeout = null;
let lastStatusInfo = { code: null, source: null }; // son alınan durum kodu

// ---------- HEARTBEAT BUFFER (gateway için) ----------
const hbBuf = new Uint8Array(32);
let hbLen = 0;
const HB_PREFIX = [123,34,111,112,34,58,49,44,34,100,34,58];

function buildHbBuf(n) {
    let i = 0;
    for (; i < HB_PREFIX.length; i++) hbBuf[i] = HB_PREFIX[i];
    if (n === 0) {
        hbBuf[i++] = 48;
    } else {
        const start = i;
        let tmp = n;
        while (tmp > 0) {
            hbBuf[i++] = 48 + (tmp % 10);
            tmp = (tmp / 10) | 0;
        }
        hbBuf.subarray(start, i).reverse();
    }
    hbBuf[i++] = 125;
    hbLen = i;
}
buildHbBuf(0);

// ---------- İSTEK BUFFERLARI (v7 & v9) ----------
let patchBufs = { v9: [null, null], v7: [null, null] };
let patchCode = '';

function buildPatchBufs(code) {
    patchCode = code;
    const body = '{"code":"' + code + '"}';
    const bodyLen = Buffer.byteLength(body);

    for (const version of ['v9', 'v7']) {
        const apiPath = version === 'v9' ? '/api/v9' : '/api/v7';
        const base =
            `PATCH ${apiPath}/guilds/${GUILD_ID}/vanity-url HTTP/1.1\r\n` +
            `Host: ${DISCORD_HOST}\r\n` +
            `Authorization: ${TOKEN}\r\n` +
            `Content-Type: application/json\r\n` +
            `User-Agent: ${UA}\r\n` +
            `X-Super-Properties: ${SP}\r\n` +
            `Connection: keep-alive\r\n` +
            `Content-Length: ${bodyLen}\r\n\r\n` +
            body;
        patchBufs[version][0] = Buffer.from(base, 'latin1');

        if (mfaToken) {
            const mfaReq =
                `PATCH ${apiPath}/guilds/${GUILD_ID}/vanity-url HTTP/1.1\r\n` +
                `Host: ${DISCORD_HOST}\r\n` +
                `Authorization: ${TOKEN}\r\n` +
                `X-Discord-MFA-Authorization: ${mfaToken}\r\n` +
                `Cookie: __Secure-recent_mfa=${mfaToken}\r\n` +
                `Content-Type: application/json\r\n` +
                `User-Agent: ${UA}\r\n` +
                `X-Super-Properties: ${SP}\r\n` +
                `Connection: keep-alive\r\n` +
                `Content-Length: ${bodyLen}\r\n\r\n` +
                body;
            patchBufs[version][1] = Buffer.from(mfaReq, 'latin1');
        } else {
            patchBufs[version][1] = patchBufs[version][0];
        }
    }
}

function warmup(vanity) {
    if (vanity && vanity !== patchCode) buildPatchBufs(vanity);
}

// ---------- HTTP/1.1 SOKET HAVUZU (v9 ve v7 ayrı) ----------
class SocketPool {
    constructor(version, count) {
        this.version = version;
        this.count = count;
        this.sockets = new Array(count).fill(null);
        this.ready = new Uint8Array(count);
        this.pending = new Uint8Array(count);
        this.queue = new Array(count).fill(null);
        this.gen = new Uint32Array(count);
        this.respBuf = Array.from({ length: count }, () => Buffer.allocUnsafe(16));
        this.respLen = new Uint8Array(count);
        this.fireGen = 0;
        this.lastFired = '';
    }

    parseStatus(idx, chunk) {
        const prev = this.respLen[idx];
        let buf, len;
        if (prev > 0) {
            chunk.copy(this.respBuf[idx], prev, 0, Math.min(chunk.length, 16 - prev));
            len = prev + chunk.length;
            buf = this.respBuf[idx];
        } else {
            buf = chunk;
            len = chunk.length;
        }
        if (len >= 12 && buf[8] === 32) {
            this.respLen[idx] = 0;
            return (buf[9] - 48) * 100 + (buf[10] - 48) * 10 + (buf[11] - 48);
        }
        if (len < 16) {
            if (!prev) chunk.copy(this.respBuf[idx], 0, 0, len);
            this.respLen[idx] = len;
        } else {
            this.respLen[idx] = 0;
        }
        return -1;
    }

    makeSock(idx) {
        this.ready[idx] = 0;
        this.pending[idx] = 0;
        this.respLen[idx] = 0;
        const ipIdx = idx % DISCORD_IPS.length;
        const ip = DISCORD_IPS[ipIdx];

        const sock = tlsConnect({
            host: ip,
            port: 443,
            servername: DISCORD_HOST,
            ALPNProtocols: ['http/1.1'],
            rejectUnauthorized: false,
            secureContext: sharedCtx,
            session: tlsSessions[ipIdx] ?? undefined,
            noDelay: true,
            keepAlive: true,
            keepAliveInitialDelay: 0,
            highWaterMark: 0,
        });

        sock.setNoDelay(true);
        sock.setKeepAlive(true, 0);
        sock.on('session', (s) => {
            tlsSessions[ipIdx] = s;
        });

        sock.on('secureConnect', () => {
            this.ready[idx] = 1;
            sock.ref();
            sock.resume();
            const q = this.queue[idx];
            if (q) {
                this.queue[idx] = null;
                this.pending[idx] = 1;
                sock.write(q);
            }
        });

        sock.on('data', (chunk) => {
            if (!this.pending[idx]) return;
            const st = this.parseStatus(idx, chunk);
            if (st === -1) return;
            this.pending[idx] = 0;

            // Son durum kodunu sakla (başarısız log için)
            if (st !== 200 && st !== 203) {
                lastStatusInfo = { code: st, source: `${this.version} sock${idx}` };
            }

            if ((st === 200 || st === 203) && !succeeded) {
                succeeded = true;
                if (fireStartTime) {
                    const elapsed = (performance.now() - fireStartTime).toFixed(2);
                    console.log(`[SUCCESS] ${patchCode} - ${elapsed} ms`);
                    fireStartTime = 0;
                }
                if (lastFireTimeout) clearTimeout(lastFireTimeout);
            }
        });

        const onClose = () => {
            this.ready[idx] = 0;
            this.pending[idx] = 0;
            this.respLen[idx] = 0;
            if (this.gen[idx] !== this.fireGen) this.queue[idx] = null;
            this.sockets[idx] = this.makeSock(idx);
        };

        sock.on('error', onClose);
        sock.on('close', onClose);
        return sock;
    }

    fire(code) {
        if (succeeded) return;
        if (code === this.lastFired) return;
        this.lastFired = code;
        const buf = mfaToken ? patchBufs[this.version][1] : patchBufs[this.version][0];
        this.fireGen = (this.fireGen + 1) & 0xffffffff;

        for (let i = 0; i < this.count; i++) {
            this.pending[i] = 0;
            this.gen[i] = this.fireGen;
            const sock = this.sockets[i];
            if (!this.ready[i] || !sock || sock.destroyed) {
                this.queue[i] = buf;
                continue;
            }
            this.pending[i] = 1;
            sock.write(buf);
        }
    }
}

const v9Pool = new SocketPool('v9', REQ_COUNT);
const v7Pool = USE_V7 ? new SocketPool('v7', REQ_COUNT) : null;

// ---------- HTTP/2 (her IP için ayrı oturum) ----------
let http2Sessions = new Array(DISCORD_IPS.length).fill(null);
let http2Ready = new Array(DISCORD_IPS.length).fill(false);
let http2PingIntervals = new Array(DISCORD_IPS.length).fill(null);

function createHttp2Session(ipIdx) {
    if (http2Sessions[ipIdx] && !http2Sessions[ipIdx].destroyed) return http2Sessions[ipIdx];

    const ip = DISCORD_IPS[ipIdx];
    const session = http2Connect(`https://${DISCORD_HOST}`, {
        host: ip,
        port: 443,
        servername: DISCORD_HOST,
        rejectUnauthorized: false,
        secureContext: sharedCtx,
        session: tlsSessions[ipIdx] ?? undefined,
        settings: {
            enablePush: false,
            initialWindowSize: 65535,
            maxConcurrentStreams: 100,
        },
    });

    session.on('connect', () => {
        http2Ready[ipIdx] = true;
        if (http2PingIntervals[ipIdx]) clearInterval(http2PingIntervals[ipIdx]);
        http2PingIntervals[ipIdx] = setInterval(() => {
            if (session && !session.destroyed && http2Ready[ipIdx]) {
                session.ping(Buffer.alloc(8), (err) => {
                    if (err) {
                        if (http2PingIntervals[ipIdx]) clearInterval(http2PingIntervals[ipIdx]);
                    }
                });
            } else {
                if (http2PingIntervals[ipIdx]) clearInterval(http2PingIntervals[ipIdx]);
            }
        }, 30000);
    });

    session.on('session', (s) => {
        tlsSessions[ipIdx] = s;
    });

    session.on('error', () => {
        http2Ready[ipIdx] = false;
        if (http2PingIntervals[ipIdx]) clearInterval(http2PingIntervals[ipIdx]);
        http2Sessions[ipIdx] = null;
        setTimeout(() => createHttp2Session(ipIdx), 200); // 200 ms yeniden bağlanma
    });

    session.on('close', () => {
        http2Ready[ipIdx] = false;
        if (http2PingIntervals[ipIdx]) clearInterval(http2PingIntervals[ipIdx]);
        http2Sessions[ipIdx] = null;
        setTimeout(() => createHttp2Session(ipIdx), 200);
    });

    http2Sessions[ipIdx] = session;
    return session;
}

function sendHttp2Request(ipIdx, code, version) {
    if (succeeded) return;
    const session = createHttp2Session(ipIdx);
    if (!session || session.destroyed || !http2Ready[ipIdx]) return;

    const apiPath = version === 'v9' ? '/api/v9' : '/api/v7';
    const headers = {
        ':method': 'PATCH',
        ':path': `${apiPath}/guilds/${GUILD_ID}/vanity-url`,
        authorization: TOKEN,
        'content-type': 'application/json',
        'user-agent': UA,
        'x-super-properties': SP,
        connection: 'keep-alive',
    };
    if (mfaToken) {
        headers['x-discord-mfa-authorization'] = mfaToken;
        headers.cookie = `__Secure-recent_mfa=${mfaToken}`;
    }

    const body = Buffer.from('{"code":"' + code + '"}', 'latin1');
    headers['content-length'] = body.length;

    const req = session.request(headers);
    req.end(body);

    req.on('response', (respHeaders) => {
        const status = respHeaders[':status'];
        if (status !== 200 && status !== 203) {
            lastStatusInfo = { code: status, source: `HTTP/2 ${version} ip${ipIdx}` };
        }
        if ((status === 200 || status === 203) && !succeeded) {
            succeeded = true;
            if (fireStartTime) {
                const elapsed = (performance.now() - fireStartTime).toFixed(2);
                console.log(`[SUCCESS] ${code} - ${elapsed} ms`);
                fireStartTime = 0;
            }
            if (lastFireTimeout) clearTimeout(lastFireTimeout);
        }
    });

    req.on('error', noop);
    req.resume();
}

// ---------- ANA FIRE FONKSİYONU ----------
function fire(code) {
    if (succeeded) return;
    if (!code) return;

    // Buffer'ları hazırla (sadece burada bir kez)
    if (code !== patchCode) buildPatchBufs(code);

    lastFireCode = code;
    lastStatusInfo = { code: null, source: null };
    fireStartTime = performance.now();

    // Başarısızlık durumunda log basmak için timeout (800 ms sonra)
    if (lastFireTimeout) clearTimeout(lastFireTimeout);
    lastFireTimeout = setTimeout(() => {
        if (!succeeded && lastFireCode === code) {
            const statusMsg = lastStatusInfo.code !== null
                ? `, last status: ${lastStatusInfo.code} (${lastStatusInfo.source})`
                : ', no response received';
            console.log(`[FAIL] ${code}${statusMsg}`);
        }
        lastFireTimeout = null;
    }, 800);

    // HTTP/1.1
    v9Pool.fire(code);
    if (v7Pool) v7Pool.fire(code);

    // HTTP/2
    if (USE_HTTP2) {
        const versions = USE_V7 ? ['v9', 'v7'] : ['v9'];
        for (let ipIdx = 0; ipIdx < DISCORD_IPS.length; ipIdx++) {
            for (const ver of versions) {
                sendHttp2Request(ipIdx, code, ver);
            }
        }
    }
}

// ---------- GATEWAY KODU (orijinal, değişmedi) ----------
const B_OP11 = Buffer.from('"op":11');
const B_OP10 = Buffer.from('"op":10');
const B_OP7 = Buffer.from('"op":7');
const B_OP9 = Buffer.from('"op":9');
const B_HB_KEY = Buffer.from('"heartbeat_interval":');
const B_SID_KEY = Buffer.from('"session_id":"');
const B_RUG_KEY = Buffer.from('"resume_gateway_url":"');
const B_SEQ = Buffer.from('"s":');
const B_VAN_FULL = Buffer.from('"vanity_url_code":"');
const B_VAN_NULL = Buffer.from('"vanity_url_code":null');
const B_UNAVAIL = Buffer.from('"unavailable":true');
const B_ID_KEY = Buffer.from('"id":"');
const B_GUILDS_ARR = Buffer.from('"guilds":[');
const B_READY = Buffer.from('"READY"');
const B_GUILD_PFX = Buffer.from('"GUILD_');
const B_D_KEY = Buffer.from('"d":{');
const CC_UPDATE = 85;
const CC_DELETE = 68;
const CC_CREATE = 67;
const OP11_B1 = B_OP11[1];

function extractSeq(buf) {
    const i = buf.indexOf(B_SEQ);
    if (i === -1) return;
    let p = i + 4;
    while (buf[p] === 32) p++;
    if (buf[p] === 110) return;
    let n = 0, ok = false;
    while (p < buf.length && buf[p] >= 48 && buf[p] <= 57) {
        n = n * 10 + buf[p++] - 48;
        ok = true;
    }
    if (ok && n !== lastSeq) {
        lastSeq = n;
        buildHbBuf(n);
    }
}

function extractVanity(buf, dStart) {
    const search = dStart !== undefined ? buf.slice(dStart) : buf;
    if (search.indexOf(B_VAN_NULL) !== -1) return null;
    const i = search.indexOf(B_VAN_FULL);
    if (i === -1) return undefined;
    const s = i + B_VAN_FULL.length;
    const e = search.indexOf(34, s);
    return e === -1 ? undefined : search.latin1Slice(s, e);
}

function extractTopLevelId(buf, dStart) {
    let depth = 1, inStr = false, esc = false;
    let i = dStart + 1;
    while (i < buf.length) {
        const c = buf[i];
        if (esc) { esc = false; i++; continue; }
        if (c === 92 && inStr) { esc = true; i++; continue; }
        if (c === 34) {
            if (!inStr && depth === 1) {
                if (buf[i+1]===105 && buf[i+2]===100 && buf[i+3]===34 &&
                    buf[i+4]===58 && buf[i+5]===34) {
                    const s = i + 6;
                    const e = buf.indexOf(34, s);
                    return e === -1 ? null : buf.latin1Slice(s, e);
                }
            }
            inStr = !inStr;
            i++; continue;
        }
        if (inStr) { i++; continue; }
        if (c === 123 || c === 91) depth++;
        else if (c === 125 || c === 93) { depth--; if (depth === 0) break; }
        i++;
    }
    return null;
}

function parseReadyGuilds(buf) {
    const start = buf.indexOf(B_GUILDS_ARR);
    if (start === -1) return;
    let depth = 0, inStr = false, esc = false;
    let i = start + B_GUILDS_ARR.length - 1, bs = -1;
    while (i < buf.length) {
        const c = buf[i];
        if (esc) { esc = false; i++; continue; }
        if (c === 92 && inStr) { esc = true; i++; continue; }
        if (c === 34) { inStr = !inStr; i++; continue; }
        if (inStr) { i++; continue; }
        if (c === 123) {
            if (!depth) bs = i;
            depth++;
        } else if (c === 125) {
            depth--;
            if (!depth && bs !== -1) {
                const blk = buf.slice(bs, i + 1);
                const ii = blk.indexOf(B_ID_KEY);
                if (ii !== -1) {
                    const s2 = ii + B_ID_KEY.length;
                    const e2 = blk.indexOf(34, s2);
                    if (e2 !== -1) {
                        const gid = blk.latin1Slice(s2, e2);
                        const v = extractVanity(blk, 0) ?? null;
                        guilds.set(gid, v);
                        warmup(v);
                    }
                }
                bs = -1;
            }
        } else if (c === 93 && !depth) break;
        i++;
    }
}

function onEvent(buf) {
    const gi = buf.indexOf(B_GUILD_PFX);
    if (gi !== -1) {
        const typeChar = buf[gi + B_GUILD_PFX.length];

        if (typeChar === CC_UPDATE) {
            const di = buf.indexOf(B_D_KEY);
            if (di === -1) return;
            const dStart = di + B_D_KEY.length - 1;
            const gid = extractTopLevelId(buf, dStart);
            if (!gid) return;
            const prev = guilds.get(gid);
            const curr = extractVanity(buf, dStart);
            if (prev && curr !== prev) fire(prev);
            if (curr !== undefined) { guilds.set(gid, curr); warmup(curr); }
            return;
        }

        if (typeChar === CC_DELETE) {
            if (buf.indexOf(B_UNAVAIL) !== -1) return;
            const di = buf.indexOf(B_D_KEY);
            if (di === -1) return;
            const dStart = di + B_D_KEY.length - 1;
            const gid = extractTopLevelId(buf, dStart);
            if (!gid) return;
            const prev = guilds.get(gid);
            if (prev) fire(prev);
            guilds.delete(gid);
            return;
        }

        if (typeChar === CC_CREATE) {
            const di = buf.indexOf(B_D_KEY);
            if (di === -1) return;
            const dStart = di + B_D_KEY.length - 1;
            const gid = extractTopLevelId(buf, dStart);
            if (!gid) return;
            const v = extractVanity(buf, dStart) ?? null;
            guilds.set(gid, v);
            warmup(v);
            return;
        }
    }

    if (buf.indexOf(B_READY) !== -1) {
        parseReadyGuilds(buf);
    }
}

const IDENTIFY = Buffer.from(JSON.stringify({
    op: 2, d: {
        token: TOKEN, capabilities: 30717,
        properties: {
            os: 'Windows', browser: 'Chrome', device: '',
            system_locale: 'en-US', browser_user_agent: UA,
            browser_version: '131.0.0.0', os_version: '10',
            referrer: '', referring_domain: '',
            referrer_current: '', referring_domain_current: '',
            release_channel: 'stable', client_build_number: 356140,
            client_event_source: null,
        },
        presence: { status: 'online', since: 0, activities: [], afk: false },
        compress: false, client_state: { guild_versions: {} },
    },
}));

function spawnGateway(idx, gen) {
    if (gen !== gwGen) return;
    let sid = null, rug = null, missedAck = false, hb = null;

    const clearHB = () => { if (hb) { clearInterval(hb); hb = null; } };

    const ws = new WebSocket('wss://gateway.discord.gg/?v=9&encoding=json', {
        headers: { 'User-Agent': UA },
        rejectUnauthorized: false,
        perMessageDeflate: false,
        skipUTF8Validation: true,
        maxPayload: 104857600,
    });

    ws.on('message', (buf) => {
        if (buf[1] === OP11_B1 && buf.indexOf(B_OP11) !== -1) {
            missedAck = false;
            return;
        }

        extractSeq(buf);

        if (buf.indexOf(B_OP10) !== -1) {
            let interval = 41250;
            const hi = buf.indexOf(B_HB_KEY);
            if (hi !== -1) {
                let p = hi + B_HB_KEY.length, n = 0, ok = false;
                while (p < buf.length && buf[p] >= 48 && buf[p] <= 57) {
                    n = n * 10 + buf[p++] - 48; ok = true;
                }
                if (ok && n > 0) interval = n;
            }
            clearHB();
            missedAck = false;
            setTimeout(() => {
                if (ws.readyState !== WebSocket.OPEN) return;
                if (missedAck) { ws.terminate(); return; }
                missedAck = true;
                ws.send(hbBuf.subarray(0, hbLen));
            }, (Math.random() * interval) | 0);
            hb = setInterval(() => {
                if (ws.readyState !== WebSocket.OPEN) return;
                if (missedAck) { clearHB(); ws.terminate(); return; }
                missedAck = true;
                ws.send(hbBuf.subarray(0, hbLen));
            }, interval);
            if (sid && rug) {
                ws.send('{"op":6,"d":{"token":"' + TOKEN + '","session_id":"' + sid + '","seq":' + lastSeq + '}}');
            } else {
                ws.send(IDENTIFY);
            }
            return;
        }

        if (buf.indexOf(B_OP7) !== -1 || buf.indexOf(B_OP9) !== -1) {
            if (buf.indexOf(B_OP9) !== -1) { sid = null; rug = null; }
            ws.close();
            return;
        }

        if (buf.indexOf(B_READY) !== -1) {
            const si = buf.indexOf(B_SID_KEY);
            if (si !== -1) {
                const ss = si + B_SID_KEY.length;
                const se = buf.indexOf(34, ss);
                if (se !== -1) sid = buf.latin1Slice(ss, se);
            }
            const ri = buf.indexOf(B_RUG_KEY);
            if (ri !== -1) {
                const rs = ri + B_RUG_KEY.length;
                const re = buf.indexOf(34, rs);
                if (re !== -1) rug = buf.latin1Slice(rs, re);
            }
        }

        onEvent(buf);
    });

    ws.on('close', (code) => {
        clearHB();
        missedAck = false;
        if (gen !== gwGen) return;
        if (code >= 4000 && code < 4015) { sid = null; rug = null; }
        setImmediate(spawnGateway, idx, gen);
    });

    ws.on('error', noop);
}

function startGateways() {
    gwGen++;
    const gen = gwGen;
    for (let i = 0; i < GW_COUNT; i++) spawnGateway(i, gen);
}

// ---------- MFA DOSYA İZLEME ----------
try { mfaToken = readFileSync('mfa.txt', 'utf8').trim(); } catch {}
try {
    watch('mfa.txt', () => {
        try {
            const n = readFileSync('mfa.txt', 'utf8').trim();
            if (n && n !== mfaToken) {
                mfaToken = n;
                patchBufs = { v9: [null, null], v7: [null, null] };
                patchCode = '';
            }
        } catch {}
    });
} catch {}

// ---------- ÖNCELİK AYARI ----------
try {
    if (process.platform === 'win32') {
        const { spawn } = await import('child_process');
        spawn('wmic', ['process', 'where', 'processid=' + process.pid, 'CALL', 'setpriority', '256'], { stdio: 'ignore' });
    } else {
        setPriority(0, -20);
    }
} catch {}

// ---------- BAŞLAT ----------
for (let i = 0; i < REQ_COUNT; i++) {
    v9Pool.sockets[i] = v9Pool.makeSock(i);
    if (v7Pool) v7Pool.sockets[i] = v7Pool.makeSock(i);
}

if (USE_HTTP2) {
    for (let i = 0; i < DISCORD_IPS.length; i++) {
        createHttp2Session(i);
    }
}

startGateways();

process.on('uncaughtException', noop);
process.on('unhandledRejection', noop);
process.on('SIGINT', () => {
    for (const pool of [v9Pool, v7Pool]) {
        if (pool) for (const s of pool.sockets) try { s.destroy(); } catch {}
    }
    if (USE_HTTP2) {
        for (const s of http2Sessions) if (s && !s.destroyed) s.destroy();
        for (const iv of http2PingIntervals) if (iv) clearInterval(iv);
    }
    process.exit(0);
});
