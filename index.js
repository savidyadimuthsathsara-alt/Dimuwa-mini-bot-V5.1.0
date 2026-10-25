"use strict";

const express = require("express");
const cors = require("cors");
const pino = require("pino");
const QRCode = require("qrcode");
const fs = require("fs");
const fsp = require("fs/promises");
const path = require("path");
const https = require("https");
const crypto = require("crypto");
const axios = require("axios");
const FormData = require("form-data");
const { execFile } = require("child_process");
const { promisify } = require("util");
const execFileAsync = promisify(execFile);
const NodeCache = require("node-cache");
const { GoogleGenAI } = require("@google/genai"); 
const yts = require("yt-search");

const {
  default: makeWASocket,
  useMultiFileAuthState,
  DisconnectReason,
  Browsers,
  downloadMediaMessage,
  getContentType,
  normalizeMessageContent,
  fetchLatestWaWebVersion
} = require("@whiskeysockets/baileys");

// ==========================================
// CONFIG
// ==========================================
const PORT = Number(process.env.PORT || 3000);
const DATA_DIR = process.env.DATA_DIR || process.env.RAILWAY_VOLUME_MOUNT_PATH || path.join(__dirname, "data");
const SESSION_DIR = path.join(DATA_DIR, "sessions_new");
const MEDIA_DIR = path.join(DATA_DIR, "media");
const TOOLS_DIR = path.join(DATA_DIR, "tools");

const SETTINGS_FILE = path.join(DATA_DIR, "settings.json");
const STATS_FILE = path.join(DATA_DIR, "stats.json");

const LOG_LEVEL = process.env.LOG_LEVEL || "info";
const LOGO_URL = "https://files.catbox.moe/4yay8z.png";
const MENU_AUDIO_URL = "https://files.catbox.moe/vsl1wg.mp3";
const CREATOR_NAME = "Dimuth Sathsara";

const logger = pino({ level: LOG_LEVEL });
const app = express();
app.use(cors());
app.use(express.json({ limit: "2mb" }));
app.use(express.urlencoded({ extended: true }));
app.use(express.static(__dirname));

for (const dir of [DATA_DIR, SESSION_DIR, MEDIA_DIR, TOOLS_DIR]) {
  fs.mkdirSync(dir, { recursive: true });
}

const DEFAULT_SETTINGS = {
  alwaysOnline: "OFF",
  autoRead: "OFF",
  botMode: "PUBLIC",
  statusRead: "ON",
  statusReact: "GREEN",
  composing: "ON",
  antiDelete: "ON",
  antiDelTarget: "PRIVATE",
  vvTarget: "PRIVATE",
  saveTarget: "PRIVATE",
  dpTarget: "SAME",
  botPower: "ON",
  autoSaveViewOnce: "ON",
  autoReact: "OFF",
  antiSpam: "OFF",
  aiAssistant: "ON",
  codingHelper: "ON",
  songSearch: "ON",
  translator: "ON",
  contactCard: "ON",
  qrGenerator: "ON",
  calculator: "ON",
  aiImage: "ON",
  stickerMaker: "ON",
  textToVoice: "ON",
  reminder: "ON",
  rank: "ON",
  weather: "ON",
  qrReader: "ON",
  currencyConv: "ON",
  mediaInfo: "ON",
  dictionary: "ON",
  bassEffect: "ON",
  uptime: "ON"
};

// ==========================================
// STORAGE & CACHE
// ==========================================
const bots = new Map();
const startingBots = new Map();
const qrStore = new Map();
const pairingStore = new Map();
const messageCache = new Map();
const msgRetryCounterCache = new NodeCache();
const userXP = new Map();

const statusReactList = ["❤️","💚","💙","💛","🤍","🧡","💜","🩷","🔥","😂","😍","😮","👍","🥰","😎","🎉","✨","💯","🙌","🤩","😘","🤗","🌟","💫"];

const MAX_MESSAGE_CACHE = 3000;
const CACHE_TTL = 2 * 60 * 60 * 1000;

// ==========================================
// DB HELPERS
// ==========================================
function readJson(file, fallback) {
  try { if (!fs.existsSync(file)) return fallback; return JSON.parse(fs.readFileSync(file, "utf8")); }
  catch { return fallback; }
}
function writeJson(file, data) {
  try { const temp = `${file}.tmp`; fs.writeFileSync(temp, JSON.stringify(data, null, 2), "utf8"); fs.renameSync(temp, file); } catch {}
}
const settingsDB = readJson(SETTINGS_FILE, {});
const statsDB = readJson(STATS_FILE, {});

function cleanUsername(u) { return String(u||"default").trim().replace(/[^a-zA-Z0-9_-]/g,"_").slice(0,60)||"default"; }
function sessionPath(u) { return path.join(SESSION_DIR, `session_${cleanUsername(u)}`); }

function getSettings(u) {
  const k = cleanUsername(u);
  if (!settingsDB[k]) { settingsDB[k] = { ...DEFAULT_SETTINGS }; writeJson(SETTINGS_FILE, settingsDB); }
  else settingsDB[k] = { ...DEFAULT_SETTINGS, ...settingsDB[k] };
  return settingsDB[k];
}
function saveSettings(u, s) { settingsDB[cleanUsername(u)] = { ...DEFAULT_SETTINGS, ...s }; writeJson(SETTINGS_FILE, settingsDB); }

function getStats(u) {
  const k = cleanUsername(u);
  if (!statsDB[k]) { statsDB[k] = { messages:0, commands:0, downloads:0, startedAt: Date.now(), connectedAt: null, lastSeen: null }; writeJson(STATS_FILE, statsDB); }
  return statsDB[k];
}
function saveStats() { writeJson(STATS_FILE, statsDB); }
function incrementStat(u, field, amount=1) { const s = getStats(u); s[field] = Number(s[field]||0)+amount; saveStats(); }

// ==========================================
// HELPERS & JID FIXES
// ==========================================
function isConnected(sock) { return !!(sock && sock.user && sock.user.id); }
function jidNumber(j) { return String(j||"").split("@")[0].split(":")[0].replace(/\D/g,""); }
function normalizePhone(p) { return String(p||"").replace(/\D/g,"").replace(/^00/,""); }
function isGroupJid(j) { return String(j||"").endsWith("@g.us"); }

function getOwnerJid(sock) {
  if (!sock) return null;
  if (sock.__realOwnerJid) return sock.__realOwnerJid;
  if (!sock.user || !sock.user.id) return null;
  return `${jidNumber(sock.user.id)}@s.whatsapp.net`;
}

function isOwner(sock, msg) {
  const o = getOwnerJid(sock); 
  if (!o) return false;
  if (msg.key?.fromMe) return true;
  return jidNumber(msg.key?.participant || msg.key?.remoteJid) === jidNumber(o);
}

function getMessageText(msg) {
  if (!msg?.message) return "";
  const m = normalizeMessageContent(msg.message) || msg.message;
  return m.conversation || m.extendedTextMessage?.text || m.imageMessage?.caption || m.videoMessage?.caption || m.documentMessage?.caption || "";
}

// ==========================================
// MESSAGE CACHE
// ==========================================
function cacheKey(k) { if (!k||!k.id) return null; return `${k.remoteJid}_${k.id}`; }
function cacheMessage(msg) {
  if (!msg||!msg.key||!msg.message) return;
  const k = cacheKey(msg.key); if (!k) return;
  messageCache.set(k, { message: msg, savedAt: Date.now() });
  if (messageCache.size > MAX_MESSAGE_CACHE) { const f = messageCache.keys().next().value; if (f) messageCache.delete(f); }
}
function getCachedMessage(k) {
  if (!k) return null;
  const ck = cacheKey(k); const item = messageCache.get(ck);
  if (item && Date.now()-item.savedAt <= CACHE_TTL) return item.message;
  return null;
}
setInterval(() => { const n = Date.now(); for (const [k,v] of messageCache) { if (n-v.savedAt > CACHE_TTL) messageCache.delete(k); } }, 10*60*1000);

// ==========================================
// STATUS (FIXED)
// ==========================================
async function handleStatus(username, sock, msg) {
  const s = getSettings(username);
  const participant = msg.key?.participant || msg.key?.remoteJid;
  if (!participant) return;

  if (s.statusRead === "ON") {
    await sock.readMessages([msg.key]).catch(() => {});
  }

  if (s.statusReact !== "OFF") {
    let emoji = "💚";
    if (s.statusReact === "RANDOM") {
      emoji = statusReactList[Math.floor(Math.random() * statusReactList.length)];
    }

    try {
      // FIXED: Removed statusJidList and formatted key correctly
      await sock.sendMessage("status@broadcast", {
        react: { 
          text: emoji, 
          key: {
            remoteJid: "status@broadcast",
            fromMe: false,
            id: msg.key.id,
            participant: participant
          }
        }
      });
      logger.info(`[STATUS REACT] ${emoji} → ${jidNumber(participant)}`);
    } catch (e) {
      logger.error("Status react failed: " + e.message);
    }
  }
}

// ==========================================
// MEDIA HELPERS
// ==========================================
function unwrapViewOnce(msg) {
  if (!msg?.message) return null;
  let m = msg.message;
  if (m.documentWithCaptionMessage) m = m.documentWithCaptionMessage.message;
  if (m.ephemeralMessage) m = m.ephemeralMessage.message;
  if (m.viewOnceMessageV2Extension) m = m.viewOnceMessageV2Extension.message;
  if (m.viewOnceMessageV2) m = m.viewOnceMessageV2.message;
  if (m.viewOnceMessage) m = m.viewOnceMessage.message;
  if (m.viewOnceMessageV3) m = m.viewOnceMessageV3.message;
  if (m.ptvMessage) m = m.ptvMessage;

  const it = getContentType(m); if (!it) return null;
  if (m[it]?.viewOnce) return { type: it, content: m[it], innerMessage: m };
  return null;
}
function isViewOnceMessage(msg) { return !!unwrapViewOnce(msg); }
function getMediaInfo(message) {
  if (!message) return null;
  const m = normalizeMessageContent(message) || message;
  const t = getContentType(m);
  const map = { imageMessage:"image", videoMessage:"video", audioMessage:"audio", documentMessage:"document", stickerMessage:"sticker" };
  if (!map[t]) return null;
  return { type: t, mediaType: map[t], content: m[t] };
}
function getQuotedMessage(msg) {
  if (!msg?.message) return null;
  const m = normalizeMessageContent(msg.message) || msg.message;
  const t = getContentType(m);
  const c = m[t]?.contextInfo;
  if (!c?.quotedMessage || !c?.stanzaId) return null;
  const rJid = c.remoteJid || msg.key.remoteJid;
  const p = c.participant || rJid;
  return { 
    key: { remoteJid: rJid, fromMe: jidNumber(p) === jidNumber(msg.key?.fromMe ? msg.key.remoteJid : null), id: c.stanzaId, participant: p }, 
    message: c.quotedMessage 
  };
}
function buildDownloadMessage(message) {
  const m = normalizeMessageContent(message.message) || message.message || {};
  const t = getContentType(m); const content = t ? m[t] : null;
  const key = { ...(message.key||{}) };
  if (content?.mediaKey) key.mediaKey = content.mediaKey;
  if (content?.directPath) key.directPath = content.directPath;
  if (content?.url) key.url = content.url;
  return { key, message: message.message };
}
async function downloadWhatsAppMedia(sock, message) {
  const info = getMediaInfo(message.message);
  if (!info) throw new Error("Unsupported media.");
  const dlMsg = buildDownloadMessage(message);
  const buffer = await downloadMediaMessage(dlMsg, "buffer", {}, { logger, reuploadRequest: async (m) => sock.updateMediaMessage(m) });
  if (!buffer?.length) throw new Error("Empty media buffer.");
  return { buffer, ...info };
}
async function downloadViewOnceMedia(sock, msg) {
  const vo = unwrapViewOnce(msg); 
  if (!vo) throw new Error("Not view-once.");
  
  const content = vo.content;
  const innerMsg = { key: msg.key, message: msg.message };
  
  if (!content.mediaKey) {
    const m = normalizeMessageContent(msg.message) || msg.message;
    const t = getContentType(m);
    if (m[t]?.mediaKey) content.mediaKey = m[t].mediaKey;
  }

  const buffer = await downloadMediaMessage(innerMsg, "buffer", {}, { logger, reuploadRequest: async (m) => sock.updateMediaMessage(m) });
  
  if (!buffer?.length) throw new Error("Empty view-once buffer.");
  const map = { imageMessage:"image", videoMessage:"video", audioMessage:"audio" };
  return { buffer, mediaType: map[vo.type], type: vo.type, content: vo.content };
}
async function sendWhatsAppMedia(sock, jid, media) {
  const { buffer, mediaType, content } = media;
  const caption = content?.caption || "";
  if (!Buffer.isBuffer(buffer) || !buffer.length) return;
  if (mediaType === "image") await sock.sendMessage(jid, { image: buffer, caption });
  else if (mediaType === "video") await sock.sendMessage(jid, { video: buffer, caption });
  else if (mediaType === "audio") await sock.sendMessage(jid, { audio: buffer, mimetype: content?.mimetype || "audio/mp4", ptt: !!content?.ptt });
  else if (mediaType === "sticker") await sock.sendMessage(jid, { sticker: buffer });
  else if (mediaType === "document") await sock.sendMessage(jid, { document: buffer, mimetype: content?.mimetype || "application/octet-stream", fileName: content?.fileName || "DIMUWA_FILE" });
}

function canProcessMessage(sock, username, msg) {
  const s = getSettings(username);
  if (s.botPower !== "ON") return false;
  const mode = String(s.botMode||"PUBLIC").toUpperCase();
  if (mode === "PUBLIC") return true;
  if (mode === "PRIVATE") return (msg.key?.fromMe || msg.key?.remoteJid === getOwnerJid(sock));
  if (mode === "INBOX") return !isGroupJid(msg.key?.remoteJid);
  return true;
}

async function handleAutoSaveViewOnce(username, sock, msg) {
  try {
    const s = getSettings(username);
    if (s.autoSaveViewOnce !== "ON" || !isViewOnceMessage(msg)) return false;
    
    const owner = getOwnerJid(sock); 
    if (!owner) return false;
    
    const sender = msg.key?.participant || msg.key?.remoteJid;
    if (msg.key?.fromMe === true) return false;
    if (sender && jidNumber(sender) === jidNumber(owner)) return false;
    
    const media = await downloadViewOnceMedia(sock, msg);
    const caption = `🔓 *AUTO-SAVED VIEW ONCE*\n\n👤 From: ${msg.pushName || jidNumber(sender)}\n📱 Number: ${jidNumber(sender)}\n🕐 Time: ${new Date().toLocaleString()}\n\n🤖 DIMUWA MINI BOT V5.4`;
    
    await sendWhatsAppMedia(sock, owner, { ...media, content: { ...media.content, caption } });
    logger.info(`✅ View once saved to Inbox from ${jidNumber(sender)}`);
    return true;
  } catch(e) { 
    logger.error("AutoSave VV Error: "+e.message); 
    return false; 
  }
}

async function handleViewOnce(sock, username, msg) {
  const q = getQuotedMessage(msg);
  if (!q) return sock.sendMessage(msg.key.remoteJid, { text: "❌ Please reply to a View Once media with *" });
  try {
    const media = isViewOnceMessage(q) ? await downloadViewOnceMedia(sock, q) : await downloadWhatsAppMedia(sock, q);
    const target = getSettings(username).vvTarget === "SAME" ? msg.key.remoteJid : getOwnerJid(sock);
    if (!target) throw new Error("No target JID");
    await sendWhatsAppMedia(sock, target, media);
  } catch(e) { await sock.sendMessage(msg.key.remoteJid, { text: `❌ * command failed: ${e.message}` }); }
}

async function handleSave(sock, username, msg) {
  const q = getQuotedMessage(msg) || msg;
  try {
    const media = isViewOnceMessage(q) ? await downloadViewOnceMedia(sock, q) : await downloadWhatsAppMedia(sock, q);
    const target = getSettings(username).saveTarget === "SAME" ? msg.key.remoteJid : getOwnerJid(sock);
    if (!target) throw new Error("No target JID");
    await sendWhatsAppMedia(sock, target, media);
  } catch(e) { await sock.sendMessage(msg.key.remoteJid, { text: `❌ .save failed: ${e.message}` }); }
}

// ==========================================
// GEMINI AI
// ==========================================
const GEMINI_API_KEY = process.env.GEMINI_API_KEY || "";
let geminiClient = null;

function getGeminiClient() {
  if (!GEMINI_API_KEY) throw new Error("GEMINI_API_KEY is not set in Railway Variables.");
  if (!geminiClient) geminiClient = new GoogleGenAI({ apiKey: GEMINI_API_KEY });
  return geminiClient;
}

async function aiChat(query, options = {}) {
  const { mode = "chat", forceModel = null } = options;
  try {
    const ai = getGeminiClient();
    let model = forceModel || (mode === "code" ? "gemini-3.1-pro" : "gemini-3.8-flash");
    let config = { temperature: 0.7, maxOutputTokens: 2048 };

    if (mode === "code") {
      config.systemInstruction = "You are an expert coding assistant. Provide concise answers with working code examples. Always wrap code in triple backticks with the language name.";
      config.temperature = 0.3;
    } else {
      config.systemInstruction = "You are DIMUWA MINI BOT, a friendly WhatsApp assistant. Answer helpfully in the language of the user (Sinhala, English, or Tamil). Keep answers concise unless asked for detail.";
    }

    const response = await ai.models.generateContent({ model: model, contents: query, config: config });
    const text = (response.text || "").trim();
    if (!text) throw new Error("Gemini returned empty response");
    return text.length > 3500 ? text.slice(0, 3400) + "\n\n... [truncated]" : text;
  } catch (e) {
    logger.error("Gemini AI error: " + e.message);
    throw new Error("AI error: " + e.message);
  }
}

// ==========================================
// OTHER COMMAND HELPERS
// ==========================================
async function aiImage(prompt) {
  const seed = Math.floor(Math.random()*1000000);
  // FIXED: New Pollinations endpoint
  const url = `https://gen.pollinations.ai/image/${encodeURIComponent(prompt)}?width=1024&height=1024&nologo=true&seed=${seed}`;
  try {
    const res = await axios.get(url, { responseType: "arraybuffer", timeout: 60000, headers: { "User-Agent": "Mozilla/5.0" } });
    return Buffer.from(res.data);
  } catch (e) {
    logger.error("Pollinations image failed: " + e.message);
    throw new Error("Image generation failed. Please try again.");
  }
}

async function translateText(text, targetLang = "si") {
  const langMap = { si:"sinhala", en:"english", ta:"tamil", hi:"hindi", es:"spanish", fr:"french", de:"german", ja:"japanese", ko:"korean", zh:"chinese", ar:"arabic", ru:"russian", pt:"portuguese", it:"italian", nl:"dutch" };
  const rev = { sinhala:"si", english:"en", tamil:"ta", hindi:"hi", spanish:"es", french:"fr", german:"de", japanese:"ja", korean:"ko", chinese:"zh", arabic:"ar", russian:"ru", portuguese:"pt", italian:"it", dutch:"nl" };
  const tl = rev[targetLang.toLowerCase()] || langMap[targetLang.toLowerCase()] ? (rev[targetLang.toLowerCase()] || targetLang) : targetLang;
  try {
    const url = "https://translate.googleapis.com/translate_a/single";
    const r = await axios.get(url, { params: { client:"gtx", sl:"auto", tl, dt:"t", q:text }, timeout: 20000 });
    if (Array.isArray(r.data?.[0])) return r.data[0].map(x => x[0]).filter(Boolean).join("");
    throw new Error("Bad translate response");
  } catch(e) { throw new Error("Translation failed: "+e.message); }
}

async function getWeather(city) {
  const r = await axios.get("https://wttr.in/"+encodeURIComponent(city)+"?format=j1", { timeout: 20000 });
  const d = r.data;
  const cur = d.current_condition?.[0];
  if (!cur) throw new Error("City not found");
  return { city: d.nearest_area?.[0]?.areaName?.[0]?.value || city, country: d.nearest_area?.[0]?.country?.[0]?.value || "", temp: cur.temp_C, feels: cur.FeelsLikeC, humidity: cur.humidity, desc: cur.weatherDesc?.[0]?.value || "", wind: cur.windspeedKmph };
}

async function defineWord(word) {
  const r = await axios.get(`https://api.dictionaryapi.dev/api/v2/entries/en/${encodeURIComponent(word)}`, { timeout: 20000 });
  const entry = r.data?.[0];
  if (!entry) throw new Error("Word not found");
  const meanings = (entry.meanings || []).slice(0,3).map(m => {
    const defs = (m.definitions || []).slice(0,2).map(d => "• " + d.definition).join("\n");
    return `_${m.partOfSpeech}_\n${defs}`;
  }).join("\n\n");
  return { word: entry.word, phonetic: entry.phonetic || "", meanings };
}

async function convertCurrency(amount, from, to) {
  const r = await axios.get(`https://api.exchangerate-api.com/v4/latest/${from.toUpperCase()}`, { timeout: 20000 });
  const rate = r.data?.rates?.[to.toUpperCase()];
  if (!rate) throw new Error("Currency not supported");
  return { amount, from: from.toUpperCase(), to: to.toUpperCase(), rate, result: (Number(amount) * rate).toFixed(2) };
}

async function generateQR(text) { return await QRCode.toBuffer(text, { margin: 2, width: 500 }); }

async function readQR(buffer) {
  const fd = new FormData();
  fd.append("file", buffer, { filename: "qr.png" });
  const r = await axios.post("https://api.qrserver.com/v1/read-qr-code/", fd, { headers: fd.getHeaders(), timeout: 30000 });
  const data = r.data?.[0]?.symbol?.[0];
  if (!data?.data) throw new Error("QR not detected");
  return data.data;
}

async function makeSticker(sock, msg, mediaBuffer) {
  try {
    const { Sticker, StickerTypes } = require("wa-sticker-formatter");
    const sticker = new Sticker(mediaBuffer, { pack: "DIMUWA", author: "DIMUTH SATHSARA", type: StickerTypes.FULL, quality: 70 });
    return await sticker.toBuffer();
  } catch(e) { throw new Error("Sticker failed: " + e.message); }
}

async function textToVoice(text) {
  const lang = /[\u0D80-\u0DFF]/.test(text) ? "si" : "en";
  const url = `https://translate.google.com/translate_tts?ie=UTF-8&q=${encodeURIComponent(text.slice(0,200))}&tl=${lang}&client=tw-ob`;
  const r = await axios.get(url, { responseType: "arraybuffer", timeout: 30000, headers: { "User-Agent": "Mozilla/5.0" } });
  
  const jobId = crypto.randomBytes(6).toString("hex");
  const inPath = path.join(MEDIA_DIR, `${jobId}_in.mp3`);
  const outPath = path.join(MEDIA_DIR, `${jobId}_out.ogg`);
  
  await fsp.writeFile(inPath, Buffer.from(r.data));
  try {
    await execFileAsync("ffmpeg", ["-y", "-i", inPath, "-c:a", "libopus", "-b:a", "32k", "-vbr", "on", "-compression_level", "10", "-frame_duration", "60", "-application", "voip", outPath], { timeout: 60000 });
    const outBuffer = await fsp.readFile(outPath);
    await fsp.unlink(inPath).catch(()=>{});
    await fsp.unlink(outPath).catch(()=>{});
    return { buffer: outBuffer, lang, mimetype: "audio/ogg; codecs=opus" };
  } catch (e) {
    await fsp.unlink(inPath).catch(()=>{});
    throw new Error("Voice conversion failed: " + e.message);
  }
}

function safeCalc(expr) {
  const cleaned = expr.replace(/[^0-9+\-*/().%\s]/g, "");
  if (!cleaned.trim()) throw new Error("Invalid expression");
  const result = Function(`"use strict";return (${cleaned})`)();
  if (typeof result !== "number" || !isFinite(result)) throw new Error("Invalid result");
  return result;
}

function parseReminderTime(str) {
  const m = str.match(/^(\d+)\s*(s|m|h|d)?$/i);
  if (!m) return null;
  const n = Number(m[1]);
  const unit = (m[2]||"m").toLowerCase();
  const mult = { s:1000, m:60000, h:3600000, d:86400000 }[unit];
  return n * mult;
}

function getRankInfo(xp) {
  const ranks = [
    { name: "🥉 Bronze", min: 0 }, { name: "🥈 Silver", min: 100 },
    { name: "🥇 Gold", min: 500 }, { name: "💎 Platinum", min: 1500 },
    { name: "💠 Diamond", min: 5000 }, { name: "👑 Legendary", min: 15000 }
  ];
  let cur = ranks[0], next = null;
  for (let i=0;i<ranks.length;i++) if (xp >= ranks[i].min) { cur = ranks[i]; next = ranks[i+1] || null; }
  return { rank: cur.name, next: next ? `${next.name} (${next.min} XP)` : "MAX", progress: next ? `${xp - cur.min}/${next.min - cur.min}` : "MAX" };
}

async function applyBassEffect(buffer) {
  const jobId = crypto.randomBytes(6).toString("hex");
  const inPath = path.join(MEDIA_DIR, `${jobId}_in`);
  const outPath = path.join(MEDIA_DIR, `${jobId}_out.mp3`);
  await fsp.writeFile(inPath, buffer);
  try {
    await execFileAsync("ffmpeg", ["-y","-i",inPath,"-af","bass=g=15","-b:a","128k",outPath], { timeout: 120000 });
    const out = await fsp.readFile(outPath);
    await fsp.unlink(inPath).catch(()=>{});
    await fsp.unlink(outPath).catch(()=>{});
    return out;
  } catch(e) { await fsp.unlink(inPath).catch(()=>{}); throw new Error("Bass effect needs ffmpeg installed"); }
}

async function sendContact(sock, jid, name, phone, quoted) {
  const vcard = `BEGIN:VCARD\nVERSION:3.0\nFN:${name}\nTEL;type=CELL;type=VOICE;waid=${normalizePhone(phone)}:+${normalizePhone(phone)}\nEND:VCARD`;
  return await sock.sendMessage(jid, { contacts: { displayName: name, contacts: [{ vcard }] } }, { quoted });
}

// ==========================================
// SETTINGS & MENUS
// ==========================================
function settingsMenu(u) {
  const s = getSettings(u);
  return `╔════════════════════════════════════════╗
║        ⚙️ 𝗕𝗢𝗧 𝗦𝗘𝗧𝗧𝗜𝗡𝗚𝗦 𝗣𝗔𝗡𝗘𝗟 ⚙️         ║
╠════════════════════════════════════════╣
║ ⚠️ 𝗢𝘄𝗻𝗲𝗿 𝗢𝗻𝗹𝘆 | 𝗥𝗲𝗽𝗹𝘆 𝘄𝗶𝘁𝗵 𝗮 𝗰𝗼𝗱𝗲     ║
╠════════════════════════════════════════╣
║ 🌐 𝗣𝗥𝗘𝗦𝗘𝗡𝗖𝗘 & 𝗦𝗖𝗢𝗣𝗘                   ║
║ » Always Online [ ${s.alwaysOnline} ] ➪ 1.1 ON / 1.2 OFF
║ » Auto Read [ ${s.autoRead} ]    ➪ 2.1 ON / 2.2 OFF
║ » Bot Mode [ ${s.botMode} ]  ➪ 3.1 PUB / 3.2 PRI / 3.3 INB
╠════════════════════════════════════════╣
║ ⚡ 𝗦𝗧𝗔𝗧𝗨𝗦 & 𝗔𝗨𝗧𝗢𝗠𝗔𝗧𝗜𝗢𝗡𝗦               ║
║ » Status Read [ ${s.statusRead} ]   ➪ 4.1 ON / 4.2 OFF
║ » Status React [ ${s.statusReact === "RANDOM" ? "RND" : s.statusReact === "GREEN" ? "GRN" : "OFF"} ] ➪ 5.1 GRN / 5.2 RND / 5.3 OFF
║ » Composing [ ${s.composing} ]     ➪ 7.1 ON / 7.2 OFF
║ » Auto React [ ${s.autoReact} ]   ➪ 39.1 ON / 39.2 OFF
║ » Anti-Spam [ ${s.antiSpam} ]    ➪ 40.1 ON / 40.2 OFF
╠════════════════════════════════════════╣
║ 🛡️ 𝗦𝗘𝗖𝗨𝗥𝗜𝗧𝗬                          ║
║ » Anti-Delete [ ${s.antiDelete} ]   ➪ 9.1 ON / 9.2 OFF
║ » Anti-Del Target [ ${s.antiDelTarget === "SAME" ? "CHAT" : "PM"} ]➪ 10.1 CHAT / 10.2 INBOX
║ » .vv Target [ ${s.vvTarget === "SAME" ? "CHAT" : "PM"} ]    ➪ 11.1 CHAT / 11.2 INBOX
║ » .save Target [ ${s.saveTarget === "SAME" ? "CHAT" : "PM"} ]  ➪ 12.1 CHAT / 12.2 INBOX
║ » Bot Power [ ${s.botPower} ]     ➪ 13.1 ON / 13.2 OFF
║ » Auto-Save VV [ ${s.autoSaveViewOnce} ]  ➪ 14.1 ON / 14.2 OFF
╠════════════════════════════════════════╣
║ ✨ 𝗡𝗘𝗪 𝗖𝗢𝗠𝗠𝗔𝗡𝗗𝗦 ( 𝗢𝗡 / 𝗢𝗙𝗙 )          ║
║ » AI Assistant [ ${s.aiAssistant} ]   ➪ 20.1 ON / 20.2 OFF
║ » Coding Helper [ ${s.codingHelper} ]  ➪ 21.1 ON / 21.2 OFF
║ » Song Search [ ${s.songSearch} ]    ➪ 22.1 ON / 22.2 OFF
║ » Translator [ ${s.translator} ]     ➪ 23.1 ON / 23.2 OFF
║ » Contact Card [ ${s.contactCard} ]   ➪ 24.1 ON / 24.2 OFF
║ » QR Generator [ ${s.qrGenerator} ]   ➪ 25.1 ON / 25.2 OFF
║ » Calculator [ ${s.calculator} ]     ➪ 26.1 ON / 26.2 OFF
║ » AI Image [ ${s.aiImage} ]       ➪ 27.1 ON / 27.2 OFF
║ » Sticker Maker [ ${s.stickerMaker} ]  ➪ 28.1 ON / 28.2 OFF
║ » Text to Voice [ ${s.textToVoice} ]  ➪ 29.1 ON / 29.2 OFF
║ » Reminder [ ${s.reminder} ]       ➪ 30.1 ON / 30.2 OFF
║ » Rank [ ${s.rank} ]           ➪ 31.1 ON / 31.2 OFF
║ » Weather [ ${s.weather} ]        ➪ 32.1 ON / 32.2 OFF
║ » QR Reader [ ${s.qrReader} ]      ➪ 33.1 ON / 33.2 OFF
║ » Currency Conv. [ ${s.currencyConv} ] ➪ 34.1 ON / 34.2 OFF
║ » Media Info [ ${s.mediaInfo} ]     ➪ 35.1 ON / 35.2 OFF
║ » Dictionary [ ${s.dictionary} ]     ➪ 36.1 ON / 36.2 OFF
║ » Bass Effect [ ${s.bassEffect} ]    ➪ 37.1 ON / 37.2 OFF
║ » Uptime [ ${s.uptime} ]         ➪ 38.1 ON / 38.2 OFF
╚════════════════════════════════════════╝
© 𝗗𝗜𝗠𝗨𝗧𝗛 𝗦𝗔𝗧𝗛𝗦𝗔𝗥𝗔`;
}

async function processSettingsCode(sock, u, msg, code) {
  if (!isOwner(sock, msg)) return true;
  const s = getSettings(u); let changed = true;
  const set = (k,v) => { s[k] = v; };
  switch(code) {
    case "1.1": case "1.2": set("alwaysOnline","OFF"); break;
    case "2.1": set("autoRead","ON"); break; case "2.2": set("autoRead","OFF"); break;
    case "3.1": set("botMode","PUBLIC"); break; case "3.2": set("botMode","PRIVATE"); break; case "3.3": set("botMode","INBOX"); break;
    case "4.1": set("statusRead","ON"); break; case "4.2": set("statusRead","OFF"); break;
    case "5.1": set("statusReact","GREEN"); break; case "5.2": set("statusReact","RANDOM"); break; case "5.3": set("statusReact","OFF"); break;
    case "7.1": set("composing","ON"); break; case "7.2": set("composing","OFF"); break;
    case "9.1": set("antiDelete","ON"); break; case "9.2": set("antiDelete","OFF"); break;
    case "10.1": set("antiDelTarget","SAME"); break; case "10.2": set("antiDelTarget","PRIVATE"); break;
    case "11.1": set("vvTarget","SAME"); break; case "11.2": set("vvTarget","PRIVATE"); break;
    case "12.1": set("saveTarget","SAME"); break; case "12.2": set("saveTarget","PRIVATE"); break;
    case "13.1": set("botPower","ON"); break; case "13.2": set("botPower","OFF"); break;
    case "14.1": set("autoSaveViewOnce","ON"); break; case "14.2": set("autoSaveViewOnce","OFF"); break;
    case "15.1": set("dpTarget","SAME"); break; case "15.2": set("dpTarget","PRIVATE"); break;
    case "20.1": set("aiAssistant","ON"); break; case "20.2": set("aiAssistant","OFF"); break;
    case "21.1": set("codingHelper","ON"); break; case "21.2": set("codingHelper","OFF"); break;
    case "22.1": set("songSearch","ON"); break; case "22.2": set("songSearch","OFF"); break;
    case "23.1": set("translator","ON"); break; case "23.2": set("translator","OFF"); break;
    case "24.1": set("contactCard","ON"); break; case "24.2": set("contactCard","OFF"); break;
    case "25.1": set("qrGenerator","ON"); break; case "25.2": set("qrGenerator","OFF"); break;
    case "26.1": set("calculator","ON"); break; case "26.2": set("calculator","OFF"); break;
    case "27.1": set("aiImage","ON"); break; case "27.2": set("aiImage","OFF"); break;
    case "28.1": set("stickerMaker","ON"); break; case "28.2": set("stickerMaker","OFF"); break;
    case "29.1": set("textToVoice","ON"); break; case "29.2": set("textToVoice","OFF"); break;
    case "30.1": set("reminder","ON"); break; case "30.2": set("reminder","OFF"); break;
    case "31.1": set("rank","ON"); break; case "31.2": set("rank","OFF"); break;
    case "32.1": set("weather","ON"); break; case "32.2": set("weather","OFF"); break;
    case "33.1": set("qrReader","ON"); break; case "33.2": set("qrReader","OFF"); break;
    case "34.1": set("currencyConv","ON"); break; case "34.2": set("currencyConv","OFF"); break;
    case "35.1": set("mediaInfo","ON"); break; case "35.2": set("mediaInfo","OFF"); break;
    case "36.1": set("dictionary","ON"); break; case "36.2": set("dictionary","OFF"); break;
    case "37.1": set("bassEffect","ON"); break; case "37.2": set("bassEffect","OFF"); break;
    case "38.1": set("uptime","ON"); break; case "38.2": set("uptime","OFF"); break;
    case "39.1": set("autoReact","ON"); break; case "39.2": set("autoReact","OFF"); break;
    case "40.1": set("antiSpam","ON"); break; case "40.2": set("antiSpam","OFF"); break;
    default: changed = false;
  }
  if (changed) {
    saveSettings(u, s);
    await sock.sendMessage(msg.key.remoteJid, { text: `✅ SETTING UPDATED: *${code}*` });
    return true;
  }
  return false;
}

function menuText(u) {
  const s = getSettings(u);
  return `👋 𝗗𝗜𝗠𝗨𝗪𝗔 𝗠𝗜𝗡𝗜 𝗕𝗢𝗧 𝗩𝟱.𝟰 🤖 👑

╭─── « 👨‍💻 𝗖𝗥𝗘𝗔𝗧𝗢𝗥 𝗜𝗡𝗙𝗢 » ───⬣
│ 👨‍💻 𝗖𝗿𝗲𝗮𝘁𝗼𝗿 : Dimuth Sathsara
│ ⚙️ 𝗣𝗿𝗲𝗳𝗶𝘅  : [ . ]
╰───────────────────────────⬣

╭─── « 🤖 𝗕𝗢𝗧 𝗦𝗧𝗔𝗧𝗨𝗦 » ─────⬣
│ 🟢 𝗦𝘁𝗮𝘁𝘂𝘀 : Online
│ ⚙️ 𝗠𝗼𝗱𝗲   : ${s.botMode}
│ 🔓 𝗔𝘂𝘁𝗼 𝗩𝗩 : ${s.autoSaveViewOnce}
╰───────────────────────────⬣

╭─── « 📁 𝗠𝗔𝗜𝗡 𝗠𝗘𝗡𝗨 » ──────⬣
│ 1️⃣ 📥 DOWNLOAD MEDIA
│ 2️⃣ ⚙️ SETTINGS MENU
│ 3️⃣ 👑 OWNER COMMANDS
│ 4️⃣ 🛠️ UTILITY COMMANDS
│ 5️⃣ 🎮 FUN COMMANDS
│ 6️⃣ 👥 GROUP COMMANDS
│ 7️⃣ 👤 NORMAL USER CMDS
│ 8️⃣ ✨ NEW COMMANDS
│ 9️⃣ 📚 ALL COMMANDS HELP
╰───────────────────────────⬣
💡 𝘛𝘺𝘱𝘦 𝘰𝘳 𝘳𝘦𝘱𝘭𝘺 𝘢 𝘯𝘶𝘮𝘣𝘦𝘳 (1-9)!`;
}

async function sendMenu(sock, u, jid, msg) {
  try { await sock.sendMessage(jid, { image: { url: LOGO_URL }, caption: menuText(u) }, { quoted: msg }); }
  catch { await sock.sendMessage(jid, { text: menuText(u) }, { quoted: msg }); }
  try { await sock.sendMessage(jid, { audio: { url: MENU_AUDIO_URL }, mimetype: "audio/mpeg", ptt: false }); } catch {}
}

// ==========================================
// ALIVE COMMAND
// ==========================================
async function sendAlive(sock, username, jid, msg) {
  const s = getSettings(username);
  const st = getStats(username);
  const upSec = st.connectedAt ? Math.floor((Date.now() - st.connectedAt) / 1000) : 0;
  const d = Math.floor(upSec / 86400);
  const h = Math.floor((upSec % 86400) / 3600);
  const m = Math.floor((upSec % 3600) / 60);
  const sec = upSec % 60;
  const ramMB = (process.memoryUsage().rss / 1024 / 1024).toFixed(1);
  const phone = jidNumber(getOwnerJid(sock));

  const caption = `👋 𝗗𝗜𝗠𝗨𝗪𝗔 𝗠𝗜𝗡𝗜 𝗕𝗢𝗧 𝗩𝟱.𝟰 🤖 👑

╭─── « 🟢 𝗕𝗢𝗧 𝗔𝗟𝗜𝗩𝗘 » ───⬣
│ 🟢 𝗦𝘁𝗮𝘁𝘂𝘀   : Online ✅
│ ⚙️ 𝗠𝗼𝗱𝗲     : ${s.botMode}
│ 🔓 𝗔𝘂𝘁𝗼 𝗩𝗩  : ${s.autoSaveViewOnce}
│ 🛡️ 𝗔𝗻𝘁𝗶-𝗗𝗲𝗹 : ${s.antiDelete}
╰───────────────────────────⬣

╭─── « 📊 𝗦𝗬𝗦𝗧𝗘𝗠 » ───⬣
│ ⏱️ 𝗨𝗽𝘁𝗶𝗺𝗲  : ${d}d ${h}h ${m}m ${sec}s
│ 💾 𝗥𝗔𝗠     : ${ramMB} MB
│ 📨 𝗠𝘀𝗴𝘀    : ${st.messages}
│ ⚙️ 𝗖𝗺𝗱𝘀    : ${st.commands}
│ 📥 𝗗𝗼𝘄𝗻𝗹𝗱𝘀 : ${st.downloads}
╰───────────────────────────⬣

╭─── « 👨‍💻 𝗖𝗥𝗘𝗔𝗧𝗢𝗥 » ───⬣
│ 👨‍💻 𝗡𝗮𝗺𝗲   : Dimuth Sathsara
│ ⚙️ 𝗣𝗿𝗲𝗳𝗶𝘅 : [ . ]
│ 📱 𝗢𝘄𝗻𝗲𝗿  : wa.me/${phone}
╰───────────────────────────⬣

╭─── « 📚 𝗠𝗔𝗜𝗡 𝗖𝗠𝗗𝗦 » ───⬣
│ 🔹 .menu    ➪ Main menu (1-9)
│ 🔹 .alive   ➪ Bot status
│ 🔹 .ping    ➪ Response speed
│ 🔹 .settings➪ Settings panel
│ 🔹 .vv      ➪ Save view-once
│ 🔹 .save    ➪ Save media
│ 🔹 .dp      ➪ Profile picture
╰───────────────────────────⬣

╭─── « 📥 𝗗𝗢𝗪𝗡𝗟𝗢𝗔𝗗𝗘𝗥 » ───⬣
│ ❖ 🎵 𝗧𝗶𝗸𝗧𝗼𝗸
│ ❖ 📘 𝗙𝗮𝗰𝗲𝗯𝗼𝗼𝗸
│ ❖ 🎬 𝗬𝗼𝘂𝗧𝘂𝗯𝗲
│ 💡 Send any URL to download!
╰───────────────────────────⬣

╭─── « ✨ 𝗡𝗘𝗪 𝗖𝗢𝗠𝗠𝗔𝗡𝗗𝗦 » ───⬣
│ 🤖 .ai       💻 .code
│ 🎵 .song     🌍 .translate
│ 📇 .contact  🔳 .qr
│ 🧮 .calc     🎨 .imagine
│ 🧩 .sticker  🗣️ .voice
│ ⏰ .remind   🏆 .rank
│ 🌤️ .weather  📷 .readqr
│ 💱 .convert  ℹ️ .media
│ 📖 .define   🔊 .bass
│ ⏱️ .uptime
╰───────────────────────────⬣

💡 Type .menu to see all options
© 𝗗𝗜𝗠𝗨𝗧𝗛 𝗦𝗔𝗧𝗛𝗦𝗔𝗥𝗔`;

  try { await sock.sendMessage(jid, { image: { url: LOGO_URL }, caption }, { quoted: msg }); }
  catch { await sock.sendMessage(jid, { text: caption }, { quoted: msg }); }

  try {
    const audioRes = await axios.get(MENU_AUDIO_URL, { responseType: "arraybuffer", timeout: 20000 });
    await sock.sendMessage(jid, { 
      audio: Buffer.from(audioRes.data), 
      mimetype: "audio/mpeg", 
      ptt: false 
    });
  } catch (e) {
    logger.warn("Alive audio failed: " + e.message);
  }
}

// ==========================================
// MENU BUTTONS (1-9)
// ==========================================
async function handleMenuNumber(sock, username, jid, num, msg) {
  if (num === "1") {
    await sock.sendMessage(jid, { text: `╭─── « 📥 𝗗𝗢𝗪𝗡𝗟𝗢𝗔𝗗 𝗠𝗘𝗡𝗨 » ───⬣
│ ❖ 🎵 𝗧𝗶𝗸𝗧𝗼𝗸
│ ❖ 📘 𝗙𝗮𝗰𝗲𝗯𝗼𝗼𝗸
│ ❖ 🎬 𝗬𝗼𝘂𝗧𝘂𝗯𝗲
╰───────────────────────────⬣
💡 𝘚𝘪𝘮𝘱𝘭𝘺 𝘴𝘦𝘯𝘥 𝘢𝘯𝘺 𝘛𝘪𝘬𝘛𝘰𝘬, 𝘍𝘢𝘤𝘦𝘣𝘰𝘰𝘬,
𝘰𝘳 𝘠𝘰𝘶𝘛𝘶𝘣𝘦 𝘜𝘙𝘓 𝘵𝘰 𝘥𝘰𝘸𝘯𝘭𝘰𝘢𝘥 𝘝𝘪𝘥𝘦𝘰,
𝘈𝘶𝘥𝘪𝘰, 𝘰𝘳 𝘐𝘮𝘢𝘨𝘦𝘴! 🚀` }, { quoted: msg });
    return true;
  }
  if (num === "2") { await sock.sendMessage(jid, { text: settingsMenu(username) }, { quoted: msg }); return true; }
  if (num === "3") {
    if (!isOwner(sock, msg)) { await sock.sendMessage(jid, { text: "❌ Owner only." }, { quoted: msg }); return true; }
    await sock.sendMessage(jid, { text: `👑 *𝗢𝗪𝗡𝗘𝗥 𝗖𝗢𝗠𝗠𝗔𝗡𝗗𝗦* 👑
━━━━━━━━━━━━━━━━━━━━
» 👤 .dp ➪ Get a profile picture
» ⚙️ .settings ➪ Change bot settings` }, { quoted: msg });
    return true;
  }
  if (num === "4") {
    await sock.sendMessage(jid, { text: `┌──「 🛠️ UTILITY COMMANDS 」──┐
│ 🔓 .vv / .viewonce ➪ Save or resend VV
│ 💾 .save ➪ Save replied media
│ ℹ️ .media ➪ Show media details
└───────────────────────────┘` }, { quoted: msg });
    return true;
  }
  if (num === "5") {
    await sock.sendMessage(jid, { text: `╭─── « 🎮 𝗙𝗨𝗡 𝗖𝗢𝗠𝗠𝗔𝗡𝗗𝗦 » ───⬣
│ 🎲 .dice ➪ Roll dice
│ 🎯 .random ➪ Random number
│ 💕 .love ➪ Love percentage
╰──────────────────────────⬣` }, { quoted: msg });
    return true;
  }
  if (num === "6") {
    await sock.sendMessage(jid, { text: `╭─── « 👥 𝗚𝗥𝗢𝗨𝗣 𝗖𝗢𝗠𝗠𝗔𝗡𝗗𝗦 » ───⬣
│ ✦ 🛡️ .antispam <on/off> ➪ Warn spam
│ ✦ 🏆 .rank ➪ Show group XP & rank
╰──────────────────────────────⬣` }, { quoted: msg });
    return true;
  }
  if (num === "7") {
    await sock.sendMessage(jid, { text: `👤 *NORMAL USER COMMANDS*
.ping, .alive, .menu, .vv, .save, .media
.ai, .code, .song, .translate, .contact
.qr, .calc, .imagine, .voice, .remind
.rank, .weather, .readqr, .convert
.define, .bass, .uptime` }, { quoted: msg });
    return true;
  }
  if (num === "8") {
    await sock.sendMessage(jid, { text: `✨ *𝗡𝗘𝗪 𝗖𝗢𝗠𝗠𝗔𝗡𝗗𝗦* ✨
━━━━━━━━━━━━━━━━━
» 🤖 .ai <query> ➪ AI assistant
» 💻 .code <query> ➪ Coding help
» 🎵 .song <name> ➪ Search songs
» 🌍 .translate <lang> <txt> ➪ Translate
» 📇 .contact <name,num> ➪ Contact card
» ⚡ .autoreact <on/off> ➪ Auto react
» 🔳 .qr <text> ➪ Create QR code
» 🧮 .calc <math> ➪ Calculator
» 🎨 .imagine <prompt> ➪ AI image gen.
» 🧩 .stickerpack ➪ Create sticker
» 🗣️ .voice <text> ➪ Text to voice
» ⏰ .remind <time> <txt> ➪ Set reminder
» 🏆 .rank ➪ Show rank & XP
» 🌤️ .weather <city> ➪ Show weather
» 📷 .readqr ➪ Read QR from image
» 💱 .convert <amt> <fr> <to> ➪ Currency
» ℹ️ .media ➪ Show media details
» 🛡️ .antispam <on/off> ➪ Anti-spam
» 📖 .define <word> ➪ Dictionary
» 🔊 .bass ➪ Bass effect media
» ⏱️ .uptime ➪ Runtime & memory` }, { quoted: msg });
    return true;
  }
  if (num === "9") {
    await sock.sendMessage(jid, { text: `╔════════════════════════════════════════╗
║          📚 𝗔𝗟𝗟 𝗖𝗢𝗠𝗠𝗔𝗡𝗗𝗦 𝗟𝗜𝗦𝗧 📚       ║
╠════════════════════════════════════════╣
║ 📌 𝗚𝗘𝗡𝗘𝗥𝗔𝗟 𝗖𝗢𝗠𝗠𝗔𝗡𝗗𝗦                    ║
║ » .ping, .menu, .help, .settings         ║
║ » .alive, .vv, .save, .dp                ║
║ » .tt / .fb / .yt (URLs)                ║
╠════════════════════════════════════════╣
║ ✨ 𝗡𝗘𝗪 𝗖𝗢𝗠𝗠𝗔𝗡𝗗𝗦                        ║
║ » .ai, .code, .song, .translate          ║
║ » .contact, .autoreact, .qr, .calc       ║
║ » .imagine, .stickerpack, .voice         ║
║ » .remind, .rank, .weather, .readqr      ║
║ » .convert, .media, .antispam, .define   ║
║ » .bass, .uptime                         ║
╚════════════════════════════════════════╝
💡 Use .settings to toggle each command ON/OFF.
© 𝗗𝗜𝗠𝗨𝗧𝗛 𝗦𝗔𝗧𝗛𝗦𝗔𝗥𝗔` }, { quoted: msg });
    return true;
  }
  return false;
}

// ==========================================
// YT-DLP DOWNLOADER
// ==========================================
function isSupportedUrl(url) { return /tiktok|youtube|youtu\.be|facebook|fb\./i.test(url); }

async function ensureYtDlp() {
  const binary = path.join(TOOLS_DIR, "yt-dlp");
  if (fs.existsSync(binary)) {
    const age = (Date.now() - fs.statSync(binary).mtimeMs) / (1000*60*60);
    if (age < 24) return binary;
  }
  const arch = process.arch === "arm64" ? "_aarch64" : "";
  const url = `https://github.com/yt-dlp/yt-dlp/releases/latest/download/yt-dlp_linux${arch}`;
  await new Promise((resolve, reject) => {
    const dl = (u, depth=0) => {
      if (depth > 5) return reject(new Error("Too many redirects"));
      https.get(u, { headers: { "User-Agent":"DIMUWA" } }, (res) => {
        const c = res.statusCode || 0;
        if ([301,302,303,307,308].includes(c) && res.headers.location) { res.resume(); return dl(res.headers.location, depth+1); }
        if (c !== 200) { res.resume(); return reject(new Error(`HTTP ${c}`)); }
        const f = fs.createWriteStream(binary);
        res.pipe(f);
        f.on("finish", () => f.close(() => resolve()));
        f.on("error", reject);
      }).on("error", reject);
    };
    dl(url);
  });
  await fsp.chmod(binary, 0o755);
  return binary;
}

async function downloadSocialMedia(username, url, type) {
  const ytDlp = await ensureYtDlp();
  const jobId = crypto.randomBytes(8).toString("hex");
  const outputTemplate = path.join(MEDIA_DIR, `${jobId}.%(ext)s`);

  let formatArgs, postArgs = [];
  if (type === "audio") {
    formatArgs = ["-f", "bestaudio[ext=m4a]/bestaudio/best[ext=m4a]/best"];
    postArgs = ["--extract-audio", "--audio-format", "mp3", "--audio-quality", "128K"];
  } else if (/youtube|youtu\.be/i.test(url)) {
    formatArgs = ["-f", "best[ext=mp4]/best[height<=720]/best"];
  } else if (/facebook|fb\./i.test(url)) {
    formatArgs = ["-f", "best[ext=mp4]/best"];
  } else {
    formatArgs = ["-f", "best"];
  }

  const baseArgs = [
    "--no-warnings","--no-playlist","--restrict-filenames",
    "--no-check-certificates","--geo-bypass",
    "--socket-timeout","30","--retries","3","--max-filesize","100M",
    "--extractor-args","youtube:player_client=ios,android,web",
    "--user-agent","Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/120.0.0.0 Safari/537.36",
    ...formatArgs,
    "-o", outputTemplate,
    "--print","after_move:filepath",
    url
  ];

  let res;
  try { res = await execFileAsync(ytDlp, [...baseArgs, ...postArgs], { timeout: 300000, maxBuffer: 10*1024*1024 }); }
  catch {
    try { res = await execFileAsync(ytDlp, baseArgs, { timeout: 300000, maxBuffer: 10*1024*1024 }); }
    catch (e2) { logger.error("yt-dlp error: " + (e2.stderr || e2.message)); throw new Error("Download failed. Link may be private/unsupported."); }
  }

  const candidates = String(res.stdout || "").split(/\r?\n/).map(x=>x.trim()).filter(Boolean);
  let file = candidates.length ? candidates[candidates.length-1] : null;
  if (file && fs.existsSync(file)) return file;

  const files = await fsp.readdir(MEDIA_DIR);
  const match = files.find(x => x.startsWith(jobId));
  if (match) return path.join(MEDIA_DIR, match);
  if (type === "audio") {
    const am = files.find(x => x.startsWith(jobId) && /\.(mp3|m4a|webm|opus|aac|ogg)$/i.test(x));
    if (am) return path.join(MEDIA_DIR, am);
  }
  throw new Error("File not found after download");
}

async function executeDownload(sock, username, msg, url, type) {
  const jid = msg.key.remoteJid;
  try {
    await sock.sendMessage(jid, { text: `⏳ Downloading ${type.toUpperCase()}...\nPlease wait.` }, { quoted: msg });
    const dlType = type === "audio" ? "audio" : "video";
    const file = await downloadSocialMedia(username, url, dlType);
    const ext = path.extname(file).toLowerCase();
    const buffer = await fsp.readFile(file);

    if (type === "audio" || [".mp3",".m4a",".aac",".webm",".opus",".ogg"].includes(ext)) {
      const mimetype = ext === ".mp3" ? "audio/mpeg" : ext === ".m4a" ? "audio/mp4" : "audio/mpeg";
      await sock.sendMessage(jid, { audio: buffer, mimetype, ptt: false }, { quoted: msg });
    } else if (type === "image" || [".jpg",".jpeg",".png",".webp"].includes(ext)) {
      try { await sock.sendMessage(jid, { image: buffer, caption: "✅ DIMUWA IMAGE" }, { quoted: msg }); }
      catch { await sock.sendMessage(jid, { video: buffer, caption: "✅ DIMUWA MEDIA" }, { quoted: msg }); }
    } else {
      await sock.sendMessage(jid, { video: buffer, mimetype: "video/mp4", caption: "✅ DIMUWA VIDEO" }, { quoted: msg });
    }
    await fsp.unlink(file).catch(()=>{});
    incrementStat(username, "downloads");
  } catch(e) {
    logger.error("Download failed: " + e.message);
    await sock.sendMessage(jid, { text: `❌ Download failed: ${e.message}` }, { quoted: msg });
  }
}

// ==========================================
// ANTI-DELETE
// ==========================================
async function handleDeletedMessages(username, sock, deletedKeys) {
  const s = getSettings(username);
  if (s.antiDelete !== "ON" || !Array.isArray(deletedKeys)) return;
  
  for (const key of deletedKeys) {
    try {
      const cached = getCachedMessage(key); 
      if (!cached) continue;
      
      const target = s.antiDelTarget === "SAME" ? key.remoteJid : getOwnerJid(sock);
      if (!target) continue;

      const t = getMessageText(cached);
      const media = getMediaInfo(cached.message);
      const sender = jidNumber(key.participant || key.remoteJid);

      if (media) {
        try {
          const dm = await downloadWhatsAppMedia(sock, cached);
          await sendWhatsAppMedia(sock, target, { 
            ...dm, 
            content: { ...dm.content, caption: `🗑️ *DELETED MEDIA*\n👤 From: ${sender}\n\n${dm.content?.caption || ""}` } 
          });
        } catch { 
          await sock.sendMessage(target, { text: `🗑️ *DELETED MEDIA*\n👤 From: ${sender}` }); 
        }
      } else if (t) {
        await sock.sendMessage(target, { text: `🗑️ *DELETED MSG*\n👤 From: ${sender}\n\n${t}` });
      } else {
        try { await sock.sendMessage(target, { forward: cached }); } catch {}
      }
    } catch (e) {
      logger.error("AntiDelete error: " + e.message);
    }
  }
}

// ==========================================
// NEW COMMANDS HANDLERS
// ==========================================
async function handleNewCommands(sock, username, msg, cmd, args, text) {
  const s = getSettings(username);
  const jid = msg.key.remoteJid;

  if (cmd === ".ai") {
    if (s.aiAssistant !== "ON") return false;
    const q = text.slice(3).trim();
    if (!q) { await sock.sendMessage(jid, { text: "❌ Usage: .ai <question>" }, { quoted: msg }); return true; }
    await sock.sendMessage(jid, { text: "🤖 Thinking..." }, { quoted: msg });
    try { const r = await aiChat(q, { mode: "chat" }); await sock.sendMessage(jid, { text: `🤖 *AI Answer:*\n\n${r}` }, { quoted: msg }); }
    catch(e) { await sock.sendMessage(jid, { text: `❌ ${e.message}` }, { quoted: msg }); }
    return true;
  }
  
  if (cmd === ".code") {
    if (s.codingHelper !== "ON") return false;
    const q = text.slice(5).trim();
    if (!q) { await sock.sendMessage(jid, { text: "❌ Usage: .code <question>" }, { quoted: msg }); return true; }
    await sock.sendMessage(jid, { text: "💻 Thinking..." }, { quoted: msg });
    try { const r = await aiChat(q, { mode: "code" }); await sock.sendMessage(jid, { text: `💻 *Code Help:*\n\n${r}` }, { quoted: msg }); }
    catch(e) { await sock.sendMessage(jid, { text: `❌ ${e.message}` }, { quoted: msg }); }
    return true;
  }

  if (cmd === ".song") {
    if (s.songSearch !== "ON") return false;
    const q = text.slice(5).trim();
    if (!q) { await sock.sendMessage(jid, { text: "❌ Usage: .song <name>" }, { quoted: msg }); return true; }
    
    await sock.sendMessage(jid, { text: "🔍 Searching..." }, { quoted: msg });
    try {
      const search = await yts(q);
      const video = search.videos[0];
      if (!video) throw new Error("No results found.");

      const caption = `🎵 *DIMUWA SONG SEARCH* 🎵\n\n📌 *Title:* ${video.title}\n👤 *Channel:* ${video.author.name}\n⏱ *Duration:* ${video.timestamp}\n👀 *Views:* ${video.views}\n\n🔗 URL: ${video.url}\n\n*Reply with a number:*\n\n1️⃣ Audio (MP3)\n2️⃣ Video (MP4)\n\n🤖 DIMUWA MINI BOT V5.4`;
      
      await sock.sendMessage(jid, { image: { url: video.thumbnail }, caption: caption }, { quoted: msg });
    } catch(e) { 
      await sock.sendMessage(jid, { text: `❌ Search failed: ${e.message}` }, { quoted: msg }); 
    }
    return true;
  }

  if (cmd === ".translate") {
    if (s.translator !== "ON") return false;
    const parts = text.split(/\s+/);
    const lang = parts[1];
    if (!lang) { await sock.sendMessage(jid, { text: "❌ Usage:\n.translate <lang> <text>\nහෝ\nMessage එකකට reply කරලා .translate <lang> දාන්න" }, { quoted: msg }); return true; }

    let body = text.slice(10 + lang.length).trim();
    const quoted = getQuotedMessage(msg);
    if (!body && quoted) body = getMessageText(quoted).trim();

    if (!body) { await sock.sendMessage(jid, { text: "❌ පරිවර්තනය කරන්න text එකක් නෑ." }, { quoted: msg }); return true; }

    await sock.sendMessage(jid, { text: "🌍 Translating..." }, { quoted: msg });
    try {
      const r = await translateText(body, lang);
      await sock.sendMessage(jid, { text: `🌍 *Translation (${lang})*\n\n${r}` }, { quoted: msg });
    } catch(e) { await sock.sendMessage(jid, { text: `❌ ${e.message}` }, { quoted: msg }); }
    return true;
  }

  if (cmd === ".contact") {
    if (s.contactCard !== "ON") return false;
    const parts = text.slice(8).trim().split(",");
    if (parts.length < 2) { await sock.sendMessage(jid, { text: "❌ Usage: .contact <name>,<number>" }, { quoted: msg }); return true; }
    try { await sendContact(sock, jid, parts[0].trim(), parts[1].trim(), msg); }
    catch(e) { await sock.sendMessage(jid, { text: `❌ ${e.message}` }, { quoted: msg }); }
    return true;
  }

  if (cmd === ".autoreact") {
    const arg = args[1]?.toLowerCase();
    if (!["on","off"].includes(arg)) { await sock.sendMessage(jid, { text: "❌ Usage: .autoreact <on/off>" }, { quoted: msg }); return true; }
    s.autoReact = arg === "on" ? "ON" : "OFF";
    saveSettings(username, s);
    await sock.sendMessage(jid, { text: `✅ Auto-React: *${s.autoReact}*` }, { quoted: msg });
    return true;
  }

  if (cmd === ".qr") {
    if (s.qrGenerator !== "ON") return false;
    const q = text.slice(3).trim();
    if (!q) { await sock.sendMessage(jid, { text: "❌ Usage: .qr <text>" }, { quoted: msg }); return true; }
    try { const buf = await generateQR(q); await sock.sendMessage(jid, { image: buf, caption: "🔳 QR Generated" }, { quoted: msg }); }
    catch(e) { await sock.sendMessage(jid, { text: `❌ ${e.message}` }, { quoted: msg }); }
    return true;
  }

  if (cmd === ".calc") {
    if (s.calculator !== "ON") return false;
    const expr = text.slice(5).trim();
    if (!expr) { await sock.sendMessage(jid, { text: "❌ Usage: .calc <math>" }, { quoted: msg }); return true; }
    try { const r = safeCalc(expr); await sock.sendMessage(jid, { text: `🧮 *Result:* ${r}` }, { quoted: msg }); }
    catch(e) { await sock.sendMessage(jid, { text: `❌ ${e.message}` }, { quoted: msg }); }
    return true;
  }

  if (cmd === ".imagine") {
    if (s.aiImage !== "ON") return false;
    const p = text.slice(8).trim();
    if (!p) { await sock.sendMessage(jid, { text: "❌ Usage: .imagine <prompt>" }, { quoted: msg }); return true; }
    await sock.sendMessage(jid, { text: "🎨 Generating image..." }, { quoted: msg });
    try { const buf = await aiImage(p); await sock.sendMessage(jid, { image: buf, caption: `🎨 ${p}` }, { quoted: msg }); }
    catch(e) { await sock.sendMessage(jid, { text: `❌ ${e.message}` }, { quoted: msg }); }
    return true;
  }

  if (cmd === ".stickerpack" || cmd === ".sticker") {
    if (s.stickerMaker !== "ON") return false;
    const q = getQuotedMessage(msg) || msg;
    try {
      const media = await downloadWhatsAppMedia(sock, q);
      if (!["image","sticker"].includes(media.mediaType)) throw new Error("Reply to an image");
      const stickerBuf = await makeSticker(sock, msg, media.buffer);
      await sock.sendMessage(jid, { sticker: stickerBuf }, { quoted: msg });
    } catch(e) { await sock.sendMessage(jid, { text: `❌ ${e.message}` }, { quoted: msg }); }
    return true;
  }

  if (cmd === ".voice") {
    if (s.textToVoice !== "ON") return false;
    const t = text.slice(6).trim();
    if (!t) { await sock.sendMessage(jid, { text: "❌ Usage: .voice <text>" }, { quoted: msg }); return true; }
    await sock.sendMessage(jid, { text: "🎙️ Converting text to voice..." }, { quoted: msg });
    try { 
      const r = await textToVoice(t); 
      await sock.sendMessage(jid, { audio: r.buffer, mimetype: r.mimetype, ptt: true }, { quoted: msg }); 
    }
    catch(e) { await sock.sendMessage(jid, { text: `❌ ${e.message}` }, { quoted: msg }); }
    return true;
  }

  if (cmd === ".remind") {
    if (s.reminder !== "ON") return false;
    const parts = text.slice(7).trim().split(/\s+/);
    const timeStr = parts[0]; const body = parts.slice(1).join(" ");
    const ms = parseReminderTime(timeStr);
    if (!ms || !body) { await sock.sendMessage(jid, { text: "❌ Usage: .remind <time> <text>\nExample: .remind 5m Drink water" }, { quoted: msg }); return true; }
    setTimeout(async () => { try { await sock.sendMessage(jid, { text: `⏰ *Reminder:*\n\n${body}` }); } catch {} }, ms);
    await sock.sendMessage(jid, { text: `✅ Reminder set in ${timeStr}` }, { quoted: msg });
    return true;
  }

  if (cmd === ".rank") {
    if (s.rank !== "ON") return false;
    const u = msg.key.participant || msg.key.remoteJid;
    const xp = (userXP.get(u) || { xp: 0 }).xp;
    const info = getRankInfo(xp);
    await sock.sendMessage(jid, { text: `🏆 *RANK INFO*\n\n👤 User: ${jidNumber(u)}\n⭐ XP: ${xp}\n🎖 Rank: ${info.rank}\n📈 Progress: ${info.progress}\n🎯 Next: ${info.next}` }, { quoted: msg });
    return true;
  }

  if (cmd === ".weather") {
    if (s.weather !== "ON") return false;
    const city = text.slice(9).trim();
    if (!city) { await sock.sendMessage(jid, { text: "❌ Usage: .weather <city>" }, { quoted: msg }); return true; }
    try { const w = await getWeather(city); await sock.sendMessage(jid, { text: `🌤 *WEATHER — ${w.city}, ${w.country}*\n\n🌡 Temp: ${w.temp}°C (feels ${w.feels}°C)\n💧 Humidity: ${w.humidity}%\n💨 Wind: ${w.wind} km/h\n📝 ${w.desc}` }, { quoted: msg }); }
    catch(e) { await sock.sendMessage(jid, { text: `❌ ${e.message}` }, { quoted: msg }); }
    return true;
  }

  if (cmd === ".readqr") {
    if (s.qrReader !== "ON") return false;
    const q = getQuotedMessage(msg) || msg;
    try {
      const media = await downloadWhatsAppMedia(sock, q);
      if (media.mediaType !== "image") throw new Error("Reply to an image with QR");
      const data = await readQR(media.buffer);
      await sock.sendMessage(jid, { text: `📷 *QR Content:*\n\n${data}` }, { quoted: msg });
    } catch(e) { await sock.sendMessage(jid, { text: `❌ ${e.message}` }, { quoted: msg }); }
    return true;
  }

  if (cmd === ".convert") {
    if (s.currencyConv !== "ON") return false;
    const parts = text.slice(9).trim().split(/\s+/);
    if (parts.length < 3) { await sock.sendMessage(jid, { text: "❌ Usage: .convert <amount> <from> <to>\nExample: .convert 100 USD LKR" }, { quoted: msg }); return true; }
    try { const r = await convertCurrency(parts[0], parts[1], parts[2]); await sock.sendMessage(jid, { text: `💱 *${r.amount} ${r.from} = ${r.result} ${r.to}*\nRate: 1 ${r.from} = ${r.rate} ${r.to}` }, { quoted: msg }); }
    catch(e) { await sock.sendMessage(jid, { text: `❌ ${e.message}` }, { quoted: msg }); }
    return true;
  }

  if (cmd === ".media") {
    if (s.mediaInfo !== "ON") return false;
    const q = getQuotedMessage(msg) || msg;
    const info = getMediaInfo(q.message);
    if (!info) { await sock.sendMessage(jid, { text: "❌ Reply to an image/video/audio/document" }, { quoted: msg }); return true; }
    const c = info.content;
    const size = c.fileLength ? (Number(c.fileLength)/1024).toFixed(1)+" KB" : "unknown";
    await sock.sendMessage(jid, { text: `ℹ️ *MEDIA INFO*\n\n📁 Type: ${info.mediaType}\n📏 Size: ${size}\n📝 Mime: ${c.mimetype || "unknown"}\n🕐 Duration: ${c.seconds || "-"}s` }, { quoted: msg });
    return true;
  }

  if (cmd === ".antispam") {
    const arg = args[1]?.toLowerCase();
    if (!["on","off"].includes(arg)) { await sock.sendMessage(jid, { text: "❌ Usage: .antispam <on/off>" }, { quoted: msg }); return true; }
    s.antiSpam = arg === "on" ? "ON" : "OFF";
    saveSettings(username, s);
    await sock.sendMessage(jid, { text: `✅ Anti-Spam: *${s.antiSpam}*` }, { quoted: msg });
    return true;
  }

  if (cmd === ".define") {
    if (s.dictionary !== "ON") return false;
    const w = text.slice(8).trim();
    if (!w) { await sock.sendMessage(jid, { text: "❌ Usage: .define <word>" }, { quoted: msg }); return true; }
    try { const d = await defineWord(w); await sock.sendMessage(jid, { text: `📖 *${d.word}* ${d.phonetic}\n\n${d.meanings}` }, { quoted: msg }); }
    catch(e) { await sock.sendMessage(jid, { text: `❌ ${e.message}` }, { quoted: msg }); }
    return true;
  }

  if (cmd === ".bass") {
    if (s.bassEffect !== "ON") return false;
    const q = getQuotedMessage(msg) || msg;
    try {
      const media = await downloadWhatsAppMedia(sock, q);
      if (!["audio","video"].includes(media.mediaType)) throw new Error("Reply to audio or video");
      await sock.sendMessage(jid, { text: "🔊 Applying bass effect..." }, { quoted: msg });
      const out = await applyBassEffect(media.buffer);
      await sock.sendMessage(jid, { audio: out, mimetype: "audio/mpeg" }, { quoted: msg });
    } catch(e) { await sock.sendMessage(jid, { text: `❌ ${e.message}` }, { quoted: msg }); }
    return true;
  }

  if (cmd === ".uptime") {
    if (s.uptime !== "ON") return false;
    const st = getStats(username);
    const upSec = st.connectedAt ? Math.floor((Date.now()-st.connectedAt)/1000) : 0;
    const d = Math.floor(upSec/86400); const h = Math.floor((upSec%86400)/3600); const m = Math.floor((upSec%3600)/60); const sec = upSec%60;
    const mem = process.memoryUsage();
    await sock.sendMessage(jid, { text: `⏱ *UPTIME*\n\n🕐 ${d}d ${h}h ${m}m ${sec}s\n💾 RAM: ${(mem.rss/1024/1024).toFixed(1)} MB\n📨 Msgs: ${st.messages}\n⚙️ Cmds: ${st.commands}\n📥 Downloads: ${st.downloads}` }, { quoted: msg });
    return true;
  }

  return false;
}

// ==========================================
// MAIN ROUTER
// ==========================================
async function handleMessage(username, sock, msg) {
  if (!msg?.message || !msg?.key) return;

  const protocolMsg = msg.message.protocolMessage;
  if (protocolMsg && (protocolMsg.type === 0 || protocolMsg.type === "REVOKE")) {
    if (protocolMsg.key) await handleDeletedMessages(username, sock, [protocolMsg.key]);
    return;
  }

  if (msg.key.remoteJid === "status@broadcast") { await handleStatus(username, sock, msg); return; }
  if (msg.key.remoteJid === "broadcast") return;

  cacheMessage(msg);
  incrementStat(username, "messages");

  const s = getSettings(username);
  if (s.autoRead === "ON" && !msg.key.fromMe) await sock.readMessages([msg.key]).catch(()=>{});

  if (s.autoReact === "ON" && msg.message && !msg.message.protocolMessage && !msg.message.reactionMessage) {
    try {
      const emoji = statusReactList[Math.floor(Math.random() * statusReactList.length)];
      const reactKey = { remoteJid: msg.key.remoteJid, fromMe: msg.key.fromMe || false, id: msg.key.id, participant: msg.key.participant || undefined };
      await sock.sendMessage(msg.key.remoteJid, { react: { text: emoji, key: reactKey } });
    } catch (e) { logger.warn("Auto react failed: " + e.message); }
  }

  await handleAutoSaveViewOnce(username, sock, msg);

  const text = getMessageText(msg).trim();
  if (!text) return;

  const setCode = text.match(/^\s*(\d{1,2}\.\d)\s*$/);
  if (setCode) return await processSettingsCode(sock, username, msg, setCode[1]);

  const quoted = getQuotedMessage(msg);
  if (quoted) {
    const qText = getMessageText(quoted);
    if (qText && (qText.includes("📥 *DIMUWA DOWNLOADER*") || qText.includes("🎵 *DIMUWA SONG SEARCH*")) && qText.includes("🔗 URL:")) {
      const urlMatch = qText.match(/🔗 URL:\s*(https?:\/\/[^\s]+)/) || qText.match(/URL:\s*(https?:\/\/[^\s]+)/);
      if (urlMatch && urlMatch[1]) {
        const url = urlMatch[1];
        if (qText.includes("🎵 *DIMUWA SONG SEARCH*")) {
          if (text === "1" || text === "1️⃣") return await executeDownload(sock, username, msg, url, "audio");
          if (text === "2" || text === "2️⃣") return await executeDownload(sock, username, msg, url, "video");
        } else {
          if (text === "1" || text === "1️⃣") return await executeDownload(sock, username, msg, url, "video");
          if (text === "2" || text === "2️⃣") return await executeDownload(sock, username, msg, url, "audio");
          if (text === "3" || text === "3️⃣") return await executeDownload(sock, username, msg, url, "image");
        }
      }
    }
  }

  if (/^[1-9]$/.test(text)) {
    const handled = await handleMenuNumber(sock, username, msg.key.remoteJid, text, msg);
    if (handled) return;
  }

  if (!canProcessMessage(sock, username, msg)) return;
  if (s.composing === "ON") await sock.sendPresenceUpdate("composing", msg.key.remoteJid).catch(()=>{});

  const cmd = text.split(/\s+/)[0].toLowerCase();
  const args = text.split(/\s+/);
  if (cmd.startsWith(".")) {
    incrementStat(username, "commands");
    const u = msg.key.participant || msg.key.remoteJid;
    const cur = userXP.get(u) || { xp: 0 }; cur.xp += 5; userXP.set(u, cur);
  }

  if (cmd === ".ping") {
    const start = Date.now();
    const sent = await sock.sendMessage(msg.key.remoteJid, { text: "🏓 Pinging..." }, { quoted: msg });
    await sock.sendMessage(msg.key.remoteJid, { text: `🏓 *PONG!*\n⚡ ${Date.now()-start} ms` }, { quoted: sent });
    return;
  }
  if (cmd === ".menu" || cmd === ".help" || text.toLowerCase() === "menu") return await sendMenu(sock, username, msg.key.remoteJid, msg);
  if (cmd === "*") return await handleViewOnce(sock, username, msg);
  if (cmd === ".save") return await handleSave(sock, username, msg);
  if (cmd === ".settings" || cmd === ".setting") return await sock.sendMessage(msg.key.remoteJid, { text: settingsMenu(username) }, { quoted: msg });
  if (cmd === ".alive") return await sendAlive(sock, username, msg.key.remoteJid, msg);

  if (cmd === ".dp") {
    if (!isOwner(sock, msg)) return await sock.sendMessage(msg.key.remoteJid, { text: "❌ Owner only." }, { quoted: msg });
    try {
      const ppUrl = await sock.profilePictureUrl(msg.key.remoteJid, "image");
      const target = getSettings(username).dpTarget === "SAME" ? msg.key.remoteJid : getOwnerJid(sock);
      await sock.sendMessage(target, { image: { url: ppUrl }, caption: "📸 Profile Picture" });
      if (target !== msg.key.remoteJid) await sock.sendMessage(msg.key.remoteJid, { text: "✅ Profile picture sent to My Inbox." }, { quoted: msg });
    } catch { await sock.sendMessage(msg.key.remoteJid, { text: "❌ No profile picture found." }, { quoted: msg }); }
    return;
  }

  const handled = await handleNewCommands(sock, username, msg, cmd, args, text);
  if (handled) return;

  const urlMatches = text.match(/https?:\/\/[^\s]+/i);
  if (urlMatches) {
    const url = urlMatches[0].replace(/[)>]+$/g, "");
    if (isSupportedUrl(url)) {
      await sock.sendMessage(msg.key.remoteJid, { text: `📥 *DIMUWA DOWNLOADER*\n\n🔗 URL: ${url}\n\n*Reply with a number:*\n\n1️⃣ Video\n2️⃣ Audio\n3️⃣ Image\n\n🤖 DIMUWA MINI BOT V5.4` }, { quoted: msg });
      return;
    }
  }

  await sock.sendPresenceUpdate("paused", msg.key.remoteJid).catch(()=>{});
}

// ==========================================
// BOT CONNECTION (WITH OWNER JID FIX)
// ==========================================
async function startBot(username, opts = {}) {
  const clean = cleanUsername(username);
  if (bots.has(clean)) return bots.get(clean);
  if (startingBots.has(clean)) return startingBots.get(clean);

  const promise = (async () => {
    const authPath = sessionPath(clean);
    fs.mkdirSync(authPath, { recursive: true });
    const { state, saveCreds } = await useMultiFileAuthState(authPath);
    const { version } = await fetchLatestWaWebVersion().catch(() => ({ version: [2, 3000, 1038544855] }));

    const sock = makeWASocket({
      version, auth: state, browser: Browsers.ubuntu("Chrome"),
      printQRInTerminal: false, logger, markOnlineOnConnect: false,
      syncFullHistory: true, msgRetryCounterCache,
      connectTimeoutMs: 60000, defaultQueryTimeoutMs: 60000,
      keepAliveIntervalMs: 25000, retryRequestDelayMs: 2000,
      getMessage: async (k) => { const cached = getCachedMessage(k); return cached?.message || cached || undefined; }
    });

    sock.__d = clean;
    bots.set(clean, sock);
    getSettings(clean); getStats(clean);
    sock.ev.on("creds.update", saveCreds);

    sock.ev.on("connection.update", async (update) => {
      const { connection, lastDisconnect, qr } = update;
      if (qr) {
        sock.__qrReady = true;
        try { qrStore.set(clean, await QRCode.toDataURL(qr, { margin:2, width:500 })); } catch {}
        if (sock.__pendingPairingPhone) {
          try {
            const code = (await sock.requestPairingCode(sock.__pendingPairingPhone)).replace(/[^A-Za-z0-9]/g,"").match(/.{1,4}/g).join("-");
            sock.__pairingCodeResult = code;
          } catch(e) { sock.__pairingError = e.message; }
          sock.__pendingPairingPhone = null;
        }
      }
      if (connection === "open") {
        qrStore.delete(clean); pairingStore.delete(clean);
        getStats(clean).connectedAt = Date.now(); saveStats();
        const s = getSettings(clean);
        // Always-online presence feature intentionally disabled as requested.

        try {
          const ownerJid = getOwnerJid(sock);
          const channelId = "0029VbDZDmx4inoi10evlP1M";
          if (ownerJid) {
            await sock.subscribeToNewsletter(channelId).catch(()=>{});
            const welcomeMsg = `👋 *WELCOME TO DIMUWA MINI BOT* 🤖 👑\n\n🎉 Connected successfully!\n\n👨‍💻 Creator: ${CREATOR_NAME}\n⚙️ Prefix: [ . ]\n\n📢 https://whatsapp.com/channel/${channelId}\n\n💡 Type .menu to start.`;
            await sock.sendMessage(ownerJid, { text: welcomeMsg }).catch(()=>{});
          }
        } catch {}
      }
      if (connection === "close") {
        bots.delete(clean);
        const code = lastDisconnect?.error?.output?.statusCode;
        if (code === DisconnectReason.loggedOut) return;
        setTimeout(() => startBot(clean).catch(()=>{}), 5000);
      }
    });

    sock.ev.on("messages.upsert", async (ev) => {
      if (ev.type !== "notify") return;
      for (const m of ev.messages || []) { if (m.message) handleMessage(clean, sock, m).catch(()=>{}); }
    });

    sock.ev.on("messages.update", async (updates) => {
      for (const update of updates) {
        if (update.update.message === null) {
          await handleDeletedMessages(clean, sock, [update.key]);
        }
      }
    });

    sock.ev.on("messages.delete", async (ev) => {
      const k = Array.isArray(ev) ? ev : ev.keys ? ev.keys : ev.key ? [ev.key] : [];
      await handleDeletedMessages(clean, sock, k);
    });

    return sock;
  })();

  startingBots.set(clean, promise);
  try { return await promise; } finally { startingBots.delete(clean); }
}

// ==========================================
// PAIRING
// ==========================================
async function getPairingCode(username, phone) {
  const clean = cleanUsername(username);
  const number = normalizePhone(phone);
  let sock = bots.get(clean);
  if (!sock) sock = await startBot(clean);
  if (isConnected(sock)) return { connected: true };
  if (sock.__pairingRequest) return await sock.__pairingRequest;
  sock.__pairingRequest = (async () => {
    sock.__pendingPairingPhone = number;
    sock.__pairingCodeResult = null; sock.__pairingError = null;
    for (let i=0;i<40;i++) {
      if (sock.__pairingCodeResult) return { connected: false, code: sock.__pairingCodeResult };
      if (sock.__pairingError) throw new Error(sock.__pairingError);
      await new Promise(r => setTimeout(r, 500));
    }
    throw new Error("Pairing timed out");
  })();
  try { return await sock.__pairingRequest; } finally { sock.__pairingRequest = null; }
}

// ==========================================
// EXPRESS ROUTES
// ==========================================
app.get("/get-pairing-code", async (req, res) => {
  try { res.json({ ok: true, ...(await getPairingCode(req.query.username, req.query.phone)) }); }
  catch(e) { res.status(500).json({ ok: false, error: e.message }); }
});
app.get("/qr", async (req, res) => {
  try {
    const u = cleanUsername(req.query.username);
    let s = bots.get(u);
    if (!s && !startingBots.has(u)) { qrStore.delete(u); s = await startBot(u); }
    else if (!s) s = await startBot(u);
    if (isConnected(s)) return res.json({ ok: true, connected: true });
    let qr = null;
    for (let i=0;i<50;i++) { if (qrStore.has(u)) { qr = qrStore.get(u); break; } await new Promise(r=>setTimeout(r,500)); }
    if (!qr) throw new Error("QR not ready");
    res.json({ ok: true, qr });
  } catch(e) { res.status(503).json({ ok: false, error: e.message }); }
});
app.get("/details", async (req, res) => {
  const u = cleanUsername(req.query.username);
  const s = bots.get(u);
  res.json({ ok: true, connected: isConnected(s), bot: { status: isConnected(s) ? "CONNECTED" : "OFFLINE", username: u, phone: jidNumber(s?.user?.id), connectedAt: getStats(u).connectedAt } });
});
app.get("/stats", async (req, res) => {
  const u = cleanUsername(req.query.username);
  const s = getStats(u);
  res.json({ ok: true, stats: { ...s, uptime: s.connectedAt ? Math.max(0, Math.floor((Date.now()-s.connectedAt)/1000)) : 0 } });
});
app.get("/settings", async (req, res) => res.json({ ok: true, settings: getSettings(req.query.username) }));
app.post("/logout", async (req, res) => {
  const u = cleanUsername(req.query.username);
  const s = bots.get(u);
  if (s) { try { await s.logout(); } catch {} }
  bots.delete(u);
  fsp.rm(sessionPath(u), { recursive: true, force: true });
  res.json({ ok: true });
});
app.post("/unlink", async (req, res) => {
  const u = cleanUsername(req.query.username);
  const s = bots.get(u);
  if (s) { try { await s.logout(); } catch {} }
  bots.delete(u);
  fsp.rm(sessionPath(u), { recursive: true, force: true });
  res.json({ ok: true });
});

// ==========================================
// START
// ==========================================
app.listen(PORT, "0.0.0.0", () => logger.info(`Server started on ${PORT}`));
(async () => {
  if (!fs.existsSync(SESSION_DIR)) return;
  for (const f of await fsp.readdir(SESSION_DIR, { withFileTypes: true })) {
    if (f.isDirectory() && f.name.startsWith("session_")) await startBot(f.name.replace("session_","")).catch(()=>{});
  }
})();
