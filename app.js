/* ============================================================
   聊天站 · 主逻辑  v2
   传输：公共 MQTT（broker.emqx.io）—— 不注册服务器、不部署后端
   账号：名字 + 密码；密码派生密钥加密聊天私钥，换设备可恢复
   加密：ECDH P-256 + HKDF + AES-GCM（浏览器自带 WebCrypto）
   图片：压缩后切片，存进多条 retained 消息
   ============================================================ */
(function () {
  'use strict';

  /* ---------------- 常量 ---------------- */
  var BROKER    = 'wss://broker.emqx.io:8084/mqtt';
  var NS        = 'wbuddy_chat_v1';
  var CHUNK     = 45 * 1024;       // retained 单条上限实测约 66KB，取 45KB 留足余量（越大越容易丢）
  var MAX_MEDIA = 340 * 1024;      // 压缩后图片上限
  var KEEP      = 400;             // 每个会话最多留多少条
  var PBKDF2    = 400000;          // 密码派生迭代次数
  var RECALL_MS = 48 * 3600 * 1000;// 48 小时内可撤回
  var EMPTY     = new Uint8Array(0);

  var LS = {
    acct:     'wchat.acct.v2',
    unlock:   'wchat.unlock.v2',
    legacy:   'wchat.id.v1',
    legacyC:  'wchat.contacts.v1',
    legacyR:  'wchat.read.v1',
    contacts: 'wchat.contacts.v2',
    read:     'wchat.read.v2',
    hidden:   'wchat.hidden.v2',
    sent:     'wchat.sent.v2',
    set:      'wchat.settings.v2',
    theme:    'wchat.theme'
  };

  var $ = function (id) { return document.getElementById(id); };
  var te = new TextEncoder();
  var td = new TextDecoder();

  /* ---------------- 状态 ---------------- */
  var me = null;            // {pid, name, priv, pub}
  var client = null;
  var connected = false;
  var desired = {};
  var presenceTimer = null;

  var contacts = [];        // [{pid, name, pub, added, pinned}]
  var msgs = {};            // peerPid -> [msg]
  var seen = {};            // msgId -> true
  var goneIds = {};         // 已撤回的 msgId
  var hidden = {};          // 本地删除的 msgId
  var sentLog = {};         // msgId -> {peer, total, t}
  var inbox = {};           // msgId -> 分片缓冲
  var peerRead = {};        // peerPid -> 他读我的消息到哪
  var myRead = {};          // peerPid -> 我读他的消息到哪
  var presence = {};        // pid -> 时间戳
  var typing = {};          // pid -> 停止时间
  var activePeer = null;
  var activeSearch = null;
  var replyTo = null;       // 正在引用的消息
  var fwdMsg = null;        // 正在转发的消息
  var uploading = false;
  var lastTypingSent = 0;

  var settings = { read: true, typing: true, preview: true };

  /* ==========================================================
     基础工具
     ========================================================== */

  function el(tag, cls, text) {
    var n = document.createElement(tag);
    if (cls) n.className = cls;
    if (text !== undefined && text !== null) n.textContent = text;
    return n;
  }
  function pad(n) { return n < 10 ? '0' + n : '' + n; }
  function fmtTime(ts) {
    var d = new Date(ts);
    return pad(d.getHours()) + ':' + pad(d.getMinutes());
  }
  function sameDay(a, b) {
    return a.getFullYear() === b.getFullYear() && a.getMonth() === b.getMonth() && a.getDate() === b.getDate();
  }
  function fmtDay(ts) {
    var d = new Date(ts), now = new Date();
    if (sameDay(d, now)) return '今天';
    var y = new Date(now); y.setDate(y.getDate() - 1);
    if (sameDay(d, y)) return '昨天';
    var o = { month: 'long', day: 'numeric' };
    if (d.getFullYear() !== now.getFullYear()) o.year = 'numeric';
    return d.toLocaleDateString('zh-CN', o);
  }
  function fmtListTime(ts) {
    if (!ts) return '';
    var d = new Date(ts), now = new Date();
    if (sameDay(d, now)) return fmtTime(ts);
    var y = new Date(now); y.setDate(y.getDate() - 1);
    if (sameDay(d, y)) return '昨天';
    return pad(d.getMonth() + 1) + '/' + pad(d.getDate());
  }
  function fmtAgo(ts) {
    var s = Math.floor((Date.now() - ts) / 1000);
    if (s < 70) return '在线';
    if (s < 3600) return Math.floor(s / 60) + ' 分钟前在线';
    if (s < 86400) return Math.floor(s / 3600) + ' 小时前在线';
    return Math.floor(s / 86400) + ' 天前在线';
  }
  function firstChar(name) {
    var s = String(name || '').trim();
    return s ? Array.from(s)[0].toUpperCase() : '?';
  }
  var PALETTE = ['#008069', '#0a7cff', '#e542a3', '#f5a623', '#7b61ff', '#00a884', '#e2564b', '#0f9b8e', '#a4508b', '#d1741f'];
  function colorFor(seed) {
    var s = String(seed || 'x'), h = 0;
    for (var i = 0; i < s.length; i++) h = (h * 31 + s.charCodeAt(i)) >>> 0;
    return PALETTE[h % PALETTE.length];
  }
  function paintAvatar(node, name, seed) {
    node.style.background = colorFor(seed || name);
    node.textContent = firstChar(name);
  }

  var toastTimer = null;
  function toast(msg, ms) {
    var t = $('toast');
    t.textContent = msg;
    t.classList.remove('hidden');
    clearTimeout(toastTimer);
    toastTimer = setTimeout(function () { t.classList.add('hidden'); }, ms || 3200);
  }

  function setConn(text, bad) {
    var n = $('conn-status');
    if (!text) { n.classList.remove('show', 'bad'); n.textContent = ''; return; }
    n.classList.add('show');
    n.classList.toggle('bad', !!bad);
    n.textContent = text;
  }

  function randId(n) {
    var a = 'abcdefghijklmnopqrstuvwxyz0123456789', s = '';
    var r = crypto.getRandomValues(new Uint8Array(n));
    for (var i = 0; i < n; i++) s += a[r[i] % 36];
    return s;
  }

  function b64(buf) {
    var b = new Uint8Array(buf), s = '';
    for (var i = 0; i < b.length; i += 0x8000) s += String.fromCharCode.apply(null, b.subarray(i, i + 0x8000));
    return btoa(s);
  }
  function unb64(str) {
    var bin = atob(str), out = new Uint8Array(bin.length);
    for (var i = 0; i < bin.length; i++) out[i] = bin.charCodeAt(i);
    return out;
  }
  function b64url(buf) {
    return b64(buf).replace(/\+/g, '-').replace(/\//g, '_').replace(/=+$/, '');
  }
  function concat(list) {
    var len = 0, i;
    for (i = 0; i < list.length; i++) len += list[i].length;
    var out = new Uint8Array(len), off = 0;
    for (i = 0; i < list.length; i++) { out.set(list[i], off); off += list[i].length; }
    return out;
  }
  function autoGrow(t) {
    t.style.height = 'auto';
    t.style.height = Math.min(t.scrollHeight, 120) + 'px';
  }
  function lsGet(k, dflt) {
    try { var v = JSON.parse(localStorage.getItem(k) || 'null'); return v === null ? dflt : v; }
    catch (e) { return dflt; }
  }
  function lsSet(k, v) { try { localStorage.setItem(k, JSON.stringify(v)); } catch (e) {} }

  /* ==========================================================
     加密
     ========================================================== */

  var keyCache = {};

  function sameKey(a, b) {
    return !!(a && b && a.x && b.x && a.x === b.x && a.y === b.y);
  }
  function importPriv(jwk) {
    return crypto.subtle.importKey('jwk', jwk, { name: 'ECDH', namedCurve: 'P-256' }, false, ['deriveBits']);
  }
  function importPub(jwk) {
    return crypto.subtle.importKey('jwk', jwk, { name: 'ECDH', namedCurve: 'P-256' }, false, []);
  }

  /* 用「我的私钥 + 对方公钥」派生会话密钥。缓存键用对方公钥的 x 坐标 */
  async function sharedKey(peerPubJwk) {
    var ck = peerPubJwk.x;
    if (keyCache[ck]) return keyCache[ck];
    var priv = await importPriv(me.priv);
    var pub = await importPub(peerPubJwk);
    var bits = await crypto.subtle.deriveBits({ name: 'ECDH', public: pub }, priv, 256);
    var hk = await crypto.subtle.importKey('raw', bits, 'HKDF', false, ['deriveKey']);
    var aes = await crypto.subtle.deriveKey(
      { name: 'HKDF', hash: 'SHA-256', salt: te.encode('wbuddy-chat-v1'), info: te.encode('message-key') },
      hk, { name: 'AES-GCM', length: 256 }, false, ['encrypt', 'decrypt']
    );
    keyCache[ck] = aes;
    return aes;
  }

  async function encryptBlob(key, plain) {
    var iv = crypto.getRandomValues(new Uint8Array(12));
    var ct = new Uint8Array(await crypto.subtle.encrypt({ name: 'AES-GCM', iv: iv }, key, plain));
    var out = new Uint8Array(12 + ct.length);
    out.set(iv, 0); out.set(ct, 12);
    return out;
  }
  async function decryptBlob(key, blob) {
    var pt = await crypto.subtle.decrypt({ name: 'AES-GCM', iv: blob.subarray(0, 12) }, key, blob.subarray(12));
    return new Uint8Array(pt);
  }

  async function safetyNumber(peerPub) {
    // 顺序必须由公钥本身决定，两边算出来才一样
    var k1 = JSON.stringify(me.pub), k2 = JSON.stringify(peerPub);
    var str = k1 < k2 ? k1 + '|' + k2 : k2 + '|' + k1;
    var d = new Uint8Array(await crypto.subtle.digest('SHA-256', te.encode(str)));
    var g = [];
    for (var i = 0; i < 3; i++) g.push(('0000' + (((d[i * 2] << 8) | d[i * 2 + 1]) % 10000)).slice(-4));
    return g.join(' ');
  }

  async function accountHash(name) {
    var norm = String(name).trim().toLowerCase().replace(/\s+/g, ' ');
    var d = new Uint8Array(await crypto.subtle.digest('SHA-256', te.encode('wbuddy-acct:' + norm)));
    return b64url(d).slice(0, 22);
  }

  /* 密码 -> 解锁密钥 */
  async function deriveUnlock(password, saltBytes, iter) {
    var base = await crypto.subtle.importKey('raw', te.encode(password), 'PBKDF2', false, ['deriveKey']);
    return crypto.subtle.deriveKey(
      { name: 'PBKDF2', salt: saltBytes, iterations: iter, hash: 'SHA-256' },
      base, { name: 'AES-GCM', length: 256 }, true, ['encrypt', 'decrypt']
    );
  }
  async function sealPriv(privJwk, key) {
    var iv = crypto.getRandomValues(new Uint8Array(12));
    var ct = new Uint8Array(await crypto.subtle.encrypt({ name: 'AES-GCM', iv: iv }, key, te.encode(JSON.stringify(privJwk))));
    return b64(concat([iv, ct]));
  }
  async function openPriv(sealedB64, key) {
    var blob = unb64(sealedB64);
    var pt = await crypto.subtle.decrypt({ name: 'AES-GCM', iv: blob.subarray(0, 12) }, key, blob.subarray(12));
    return JSON.parse(td.decode(pt));
  }

  /* 明文负载：[1B 版本][2B 头长度][头 JSON][二进制图片] */
  function packPayload(header, media) {
    var hj = te.encode(JSON.stringify(header));
    var out = new Uint8Array(3 + hj.length + (media ? media.length : 0));
    out[0] = 2;
    out[1] = (hj.length >> 8) & 255;
    out[2] = hj.length & 255;
    out.set(hj, 3);
    if (media) out.set(media, 3 + hj.length);
    return out;
  }
  function unpackPayload(bytes) {
    var hl = (bytes[1] << 8) | bytes[2];
    var header = JSON.parse(td.decode(bytes.subarray(3, 3 + hl)));
    var media = bytes.length > 3 + hl ? bytes.subarray(3 + hl) : null;
    return { header: header, media: media };
  }

  /* ==========================================================
     联系人 / 本地状态
     ========================================================== */

  function findContact(pid) {
    for (var i = 0; i < contacts.length; i++) if (contacts[i].pid === pid) return contacts[i];
    return null;
  }
  function addContact(pid, name, pub) {
    var c = findContact(pid);
    if (c) {
      var ch = false;
      if (name && c.name !== name) { c.name = name; ch = true; }
      if (pub && !c.pub) { c.pub = pub; ch = true; }
      if (ch) lsSet(LS.contacts, contacts);
      return c;
    }
    c = { pid: pid, name: name || '未知用户', pub: pub || null, added: Date.now(), pinned: false };
    contacts.push(c);
    lsSet(LS.contacts, contacts);
    return c;
  }
  function lastMsg(pid) {
    var a = msgs[pid];
    if (!a || !a.length) return null;
    for (var i = a.length - 1; i >= 0; i--) if (!hidden[a[i].id]) return a[i];
    return null;
  }
  function visibleMsgs(pid) {
    return (msgs[pid] || []).filter(function (m) { return !hidden[m.id]; });
  }
  function unreadOf(pid) {
    var since = myRead[pid] || 0, n = 0;
    (msgs[pid] || []).forEach(function (m) {
      if (m.from !== me.pid && !hidden[m.id] && m.t > since) n++;
    });
    return n;
  }
  function findMsg(pid, id) {
    var a = msgs[pid] || [];
    for (var i = 0; i < a.length; i++) if (a[i].id === id) return a[i];
    return null;
  }

  /* ==========================================================
     MQTT
     ========================================================== */

  function ensureSub(topic, opts) {
    if (desired[topic]) return;
    desired[topic] = opts || { qos: 1 };
    if (connected) client.subscribe(topic, desired[topic]);
  }
  function whenConnected() {
    return new Promise(function (res) {
      if (connected) return res(true);
      var n = 0;
      var t = setInterval(function () { if (connected || ++n > 90) { clearInterval(t); res(connected); } }, 200);
    });
  }
  function mqttPub(topic, payload, opts) {
    var o = opts || { retain: true, qos: 1 };
    return new Promise(function (res) {
      if (!client) return res(true);
      var tries = 0;
      function attempt() {
        tries++;
        client.publish(topic, payload, o, function (err) {
          if (!err) return res(true);
          if (tries < 2) return setTimeout(attempt, 400);
          res(false);
        });
      }
      attempt();
    });
  }
  function clearRetained(topic) {
    return mqttPub(topic, EMPTY, { retain: true, qos: 1 });
  }

  function connectBroker() {
    if (client) return;
    client = mqtt.connect(BROKER, {
      clientId: 'wc_' + randId(10) + '_' + randId(6),
      clean: true, reconnectPeriod: 3000, connectTimeout: 12000, keepalive: 30
    });
    client.on('connect', function () {
      connected = true;
      setConn('');
      Object.keys(desired).forEach(function (t) { client.subscribe(t, desired[t]); });
      if (me) {
        publishPresence();
        clearInterval(presenceTimer);
        presenceTimer = setInterval(publishPresence, 25000);
      }
    });
    client.on('reconnect', function () { setConn('正在重连…', true); });
    client.on('close', function () { connected = false; setConn('连接断开，正在重试…', true); });
    client.on('error', function () { connected = false; setConn('连不上服务器，检查一下网络', true); });
    client.on('message', onMessage);
  }

  function publishPresence() {
    mqttPub(NS + '/p/' + me.pid, te.encode(JSON.stringify({ t: Date.now() })), { retain: true, qos: 0 });
  }

  /* 读一次账号记录；没有就等超时返回 null
     注意：先退订再订阅 —— 对已订阅的主题重复 subscribe，broker 不会重发 retained */
  function fetchAccount(hash, waitMs) {
    var topic = NS + '/a/' + hash;
    return new Promise(function (res) {
      var done = false;
      function finish(v) {
        if (done) return;
        done = true;
        client.removeListener('message', handler);
        res(v);
      }
      function handler(t, payload) {
        if (t !== topic) return;
        try { finish(JSON.parse(td.decode(payload))); } catch (e) { finish(null); }
      }
      client.on('message', handler);
      client.unsubscribe(topic, function () {
        if (done) return;
        client.subscribe(topic, { qos: 1 });
      });
      setTimeout(function () { finish(null); }, waitMs || 5000);
    });
  }

  function onMessage(topic, payload) {
    if (!me) return;
    var p = topic.split('/');
    if (p[0] !== NS) return;

    if (p[1] === 'u' && p[3] === 'm') {
      var m = /^([a-z0-9]+)_(\d+)_(\d+)$/.exec(p[4]);
      if (m) addChunk(m[1], +m[2], +m[3], new Uint8Array(payload));
      return;
    }
    if (p[1] === 'a' && p[2]) { onAccount(p[2], new Uint8Array(payload)); return; }
    if (p[1] === 'r' && p[3] === me.pid) { onReadMark(p[2], new Uint8Array(payload)); return; }
    if (p[1] === 'p' && p[2]) { onPresence(p[2], new Uint8Array(payload)); return; }
    if (p[1] === 't' && p[2] === me.pid && p[3]) { onTyping(p[3]); return; }
  }

  function onAccount(hash, bytes) {
    var e;
    try { e = JSON.parse(td.decode(bytes)); } catch (err) { return; }
    if (!e || !e.pid || !e.acc) return;
    if (activeSearch && activeSearch.hash === hash) {
      activeSearch.hits[e.pid] = { pid: e.pid, name: e.acc, pub: e.pub };
      renderSearchResults();
    }
  }

  function onPresence(pid, bytes) {
    try { var o = JSON.parse(td.decode(bytes)); if (o && o.t) presence[pid] = o.t; } catch (e) {}
    if (pid === activePeer) updatePeerStatus();
  }
  function onReadMark(readerPid, bytes) {
    try { var o = JSON.parse(td.decode(bytes)); if (!o || !o.t) return; peerRead[readerPid] = o.t; } catch (e) { return; }
    if (readerPid === activePeer) renderMessages(activePeer);
    renderChatList();
  }
  function onTyping(fromPid) {
    if (!settings.typing) return;
    typing[fromPid] = Date.now() + 3500;
    if (fromPid === activePeer) updatePeerStatus();
  }

  /* ==========================================================
     消息分片
     主题：NS/u/{信箱主人}/m/{msgId}_{片号}_{总片数}
     第 0 片 = [2B pk1长度][发送者公钥][2B pk2长度][接收者公钥][密文片段]
     ========================================================== */

  function addChunk(msgId, idx, total, bytes) {
    var e = inbox[msgId];
    if (!e) {
      e = inbox[msgId] = {
        total: total, parts: {}, missing: {}, tries: 0,
        prefix: NS + '/u/' + me.pid + '/m/' + msgId
      };
      for (var i = 0; i < total; i++) e.missing[i] = true;
      e.timer = setTimeout(function () { repair(msgId); }, 2500);
    }
    if (e.parts[idx]) return;
    e.parts[idx] = bytes;
    delete e.missing[idx];
    if (Object.keys(e.parts).length === total) {
      clearTimeout(e.timer);
      delete inbox[msgId];
      assemble(msgId, e);
    }
  }

  /* 公共 broker 实测首次送达率约 90%，缺哪片就重新订阅哪片（重订阅会触发 retained 重推，实测可 100% 补齐）
     注意：放弃时也不能删掉缓冲，否则迟到的分片会重新开始、永远拼不齐 */
  function repair(msgId) {
    var e = inbox[msgId];
    if (!e) return;
    var miss = Object.keys(e.missing);
    if (!miss.length) return;
    e.tries++;
    if (e.tries > 6) return;                     // 停止主动重试，但保留缓冲等迟到的片
    if (e.tries === 3) toast('有消息没收全，正在重试…', 3000);
    miss.forEach(function (i) {
      var t = e.prefix + '_' + i + '_' + e.total;
      client.subscribe(t, { qos: 1 }, function () {
        setTimeout(function () { client.unsubscribe(t); }, 2000);
      });
    });
    e.timer = setTimeout(function () { repair(msgId); }, 2500);
  }

  async function assemble(msgId, e) {
    var idxs = Object.keys(e.parts).map(Number).sort(function (a, b) { return a - b; });
    var first = e.parts[idxs[0]];
    var o = 0;
    try {
      var l1 = (first[o] << 8) | first[o + 1]; o += 2;
      var pk1 = JSON.parse(td.decode(first.subarray(o, o + l1))); o += l1;
      var l2 = (first[o] << 8) | first[o + 1]; o += 2;
      var pk2 = JSON.parse(td.decode(first.subarray(o, o + l2))); o += l2;
      var rest = first.subarray(o);
    } catch (err) { return; }

    var peerPub = sameKey(pk1, me.pub) ? pk2 : pk1;
    if (!peerPub || !peerPub.x) return;

    var parts = [rest];
    for (var i = 1; i < idxs.length; i++) parts.push(e.parts[idxs[i]]);

    var payload;
    try {
      var key = await sharedKey(peerPub);
      payload = unpackPayload(await decryptBlob(key, concat(parts)));
    } catch (err) { return; }

    deliver(msgId, payload, peerPub);
  }

  function deliver(msgId, payload, peerPub) {
    var h = payload.header;
    if (!h || !h.t || !h.f) return;

    var peerPid = (h.f === me.pid) ? h.to : h.f;
    if (!peerPid) return;

    /* 撤回墓碑 */
    if (h.k === 'del') {
      goneIds[h.d] = true;
      var target = findMsg(peerPid, h.d);
      if (target) target.deleted = true;
      else {
        /* 原文已经被清掉了（重新加载后就是这种情况），补一个占位，位置按原始时间放 */
        if (!msgs[peerPid]) msgs[peerPid] = [];
        if (!msgs[peerPid].some(function (x) { return x.id === h.d; })) {
          msgs[peerPid].push({
            id: h.d, from: h.f, t: h.ot || h.t, k: 'text', x: '',
            mime: null, name: null, re: null, media: null, url: null, deleted: true
          });
          msgs[peerPid].sort(function (a, b) { return a.t - b.t; });
        }
      }
      if (peerPid === activePeer) renderMessages(activePeer);
      renderChatList();
      return;
    }

    if (seen[msgId]) return;
    seen[msgId] = true;

    var msg = {
      id: msgId, from: h.f, t: h.t, k: h.k || 'text', x: h.x || '',
      mime: h.m || null, name: h.n || null,
      re: h.re || null,
      media: payload.media || null, url: null,
      deleted: !!goneIds[msgId]
    };
    if (msg.media) {
      try { msg.url = URL.createObjectURL(new Blob([msg.media], { type: msg.mime || 'image/jpeg' })); } catch (e) {}
    }

    if (!msgs[peerPid]) msgs[peerPid] = [];
    msgs[peerPid].push(msg);
    msgs[peerPid].sort(function (a, b) { return a.t - b.t; });
    if (msgs[peerPid].length > KEEP) msgs[peerPid] = msgs[peerPid].slice(-KEEP);

    var c = findContact(peerPid);
    if (!c) c = addContact(peerPid, null, null);
    if (!c.pub && peerPub) { c.pub = peerPub; lsSet(LS.contacts, contacts); }

    if (peerPid === activePeer) {
      appendMessageDom(msg);
      scrollToBottom();
      if (h.f !== me.pid) markRead(peerPid);
    }
    renderChatList();
  }

  /* ==========================================================
     发送
     ========================================================== */

  function packChunk0(blobPart, peerPub) {
    var p1 = te.encode(JSON.stringify(me.pub));
    var p2 = te.encode(JSON.stringify(peerPub));
    var out = new Uint8Array(2 + p1.length + 2 + p2.length + blobPart.length);
    var o = 0;
    out[o] = (p1.length >> 8) & 255; out[o + 1] = p1.length & 255; o += 2;
    out.set(p1, o); o += p1.length;
    out[o] = (p2.length >> 8) & 255; out[o + 1] = p2.length & 255; o += 2;
    out.set(p2, o); o += p2.length;
    out.set(blobPart, o);
    return out;
  }

  async function sendMsg(peer, header, media) {
    var key = await sharedKey(peer.pub);
    var blob = await encryptBlob(key, packPayload(header, media));
    var total = Math.max(1, Math.ceil(blob.length / CHUNK));
    /* 顺序发，不要并发：公共 broker 扛不住一瞬间的 16 条大包，会悄悄丢 */
    var msgId = randId(10);
    for (var i = 0; i < total; i++) {
      var part = blob.subarray(i * CHUNK, (i + 1) * CHUNK);
      var out = (i === 0) ? packChunk0(part, peer.pub) : part;
      var leafMine = msgId + '_' + i + '_' + total;
      if (!await mqttPub(NS + '/u/' + me.pid + '/m/' + leafMine, out)) throw new Error('网络不稳，有分片没发出去，再发一次吧');
      if (!await mqttPub(NS + '/u/' + peer.pid + '/m/' + leafMine, out)) throw new Error('网络不稳，有分片没发出去，再发一次吧');
    }

    sentLog[msgId] = { peer: peer.pid, total: total, t: header.t };
    lsSet(LS.sent, sentLog);
    return msgId;
  }

  async function recall(msgId) {
    var peerPid = activePeer;
    var rec = sentLog[msgId];
    if (!rec) { toast('这条消息的发送记录不在了，撤不回来'); return; }
    var m = findMsg(peerPid, msgId);
    if (m && Date.now() - m.t > RECALL_MS) { toast('超过 48 小时的消息不能撤回了'); return; }

    /* 1. 把双方信箱里的原分片清掉（retained 置空 = 删除） */
    var jobs = [];
    for (var i = 0; i < rec.total; i++) {
      var leaf = msgId + '_' + i + '_' + rec.total;
      jobs.push(clearRetained(NS + '/u/' + me.pid + '/m/' + leaf));
      jobs.push(clearRetained(NS + '/u/' + rec.peer + '/m/' + leaf));
    }
    await Promise.all(jobs);

    /* 2. 发墓碑，让双方界面都变成「已撤回」 */
    var peer = findContact(peerPid);
    if (peer && peer.pub) {
      await sendMsg(peer, {
        v: 2, f: me.pid, to: peer.pid, t: Date.now(), k: 'del', d: msgId,
        ot: (m ? m.t : rec.t)
      });
    }

    /* 3. 本地立即标记 */
    goneIds[msgId] = true;
    if (m) m.deleted = true;
    delete sentLog[msgId];
    lsSet(LS.sent, sentLog);
    renderMessages(peerPid);
    renderChatList();
    toast('已撤回');
  }

  function markRead(peerPid) {
    if (!peerPid) return;
    myRead[peerPid] = Date.now();          // 本地未读计数永远要清
    lsSet(LS.read, myRead);
    if (settings.read) {                   // 但只有开了回执才告诉对方
      mqttPub(NS + '/r/' + me.pid + '/' + peerPid, te.encode(JSON.stringify({ t: myRead[peerPid] })), { retain: true, qos: 0 });
    }
    renderChatList();
  }

  function pingTyping() {
    if (!settings.typing || !activePeer) return;
    var now = Date.now();
    if (now - lastTypingSent < 3000) return;
    lastTypingSent = now;
    mqttPub(NS + '/t/' + activePeer + '/' + me.pid, te.encode(JSON.stringify({ t: now })), { retain: false, qos: 0 });
  }

  /* ==========================================================
     图片压缩
     ========================================================== */

  function loadImage(file) {
    return new Promise(function (res, rej) {
      var url = URL.createObjectURL(file);
      var img = new Image();
      img.onload = function () { res({ img: img, url: url }); };
      img.onerror = function () { URL.revokeObjectURL(url); rej(new Error('图片读不出来')); };
      img.src = url;
    });
  }

  async function compressImage(file) {
    var o = await loadImage(file);
    try {
      var w = o.img.naturalWidth, h = o.img.naturalHeight;
      var steps = [[1400, .82], [1400, .7], [1100, .68], [1100, .58], [900, .6], [760, .55], [600, .5]];
      var best = null;
      for (var i = 0; i < steps.length; i++) {
        var sc = Math.min(1, steps[i][0] / Math.max(w, h));
        var cw = Math.max(1, Math.round(w * sc)), ch = Math.max(1, Math.round(h * sc));
        var cv = document.createElement('canvas');
        cv.width = cw; cv.height = ch;
        var ctx = cv.getContext('2d');
        ctx.fillStyle = '#fff';
        ctx.fillRect(0, 0, cw, ch);
        ctx.drawImage(o.img, 0, 0, cw, ch);
        var blob = await new Promise(function (r) { cv.toBlob(r, 'image/jpeg', steps[i][1]); });
        if (!blob) continue;
        if (!best || blob.size < best.blob.size) best = { blob: blob, w: cw, h: ch };
        if (blob.size <= MAX_MEDIA) break;
      }
      if (!best) throw new Error('图片处理失败');
      return { bytes: new Uint8Array(await best.blob.arrayBuffer()), w: best.w, h: best.h, size: best.blob.size };
    } finally {
      URL.revokeObjectURL(o.url);
    }
  }

  /* ==========================================================
     渲染
     ========================================================== */

  var URL_RE = /https?:\/\/[^\s<>"'）】]+/g;

  function renderRichText(text) {
    var frag = document.createDocumentFragment();
    var last = 0, m;
    URL_RE.lastIndex = 0;
    while ((m = URL_RE.exec(text)) !== null) {
      if (m.index > last) frag.appendChild(document.createTextNode(text.slice(last, m.index)));
      var url = m[0], trail = '';
      while (url.length > 1 && /[.,;:!?)\]）】、。，]$/.test(url)) { trail = url.slice(-1) + trail; url = url.slice(0, -1); }
      var a = document.createElement('a');
      a.textContent = url;
      a.href = url;
      a.target = '_blank';
      a.rel = 'noopener noreferrer nofollow';
      frag.appendChild(a);
      if (trail) frag.appendChild(document.createTextNode(trail));
      last = m.index + m[0].length;
    }
    if (last < text.length) frag.appendChild(document.createTextNode(text.slice(last)));
    return frag;
  }

  function previewOf(m) {
    if (!m) return '还没有消息';
    if (m.deleted) return '🚫 已撤回一条消息';
    if (!settings.preview) return '有新消息';
    if (m.k === 'image') return m.x ? '🖼️ ' + m.x : '🖼️ 图片';
    return (m.x || '').replace(/\s+/g, ' ').slice(0, 60);
  }

  function renderChatList() {
    var box = $('chat-list');
    box.innerHTML = '';
    if (!contacts.length) {
      box.appendChild(el('div', 'list-empty',
        '还没有聊天。\n在上面搜索框输入对方的完整名字，加个好友就能开聊。'));
      return;
    }
    var list = contacts.slice().sort(function (a, b) {
      if (!!a.pinned !== !!b.pinned) return a.pinned ? -1 : 1;
      var la = lastMsg(a.pid), lb = lastMsg(b.pid);
      return (lb ? lb.t : b.added) - (la ? la.t : a.added);
    });

    list.forEach(function (c) {
      var row = el('div', 'chat-row' + (c.pid === activePeer ? ' active' : ''));
      var av = el('div', 'avatar');
      paintAvatar(av, c.name, c.pid);
      row.appendChild(av);

      var main = el('div', 'chat-row-main');
      var top = el('div', 'chat-row-top');
      var nameEl = el('div', 'chat-row-name', c.name);
      top.appendChild(nameEl);

      var lm = lastMsg(c.pid);
      var unread = (c.pid === activePeer) ? 0 : unreadOf(c.pid);
      top.appendChild(el('div', 'chat-row-time' + (unread ? ' unread' : ''), lm ? fmtListTime(lm.t) : ''));
      main.appendChild(top);

      var bot = el('div', 'chat-row-bot');
      var prev = previewOf(lm);
      if (lm && lm.from === me.pid && !lm.deleted) prev = '你：' + prev;
      bot.appendChild(el('div', 'chat-row-preview', prev));
      if (c.pinned) bot.appendChild(el('div', 'pin-ico', '📌'));
      if (unread) bot.appendChild(el('div', 'badge', String(unread)));
      main.appendChild(bot);
      row.appendChild(main);

      row.addEventListener('click', function () { openChat(c.pid); });
      row.addEventListener('contextmenu', function (ev) { ev.preventDefault(); openChatCtx(c.pid, ev.clientX, ev.clientY); });
      box.appendChild(row);
    });
  }

  function messageNode(m, peerPid) {
    var mine = m.from === me.pid;
    var row = el('div', 'msg-row ' + (mine ? 'out' : 'in'));
    row.dataset.mid = m.id;
    var bubble = el('div', 'bubble');

    if (m.deleted) {
      bubble.classList.add('gone');
      bubble.appendChild(el('div', 'text', mine ? '你撤回了一条消息' : '对方撤回了一条消息'));
    } else {
      if (m.re) {
        var q = el('div', 'quote');
        var who = m.re.f === me.pid ? '你' : (findContact(m.re.f) || {}).name || '对方';
        q.appendChild(el('div', 'q-name', who));
        q.appendChild(el('div', 'q-text', m.re.x || (m.re.k === 'image' ? '🖼️ 图片' : '消息')));
        q.addEventListener('click', function (ev) {
          ev.stopPropagation();
          var t = document.querySelector('[data-mid="' + m.re.id + '"]');
          if (t) { t.scrollIntoView({ block: 'center', behavior: 'smooth' }); t.classList.add('flash'); setTimeout(function () { t.classList.remove('flash'); }, 1200); }
        });
        bubble.appendChild(q);
      }

      if (m.k === 'image') {
        if (m.url) {
          var img = el('img', 'media-img');
          img.alt = m.name || '图片';
          img.loading = 'lazy';
          img.src = m.url;
          img.addEventListener('click', function () { openLightbox(m.url); });
          bubble.appendChild(img);
        } else {
          bubble.appendChild(el('div', 'media-ph fail', '图片打不开'));
        }
      }
      if (m.x) {
        var t = el('div', 'text' + (m.k === 'text' ? '' : ' caption'));
        t.appendChild(renderRichText(m.x));
        bubble.appendChild(t);
      }
    }

    var meta = el('div', 'meta');
    meta.appendChild(el('span', 'time', fmtTime(m.t)));
    if (mine && !m.deleted) {
      var isRead = !!(settings.read && peerRead[peerPid] && m.t <= peerRead[peerPid]);
      meta.appendChild(el('span', 'tick' + (isRead ? ' read' : ''), isRead ? '✓✓' : '✓'));
    }
    bubble.appendChild(meta);
    row.appendChild(bubble);
    return row;
  }

  function renderMessages(peerPid, force) {
    var box = $('messages');
    var nearBottom = box.scrollHeight - box.scrollTop - box.clientHeight < 150;
    box.innerHTML = '';
    var list = visibleMsgs(peerPid);
    var lastDay = null;
    list.forEach(function (m) {
      var d = new Date(m.t);
      if (!lastDay || !sameDay(lastDay, d)) {
        box.appendChild(el('div', 'day-sep', fmtDay(m.t)));
        lastDay = d;
      }
      box.appendChild(messageNode(m, peerPid));
    });
    if (force || nearBottom) scrollToBottom(true);
  }

  function appendMessageDom(m) {
    var box = $('messages');
    var list = visibleMsgs(activePeer);
    if (list.length && list[list.length - 1].id !== m.id) { renderMessages(activePeer); return; }
    var prev = list[list.length - 2];
    if (!prev || !sameDay(new Date(prev.t), new Date(m.t))) {
      box.appendChild(el('div', 'day-sep', fmtDay(m.t)));
    }
    box.appendChild(messageNode(m, activePeer));
  }

  function scrollToBottom(force) {
    var box = $('messages');
    if (force || box.scrollHeight - box.scrollTop - box.clientHeight < 150) {
      requestAnimationFrame(function () { box.scrollTop = box.scrollHeight; });
    }
  }

  function updatePeerStatus() {
    if (!activePeer) return;
    var node = $('peer-status');
    if (typing[activePeer] && typing[activePeer] > Date.now()) {
      node.textContent = '正在输入…';
      node.classList.add('typing');
      return;
    }
    node.classList.remove('typing');
    var p = presence[activePeer];
    node.textContent = p ? fmtAgo(p) : '好友';
  }

  function openChat(pid) {
    var c = findContact(pid);
    if (!c) return;
    activePeer = pid;
    clearReply();

    $('chat-empty').classList.add('hidden');
    $('chat-active').classList.remove('hidden');
    $('main').classList.add('chat-open');
    paintAvatar($('peer-avatar'), c.name, pid);
    $('peer-name').textContent = c.name;
    updatePeerStatus();

    ensureSub(NS + '/p/' + pid, { qos: 0 });
    renderMessages(pid, true);
    markRead(pid);
    $('input-msg').focus();
  }

  /* ==========================================================
     长按 / 右键菜单
     ========================================================== */

  var ctxOpen = false;
  function closeCtx() {
    var m = $('ctx-menu');
    m.classList.add('hidden');
    m.innerHTML = '';
    ctxOpen = false;
  }
  function showCtx(items, x, y) {
    var m = $('ctx-menu');
    m.innerHTML = '';
    items.forEach(function (it) {
      if (it === '-') { m.appendChild(el('div', 'ctx-sep')); return; }
      var b = el('button', it.danger ? 'danger' : null);
      b.type = 'button';
      b.appendChild(el('span', 'ctx-ico', it.ico));
      b.appendChild(el('span', null, it.label));
      b.addEventListener('click', function () { closeCtx(); it.run(); });
      m.appendChild(b);
    });
    m.classList.remove('hidden');
    var r = m.getBoundingClientRect();
    var px = Math.min(x, window.innerWidth - r.width - 8);
    var py = Math.min(y, window.innerHeight - r.height - 8);
    m.style.left = Math.max(8, px) + 'px';
    m.style.top = Math.max(8, py) + 'px';
    ctxOpen = true;
  }

  function openMsgCtx(msgId, x, y) {
    var m = findMsg(activePeer, msgId);
    if (!m || m.deleted) return;
    var mine = m.from === me.pid;
    var items = [];

    items.push({ ico: '↩️', label: '回复', run: function () { setReply(m); } });

    if (m.k === 'text' && m.x) {
      items.push({ ico: '📋', label: '复制', run: function () {
        copyText(m.x);
      } });
    }
    items.push({ ico: '➡️', label: '转发', run: function () { openForward(m); } });

    if (m.k === 'image' && m.url) {
      items.push({ ico: '🖼️', label: '查看大图', run: function () { openLightbox(m.url); } });
    }

    items.push('-');

    if (mine && sentLog[msgId] && Date.now() - m.t <= RECALL_MS) {
      items.push({ ico: '🚫', label: '撤回', danger: true, run: function () { recall(msgId); } });
    }
    items.push({ ico: '🗑️', label: '删除（仅本机）', danger: true, run: function () {
      hidden[msgId] = 1;
      lsSet(LS.hidden, hidden);
      renderMessages(activePeer);
      renderChatList();
      toast('已在本机删除，对方那边还在');
    } });

    showCtx(items, x, y);
  }

  function openChatCtx(pid, x, y) {
    var c = findContact(pid);
    if (!c) return;
    showCtx([
      { ico: '📌', label: c.pinned ? '取消置顶' : '置顶聊天', run: function () {
        c.pinned = !c.pinned; lsSet(LS.contacts, contacts); renderChatList();
      } },
      { ico: '✅', label: '标记为已读', run: function () { markRead(pid); renderChatList(); } },
      '-',
      { ico: '🧹', label: '清空本机聊天记录', danger: true, run: function () {
        if (!confirm('只清掉这台设备上的记录，对方那边不受影响。确定吗？')) return;
        (msgs[pid] || []).forEach(function (m) { hidden[m.id] = 1; });
        lsSet(LS.hidden, hidden);
        if (activePeer === pid) renderMessages(pid);
        renderChatList();
      } },
      { ico: '👋', label: '删除联系人', danger: true, run: function () {
        if (!confirm('从列表里移除「' + c.name + '」？聊天记录也会一起清掉。')) return;
        (msgs[pid] || []).forEach(function (m) { hidden[m.id] = 1; });
        lsSet(LS.hidden, hidden);
        contacts = contacts.filter(function (x) { return x.pid !== pid; });
        lsSet(LS.contacts, contacts);
        if (activePeer === pid) {
          activePeer = null;
          $('main').classList.remove('chat-open');
          $('chat-active').classList.add('hidden');
          $('chat-empty').classList.remove('hidden');
        }
        renderChatList();
      } }
    ], x, y);
  }

  function copyText(text) {
    if (navigator.clipboard && navigator.clipboard.writeText) {
      navigator.clipboard.writeText(text).then(function () { toast('已复制'); },
        function () { toast('复制失败，手动选一下吧'); });
    } else {
      var ta = document.createElement('textarea');
      ta.value = text;
      document.body.appendChild(ta);
      ta.select();
      try { document.execCommand('copy'); toast('已复制'); } catch (e) { toast('复制失败'); }
      document.body.removeChild(ta);
    }
  }

  /* ==========================================================
     引用 / 转发
     ========================================================== */

  function setReply(m) {
    replyTo = m;
    var who = m.from === me.pid ? '你' : (findContact(m.from) || {}).name || '对方';
    $('reply-name').textContent = who;
    $('reply-text').textContent = m.k === 'image' ? (m.x || '🖼️ 图片') : (m.x || '').slice(0, 80);
    $('reply-bar').classList.remove('hidden');
    $('input-msg').focus();
  }
  function clearReply() {
    replyTo = null;
    $('reply-bar').classList.add('hidden');
  }

  function openForward(m) {
    fwdMsg = m;
    var list = $('fwd-list');
    list.innerHTML = '';
    if (!contacts.length) {
      list.appendChild(el('div', 'search-empty', '还没有联系人'));
    }
    contacts.forEach(function (c) {
      var item = el('div', 'fwd-item');
      var av = el('div', 'avatar sm');
      paintAvatar(av, c.name, c.pid);
      item.appendChild(av);
      item.appendChild(el('div', 'name', c.name));
      item.addEventListener('click', function () {
        $('modal-forward').classList.add('hidden');
        doForward(c, m);
      });
      list.appendChild(item);
    });
    $('modal-forward').classList.remove('hidden');
  }

  async function doForward(c, m) {
    if (!c.pub) { toast('还没拿到对方的公钥，让他先给你发条消息'); return; }
    try {
      if (m.k === 'image' && m.media) {
        await sendMsg(c, { v: 2, f: me.pid, to: c.pid, t: Date.now(), k: 'image', m: m.mime || 'image/jpeg', n: m.name || '图片.jpg', x: m.x || '' }, m.media);
      } else if (m.x) {
        await sendMsg(c, { v: 2, f: me.pid, to: c.pid, t: Date.now(), k: 'text', x: m.x }, null);
      }
      toast('已转发给 ' + c.name);
      if (activePeer === c.pid) renderChatList();
    } catch (e) { toast('转发失败：' + (e.message || e)); }
  }

  /* ==========================================================
     搜索
     ========================================================== */

  function renderSearchResults() {
    var box = $('search-results');
    box.innerHTML = '';
    if (!activeSearch) { box.classList.add('hidden'); return; }
    var hits = Object.keys(activeSearch.hits).map(function (k) { return activeSearch.hits[k]; });

    if (!hits.length) {
      if (activeSearch.loading) box.appendChild(el('div', 'search-empty', '搜索中…'));
      else box.appendChild(el('div', 'search-empty',
        '没找到叫「' + activeSearch.name + '」的人。\n\n名字要一字不差（空格、大小写不影响）。让对方确认一下他的名字。'));
    } else {
      hits.forEach(function (e) {
        var item = el('div', 'search-item');
        var av = el('div', 'avatar sm');
        paintAvatar(av, e.name, e.pid);
        item.appendChild(av);
        var info = el('div');
        info.appendChild(el('div', 'name', e.name));
        info.appendChild(el('div', 'sub', findContact(e.pid) ? '已在列表里，点击打开' : '点击开始聊天'));
        item.appendChild(info);
        item.addEventListener('click', function () {
          box.classList.add('hidden');
          $('input-search').value = '';
          $('btn-clear-search').classList.add('hidden');
          if (e.pid === me.pid) { toast('这是你自己'); return; }
          addContact(e.pid, e.name, e.pub);
          openChat(e.pid);
        });
        box.appendChild(item);
      });
    }
    box.classList.remove('hidden');
  }

  async function doSearch(name) {
    var h = await accountHash(name);
    activeSearch = { hash: h, name: name, hits: {}, loading: true };
    renderSearchResults();

    var ok = await whenConnected();
    if (!ok) { activeSearch.loading = false; renderSearchResults(); toast('还没连上服务器，稍后再试', 4000); return; }
    if (!activeSearch || activeSearch.hash !== h) return;

    var topic = NS + '/a/' + h;
    client.unsubscribe(topic, function () {
      if (activeSearch && activeSearch.hash === h) client.subscribe(topic, { qos: 1 });
    });
    setTimeout(function () {
      client.unsubscribe(topic);
      if (activeSearch && activeSearch.hash === h) { activeSearch.loading = false; renderSearchResults(); }
    }, 2200);
  }

  /* ==========================================================
     账号：注册 / 登录
     ========================================================== */

  function showScreen(which) {
    $('screen-auth').classList.toggle('hidden', which !== 'auth');
    $('screen-upgrade').classList.toggle('hidden', which !== 'upgrade');
    $('main').classList.toggle('hidden', which !== 'main');
  }

  function friendlyAuthError(e) {
    var m = (e && e.message) || String(e || '出错了');
    if (/占用/.test(m) || /密码不对/.test(m) || /没找到/.test(m)) return m;
    if (/NetworkError|Failed to fetch/i.test(m)) return '连不上服务器，检查一下网络';
    return m;
  }

  async function doRegister(name, password, remember) {
    if (!await whenConnected()) throw new Error('连不上服务器，检查一下网络再试');
    var h = await accountHash(name);
    var exist = await fetchAccount(h, 2500);
    if (exist) throw new Error('这个名字已经被别人用了，换一个');

    var kp = await crypto.subtle.generateKey({ name: 'ECDH', namedCurve: 'P-256' }, true, ['deriveBits']);
    var priv = await crypto.subtle.exportKey('jwk', kp.privateKey);
    var pub = await crypto.subtle.exportKey('jwk', kp.publicKey);
    var pid = randId(12);

    var salt = crypto.getRandomValues(new Uint8Array(16));
    var uk = await deriveUnlock(password, salt, PBKDF2);
    var sealed = await sealPriv(priv, uk);

    var rec = { v: 1, acc: name, pid: pid, pub: pub, sealed: sealed, kdf: { salt: b64(salt), iter: PBKDF2 }, t: Date.now() };
    await mqttPub(NS + '/a/' + h, te.encode(JSON.stringify(rec)), { retain: true, qos: 1 });

    return { acct: { name: name, pid: pid, pub: pub, sealed: sealed, kdf: rec.kdf }, priv: priv, uk: uk, remember: remember };
  }

  async function doLogin(name, password, remember) {
    if (!await whenConnected()) throw new Error('连不上服务器，检查一下网络再试');
    var h = await accountHash(name);
    var rec = await fetchAccount(h, 6000);
    if (!rec || !rec.sealed) throw new Error('没找到这个账号。是不是还没注册过？');
    var uk = await deriveUnlock(password, unb64(rec.kdf.salt), rec.kdf.iter);
    var priv;
    try { priv = await openPriv(rec.sealed, uk); }
    catch (e) { throw new Error('密码不对'); }
    return { acct: { name: rec.acc, pid: rec.pid, pub: rec.pub, sealed: rec.sealed, kdf: rec.kdf }, priv: priv, uk: uk, remember: remember };
  }

  async function enterApp(acct, priv, uk, remember) {
    me = { pid: acct.pid, name: acct.name, priv: priv, pub: acct.pub };
    lsSet(LS.acct, { name: acct.name, pid: acct.pid, pub: acct.pub, sealed: acct.sealed, kdf: acct.kdf });
    if (remember && uk) {
      var raw = await crypto.subtle.exportKey('raw', uk);
      lsSet(LS.unlock, b64(raw));
    } else {
      localStorage.removeItem(LS.unlock);
    }
    showScreen('main');
    wireMain();
    startUp();
  }

  async function tryAutoLogin() {
    var acct = lsGet(LS.acct, null);
    var raw = lsGet(LS.unlock, null);
    if (!acct || !raw) return false;
    try {
      var uk = await crypto.subtle.importKey('raw', unb64(raw), { name: 'AES-GCM' }, false, ['encrypt', 'decrypt']);
      var priv = await openPriv(acct.sealed, uk);
      await enterApp(acct, priv, null, false);
      return true;
    } catch (e) {
      localStorage.removeItem(LS.unlock);
      return false;
    }
  }

  /* ==========================================================
     启动
     ========================================================== */

  async function boot() {
    applyTheme(lsGet(LS.theme, 'light'));
    settings = Object.assign({ read: true, typing: true, preview: true }, lsGet(LS.set, {}));

    if (!window.crypto || !crypto.subtle) {
      showScreen('auth');
      $('auth-error').textContent = '这个页面必须用 https 打开（或 localhost），浏览器才允许用加密功能。';
      $('btn-auth').disabled = true;
      return;
    }
    if (!window.mqtt) {
      showScreen('auth');
      $('auth-error').textContent = '通讯组件没加载出来，确认 vendor/mqtt.min.js 在不在。';
      $('btn-auth').disabled = true;
      return;
    }

    /* 先把连接建起来：注册/登录/搜人都要用它 */
    connectBroker();

    contacts = lsGet(LS.contacts, null) || lsGet(LS.legacyC, []) || [];
    myRead = lsGet(LS.read, null) || lsGet(LS.legacyR, {}) || {};
    hidden = lsGet(LS.hidden, {}) || {};
    sentLog = lsGet(LS.sent, {}) || {};
    if (!lsGet(LS.contacts, null) && contacts.length) lsSet(LS.contacts, contacts);

    if (await tryAutoLogin()) return;

    var acct = lsGet(LS.acct, null);
    if (acct) { showScreen('auth'); setAuthMode('login'); return; }

    var legacy = lsGet(LS.legacy, null);
    if (legacy && legacy.pid && legacy.priv) {
      $('up-account').value = legacy.name || '';
      showScreen('upgrade');
      return;
    }
    showScreen('auth');
  }

  function startUp() {
    $('me-tag').textContent = me.name;
    $('me-name').textContent = me.name;
    $('me-pid').textContent = me.pid;
    $('set-read').checked = settings.read;
    $('set-typing').checked = settings.typing;
    $('set-preview').checked = settings.preview;
    renderChatList();
    ensureSub(NS + '/u/' + me.pid + '/m/+', { qos: 1 });
    ensureSub(NS + '/r/+/' + me.pid, { qos: 0 });
    ensureSub(NS + '/t/' + me.pid + '/+', { qos: 0 });
    publishPresence();
    clearInterval(presenceTimer);
    presenceTimer = setInterval(publishPresence, 25000);
    setInterval(function () { if (activePeer) updatePeerStatus(); }, 1500);
  }

  /* ==========================================================
     事件绑定
     ========================================================== */

  var authMode = 'register';
  function setAuthMode(mode) {
    authMode = mode;
    $('tab-register').classList.toggle('is-on', mode === 'register');
    $('tab-login').classList.toggle('is-on', mode === 'login');
    $('auth-password2').classList.toggle('hidden', mode === 'login');
    $('chk-remember-wrap').classList.toggle('hidden', mode === 'login');
    $('btn-auth').textContent = mode === 'register' ? '注册并开始' : '登录';
    $('auth-password').setAttribute('autocomplete', mode === 'register' ? 'new-password' : 'current-password');
    $('auth-note').classList.toggle('hidden', mode === 'login');
    $('auth-error').textContent = '';
  }
  $('tab-register').addEventListener('click', function () { setAuthMode('register'); });
  $('tab-login').addEventListener('click', function () { setAuthMode('login'); });

  $('form-auth').addEventListener('submit', async function (ev) {
    ev.preventDefault();
    var name = $('auth-account').value.trim();
    var pw = $('auth-password').value;
    var pw2 = $('auth-password2').value;
    var remember = $('auth-remember').checked;
    var btn = $('btn-auth');
    var err = $('auth-error');

    err.textContent = '';
    $('auth-account').classList.toggle('bad', !name);
    $('auth-password').classList.toggle('bad', !pw);
    if (!name) { err.textContent = '先起个名字'; return; }
    if (pw.length < 8) { err.textContent = '密码至少 8 位'; $('auth-password').classList.add('bad'); return; }
    if (authMode === 'register' && pw !== pw2) { err.textContent = '两次密码不一样'; $('auth-password2').classList.add('bad'); return; }

    btn.disabled = true;
    btn.textContent = authMode === 'register' ? '正在注册…' : '正在登录…';
    try {
      var r = authMode === 'register' ? await doRegister(name, pw, remember) : await doLogin(name, pw, remember);
      await enterApp(r.acct, r.priv, r.uk, r.remember);
    } catch (e) {
      err.textContent = friendlyAuthError(e);
      btn.disabled = false;
      btn.textContent = authMode === 'register' ? '注册并开始' : '登录';
    }
  });

  $('form-upgrade').addEventListener('submit', async function (ev) {
    ev.preventDefault();
    var name = $('up-account').value.trim();
    var pw = $('up-password').value;
    var pw2 = $('up-password2').value;
    var err = $('up-error');
    err.textContent = '';
    if (!name) { err.textContent = '填一下你的名字'; return; }
    if (pw.length < 8) { err.textContent = '密码至少 8 位'; return; }
    if (pw !== pw2) { err.textContent = '两次密码不一样'; return; }

    var legacy = lsGet(LS.legacy, null);
    if (!legacy) { err.textContent = '旧身份找不到了'; return; }

    var btn = $('btn-upgrade');
    btn.disabled = true;
    btn.textContent = '正在设置…';
    try {
      if (!await whenConnected()) throw new Error('连不上服务器，检查一下网络再试');
      var h = await accountHash(name);
      var exist = await fetchAccount(h, 2500);
      if (exist && exist.pid !== legacy.pid) throw new Error('这个名字已经被别人用了，换一个');

      var salt = crypto.getRandomValues(new Uint8Array(16));
      var uk = await deriveUnlock(pw, salt, PBKDF2);
      var sealed = await sealPriv(legacy.priv, uk);
      var rec = { v: 1, acc: name, pid: legacy.pid, pub: legacy.pub, sealed: sealed, kdf: { salt: b64(salt), iter: PBKDF2 }, t: Date.now() };
      await mqttPub(NS + '/a/' + h, te.encode(JSON.stringify(rec)), { retain: true, qos: 1 });

      await enterApp({ name: name, pid: legacy.pid, pub: legacy.pub, sealed: sealed, kdf: rec.kdf }, legacy.priv, uk, $('up-remember').checked);
      localStorage.removeItem(LS.legacy);
    } catch (e) {
      err.textContent = friendlyAuthError(e);
      btn.disabled = false;
      btn.textContent = '设置密码并继续';
    }
  });

  $('btn-upgrade-skip').addEventListener('click', function () {
    var legacy = lsGet(LS.legacy, null);
    if (!legacy) return;
    enterApp({ name: legacy.name, pid: legacy.pid, pub: legacy.pub, sealed: '', kdf: null }, legacy.priv, null, false);
  });

  var wired = false;
  function wireMain() {
    if (wired) return;
    wired = true;

    /* --- 搜索 --- */
    var input = $('input-search');
    var box = $('search-results');
    var clear = $('btn-clear-search');
    var searchBtn = $('btn-search');
    function runSearch() {
      var q = input.value.trim();
      if (!q) { input.focus(); return; }
      doSearch(q);
    }
    searchBtn.addEventListener('click', runSearch);
    input.addEventListener('keydown', function (e) { if (e.key === 'Enter') { e.preventDefault(); runSearch(); } });
    input.addEventListener('input', function () { clear.classList.toggle('hidden', !input.value.trim()); });
    clear.addEventListener('click', function () {
      input.value = ''; clear.classList.add('hidden');
      activeSearch = null; box.classList.add('hidden'); box.innerHTML = '';
      input.focus();
    });
    document.addEventListener('click', function (ev) {
      if (!box.contains(ev.target) && !input.contains(ev.target) &&
          ev.target !== clear && !searchBtn.contains(ev.target)) box.classList.add('hidden');
      if (ctxOpen && !$('ctx-menu').contains(ev.target)) closeCtx();
    });

    /* --- 返回 --- */
    $('btn-back').addEventListener('click', function () {
      $('main').classList.remove('chat-open');
      activePeer = null;
      clearReply();
      $('chat-active').classList.add('hidden');
      $('chat-empty').classList.remove('hidden');
      renderChatList();
    });

    /* --- 输入 --- */
    var msgInput = $('input-msg');
    msgInput.addEventListener('input', function () { autoGrow(msgInput); pingTyping(); });
    msgInput.addEventListener('keydown', function (e) {
      if (e.key === 'Enter' && !e.shiftKey) { e.preventDefault(); sendText(); }
    });
    $('btn-send').addEventListener('click', sendText);

    $('btn-image').addEventListener('click', function () { $('file-image').click(); });
    $('file-image').addEventListener('change', function (ev) {
      var f = ev.target.files[0];
      ev.target.value = '';
      if (f) sendImage(f);
    });

    $('btn-reply-cancel').addEventListener('click', clearReply);

    /* --- 主题 --- */
    $('btn-theme').addEventListener('click', function () {
      var next = document.documentElement.getAttribute('data-theme') === 'dark' ? 'light' : 'dark';
      applyTheme(next); lsSet(LS.theme, next);
    });

    /* --- 设置 --- */
    $('btn-settings').addEventListener('click', function () {
      $('set-read').checked = settings.read;
      $('set-typing').checked = settings.typing;
      $('set-preview').checked = settings.preview;
      $('modal-settings').classList.remove('hidden');
    });
    function saveSettings() {
      settings.read = $('set-read').checked;
      settings.typing = $('set-typing').checked;
      settings.preview = $('set-preview').checked;
      lsSet(LS.set, settings);
      renderChatList();
      if (activePeer) renderMessages(activePeer);
    }
    ['set-read', 'set-typing', 'set-preview'].forEach(function (id) {
      $(id).addEventListener('change', saveSettings);
    });
    $('btn-set-ok').addEventListener('click', function () { saveSettings(); $('modal-settings').classList.add('hidden'); });
    $('modal-settings').addEventListener('click', function (e) { if (e.target === $('modal-settings')) { saveSettings(); $('modal-settings').classList.add('hidden'); } });
    $('btn-wipe').addEventListener('click', function () {
      if (!confirm('会清掉这台设备上的身份和全部聊天记录。账号还在服务器上，用「名字 + 密码」还能登回来。确定吗？')) return;
      Object.keys(LS).forEach(function (k) { localStorage.removeItem(LS[k]); });
      location.reload();
    });

    /* --- 我的账号 --- */
    $('btn-me').addEventListener('click', function () { $('modal-me').classList.remove('hidden'); });
    $('btn-me-ok').addEventListener('click', function () { $('modal-me').classList.add('hidden'); });
    $('modal-me').addEventListener('click', function (e) { if (e.target === $('modal-me')) $('modal-me').classList.add('hidden'); });
    $('btn-logout').addEventListener('click', function () {
      if (!confirm('退出后要重新输密码。这台设备上的聊天记录也会清掉（服务器上还在，登回来就有）。确定吗？')) return;
      [LS.acct, LS.unlock, LS.contacts, LS.read, LS.hidden, LS.sent].forEach(function (k) { localStorage.removeItem(k); });
      location.reload();
    });

    /* --- 验证码 --- */
    $('btn-safety').addEventListener('click', async function () {
      var c = activePeer ? findContact(activePeer) : null;
      if (!c || !c.pub) { toast('还没拿到对方的公钥，收到他一条消息后再看'); return; }
      $('safety-num').textContent = await safetyNumber(c.pub);
      $('modal-safety').classList.remove('hidden');
    });
    $('btn-safety-ok').addEventListener('click', function () { $('modal-safety').classList.add('hidden'); });
    $('modal-safety').addEventListener('click', function (e) { if (e.target === $('modal-safety')) $('modal-safety').classList.add('hidden'); });

    /* --- 转发弹窗 --- */
    $('btn-fwd-cancel').addEventListener('click', function () { $('modal-forward').classList.add('hidden'); });
    $('modal-forward').addEventListener('click', function (e) { if (e.target === $('modal-forward')) $('modal-forward').classList.add('hidden'); });

    /* --- 消息长按 / 右键 --- */
    var msgsEl = $('messages');
    var pressTimer = null, pressMoved = false, pressId = null;
    msgsEl.addEventListener('contextmenu', function (ev) {
      var row = ev.target.closest ? ev.target.closest('.msg-row') : null;
      if (!row || !row.dataset.mid) return;
      ev.preventDefault();
      openMsgCtx(row.dataset.mid, ev.clientX, ev.clientY);
    });
    msgsEl.addEventListener('touchstart', function (ev) {
      var row = ev.target.closest ? ev.target.closest('.msg-row') : null;
      if (!row || !row.dataset.mid) return;
      pressId = row.dataset.mid;
      pressMoved = false;
      var t = ev.touches[0];
      var sx = t.clientX, sy = t.clientY;
      pressTimer = setTimeout(function () {
        pressTimer = null;
        if (pressMoved) return;
        if (navigator.vibrate) navigator.vibrate(12);
        openMsgCtx(pressId, sx, sy);
      }, 480);
    }, { passive: true });
    msgsEl.addEventListener('touchmove', function (ev) {
      if (!pressTimer) return;
      var t = ev.touches[0];
      pressMoved = true;
      clearTimeout(pressTimer); pressTimer = null;
    }, { passive: true });
    msgsEl.addEventListener('touchend', function () {
      if (pressTimer) { clearTimeout(pressTimer); pressTimer = null; }
    }, { passive: true });

    /* --- 表情 --- */
    var EMOJIS = ['😀','😃','😄','😁','😆','😅','😂','🤣','🙂','🙃','😉','😊','😇','🥰','😍','😘',
                  '😜','🤪','🤗','🤔','🤨','😐','😴','🥱','😢','😭','😤','😡','🥺','😱','🤯','😎',
                  '👍','👎','👌','🙏','👏','🤝','💪','✌️','🫶','❤️','🔥','✨','🎉','🎁','🌹','☕',
                  '🍺','🍜','🍕','⚽','🚀','🌈','☀️','🌙','⭐','💯','✅','❌','⏰','📌','💡','🐶'];
    var pop = $('emoji-pop');
    EMOJIS.forEach(function (e) {
      var b = el('button', null, e);
      b.type = 'button';
      b.addEventListener('click', function () { msgInput.value += e; autoGrow(msgInput); msgInput.focus(); });
      pop.appendChild(b);
    });
    $('btn-emoji').addEventListener('click', function (ev) {
      ev.stopPropagation();
      pop.classList.toggle('hidden');
    });
    document.addEventListener('click', function (ev) {
      if (!pop.classList.contains('hidden') && !pop.contains(ev.target) && ev.target !== $('btn-emoji')) pop.classList.add('hidden');
    });

    /* --- 图片放大 --- */
    $('btn-lightbox-close').addEventListener('click', closeLightbox);
    $('lightbox').addEventListener('click', function (e) { if (e.target === $('lightbox')) closeLightbox(); });

    document.addEventListener('keydown', function (e) {
      if (e.key === 'Escape') {
        closeLightbox(); closeCtx();
        $('modal-me').classList.add('hidden');
        $('modal-safety').classList.add('hidden');
        $('modal-settings').classList.add('hidden');
        $('modal-forward').classList.add('hidden');
        pop.classList.add('hidden');
      }
    });
    document.addEventListener('visibilitychange', function () {
      if (!document.hidden && activePeer) markRead(activePeer);
    });
    window.addEventListener('resize', closeCtx);
  }

  /* ==========================================================
     发送动作
     ========================================================== */

  function buildRef(m) {
    if (!m) return null;
    return {
      id: m.id, f: m.from, t: m.t, k: m.k,
      x: m.k === 'image' ? (m.x || '') : (m.x || '').slice(0, 120)
    };
  }

  async function sendText() {
    var input = $('input-msg');
    var text = input.value.trim();
    if (!text || !activePeer || uploading) return;
    var c = findContact(activePeer);
    if (!c || !c.pub) { toast('还没拿到对方的公钥，让他先给你发条消息'); return; }
    var ref = buildRef(replyTo);
    input.value = '';
    autoGrow(input);
    clearReply();
    try {
      await sendMsg(c, { v: 2, f: me.pid, to: c.pid, t: Date.now(), k: 'text', x: text, re: ref }, null);
    } catch (e) { toast('发送失败：' + (e.message || e)); }
  }

  async function sendImage(file) {
    if (!activePeer || uploading) return;
    var c = findContact(activePeer);
    if (!c || !c.pub) { toast('还没拿到对方的公钥，让他先给你发条消息'); return; }

    uploading = true;
    $('upload-bar').classList.remove('hidden');
    $('upload-text').textContent = '正在压缩图片…';
    var ref = buildRef(replyTo);
    try {
      var r = await compressImage(file);
      $('upload-text').textContent = '正在发送（' + Math.round(r.size / 1024) + 'KB）…';
      await sendMsg(c, {
        v: 2, f: me.pid, to: c.pid, t: Date.now(), k: 'image',
        m: 'image/jpeg', w: r.w, h: r.h, n: file.name || '图片.jpg', re: ref
      }, r.bytes);
      clearReply();
    } catch (e) {
      toast('图片发送失败：' + (e.message || e), 4500);
    } finally {
      uploading = false;
      $('upload-bar').classList.add('hidden');
    }
  }

  /* ==========================================================
     杂项
     ========================================================== */

  function applyTheme(name) {
    document.documentElement.setAttribute('data-theme', name === 'dark' ? 'dark' : 'light');
    var meta = document.querySelector('meta[name="theme-color"]');
    if (meta) meta.setAttribute('content', name === 'dark' ? '#202c33' : '#008069');
  }
  function openLightbox(url) {
    var body = $('lightbox-body');
    body.innerHTML = '';
    var img = el('img');
    img.src = url;
    body.appendChild(img);
    $('lightbox').classList.remove('hidden');
  }
  function closeLightbox() {
    $('lightbox').classList.add('hidden');
    $('lightbox-body').innerHTML = '';
  }

  if (document.readyState === 'loading') document.addEventListener('DOMContentLoaded', boot);
  else boot();
})();
