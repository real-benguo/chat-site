/* ============================================================
   聊天站 · 主逻辑
   传输：公共 MQTT（broker.emqx.io）—— 不注册、不部署后端
   加密：ECDH P-256 + HKDF + AES-GCM（浏览器自带 WebCrypto）
   图片：压缩后切片，存进多条 retained 消息
   ============================================================ */
(function () {
  'use strict';

  /* ---------------- 常量 ---------------- */
  var BROKER    = 'wss://broker.emqx.io:8084/mqtt';
  var NS        = 'wbuddy_chat_v1';
  var CHUNK     = 60 * 1024;      // retained 单条上限实测约 66KB，留余量
  var MAX_MEDIA = 340 * 1024;     // 压缩后图片上限
  var KEEP      = 300;            // 每个会话最多留多少条

  var LS_ID      = 'wchat.id.v1';
  var LS_CONTACT = 'wchat.contacts.v1';
  var LS_READ    = 'wchat.read.v1';
  var LS_THEME   = 'wchat.theme';

  var $ = function (id) { return document.getElementById(id); };
  var te = new TextEncoder();
  var td = new TextDecoder();

  /* ---------------- 状态 ---------------- */
  var me = null;
  var client = null;
  var connected = false;
  var desired = {};
  var presenceTimer = null;

  var contacts = [];     // [{pid, name, pub, added}]
  var msgs = {};         // peerPid -> [msg]
  var seen = {};         // 去重
  var inbox = {};        // msgId -> 分片缓冲
  var dirCache = {};     // pid -> 目录条目
  var peerRead = {};     // peerPid -> 他读我的消息到哪个时间点
  var myRead = {};       // peerPid -> 我读他的消息到哪个时间点
  var presence = {};     // pid -> 时间戳
  var activePeer = null;
  var activeSearch = null;
  var uploading = false;

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

  /* ==========================================================
     加密
     ========================================================== */

  var keyCache = {};

  function importPriv(jwk) {
    return crypto.subtle.importKey('jwk', jwk, { name: 'ECDH', namedCurve: 'P-256' }, false, ['deriveBits']);
  }
  function importPub(jwk) {
    return crypto.subtle.importKey('jwk', jwk, { name: 'ECDH', namedCurve: 'P-256' }, false, []);
  }

  async function sharedKey(peerPid, peerPubJwk) {
    if (keyCache[peerPid]) return keyCache[peerPid];
    var priv = await importPriv(me.priv);
    var pub = await importPub(peerPubJwk);
    var bits = await crypto.subtle.deriveBits({ name: 'ECDH', public: pub }, priv, 256);
    var hk = await crypto.subtle.importKey('raw', bits, 'HKDF', false, ['deriveKey']);
    var aes = await crypto.subtle.deriveKey(
      { name: 'HKDF', hash: 'SHA-256', salt: te.encode('wbuddy-chat-v1'), info: te.encode('message-key') },
      hk, { name: 'AES-GCM', length: 256 }, false, ['encrypt', 'decrypt']
    );
    keyCache[peerPid] = aes;
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

  async function safetyNumber(peerPid, peerPub) {
    var a = { pid: me.pid, pk: JSON.stringify(me.pub) };
    var b = { pid: peerPid, pk: JSON.stringify(peerPub) };
    var pair = a.pid < b.pid ? [a, b] : [b, a];
    var str = pair.map(function (x) { return x.pid + ':' + x.pk; }).join('|');
    var d = new Uint8Array(await crypto.subtle.digest('SHA-256', te.encode(str)));
    var g = [];
    for (var i = 0; i < 3; i++) g.push(('0000' + (((d[i * 2] << 8) | d[i * 2 + 1]) % 10000)).slice(-4));
    return g.join(' ');
  }

  async function nameHash(name) {
    var norm = String(name).trim().toLowerCase().replace(/\s+/g, ' ');
    var d = new Uint8Array(await crypto.subtle.digest('SHA-256', te.encode('wbuddy-name:' + norm)));
    return b64url(d).slice(0, 22);
  }

  /* 明文负载：[1B 版本][2B 头长度][头 JSON][二进制图片] */
  function packPayload(header, media) {
    var hj = te.encode(JSON.stringify(header));
    var out = new Uint8Array(3 + hj.length + (media ? media.length : 0));
    out[0] = 1;
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
     本地存储
     ========================================================== */

  function lsGet(k, dflt) {
    try { var v = JSON.parse(localStorage.getItem(k) || 'null'); return v === null ? dflt : v; }
    catch (e) { return dflt; }
  }
  function lsSet(k, v) { try { localStorage.setItem(k, JSON.stringify(v)); } catch (e) {} }

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
      if (ch) lsSet(LS_CONTACT, contacts);
      return c;
    }
    c = { pid: pid, name: name || '未知用户', pub: pub || null, added: Date.now() };
    contacts.push(c);
    lsSet(LS_CONTACT, contacts);
    return c;
  }

  async function createIdentity(name) {
    var kp = await crypto.subtle.generateKey({ name: 'ECDH', namedCurve: 'P-256' }, true, ['deriveBits']);
    return {
      pid: randId(12),
      name: name,
      priv: await crypto.subtle.exportKey('jwk', kp.privateKey),
      pub: await crypto.subtle.exportKey('jwk', kp.publicKey)
    };
  }

  /* ==========================================================
     MQTT 层
     ========================================================== */

  function ensureSub(topic, opts) {
    if (desired[topic]) return;
    desired[topic] = opts || { qos: 1 };
    if (connected) client.subscribe(topic, desired[topic]);
  }

  /* 等连接就绪；最多等 15 秒 */
  function whenConnected() {
    return new Promise(function (res) {
      if (connected) return res(true);
      var n = 0;
      var t = setInterval(function () {
        if (connected || ++n > 75) { clearInterval(t); res(connected); }
      }, 200);
    });
  }

  function pub(topic, payload, opts) {
    return new Promise(function (res) {
      if (!client) return res();
      client.publish(topic, payload, opts || { retain: true, qos: 1 }, function () { res(); });
    });
  }

  function connectBroker() {
    client = mqtt.connect(BROKER, {
      clientId: 'wc_' + me.pid + '_' + randId(6),
      clean: true,
      reconnectPeriod: 3000,
      connectTimeout: 12000,
      keepalive: 30
    });

    client.on('connect', function () {
      connected = true;
      setConn('');
      Object.keys(desired).forEach(function (t) { client.subscribe(t, desired[t]); });
      publishProfile();
      publishPresence();
      clearInterval(presenceTimer);
      presenceTimer = setInterval(publishPresence, 25000);
    });
    client.on('reconnect', function () { setConn('正在重连…', true); });
    client.on('close', function () { connected = false; setConn('连接断开，正在重试…', true); });
    client.on('error', function () { connected = false; setConn('连不上服务器，检查一下网络', true); });
    client.on('message', onMessage);
  }

  function publishPresence() {
    pub(NS + '/p/' + me.pid, te.encode(JSON.stringify({ t: Date.now(), n: me.name })), { retain: true, qos: 0 });
  }

  async function publishProfile() {
    var h = await nameHash(me.name);
    var body = te.encode(JSON.stringify({ v: 1, pid: me.pid, n: me.name, pk: me.pub, t: Date.now() }));
    pub(NS + '/d/' + h + '/' + me.pid, body, { retain: true, qos: 1 });
  }

  function onMessage(topic, payload) {
    var p = topic.split('/');
    if (p[0] !== NS) return;

    if (p[1] === 'u' && p[3] === 'm') {
      var m = /^([a-z0-9]+)_([a-z0-9]+)_(\d+)_(\d+)$/.exec(p[4]);
      if (m) addChunk(m[1], m[2], +m[3], +m[4], new Uint8Array(payload));
      return;
    }
    if (p[1] === 'd' && p[3]) { onDirEntry(p[2], p[3], new Uint8Array(payload)); return; }
    if (p[1] === 'r' && p[3] === me.pid) { onReadMark(p[2], new Uint8Array(payload)); return; }
    if (p[1] === 'p' && p[2]) { onPresence(p[2], new Uint8Array(payload)); return; }
  }

  function onPresence(pid, bytes) {
    try {
      var o = JSON.parse(td.decode(bytes));
      if (o && o.t) presence[pid] = o.t;
    } catch (e) {}
    if (pid === activePeer) updatePeerStatus();
  }

  function onReadMark(readerPid, bytes) {
    try {
      var o = JSON.parse(td.decode(bytes));
      if (!o || !o.t) return;
      peerRead[readerPid] = o.t;
    } catch (e) { return; }
    if (readerPid === activePeer) renderMessages(activePeer);
    renderChatList();
  }

  function onDirEntry(hash, pid, bytes) {
    var e;
    try { e = JSON.parse(td.decode(bytes)); } catch (err) { return; }
    if (!e || e.pid !== pid) return;
    dirCache[pid] = e;

    var c = findContact(pid);
    if (c) {
      var ch = false;
      if (e.n && c.name !== e.n) { c.name = e.n; ch = true; }
      if (e.pk && !c.pub) { c.pub = e.pk; ch = true; }
      if (ch) {
        lsSet(LS_CONTACT, contacts);
        renderChatList();
        if (pid === activePeer) {
          paintAvatar($('peer-avatar'), c.name, pid);
          $('peer-name').textContent = c.name;
        }
      }
    }
    if (activeSearch && activeSearch.hash === hash) {
      activeSearch.hits[pid] = e;
      renderSearchResults();
    }
  }

  /* ==========================================================
     消息分片
     ========================================================== */

  /* 分片主题：NS/u/{信箱主人}/m/{对端pid}_{msgId}_{片号}_{总片数}
     第 0 片开头带发送者的公钥（公钥本来就是公开的） */
  function addChunk(peerPid, msgId, idx, total, bytes) {
    var e = inbox[msgId];
    if (!e) {
      e = inbox[msgId] = {
        peer: peerPid, total: total, parts: {}, missing: {},
        prefix: NS + '/u/' + me.pid + '/m/' + peerPid + '_' + msgId
      };
      for (var i = 0; i < total; i++) e.missing[i] = true;
      e.timer = setTimeout(function () { repair(msgId); }, 3000);
    }
    if (e.parts[idx]) return;
    e.parts[idx] = bytes;
    delete e.missing[idx];

    if (Object.keys(e.parts).length === total) {
      clearTimeout(e.timer);
      delete inbox[msgId];
      assemble(e);
    }
  }

  function repair(msgId) {
    var e = inbox[msgId];
    if (!e) return;
    Object.keys(e.missing).forEach(function (i) {
      var t = e.prefix + '_' + i + '_' + e.total;
      client.subscribe(t, { qos: 1 }, function () {
        setTimeout(function () { client.unsubscribe(t); }, 2500);
      });
    });
    e.timer = setTimeout(function () {
      if (inbox[msgId]) {
        delete inbox[msgId];
        toast('有 1 条消息没收全，刷新一下页面会自动补上', 4500);
      }
    }, 6000);
  }

  async function assemble(e) {
    var idxs = Object.keys(e.parts).map(Number).sort(function (a, b) { return a - b; });
    var first = e.parts[idxs[0]];
    var pkLen = (first[0] << 8) | first[1];
    var pk, rest;
    try {
      pk = JSON.parse(td.decode(first.subarray(2, 2 + pkLen)));
      rest = first.subarray(2 + pkLen);
    } catch (err) { return; }

    // 公钥是我自己的 => 这条是我发的，要和「对端」派生；否则用发送者的公钥
    var mineKey = pk && pk.x && me.pub && pk.x === me.pub.x && pk.y === me.pub.y;
    var keyPub = mineKey ? (findContact(e.peer) || {}).pub : pk;
    if (!keyPub) return;

    var parts = [rest];
    for (var i = 1; i < idxs.length; i++) parts.push(e.parts[idxs[i]]);

    var payload;
    try {
      var key = await sharedKey(e.peer, keyPub);
      payload = unpackPayload(await decryptBlob(key, concat(parts)));
    } catch (err) {
      console.warn('解密失败', err);
      return;
    }
    if (!mineKey) {
      // 顺手把对方的公钥记下来（这样我一定能回消息）
      var c = findContact(e.peer);
      if (c && !c.pub) { c.pub = pk; lsSet(LS_CONTACT, contacts); }
      else if (!c) addContact(e.peer, null, pk);
    }

    deliver(payload);
  }

  function deliver(payload) {
    var h = payload.header;
    if (!h || !h.t || !h.f) return;

    var peerPid = (h.f === me.pid) ? h.to : h.f;
    if (!peerPid) return;

    var id = h.f + '|' + h.to + '|' + h.t + '|' + (h.k || 'text');
    if (seen[id]) return;
    seen[id] = true;

    var msg = {
      id: id, from: h.f, t: h.t, k: h.k || 'text', x: h.x || '',
      mime: h.m || null, name: h.n || null,
      media: payload.media || null, url: null
    };
    if (msg.media) {
      try { msg.url = URL.createObjectURL(new Blob([msg.media], { type: msg.mime || 'image/jpeg' })); } catch (e) {}
    }

    if (!msgs[peerPid]) msgs[peerPid] = [];
    msgs[peerPid].push(msg);
    msgs[peerPid].sort(function (a, b) { return a.t - b.t; });
    if (msgs[peerPid].length > KEEP) msgs[peerPid] = msgs[peerPid].slice(-KEEP);

    if (!findContact(peerPid)) {
      addContact(peerPid, dirCache[peerPid] ? dirCache[peerPid].n : null, null);
      ensureSub(NS + '/d/+/' + peerPid, { qos: 1 });
    }

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

  async function send(peer, header, media) {
    var key = await sharedKey(peer.pid, peer.pub);
    var blob = await encryptBlob(key, packPayload(header, media));
    var total = Math.max(1, Math.ceil(blob.length / CHUNK));
    var msgId = randId(10);
    var pkBytes = te.encode(JSON.stringify(me.pub));
    var jobs = [];

    for (var i = 0; i < total; i++) {
      var part = blob.subarray(i * CHUNK, (i + 1) * CHUNK);
      var out;
      if (i === 0) {
        out = new Uint8Array(2 + pkBytes.length + part.length);
        out[0] = (pkBytes.length >> 8) & 255;
        out[1] = pkBytes.length & 255;
        out.set(pkBytes, 2);
        out.set(part, 2 + pkBytes.length);
      } else {
        out = part;
      }
      var leafMine = peer.pid + '_' + msgId + '_' + i + '_' + total;
      var leafPeer = me.pid + '_' + msgId + '_' + i + '_' + total;
      jobs.push(pub(NS + '/u/' + me.pid + '/m/' + leafMine, out));
      jobs.push(pub(NS + '/u/' + peer.pid + '/m/' + leafPeer, out));
    }
    await Promise.all(jobs);
  }

  function markRead(peerPid) {
    if (!peerPid) return;
    myRead[peerPid] = Date.now();
    lsSet(LS_READ, myRead);
    pub(NS + '/r/' + me.pid + '/' + peerPid, te.encode(JSON.stringify({ t: myRead[peerPid] })), { retain: true, qos: 0 });
    renderChatList();
  }

  function unreadOf(pid) {
    var since = myRead[pid] || 0;
    var n = 0;
    (msgs[pid] || []).forEach(function (m) { if (m.from !== me.pid && m.t > since) n++; });
    return n;
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
     界面
     ========================================================== */

  function previewOf(m) {
    if (!m) return '还没有消息';
    if (m.k === 'image') return m.x ? '🖼️ ' + m.x : '🖼️ 图片';
    return (m.x || '').replace(/\s+/g, ' ').slice(0, 60);
  }
  function lastMsg(pid) {
    var a = msgs[pid];
    return a && a.length ? a[a.length - 1] : null;
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
      top.appendChild(el('div', 'chat-row-name', c.name));

      var lm = lastMsg(c.pid);
      var unread = (c.pid === activePeer) ? 0 : unreadOf(c.pid);
      top.appendChild(el('div', 'chat-row-time' + (unread ? ' unread' : ''), lm ? fmtListTime(lm.t) : ''));
      main.appendChild(top);

      var bot = el('div', 'chat-row-bot');
      var prev = previewOf(lm);
      if (lm && lm.from === me.pid) prev = '你：' + prev;
      bot.appendChild(el('div', 'chat-row-preview', prev));
      if (unread) bot.appendChild(el('div', 'badge', String(unread)));
      main.appendChild(bot);
      row.appendChild(main);

      row.addEventListener('click', function () { openChat(c.pid); });
      box.appendChild(row);
    });
  }

  function messageNode(m, peerPid) {
    var mine = m.from === me.pid;
    var row = el('div', 'msg-row ' + (mine ? 'out' : 'in'));
    row.dataset.mid = m.id;
    var bubble = el('div', 'bubble');

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
      t.textContent = m.x;
      bubble.appendChild(t);
    }

    var meta = el('div', 'meta');
    meta.appendChild(el('span', 'time', fmtTime(m.t)));
    if (mine) {
      var isRead = !!(peerRead[peerPid] && m.t <= peerRead[peerPid]);
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
    var list = msgs[peerPid] || [];
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
    var list = msgs[activePeer] || [];
    // 补回来的旧消息（不是最后一条）→ 整段重画，保证顺序对
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
    var p = presence[activePeer];
    $('peer-status').textContent = p ? fmtAgo(p) : '好友';
  }

  function openChat(pid) {
    var c = findContact(pid);
    if (!c) return;
    activePeer = pid;

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

  function renderSearchResults() {
    var box = $('search-results');
    box.innerHTML = '';
    if (!activeSearch) { box.classList.add('hidden'); return; }

    var hits = Object.keys(activeSearch.hits).map(function (k) { return activeSearch.hits[k]; });

    if (!hits.length) {
      if (activeSearch.loading) {
        box.appendChild(el('div', 'search-empty', '搜索中…'));
      } else {
        box.appendChild(el('div', 'search-empty',
          '没找到叫「' + activeSearch.name + '」的人。\n\n名字要一字不差（空格、大小写不影响）。让对方确认一下他的名字。'));
      }
    } else {
      hits.forEach(function (e) {
        var item = el('div', 'search-item');
        var av = el('div', 'avatar sm');
        paintAvatar(av, e.n, e.pid);
        item.appendChild(av);
        var info = el('div');
        info.appendChild(el('div', 'name', e.n));
        info.appendChild(el('div', 'sub', findContact(e.pid) ? '已在列表里，点击打开' : '点击开始聊天'));
        item.appendChild(info);
        item.addEventListener('click', function () {
          box.classList.add('hidden');
          $('input-search').value = '';
          $('btn-clear-search').classList.add('hidden');
          addContact(e.pid, e.n, e.pk);
          openChat(e.pid);
        });
        box.appendChild(item);
      });
    }
    box.classList.remove('hidden');
  }

  async function doSearch(name) {
    var h = await nameHash(name);
    var topic = NS + '/d/' + h + '/+';
    activeSearch = { hash: h, name: name, hits: {}, loading: true, topic: topic };
    renderSearchResults();

    var ok = await whenConnected();
    if (!ok) {
      activeSearch.loading = false;
      renderSearchResults();
      toast('还没连上服务器，等左下角不报错了再搜', 4000);
      return;
    }
    if (!activeSearch || activeSearch.topic !== topic) return;   // 已经换了新的搜索

    client.subscribe(topic, { qos: 1 }, function () {
      setTimeout(function () {
        client.unsubscribe(topic);
        if (activeSearch && activeSearch.topic === topic) {
          activeSearch.loading = false;
          renderSearchResults();
        }
      }, 2200);
    });
  }

  /* ==========================================================
     启动
     ========================================================== */

  function showScreen(which) {
    $('screen-onboarding').classList.toggle('hidden', which !== 'onboarding');
    $('main').classList.toggle('hidden', which !== 'main');
  }

  async function boot() {
    applyTheme(lsGet(LS_THEME, 'light'));

    if (!window.crypto || !crypto.subtle) {
      showScreen('onboarding');
      $('onboarding-error').textContent = '这个页面必须用 https 打开（或 localhost），浏览器才允许用加密功能。';
      $('btn-start').disabled = true;
      return;
    }
    if (!window.mqtt) {
      showScreen('onboarding');
      $('onboarding-error').textContent = '通讯组件没加载出来，确认 vendor/mqtt.min.js 在不在。';
      $('btn-start').disabled = true;
      return;
    }

    contacts = lsGet(LS_CONTACT, []) || [];
    myRead = lsGet(LS_READ, {}) || {};

    var id = lsGet(LS_ID, null);
    if (!id || !id.pid || !id.priv) { showScreen('onboarding'); return; }

    me = id;
    showScreen('main');
    wireMain();
    startUp();
  }

  function startUp() {
    $('me-tag').textContent = me.name;
    $('my-id-note').textContent = '你的账号 ID：' + me.pid + '（好友搜名字就能找到你）';
    renderChatList();
    connectBroker();
    ensureSub(NS + '/u/' + me.pid + '/m/+', { qos: 1 });
    ensureSub(NS + '/r/+/' + me.pid, { qos: 0 });
  }

  /* ==========================================================
     发送动作
     ========================================================== */

  async function sendText() {
    var input = $('input-msg');
    var text = input.value.trim();
    if (!text || !activePeer || uploading) return;
    var c = findContact(activePeer);
    if (!c || !c.pub) { toast('还没拿到对方的公钥，让对方先给你发一条消息'); return; }
    input.value = '';
    autoGrow(input);
    try {
      await send(c, { v: 1, f: me.pid, to: c.pid, t: Date.now(), k: 'text', x: text }, null);
    } catch (e) {
      toast('发送失败：' + (e.message || e));
    }
  }

  async function sendImage(file) {
    if (!activePeer || uploading) return;
    var c = findContact(activePeer);
    if (!c || !c.pub) { toast('还没拿到对方的公钥，让对方先给你发一条消息'); return; }

    uploading = true;
    $('upload-bar').classList.remove('hidden');
    $('upload-text').textContent = '正在压缩图片…';
    try {
      var r = await compressImage(file);
      $('upload-text').textContent = '正在发送（' + Math.round(r.size / 1024) + 'KB）…';
      await send(c, {
        v: 1, f: me.pid, to: c.pid, t: Date.now(), k: 'image',
        m: 'image/jpeg', w: r.w, h: r.h, n: file.name || '图片.jpg'
      }, r.bytes);
    } catch (e) {
      toast('图片发送失败：' + (e.message || e), 4500);
    } finally {
      uploading = false;
      $('upload-bar').classList.add('hidden');
    }
  }

  /* ==========================================================
     事件绑定
     ========================================================== */

  $('form-onboarding').addEventListener('submit', async function (ev) {
    ev.preventDefault();
    var name = $('input-name').value.trim();
    if (!name) { $('onboarding-error').textContent = '先起个名字吧'; return; }
    var btn = $('btn-start');
    btn.disabled = true;
    btn.textContent = '正在创建身份…';
    $('onboarding-error').textContent = '';
    try {
      me = await createIdentity(name);
      lsSet(LS_ID, me);
      showScreen('main');
      wireMain();
      startUp();
    } catch (e) {
      $('onboarding-error').textContent = '创建身份失败：' + (e.message || e);
      btn.disabled = false;
      btn.textContent = '开始聊天';
    }
  });

  var wired = false;
  function wireMain() {
    if (wired) return;
    wired = true;

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
          ev.target !== clear && !searchBtn.contains(ev.target)) {
        box.classList.add('hidden');
      }
    });

    $('btn-back').addEventListener('click', function () {
      $('main').classList.remove('chat-open');
      activePeer = null;
      $('chat-active').classList.add('hidden');
      $('chat-empty').classList.remove('hidden');
      renderChatList();
    });

    var msgInput = $('input-msg');
    msgInput.addEventListener('input', function () { autoGrow(msgInput); });
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

    $('btn-theme').addEventListener('click', function () {
      var next = document.documentElement.getAttribute('data-theme') === 'dark' ? 'light' : 'dark';
      applyTheme(next);
      lsSet(LS_THEME, next);
    });

    $('btn-me').addEventListener('click', function () {
      $('input-me-name').value = me.name;
      $('my-id-note').textContent = '你的账号 ID：' + me.pid + '（好友搜名字就能找到你）';
      $('modal-me').classList.remove('hidden');
      setTimeout(function () { $('input-me-name').focus(); }, 30);
    });
    $('btn-me-cancel').addEventListener('click', function () { $('modal-me').classList.add('hidden'); });
    $('modal-me').addEventListener('click', function (e) { if (e.target === $('modal-me')) $('modal-me').classList.add('hidden'); });
    $('btn-me-save').addEventListener('click', function () {
      var name = $('input-me-name').value.trim();
      if (!name) return;
      me.name = name;
      lsSet(LS_ID, me);
      $('me-tag').textContent = name;
      $('modal-me').classList.add('hidden');
      publishProfile();
      publishPresence();
      toast('名字改好了，好友现在能搜到新名字');
    });
    $('btn-signout').addEventListener('click', function () {
      if (!confirm('清空后本机聊天记录和身份都没了，重新起名就是新账号。确定吗？')) return;
      localStorage.removeItem(LS_ID);
      localStorage.removeItem(LS_CONTACT);
      localStorage.removeItem(LS_READ);
      location.reload();
    });

    $('btn-safety').addEventListener('click', async function () {
      var c = activePeer ? findContact(activePeer) : null;
      if (!c || !c.pub) { toast('还没拿到对方的公钥，收到他一条消息后再看'); return; }
      $('safety-num').textContent = await safetyNumber(c.pid, c.pub);
      $('modal-safety').classList.remove('hidden');
    });
    $('btn-safety-ok').addEventListener('click', function () { $('modal-safety').classList.add('hidden'); });
    $('modal-safety').addEventListener('click', function (e) { if (e.target === $('modal-safety')) $('modal-safety').classList.add('hidden'); });

    var EMOJIS = ['😀','😃','😄','😁','😆','😅','😂','🤣','🙂','🙃','😉','😊','😇','🥰','😍','😘',
                  '😜','🤪','🤗','🤔','🤨','😐','😴','🥱','😢','😭','😤','😡','🥺','😱','🤯','😎',
                  '👍','👎','👌','🙏','👏','🤝','💪','✌️','🫶','❤️','🔥','✨','🎉','🎁','🌹','☕',
                  '🍺','🍜','🍕','⚽','🚀','🌈','☀️','🌙','⭐','💯','✅','❌','⏰','📌','💡','🐶'];
    var pop = $('emoji-pop');
    EMOJIS.forEach(function (e) {
      var b = el('button', null, e);
      b.type = 'button';
      b.addEventListener('click', function () {
        msgInput.value += e; autoGrow(msgInput); msgInput.focus();
      });
      pop.appendChild(b);
    });
    $('btn-emoji').addEventListener('click', function (ev) {
      ev.stopPropagation();
      pop.classList.toggle('hidden');
    });
    document.addEventListener('click', function (ev) {
      if (!pop.classList.contains('hidden') && !pop.contains(ev.target) && ev.target !== $('btn-emoji')) pop.classList.add('hidden');
    });

    $('btn-lightbox-close').addEventListener('click', closeLightbox);
    $('lightbox').addEventListener('click', function (e) { if (e.target === $('lightbox')) closeLightbox(); });
    document.addEventListener('keydown', function (e) {
      if (e.key === 'Escape') {
        closeLightbox();
        $('modal-me').classList.add('hidden');
        $('modal-safety').classList.add('hidden');
        pop.classList.add('hidden');
      }
    });
    document.addEventListener('visibilitychange', function () {
      if (!document.hidden && activePeer) markRead(activePeer);
    });
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
