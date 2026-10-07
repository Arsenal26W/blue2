'use strict';
(() => {
  const $ = (s) => document.querySelector(s);

  // 게임이 직접 쓰는 세이브/설정 파일
  const SAVE_FILES = ['AFRICA2.SAV'];
  // 낱개 파일로 넣을 때 꼭 있어야 하는 파일
  const REQUIRED = ['AFR2CD.EXE', 'AFR2CD.INI', 'DOS4GW.EXE', 'FONT.DAT', 'AFRPIC.DAT', 'ENGLISH.FNT',
    'HANGUL.FNT', 'KOR.OMF', 'TITLE.OMF', 'MUSIC.AD', 'MUSIC.ADV', 'MUSIC.COM', 'SOUND.COM', 'PANDA.CFG'];
  const SKIP = /\.PIF$|^RETROMON\./;
  const KEY = { esc: 256, enter: 257, space: 32, backspace: 259, tab: 258, up: 265, down: 264, left: 263, right: 262, shift: 340 };
  // 성능 단계: 에뮬레이터가 한 번에 돌리는 CPU 양
  const PERF = {
    light: { label: '가볍게', cycles: 'fixed 20000' },
    normal: { label: '보통', cycles: 'fixed 40000' },
    max: { label: '최대', cycles: 'max' },
  };
  const PERF_ORDER = ['normal', 'light', 'max'];
  const prefs = Object.assign({ perf: 'normal', hideCursor: true, render: 'smooth', guideSeen: false, enterBar: true, remind: true, engine: 'main' },
    (() => { try { return JSON.parse(localStorage.getItem('africa2-prefs') || '{}'); } catch (_) { return {}; } })());
  const savePrefs = () => { try { localStorage.setItem('africa2-prefs', JSON.stringify(prefs)); } catch (_) { /* 무시 */ } };

  const state = { game: null, saves: { files: {}, zip: null, updated: 0 } };
  let dosProps = null;
  let ci = null;
  let syncTimer = 0;
  let syncing = false;
  let watchdog = 0;
  let wakeLock = null;
  let workingPath = null;
  let lastInput = 0;
  let persistTried = false;
  let lastSyncAt = Date.now();
  let retryTimer = 0;

  /* ───────── 개발용: ?insets=위,오른쪽,아래,왼쪽 으로 안전 영역 흉내 ───────── */
  const qs = new URLSearchParams(location.search);
  if (qs.get('insets')) {
    const [t, r, b, l] = qs.get('insets').split(',').map((v) => (parseFloat(v) || 0) + 'px');
    const st = document.documentElement.style;
    st.setProperty('--sat', t); st.setProperty('--sar', r); st.setProperty('--sab', b); st.setProperty('--sal', l);
  }

  /* ───────── IndexedDB ───────── */
  let dbPromise = null;
  function db() {
    if (!dbPromise) {
      dbPromise = new Promise((resolve, reject) => {
        const req = indexedDB.open('africa2', 1);
        req.onupgradeneeded = () => req.result.createObjectStore('kv');
        req.onsuccess = () => resolve(req.result);
        req.onerror = () => reject(req.error);
      });
    }
    return dbPromise;
  }
  async function idbGet(key) {
    const d = await db();
    return new Promise((resolve, reject) => {
      const r = d.transaction('kv').objectStore('kv').get(key);
      r.onsuccess = () => resolve(r.result);
      r.onerror = () => reject(r.error);
    });
  }
  async function idbSet(key, value) {
    const d = await db();
    return new Promise((resolve, reject) => {
      const tx = d.transaction('kv', 'readwrite');
      tx.objectStore('kv').put(value, key);
      tx.oncomplete = () => resolve();
      tx.onerror = () => reject(tx.error);
      tx.onabort = () => reject(tx.error || new Error('저장 공간에 쓰지 못했어요.'));
    });
  }

  /* ───────── 작은 도구들 ───────── */
  function hash(u8) {
    let h = 0x811c9dc5;
    for (let i = 0; i < u8.length; i++) { h ^= u8[i]; h = Math.imul(h, 0x01000193); }
    return (h >>> 0).toString(16) + ':' + u8.length;
  }
  function withTimeout(p, ms) {
    return Promise.race([p, new Promise((_, rej) => setTimeout(() => rej(new Error('timeout')), ms))]);
  }
  const sleep = (ms) => new Promise((r) => setTimeout(r, ms));
  let toastTimer = 0;
  function toast(msg, ms = 2400) {
    const t = $('#toast');
    t.textContent = msg; t.classList.add('show');
    clearTimeout(toastTimer); toastTimer = setTimeout(() => t.classList.remove('show'), ms);
  }
  function busy(msg) {
    const b = $('#busy');
    if (msg) { b.textContent = msg; b.hidden = false; } else b.hidden = true;
  }
  function showError(msg) {
    const e = $('#error');
    if (msg) { e.textContent = msg; e.hidden = false; } else e.hidden = true;
  }
  function fmtTime(ms) {
    const d = new Date(ms);
    return `${d.getMonth() + 1}월 ${d.getDate()}일 ${String(d.getHours()).padStart(2, '0')}:${String(d.getMinutes()).padStart(2, '0')}`;
  }
  const isStandalone = () => window.navigator.standalone === true || matchMedia('(display-mode: standalone), (display-mode: fullscreen)').matches;
  const isIOS = () => /iPhone|iPad|iPod/.test(navigator.userAgent) || (navigator.platform === 'MacIntel' && navigator.maxTouchPoints > 1);

  /* ───────── zip 목차 읽기 (압축은 풀지 않음) ───────── */
  function zipNames(u8) {
    const dv = new DataView(u8.buffer, u8.byteOffset, u8.byteLength);
    let eocd = -1;
    for (let i = u8.length - 22; i >= Math.max(0, u8.length - 65557); i--) {
      if (dv.getUint32(i, true) === 0x06054b50) { eocd = i; break; }
    }
    if (eocd < 0) throw new Error('zip 파일을 읽지 못했어요. 파일이 손상됐을 수 있어요.');
    const count = dv.getUint16(eocd + 10, true);
    let p = dv.getUint32(eocd + 16, true);
    const entries = [];
    const utf8 = new TextDecoder('utf-8');
    for (let n = 0; n < count && p + 46 <= u8.length; n++) {
      if (dv.getUint32(p, true) !== 0x02014b50) break;
      const nl = dv.getUint16(p + 28, true), el = dv.getUint16(p + 30, true), cl = dv.getUint16(p + 32, true);
      entries.push({
        name: utf8.decode(u8.subarray(p + 46, p + 46 + nl)),
        method: dv.getUint16(p + 10, true),
        csize: dv.getUint32(p + 20, true),
        local: dv.getUint32(p + 42, true),
      });
      p += 46 + nl + el + cl;
    }
    return entries;
  }

  // zip을 낱개 파일로 풀기 (아이폰 기본 기능 사용)
  async function inflateRaw(u8) {
    const stream = new Blob([u8]).stream().pipeThrough(new DecompressionStream('deflate-raw'));
    return new Uint8Array(await new Response(stream).arrayBuffer());
  }
  async function unzipGame(buf) {
    const u8 = new Uint8Array(buf);
    const dv = new DataView(buf);
    const entries = zipNames(u8);
    const info = analyzeZip(entries.map((e) => e.name));
    const files = [];
    let size = 0;
    for (const e of entries) {
      if (e.name.endsWith('/')) continue;
      if (!e.name.toLowerCase().startsWith(info.root.toLowerCase())) continue;
      const rel = e.name.slice(info.root.length);
      if (rel.includes('/')) continue; // 하위 폴더는 게임에 필요 없음
      const upper = rel.toUpperCase();
      if (SKIP.test(upper)) continue;
      const isIso = e.name === info.iso;
      if (/\.ISO$/.test(upper) && !isIso) continue;
      const lo = e.local;
      if (dv.getUint32(lo, true) !== 0x04034b50) throw new Error('zip 파일 구조가 이상해요.');
      const start = lo + 30 + dv.getUint16(lo + 26, true) + dv.getUint16(lo + 28, true);
      const raw = u8.subarray(start, start + e.csize);
      let data;
      if (e.method === 0) data = raw.slice();
      else if (e.method === 8) data = await inflateRaw(raw);
      else throw new Error('지원하지 않는 압축 방식이에요. 일반 zip으로 다시 압축해주세요.');
      size += data.byteLength;
      files.push({ name: isIso ? 'CD.ISO' : upper, data: data.buffer });
    }
    return { kind: 'files', files, root: '', iso: 'CD.ISO', size };
  }
  const canUnzip = () => typeof DecompressionStream === 'function';
  function analyzeZip(names) {
    const exe = names.find((n) => /(^|\/)AFR2CD\.EXE$/i.test(n));
    if (!exe) throw new Error('zip 안에 AFR2CD.EXE가 없어요. 게임 폴더를 통째로 압축했는지 확인해주세요.');
    const root = exe.slice(0, exe.length - 'AFR2CD.EXE'.length);
    const isos = names.filter((n) => /\.iso$/i.test(n));
    const iso = isos.find((n) => n.toLowerCase().startsWith(root.toLowerCase())) || isos[0];
    if (!iso) throw new Error('zip 안에 CD 이미지(.iso)가 없어요. Arf2.iso를 함께 넣어주세요.');
    return { root, iso };
  }

  /* ───────── 게임 파일 넣기 ───────── */
  async function importGame(fileList) {
    const files = [...fileList];
    if (!files.length) return;
    showError(null);
    busy('게임 파일을 읽는 중');
    try {
      let rec;
      if (files.length === 1 && /\.zip$/i.test(files[0].name)) {
        const buf = await files[0].arrayBuffer();
        if (canUnzip()) {
          busy('게임 파일을 푸는 중');
          rec = await unzipGame(buf);
        } else {
          const info = analyzeZip(zipNames(new Uint8Array(buf)).map((e) => e.name));
          rec = { kind: 'zip', data: buf, root: info.root, iso: info.iso, size: buf.byteLength };
        }
      } else {
        const byName = new Map();
        let iso = null;
        for (const f of files) {
          const n = f.name.toUpperCase();
          if (SKIP.test(n)) continue;
          if (/\.ISO$/.test(n)) { iso = iso || f; continue; }
          byName.set(n, f);
        }
        const missing = REQUIRED.filter((n) => !byName.has(n));
        if (!iso) missing.push('CD 이미지(.iso)');
        if (missing.length) throw new Error('빠진 파일이 있어요: ' + missing.join(', '));
        const out = [];
        let size = 0;
        for (const [name, f] of byName) { const data = await f.arrayBuffer(); size += data.byteLength; out.push({ name, data }); }
        const isoData = await iso.arrayBuffer(); size += isoData.byteLength;
        out.push({ name: 'CD.ISO', data: isoData });
        rec = { kind: 'files', files: out, root: '', iso: 'CD.ISO', size };
      }
      await idbSet('game', rec);
      await idbSet('game-meta', metaOf(rec));
      state.game = rec;
      try { await navigator.storage?.persist?.(); } catch (_) { /* 무시 */ }
      toast('게임 파일을 넣었어요');
    } catch (e) {
      showError(e && e.name === 'QuotaExceededError'
        ? '아이폰 저장 공간이 부족해요. 공간을 비운 뒤 다시 넣어주세요.'
        : (e && e.message) || '게임 파일을 넣지 못했어요.');
    } finally {
      busy(null);
      renderLauncher();
    }
  }

  function metaOf(rec) { return { kind: rec.kind, root: rec.root || '', iso: rec.iso, size: rec.size, meta: true }; }

  /* ───────── DOSBox 설정 ───────── */
  function q(p) { return /\s/.test(p) ? `"${p}"` : p; }
  function buildConf(game) {
    const root = (game.root || '').replace(/\/$/, '');
    const isoHost = game.iso;
    let isoDos = isoHost;
    if (game.root && isoHost.toLowerCase().startsWith(game.root.toLowerCase())) isoDos = isoHost.slice(game.root.length);
    isoDos = isoDos.replace(/\//g, '\\');
    const dosFallback = /^[\x21-\x7e\\]+$/.test(isoDos) ? `imgmount d C:\\${isoDos} -t iso` : 'rem';
    return [
      '[sdl]', 'autolock=false', 'fullscreen=false', '',
      '[dosbox]', 'machine=svga_s3', 'memsize=16', '',
      '[cpu]', 'core=auto', 'cputype=auto', `cycles=${(PERF[prefs.perf] || PERF.normal).cycles}`, 'cycleup=2000', 'cycledown=2000', '',
      '[render]', 'frameskip=0', 'aspect=false', 'scaler=none', '',
      '[mixer]', 'nosound=false', 'rate=22050', 'blocksize=1024', 'prebuffer=60', '',
      '[sblaster]', 'sbtype=sb16', 'sbbase=220', 'irq=7', 'dma=1', 'hdma=5', 'oplmode=auto', 'oplrate=22050', '',
      '[speaker]', 'pcspeaker=false', '',
      '[dos]', 'xms=true', 'ems=true', 'umb=true', '',
      '[autoexec]',
      '@echo off',
      `mount c ${root ? q(root) : '.'}`,
      'c:',
      `imgmount d ${q(isoHost)} -t iso`,
      'if exist D:\\AFR2CD\\CODE.PAK goto run',
      dosFallback,
      ':run',
      'afr2cd',
      '',
    ].join('\n');
  }

  // CD 이미지(ISO9660) 안에서 파일 위치 찾기
  function isoFind(u8, parts) {
    const dv = new DataView(u8.buffer, u8.byteOffset, u8.byteLength);
    const pvd = 16 * 2048;
    if (u8.length < pvd + 2048 || String.fromCharCode(...u8.subarray(pvd + 1, pvd + 6)) !== 'CD001') return null;
    let lba = dv.getUint32(pvd + 158, true), size = dv.getUint32(pvd + 166, true);
    for (let depth = 0; depth < parts.length; depth++) {
      let p = lba * 2048;
      const end = Math.min(p + size, u8.length);
      let found = null;
      while (p < end) {
        const len = u8[p];
        if (len === 0) { p = (Math.floor(p / 2048) + 1) * 2048; continue; }
        const nl = u8[p + 32];
        let name = String.fromCharCode(...u8.subarray(p + 33, p + 33 + nl)).split(';')[0].toUpperCase();
        if (name.endsWith('.')) name = name.slice(0, -1);
        if (name === parts[depth]) { found = { lba: dv.getUint32(p + 2, true), size: dv.getUint32(p + 10, true) }; break; }
        p += len;
      }
      if (!found) return null;
      lba = found.lba; size = found.size;
    }
    return { offset: lba * 2048, size };
  }
  // CURSOR.PAK의 첫 번째 그림(지팡이)을 투명(0)으로 칠하기. 메모리에서만 바꾸고 원본은 그대로.
  function hideWandCursor(iso) {
    try {
      const f = isoFind(iso, ['AFR2CD', 'CURSOR.PAK']);
      if (!f || f.offset + f.size > iso.length) return false;
      const dv = new DataView(iso.buffer, iso.byteOffset + f.offset, f.size);
      const a = dv.getUint32(0, true), b = dv.getUint32(4, true);
      if (a !== 36 || b <= a || b > f.size) return false;
      iso.fill(0, f.offset + a, f.offset + b);
      return true;
    } catch (_) { return false; }
  }

  function buildInitFs(game, saves) {
    const fs = [];
    if (game.kind === 'zip') fs.push(new Uint8Array(game.data));
    else {
      for (const f of game.files) {
        const contents = new Uint8Array(f.data);
        if (f.name === 'CD.ISO' && prefs.hideCursor) hideWandCursor(contents);
        fs.push({ path: f.name, contents });
      }
    }
    if (saves.zip && saves.zip.data) fs.push(new Uint8Array(saves.zip.data));
    const base = game.root || '';
    for (const [name, rec] of Object.entries(saves.files || {})) {
      if (rec && rec.data) fs.push({ path: base + name, contents: new Uint8Array(rec.data) });
    }
    return fs;
  }

  /* ───────── 게임 실행 ───────── */
  async function startGame() {
    if (!state.game) return;
    showError(null);
    try { if (navigator.audioSession) navigator.audioSession.type = 'playback'; } catch (_) { /* 무시 */ }
    $('#launcher').hidden = true;
    $('#play').hidden = false;
    layout();
    requestWake();

    if (!window.Dos) {
      for (let i = 0; i < 50 && !window.Dos && !window.__dosLoadFailed; i++) await sleep(200);
    }
    if (!window.Dos) {
      loadingFail('실행기를 내려받지 못했어요. 인터넷에 연결된 상태에서 다시 열어주세요. 처음 실행할 때만 인터넷이 필요해요.');
      return;
    }

    if (state.game.meta || state.game.released) {
      $('#loading-msg').textContent = '게임 파일을 불러오는 중이에요.';
      const full = await idbGet('game');
      if (!full) { loadingFail('저장된 게임 파일을 찾지 못했어요. 처음 화면에서 게임 파일을 다시 넣어주세요.'); return; }
      state.game = full;
    }
    if (state.game.kind === 'zip' && canUnzip()) {
      $('#loading-msg').textContent = '처음 한 번만 게임 파일을 정리하는 중이에요.';
      try {
        const rec = await unzipGame(state.game.data);
        await idbSet('game', rec);
        await idbSet('game-meta', metaOf(rec));
        state.game = rec;
      } catch (_) { /* 실패하면 zip 그대로 실행 */ }
    }
    $('#loading-msg').textContent = '게임 파일을 준비하는 중이에요.';
    await sleep(30);
    let initFs;
    try { initFs = buildInitFs(state.game, state.saves); } catch (e) {
      loadingFail('게임 파일을 읽지 못했어요. 처음 화면에서 게임 파일을 다시 넣어주세요.');
      return;
    }

    watchdog = setTimeout(() => {
      if (!ci) loadingFail('게임이 시작되지 않았어요. 인터넷 연결을 확인하고 다시 시도해주세요.');
    }, 60000);

    try {
      dosProps = window.Dos($('#dos'), {
        dosboxConf: buildConf(state.game),
        jsdosConf: { version: 'js-dos-8' },
        initFs,
        kiosk: true,
        autoStart: true,
        noCloud: true,
        noNetworking: true,
        theme: 'dark',
        renderAspect: '4/3',
        imageRendering: prefs.render,
        mouseCapture: false,
        // '절약' 방식: 에뮬레이터를 화면과 같은 곳에서 돌려 매 장면·소리마다 생기던 데이터 복사를 없앤다
        workerThread: prefs.engine !== 'main',
        // 세이브는 이 앱이 직접 관리하므로 실행기 자체 저장 기능은 끈다
        fsChanges: { local: false },
        autoSave: false,
        quickSave: false,
        onEvent: (ev, arg) => { if (ev === 'ci-ready') onCiReady(arg); },
      });
    } catch (e) {
      loadingFail('실행기를 시작하지 못했어요: ' + (e && e.message ? e.message : e));
    }
  }

  function onCiReady(c) {
    ci = c;
    clearTimeout(watchdog);
    $('#loading').hidden = true;
    clearInterval(syncTimer);
    syncTimer = setInterval(() => syncSaves(false), 60000);
    if (prefs.guideSeen !== 2 && !resumedAfterCrash) $('#guide').hidden = false;
    startSession();
    // 실행기에 넘겨준 게임 파일(약 50MB)을 이쪽 메모리에서 비운다. 실행기 안에는 이미 복사돼 있다.
    setTimeout(releaseGameData, 4000);
    if (resumedAfterCrash) {
      const msg = lastEnd && lastEnd.vis === 'hidden'
        ? '지난 게임이 끝나지 않은 채 닫혀서 바로 다시 열었어요. 게임 안의 불러오기로 이어서 하세요.'
        : '앱이 갑자기 꺼져서 다시 열었어요. 게임 안의 불러오기로 이어서 하세요.';
      setTimeout(() => toast(msg, 6000), 1500);
    }
  }

  /* ───────── 일시정지 (메뉴를 열었거나 다른 앱으로 갔을 때) ───────── */
  let paused = false;
  function pauseEmu(p) {
    if (!ci || paused === p) return;
    paused = p;
    try { if (p) ci.pause(); else ci.resume(); } catch (_) { /* 무시 */ }
  }

  /* ───────── 메모리 줄이기 ─────────
     아이폰은 웹앱이 메모리를 많이 쓰면 경고 없이 앱을 다시 시작시킨다(처음 화면으로 튕김).
     게임 파일은 실행기 안에 복사본이 있으므로, 이쪽에 들고 있던 원본은 바로 놓아준다. */
  function releaseGameData() {
    if (!state.game || state.game.released) return;
    const bufs = [];
    if (state.game.kind === 'files') { for (const f of state.game.files) if (f.data && f.data.byteLength) bufs.push(f.data); }
    else if (state.game.data && state.game.data.byteLength) bufs.push(state.game.data);
    try {
      // 버퍼를 '넘겨버리는' 방식으로 즉시 비운다(넘겨받은 쪽은 바로 버려짐)
      if (bufs.length && typeof structuredClone === 'function') structuredClone(bufs, { transfer: bufs });
    } catch (_) { /* 무시 */ }
    state.game = { kind: state.game.kind, root: state.game.root, iso: state.game.iso, size: state.game.size, released: true };
  }

  /* ───────── 갑자기 꺼졌을 때 대비 ─────────
     게임 중에는 10초마다 '살아 있음'을 적어둔다. 다음에 열 때 정상 종료 표시가 없으면 갑자기 꺼진 것. */
  const SESSION_KEY = 'africa2-session';
  const CRASH_KEY = 'africa2-crashes';
  let session = null;
  let beatTimer = 0;
  let resumedAfterCrash = false;
  let lastEnd = null;
  let lastRemindAt = 0;
  function writeSession() {
    if (!session) return;
    try { localStorage.setItem(SESSION_KEY, JSON.stringify(session)); } catch (_) { /* 무시 */ }
  }
  function startSession() {
    const now = Date.now();
    session = { start: now, beat: now, lastSaveAt: now, vis: 'visible', clean: false };
    writeSession();
    lastRemindAt = now;
    clearInterval(beatTimer);
    beatTimer = setInterval(heartbeat, 10000);
  }
  function endSessionClean() {
    if (session) { session.clean = true; writeSession(); }
    clearInterval(beatTimer);
  }
  let diagTick = 0;
  async function collectDiag() {
    if (!ci || !session) return;
    const d = { t: Math.round((Date.now() - session.start) / 1000), eng: prefs.engine, perf: prefs.perf };
    try {
      if (typeof ci.asyncifyStats === 'function') {
        const st = await withTimeout(ci.asyncifyStats(), 3000);
        if (st) d.st = JSON.stringify(st).slice(0, 300);
      }
    } catch (_) { /* 무시 */ }
    try {
      if (typeof ci.fsTree === 'function') {
        const tree = await withTimeout(ci.fsTree(), 3000);
        let total = 0, n = 0;
        const walk = (node) => { if (!node) return; if (typeof node.size === 'number') { total += node.size; n++; } (node.nodes || []).forEach(walk); };
        walk(tree);
        d.fsMB = Math.round(total / 104857.6) / 10; d.files = n;
      }
    } catch (_) { /* 무시 */ }
    session.diag = d;
    writeSession();
  }
  function heartbeat() {
    if (!session) return;
    const now = Date.now();
    if (++diagTick % 3 === 0 && !document.hidden) collectDiag();
    session.beat = now;
    session.vis = document.hidden ? 'hidden' : 'visible';
    writeSession();
    // 저장 알림: 게임 안에서 10분 넘게 저장하지 않았으면 살짝 알려준다
    if (prefs.remind && !document.hidden && $('#menu').hidden && now - session.lastSaveAt > 600000 && now - lastRemindAt > 600000) {
      lastRemindAt = now;
      const mins = Math.floor((now - session.lastSaveAt) / 60000);
      toast(`마지막 저장 후 ${mins}분 지났어요. 게임 안에서 저장해두면 앱이 꺼져도 이어서 할 수 있어요.`, 5000);
    }
  }
  function readCrashLog() {
    try { return JSON.parse(localStorage.getItem(CRASH_KEY) || '[]'); } catch (_) { return []; }
  }
  // 앱을 열 때: 지난 게임이 정상 종료되지 않았는지 확인
  function checkLastSession() {
    let prev = null;
    try { prev = JSON.parse(localStorage.getItem(SESSION_KEY) || 'null'); } catch (_) { /* 무시 */ }
    try { localStorage.removeItem(SESSION_KEY); } catch (_) { /* 무시 */ }
    if (!prev || prev.clean) return false;
    lastEnd = prev;
    // 화면을 보던 중에 끊긴 것만 '갑자기 꺼짐'으로 기록 (다른 앱으로 간 사이 닫힌 건 제외)
    if (prev.vis !== 'hidden') {
      const log = readCrashLog();
      log.push({ at: prev.beat, mins: Math.round((prev.beat - prev.start) / 60000), perf: prefs.perf, diag: prev.diag || null,
        os: (navigator.userAgent.match(/OS [\d_]+/) || [''])[0] });
      try { localStorage.setItem(CRASH_KEY, JSON.stringify(log.slice(-10))); } catch (_) { /* 무시 */ }
    }
    // 30분 안에 다시 열었으면 곧장 게임을 다시 띄운다
    return Date.now() - prev.beat < 30 * 60000;
  }

  function loadingFail(msg) {
    const l = $('#loading');
    l.hidden = false;
    l.innerHTML = '';
    const s = document.createElement('strong'); s.textContent = '시작하지 못했어요';
    const p = document.createElement('span'); p.textContent = msg;
    const b = document.createElement('button'); b.className = 'ui-btn primary'; b.textContent = '처음 화면으로';
    b.addEventListener('click', () => location.reload());
    l.append(s, p, b);
  }

  /* ───────── 세이브 보관 ───────── */
  async function readGameFile(name) {
    if (!ci || typeof ci.fsReadFile !== 'function') return null;
    const base = state.game.root || '';
    const candidates = workingPath ? [workingPath(name)] : [];
    const makers = [
      (n) => base + n, (n) => base + n.toLowerCase(),
      (n) => '/home/web_user/' + base + n, (n) => '/home/web_user/' + base + n.toLowerCase(),
      (n) => './' + base + n,
    ];
    for (const m of makers) candidates.push(m(name));
    for (let i = 0; i < candidates.length; i++) {
      try {
        const d = await withTimeout(ci.fsReadFile(candidates[i]), 4000);
        if (d && d.length) {
          if (!workingPath) {
            const m = makers.find((mk) => mk(name) === candidates[i]);
            if (m && name === SAVE_FILES[0]) workingPath = m;
          }
          return d instanceof Uint8Array ? d : new Uint8Array(d);
        }
      } catch (_) { /* 다음 후보 */ }
    }
    return null;
  }

  async function syncSaves(manual, force) {
    if (!ci || syncing) { if (manual && !ci) toast('게임이 아직 시작되지 않았어요'); return; }
    // 손가락으로 조작하는 중이면 잠깐 미뤄서 화면이 걸리지 않게 (단, 2분 넘게 미루지는 않음)
    if (!manual && !force && Date.now() - lastInput < 4000 && Date.now() - lastSyncAt < 120000) {
      clearTimeout(retryTimer);
      retryTimer = setTimeout(() => syncSaves(false), 5000);
      return;
    }
    syncing = true;
    let changed = 0, found = 0;
    try {
      for (const name of SAVE_FILES) {
        const data = await readGameFile(name);
        if (!data) continue;
        found++;
        const h = hash(data);
        if (!state.saves.files[name] || state.saves.files[name].h !== h) {
          const first = !state.saves.files[name];
          state.saves.files[name] = { h, data: data.slice().buffer };
          changed++;
          if (!first && session) { session.lastSaveAt = Date.now(); writeSession(); }
        }
      }
      if (!found && !persistTried && typeof ci.persist === 'function') {
        persistTried = true;
        // 파일을 직접 못 읽는 경우: 바뀐 파일 묶음을 통째로 보관
        const z = await withTimeout(ci.persist(true), 10000);
        if (z && z.length > 22 && z.length < 20e6) {
          found++;
          const h = hash(z);
          if (!state.saves.zip || state.saves.zip.h !== h) { state.saves.zip = { h, data: z.slice().buffer }; changed++; }
        }
      }
      lastSyncAt = Date.now();
      if (changed) {
        state.saves.updated = Date.now();
        await idbSet('saves', state.saves);
      }
      if (manual) toast(changed ? '세이브를 아이폰에 보관했어요' : (found ? '바뀐 세이브가 없어요. 이미 보관돼 있어요.' : '세이브 파일을 찾지 못했어요'));
    } catch (e) {
      if (manual) toast('세이브를 보관하지 못했어요');
    } finally {
      syncing = false;
    }
  }

  function exportSave() {
    const s = state.saves;
    let file = null;
    if (s.files['AFRICA2.SAV']) file = new File([s.files['AFRICA2.SAV'].data], 'AFRICA2.SAV', { type: 'application/octet-stream' });
    else if (s.zip) file = new File([s.zip.data], 'africa2-save.zip', { type: 'application/zip' });
    if (!file) { toast('아직 보관된 세이브가 없어요. 게임을 한 번 실행한 뒤 해주세요.'); return; }
    if (navigator.canShare && navigator.canShare({ files: [file] })) {
      navigator.share({ files: [file] }).catch(() => {});
    } else {
      const a = document.createElement('a');
      a.href = URL.createObjectURL(file); a.download = file.name;
      document.body.appendChild(a); a.click(); a.remove();
      setTimeout(() => URL.revokeObjectURL(a.href), 15000);
    }
  }

  async function importSave(file) {
    if (!file) return;
    try {
      const buf = await file.arrayBuffer();
      const u8 = new Uint8Array(buf);
      if (u8.length < 1024) throw new Error('세이브 파일이 아닌 것 같아요.');
      if (u8[0] === 0x50 && u8[1] === 0x4b) state.saves.zip = { h: hash(u8), data: buf };
      else state.saves.files['AFRICA2.SAV'] = { h: hash(u8), data: buf };
      state.saves.updated = Date.now();
      await idbSet('saves', state.saves);
      toast('세이브를 가져왔어요. 게임을 시작하면 적용돼요.');
      renderLauncher();
    } catch (e) {
      toast((e && e.message) || '세이브를 가져오지 못했어요');
    }
  }

  /* ───────── 항상 가로 화면 ─────────
     세로로 들고 있으면 앱 전체를 시계 방향으로 90도 돌린다(회전 잠금을 켜둬도 가로로 보임). */
  const appEl = $('#app');
  let rotated = false;
  // 세로로 들었을 때도 '진짜 가로 화면'과 똑같은 여백을 쓰기 위해, 가로일 때 잰 여백을 기억해둔다.
  function readInsets() {
    const cs = getComputedStyle($('#inset-probe'));
    return { t: parseFloat(cs.paddingTop) || 0, r: parseFloat(cs.paddingRight) || 0,
      b: parseFloat(cs.paddingBottom) || 0, l: parseFloat(cs.paddingLeft) || 0 };
  }
  function landscapeInsets() {
    const now = readInsets();
    if (!rotated) {
      if (now.l || now.r || now.b) { try { localStorage.setItem('africa2-land-insets', JSON.stringify(now)); } catch (_) { /* 무시 */ } }
      return now;
    }
    try {
      const saved = JSON.parse(localStorage.getItem('africa2-land-insets') || 'null');
      if (saved) return saved;
    } catch (_) { /* 무시 */ }
    // 아직 가로로 연 적이 없으면 세로 여백으로 가로 여백을 짐작 (다이나믹 아일랜드 폭을 양옆에, 홈 바 자리 21pt를 아래에)
    const side = Math.max(now.t, now.b, now.l, now.r);
    return { t: 0, r: side, b: now.b > 0 ? 21 : 0, l: side };
  }
  // 홈 화면 앱은 화면 전체를 쓰는데, 세로일 때 아이폰이 높이를 상태 표시줄만큼 작게 알려주는 경우가 있어
  // 홈 화면 앱에서는 기기 화면 크기를 직접 쓴다.
  function viewportSize() {
    const iw = window.innerWidth, ih = window.innerHeight;
    const portrait = ih > iw;
    const sw = screen.width, sh = screen.height;
    if (isStandalone() && sw && sh) {
      const a = Math.min(sw, sh), b = Math.max(sw, sh);
      // 화면 크기와 창 크기가 크게 다르면(아이패드 분할 화면 등) 창 크기를 믿는다
      if (Math.abs(Math.min(iw, ih) - a) <= 2 && Math.max(iw, ih) <= b + 2) return portrait ? { W: a, H: b } : { W: b, H: a };
    }
    return { W: iw, H: ih };
  }
  function applyOrientation() {
    const { W, H } = viewportSize();
    rotated = H > W;
    appEl.classList.toggle('rotated', rotated);
    appEl.style.width = (rotated ? H : W) + 'px';
    appEl.style.height = (rotated ? W : H) + 'px';
    appEl.style.transform = rotated ? `translateX(${W}px) rotate(90deg)` : 'none';
    const ins = landscapeInsets();
    // 가로 화면은 왼쪽·오른쪽 여백이 같으므로 큰 쪽으로 맞춤 → 어느 방향으로 들어도 같은 모습
    const side = Math.max(ins.l, ins.r);
    appEl.style.setProperty('--pt', ins.t + 'px');
    appEl.style.setProperty('--pb', ins.b + 'px');
    appEl.style.setProperty('--pl', side + 'px');
    appEl.style.setProperty('--pr', side + 'px');
  }

  const dosEl = $('#dos');
  const origRect = Element.prototype.getBoundingClientRect;
  Element.prototype.getBoundingClientRect = function () {
    const r = origRect.call(this);
    if (!rotated || !dosEl.contains(this) || !(this.offsetWidth || this.offsetHeight)) return r;
    return new DOMRect(r.x, r.y, this.offsetWidth, this.offsetHeight);
  };

  /* ───────── 화면 맞춤 (4:3, 안전 영역 안쪽) ───────── */
  const LEFT_MIN = 132;  // 방향키·스페이스·엔터 칸
  const RIGHT_MIN = 74;  // ESC·메뉴 칸
  function layout() {
    if ($('#play').hidden) return;
    const stage = $('#stage');
    const W = stage.clientWidth, H = stage.clientHeight;
    // 높이를 꽉 채우는 게 우선. 양옆 버튼 칸이 모자랄 때만 줄인다.
    let h = Math.min(H, ((W - LEFT_MIN - RIGHT_MIN) * 3) / 4);
    h = Math.max(120, Math.floor(h));
    const w = Math.floor((h * 4) / 3);
    // 남는 폭은 왼쪽 칸에 더 많이(7:3) 줘서 게임이 살짝 오른쪽으로 가게
    const extra = Math.max(0, W - w - LEFT_MIN - RIGHT_MIN);
    const left = LEFT_MIN + Math.round(extra * 0.7);
    const right = Math.max(0, W - w - left);
    stage.style.gridTemplateColumns = `${left}px ${w}px ${right}px`;
    const g = $('#game');
    g.style.width = w + 'px';
    g.style.height = h + 'px';
  }
  let layoutRaf = 0;
  function relayout() { applyOrientation(); layout(); }
  function scheduleLayout() { cancelAnimationFrame(layoutRaf); layoutRaf = requestAnimationFrame(() => { relayout(); setTimeout(relayout, 300); }); }
  window.addEventListener('resize', scheduleLayout);
  window.addEventListener('orientationchange', scheduleLayout);
  if (window.visualViewport) window.visualViewport.addEventListener('resize', scheduleLayout);
  applyOrientation();

  /* ───────── 화면 꺼짐 방지 ───────── */
  async function requestWake() {
    try { if ('wakeLock' in navigator && !wakeLock) { wakeLock = await navigator.wakeLock.request('screen'); wakeLock.addEventListener('release', () => { wakeLock = null; }); } } catch (_) { /* 무시 */ }
  }

  /* ───────── 키 입력 ───────── */
  function press(code, withShift) {
    if (!ci) return;
    lastInput = Date.now();
    try {
      if (typeof ci.simulateKeyPress === 'function') {
        if (withShift) ci.simulateKeyPress(KEY.shift, code); else ci.simulateKeyPress(code);
      } else if (typeof ci.sendKeyEvent === 'function') {
        if (withShift) ci.sendKeyEvent(KEY.shift, true);
        ci.sendKeyEvent(code, true);
        setTimeout(() => { ci.sendKeyEvent(code, false); if (withShift) ci.sendKeyEvent(KEY.shift, false); }, 80);
      }
    } catch (_) { /* 무시 */ }
  }
  function wakeAudio() {
    const list = window.__audioCtxs || [];
    for (const c of list) { try { if (c.state !== 'running') c.resume(); } catch (_) { /* 무시 */ } }
  }

  document.querySelectorAll('#stage [data-key]').forEach((b) => {
    b.addEventListener('pointerdown', (e) => { e.preventDefault(); wakeAudio(); b.classList.add('on'); press(KEY[b.dataset.key]); });
    const off = () => b.classList.remove('on');
    b.addEventListener('pointerup', off); b.addEventListener('pointercancel', off); b.addEventListener('pointerleave', off);
  });

  /* ───────── 터치 → 마우스 ─────────
     톡: 그 자리로 커서를 옮겨 잠깐 머문 뒤 클릭 (게임이 위치를 먼저 알아채도록)
     누른 채 끌기: 커서가 손가락을 따라가고, 손을 뗀 곳을 클릭
     꾹: 스페이스(선택) / 두 손가락 톡: ESC */
  const pad = $('#pad');
  const game = $('#game');
  const TAP_SLOP = 14;     // 이만큼 넘게 움직이면 '끌기'
  const HOLD_MS = 450;     // 꾹 누르기 판정 시간
  const HOVER_MS = 120;    // 클릭 전에 커서를 그 자리에 머물게 하는 시간
  const CLICK_HOLD = 120;  // 게임이 클릭을 놓치지 않도록 버튼을 누르고 있는 시간
  const pointers = new Map();
  let gesture = null;
  let clickChain = Promise.resolve();
  let lastMoveAt = 0;
  let movedAt = 0;

  function normPos(cx, cy) {
    const r = game.getBoundingClientRect();
    let x, y;
    if (rotated) { x = (cy - r.top) / r.height; y = (r.right - cx) / r.width; }
    else { x = (cx - r.left) / r.width; y = (cy - r.top) / r.height; }
    x = Math.min(1, Math.max(0, x)); y = Math.min(1, Math.max(0, y));
    return { x, y, px: x * game.offsetWidth, py: y * game.offsetHeight };
  }
  function moveMouse(p) {
    try {
      if (ci && ci.sendMouseMotion) { ci.sendMouseMotion(p.x, p.y); movedAt = performance.now(); }
    } catch (_) { /* 무시 */ }
  }
  function click(p, alreadyThere) {
    // 손가락을 댄 순간부터 커서가 이미 그 자리에 있었다면, 그동안 머문 시간만큼은 덜 기다림
    const hovered = alreadyThere ? performance.now() - movedAt : 0;
    clickChain = clickChain.then(async () => {
      if (!ci || typeof ci.sendMouseButton !== 'function') return;
      moveMouse(p);
      await sleep(Math.max(40, HOVER_MS - hovered));
      moveMouse(p);
      ci.sendMouseButton(0, true);
      await sleep(CLICK_HOLD);
      ci.sendMouseButton(0, false);
      await sleep(30);
    }).catch(() => {});
  }
  function mark(p, kind) {
    const d = document.createElement('div');
    d.className = 'ripple' + (kind ? ' ' + kind : '');
    d.style.left = p.px + 'px'; d.style.top = p.py + 'px';
    game.appendChild(d);
    setTimeout(() => d.remove(), 420);
  }

  pad.addEventListener('pointerdown', (e) => {
    e.preventDefault();
    wakeAudio();
    lastInput = Date.now();
    try { pad.setPointerCapture(e.pointerId); } catch (_) { /* 무시 */ }
    pointers.set(e.pointerId, true);
    if (!ci) return;
    if (pointers.size >= 2) {
      if (gesture) { clearTimeout(gesture.holdTimer); gesture.multi = true; }
      return;
    }
    const p = normPos(e.clientX, e.clientY);
    gesture = { id: e.pointerId, start: p, last: p, sx: e.clientX, sy: e.clientY,
      dragging: false, done: false, multi: false, t0: performance.now() };
    moveMouse(p);
    gesture.holdTimer = setTimeout(() => {
      if (gesture && !gesture.dragging && !gesture.multi && !gesture.done) {
        gesture.done = true;
        press(KEY.space);
        mark(gesture.start, 'hold');
      }
    }, HOLD_MS);
  });

  pad.addEventListener('pointermove', (e) => {
    if (!gesture || e.pointerId !== gesture.id || gesture.multi || gesture.done) return;
    lastInput = Date.now();
    if (!gesture.dragging && Math.hypot(e.clientX - gesture.sx, e.clientY - gesture.sy) > TAP_SLOP) {
      gesture.dragging = true;
      clearTimeout(gesture.holdTimer);
    }
    if (!gesture.dragging) return;
    gesture.last = normPos(e.clientX, e.clientY);
    const now = performance.now();
    if (now - lastMoveAt > 30) { lastMoveAt = now; moveMouse(gesture.last); }
  });

  function endPointer(e, cancelled) {
    const wasMulti = pointers.size >= 2;
    pointers.delete(e.pointerId);
    if (!gesture) return;
    if (gesture.multi) {
      if (pointers.size === 0) {
        if (!cancelled && performance.now() - gesture.t0 < 600) { press(KEY.esc); mark(gesture.start, 'hold'); }
        gesture = null;
      }
      return;
    }
    if (e.pointerId !== gesture.id) return;
    clearTimeout(gesture.holdTimer);
    if (!cancelled && !wasMulti && !gesture.done) {
      const target = gesture.dragging ? normPos(e.clientX, e.clientY) : gesture.start;
      click(target, !gesture.dragging);
      mark(target);
    }
    gesture = null;
  }
  pad.addEventListener('pointerup', (e) => endPointer(e, false));
  pad.addEventListener('pointercancel', (e) => endPointer(e, true));
  pad.addEventListener('contextmenu', (e) => e.preventDefault());

  /* ───────── 방향키 버튼 (누르고 있으면 반복) ───────── */
  document.querySelectorAll('.dpad [data-arrow]').forEach((b) => {
    let rep = 0, first = 0;
    const stop = () => { clearTimeout(first); clearInterval(rep); b.classList.remove('on'); };
    b.addEventListener('pointerdown', (e) => {
      e.preventDefault(); wakeAudio();
      b.classList.add('on');
      const code = KEY[b.dataset.arrow];
      press(code);
      first = setTimeout(() => { rep = setInterval(() => press(code), 140); }, 380);
    });
    b.addEventListener('pointerup', stop); b.addEventListener('pointercancel', stop); b.addEventListener('pointerleave', stop);
  });

  /* ───────── 버튼 연결 ───────── */
  $('#crash-meta').addEventListener('click', () => { $('#crash-diag').hidden = !$('#crash-diag').hidden; });
  $('#btn-pick').addEventListener('click', () => $('#pick-game').click());
  $('#btn-repick').addEventListener('click', () => $('#pick-game').click());
  $('#pick-game').addEventListener('change', (e) => { importGame(e.target.files); e.target.value = ''; });
  $('#btn-start').addEventListener('click', startGame);
  $('#btn-export').addEventListener('click', exportSave);
  $('#btn-import').addEventListener('click', () => $('#pick-save').click());
  $('#pick-save').addEventListener('change', (e) => { importSave(e.target.files[0]); e.target.value = ''; });

  function openMenu() { $('#menu').hidden = false; pauseEmu(true); syncSaves(false, true); }
  function closeMenu() { $('#menu').hidden = true; if (!document.hidden) pauseEmu(false); }
  $('#btn-menu').addEventListener('click', openMenu);
  $('#m-close').addEventListener('click', closeMenu);
  $('#menu').addEventListener('click', (e) => { if (e.target.id === 'menu') closeMenu(); });
  $('#m-sync').addEventListener('click', () => syncSaves(true));
  $('#m-export').addEventListener('click', async () => { await syncSaves(false, true); exportSave(); });
  $('#m-guide').addEventListener('click', () => { closeMenu(); $('#guide').hidden = false; });
  $('#guide-ok').addEventListener('click', () => { $('#guide').hidden = true; prefs.guideSeen = 2; savePrefs(); });

  function renderMenuLabels() {
    $('#m-perf').textContent = '성능: ' + (PERF[prefs.perf] || PERF.normal).label;
    $('#m-cursor').textContent = '지팡이 커서: ' + (prefs.hideCursor ? '숨김' : '보이기');
    $('#m-render').textContent = '화면: ' + (prefs.render === 'smooth' ? '부드럽게' : '선명하게');
    $('#m-enter').textContent = '엔터 바: ' + (prefs.enterBar ? '보이기' : '숨김');
    $('#m-remind').textContent = '저장 알림: ' + (prefs.remind ? '켬' : '끔');
    $('#m-engine').textContent = '실행 방식: ' + (prefs.engine === 'main' ? '절약' : '일반');
    $('#bar-enter').hidden = !prefs.enterBar;
  }
  $('#m-enter').addEventListener('click', () => { prefs.enterBar = !prefs.enterBar; savePrefs(); renderMenuLabels(); });
  $('#m-remind').addEventListener('click', () => { prefs.remind = !prefs.remind; savePrefs(); renderMenuLabels(); });
  $('#m-engine').addEventListener('click', () => restartWith(() => { prefs.engine = prefs.engine === 'main' ? 'worker' : 'main'; }));

  // 돌린 화면에서도 똑바로 보이도록 기본 확인창 대신 직접 만든 확인창 사용
  function askConfirm(msg) {
    return new Promise((resolve) => {
      $('#confirm-msg').textContent = msg;
      $('#confirm').hidden = false;
      const done = (v) => { $('#confirm').hidden = true; yes.removeEventListener('click', onYes); no.removeEventListener('click', onNo); resolve(v); };
      const yes = $('#confirm-yes'), no = $('#confirm-no');
      const onYes = () => done(true), onNo = () => done(false);
      yes.addEventListener('click', onYes); no.addEventListener('click', onNo);
    });
  }
  async function restartWith(change) {
    if (!(await askConfirm('게임을 다시 시작해야 적용돼요. 게임 안에서 저장하지 않은 진행은 사라져요. 바꿀까요?'))) return;
    change();
    savePrefs();
    busy('세이브를 보관하고 다시 시작하는 중');
    await syncSaves(false, true);
    endSessionClean();
    try { await withTimeout(Promise.resolve(dosProps && dosProps.stop && dosProps.stop()), 3000); } catch (_) { /* 무시 */ }
    try { sessionStorage.setItem('africa2-autostart', '1'); } catch (_) { /* 무시 */ }
    location.reload();
  }
  $('#m-perf').addEventListener('click', () => restartWith(() => {
    prefs.perf = PERF_ORDER[(PERF_ORDER.indexOf(prefs.perf) + 1) % PERF_ORDER.length];
  }));
  $('#m-cursor').addEventListener('click', () => restartWith(() => { prefs.hideCursor = !prefs.hideCursor; }));
  $('#m-render').addEventListener('click', () => {
    prefs.render = prefs.render === 'smooth' ? 'pixelated' : 'smooth';
    savePrefs();
    try { dosProps && dosProps.setImageRendering && dosProps.setImageRendering(prefs.render); } catch (_) { /* 무시 */ }
    renderMenuLabels();
  });
  $('#m-quit').addEventListener('click', async () => {
    busy('세이브를 보관하는 중');
    await syncSaves(false, true);
    endSessionClean();
    try { await withTimeout(Promise.resolve(dosProps && dosProps.stop && dosProps.stop()), 3000); } catch (_) { /* 무시 */ }
    location.reload();
  });
  renderMenuLabels();

  document.addEventListener('visibilitychange', () => {
    if (session) { session.vis = document.hidden ? 'hidden' : 'visible'; session.beat = Date.now(); writeSession(); }
    if (document.hidden) { pauseEmu(true); syncSaves(false, true); }
    else if ($('#menu').hidden) pauseEmu(false);
    else if (!$('#play').hidden) requestWake();
  });
  window.addEventListener('pagehide', () => syncSaves(false, true));
  document.addEventListener('gesturestart', (e) => e.preventDefault());
  document.addEventListener('dblclick', (e) => e.preventDefault(), { passive: false });

  /* ───────── 시작 화면 ───────── */
  function renderLauncher() {
    const has = !!state.game;
    $('#state-empty').hidden = has;
    $('#state-ready').hidden = !has;
    const parts = [];
    if (has) parts.push(`게임 파일 ${Math.round(state.game.size / 1048576)}MB 보관 중.`);
    parts.push(state.saves.updated ? `마지막 세이브 보관: ${fmtTime(state.saves.updated)}` : '보관된 세이브는 아직 없어요.');
    $('#save-meta').textContent = parts.join(' ');
    const log = readCrashLog();
    const last = log[log.length - 1];
    $('#crash-meta').hidden = !last;
    if (last) {
      $('#crash-meta').textContent = `최근 갑자기 꺼짐: ${fmtTime(last.at)}, 게임 ${last.mins}분째 (지금까지 ${log.length}번)`;
      $('#crash-diag').textContent = log.slice(-3).reverse().map((c) =>
        `${fmtTime(c.at)} ${c.mins}분 성능:${c.perf}` + (c.diag ? ` 방식:${c.diag.eng} 파일:${c.diag.fsMB}MB/${c.diag.files}개 ${c.diag.st || ''}` : '')).join('\n');
    } else $('#crash-diag').hidden = true;
    $('#tip-home').hidden = !(isIOS() && !isStandalone());
  }

  async function init() {
    try {
      // 시작 화면에서는 50MB 게임 파일을 메모리에 올리지 않고 요약 정보만 읽는다
      state.game = (await idbGet('game-meta')) || null;
      if (!state.game) {
        const full = await idbGet('game');
        if (full) { state.game = metaOf(full); try { await idbSet('game-meta', state.game); } catch (_) { /* 무시 */ } }
      }
      const s = await idbGet('saves');
      if (s) state.saves = { files: s.files || {}, zip: s.zip || null, updated: s.updated || 0 };
    } catch (e) {
      showError('이 브라우저에서는 저장 공간을 쓸 수 없어요. 개인정보 보호 브라우징을 끄고 다시 열어주세요.');
    }
    renderLauncher();
    let auto = false;
    try { auto = sessionStorage.getItem('africa2-autostart') === '1'; sessionStorage.removeItem('africa2-autostart'); } catch (_) { /* 무시 */ }
    const crashed = checkLastSession();
    renderLauncher();
    if (crashed && state.game && lastEnd && lastEnd.vis !== 'hidden') {
      toast('게임이 갑자기 꺼졌어요. 게임 시작 → 게임 안의 불러오기로 이어서 하세요.', 6000);
    }
    if (auto && state.game) startGame();
  }
  init();
})();
