'use strict';
(() => {
  const $ = (s) => document.querySelector(s);

  // 게임이 직접 쓰는 세이브/설정 파일
  const SAVE_FILES = ['AFRICA2.SAV', 'AFRICA2.CFG'];
  // 낱개 파일로 넣을 때 꼭 있어야 하는 파일
  const REQUIRED = ['AFR2CD.EXE', 'AFR2CD.INI', 'DOS4GW.EXE', 'FONT.DAT', 'AFRPIC.DAT', 'ENGLISH.FNT',
    'HANGUL.FNT', 'KOR.OMF', 'TITLE.OMF', 'MUSIC.AD', 'MUSIC.ADV', 'MUSIC.COM', 'SOUND.COM', 'PANDA.CFG'];
  const SKIP = /\.PIF$|^RETROMON\./;
  const KEY = { esc: 256, enter: 257, space: 32, backspace: 259, tab: 258, up: 265, down: 264, left: 263, right: 262, shift: 340 };

  const state = { game: null, saves: { files: {}, zip: null, updated: 0 } };
  let dosProps = null;
  let ci = null;
  let syncTimer = 0;
  let syncing = false;
  let watchdog = 0;
  let wakeLock = null;
  let touchMode = 'direct';
  let renderMode = 'smooth';
  let workingPath = null;

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
    const names = [];
    const utf8 = new TextDecoder('utf-8');
    for (let n = 0; n < count && p + 46 <= u8.length; n++) {
      if (dv.getUint32(p, true) !== 0x02014b50) break;
      const nl = dv.getUint16(p + 28, true), el = dv.getUint16(p + 30, true), cl = dv.getUint16(p + 32, true);
      names.push(utf8.decode(u8.subarray(p + 46, p + 46 + nl)));
      p += 46 + nl + el + cl;
    }
    return names;
  }
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
        const info = analyzeZip(zipNames(new Uint8Array(buf)));
        rec = { kind: 'zip', data: buf, root: info.root, iso: info.iso, size: buf.byteLength };
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
      '[cpu]', 'core=auto', 'cputype=auto', 'cycles=max', '',
      '[render]', 'aspect=false', 'scaler=none', '',
      '[mixer]', 'nosound=false', 'rate=44100', 'blocksize=1024', 'prebuffer=40', '',
      '[sblaster]', 'sbtype=sb16', 'sbbase=220', 'irq=7', 'dma=1', 'hdma=5', 'oplmode=auto', 'oplrate=44100', '',
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

  function buildInitFs(game, saves) {
    const fs = [];
    if (game.kind === 'zip') fs.push(new Uint8Array(game.data));
    else for (const f of game.files) fs.push({ path: f.name, contents: new Uint8Array(f.data) });
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
        imageRendering: renderMode,
        mouseCapture: false,
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
    syncTimer = setInterval(() => syncSaves(false), 10000);
    setTimeout(() => syncSaves(false), 5000);
  }

  function loadingFail(msg) {
    const l = $('#loading');
    l.hidden = false;
    l.innerHTML = '';
    const s = document.createElement('strong'); s.textContent = '시작하지 못했어요';
    const p = document.createElement('span'); p.textContent = msg;
    const b = document.createElement('button'); b.className = 'btn primary'; b.textContent = '처음 화면으로';
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

  async function syncSaves(manual) {
    if (!ci || syncing) { if (manual && !ci) toast('게임이 아직 시작되지 않았어요'); return; }
    syncing = true;
    let changed = 0, found = 0;
    try {
      for (const name of SAVE_FILES) {
        const data = await readGameFile(name);
        if (!data) continue;
        found++;
        const h = hash(data);
        if (!state.saves.files[name] || state.saves.files[name].h !== h) {
          state.saves.files[name] = { h, data: data.slice().buffer };
          changed++;
        }
      }
      if (!found && typeof ci.persist === 'function') {
        // 파일을 직접 못 읽는 경우: 바뀐 파일 묶음을 통째로 보관
        const z = await withTimeout(ci.persist(true), 10000);
        if (z && z.length > 22 && z.length < 20e6) {
          found++;
          const h = hash(z);
          if (!state.saves.zip || state.saves.zip.h !== h) { state.saves.zip = { h, data: z.slice().buffer }; changed++; }
        }
      }
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

  /* ───────── 화면 맞춤 (4:3, 안전 영역 안쪽) ───────── */
  function layout() {
    if ($('#play').hidden) return;
    const stage = $('#stage');
    const r = stage.getBoundingClientRect();
    const W = r.width, H = r.height;
    const portrait = H > W;
    stage.classList.toggle('portrait', portrait);
    let h;
    if (!portrait) {
      const side = H < 340 ? 64 : 74; // 양옆 버튼 칸 최소 폭
      h = Math.min(H, ((W - side * 2) * 3) / 4);
    } else {
      const bar = 110;
      h = Math.min((W * 3) / 4, H - bar);
    }
    h = Math.max(120, Math.floor(h / 3) * 3);
    const g = $('#game');
    g.style.width = (h / 3) * 4 + 'px';
    g.style.height = h + 'px';
  }
  let layoutRaf = 0;
  function scheduleLayout() { cancelAnimationFrame(layoutRaf); layoutRaf = requestAnimationFrame(() => { layout(); setTimeout(layout, 300); }); }
  window.addEventListener('resize', scheduleLayout);
  window.addEventListener('orientationchange', scheduleLayout);
  if (window.visualViewport) window.visualViewport.addEventListener('resize', scheduleLayout);

  /* ───────── 화면 꺼짐 방지 ───────── */
  async function requestWake() {
    try { if ('wakeLock' in navigator && !wakeLock) { wakeLock = await navigator.wakeLock.request('screen'); wakeLock.addEventListener('release', () => { wakeLock = null; }); } } catch (_) { /* 무시 */ }
  }

  /* ───────── 키 입력 ───────── */
  function press(code, withShift) {
    if (!ci) return;
    try {
      if (typeof ci.simulateKeyPress === 'function') {
        if (withShift) ci.simulateKeyPress(KEY.shift, code); else ci.simulateKeyPress(code);
      } else if (typeof ci.sendKeyEvent === 'function') {
        if (withShift) ci.sendKeyEvent(KEY.shift, true);
        ci.sendKeyEvent(code, true);
        setTimeout(() => { ci.sendKeyEvent(code, false); if (withShift) ci.sendKeyEvent(KEY.shift, false); }, 70);
      }
    } catch (_) { /* 무시 */ }
  }
  const charQueue = [];
  let charBusy = false;
  async function pumpChars() {
    if (charBusy) return;
    charBusy = true;
    while (charQueue.length) {
      const ch = charQueue.shift();
      const m = charToKey(ch);
      if (m) press(m.code, m.shift);
      await sleep(60);
    }
    charBusy = false;
  }
  function charToKey(ch) {
    if (/[a-z]/.test(ch)) return { code: ch.toUpperCase().charCodeAt(0) };
    if (/[A-Z]/.test(ch)) return { code: ch.charCodeAt(0), shift: true };
    if (/[0-9]/.test(ch)) return { code: ch.charCodeAt(0) };
    const map = { ' ': 32, '-': 45, '.': 46, ',': 44, '/': 47, ';': 59, '=': 61, "'": 39, '[': 91, ']': 93, '\\': 92, '`': 96 };
    return map[ch] !== undefined ? { code: map[ch] } : null;
  }

  document.querySelectorAll('.key[data-key]').forEach((b) => {
    b.addEventListener('pointerdown', (e) => { e.preventDefault(); b.classList.add('on'); press(KEY[b.dataset.key]); });
    const off = () => b.classList.remove('on');
    b.addEventListener('pointerup', off); b.addEventListener('pointercancel', off); b.addEventListener('pointerleave', off);
  });

  const kbd = $('#kbd');
  $('#btn-kbd').addEventListener('click', () => {
    if (document.activeElement === kbd) { kbd.blur(); $('#btn-kbd').classList.remove('on'); }
    else { kbd.value = ''; kbd.focus(); $('#btn-kbd').classList.add('on'); }
  });
  kbd.addEventListener('blur', () => $('#btn-kbd').classList.remove('on'));
  kbd.addEventListener('keydown', (e) => {
    const special = { Enter: KEY.enter, Backspace: KEY.backspace, Escape: KEY.esc, Tab: KEY.tab,
      ArrowUp: KEY.up, ArrowDown: KEY.down, ArrowLeft: KEY.left, ArrowRight: KEY.right };
    if (special[e.key] !== undefined) { e.preventDefault(); press(special[e.key]); }
  });
  kbd.addEventListener('input', () => {
    const v = kbd.value; kbd.value = '';
    for (const ch of v) charQueue.push(ch);
    pumpChars();
  });

  /* ───────── 버튼 연결 ───────── */
  $('#btn-pick').addEventListener('click', () => $('#pick-game').click());
  $('#btn-repick').addEventListener('click', () => $('#pick-game').click());
  $('#pick-game').addEventListener('change', (e) => { importGame(e.target.files); e.target.value = ''; });
  $('#btn-start').addEventListener('click', startGame);
  $('#btn-export').addEventListener('click', exportSave);
  $('#btn-import').addEventListener('click', () => $('#pick-save').click());
  $('#pick-save').addEventListener('change', (e) => { importSave(e.target.files[0]); e.target.value = ''; });

  $('#btn-sync').addEventListener('click', () => syncSaves(true));
  $('#btn-menu').addEventListener('click', () => { kbd.blur(); $('#menu').hidden = false; });
  $('#m-close').addEventListener('click', () => { $('#menu').hidden = true; });
  $('#menu').addEventListener('click', (e) => { if (e.target.id === 'menu') $('#menu').hidden = true; });
  $('#m-export').addEventListener('click', async () => { await syncSaves(false); exportSave(); });
  $('#m-touch').addEventListener('click', () => {
    touchMode = touchMode === 'direct' ? 'pad' : 'direct';
    try { dosProps && dosProps.setMouseCapture && dosProps.setMouseCapture(touchMode === 'pad'); } catch (_) { /* 무시 */ }
    $('#m-touch').textContent = touchMode === 'direct' ? '터치 방식: 직접 누르기' : '터치 방식: 트랙패드';
    toast(touchMode === 'direct' ? '누른 곳을 바로 클릭해요' : '화면을 문질러 커서를 옮기고, 톡 쳐서 클릭해요');
  });
  $('#m-render').addEventListener('click', () => {
    renderMode = renderMode === 'smooth' ? 'pixelated' : 'smooth';
    try { dosProps && dosProps.setImageRendering && dosProps.setImageRendering(renderMode); } catch (_) { /* 무시 */ }
    $('#m-render').textContent = renderMode === 'smooth' ? '화면: 부드럽게' : '화면: 선명하게';
  });
  $('#m-quit').addEventListener('click', async () => {
    busy('세이브를 보관하는 중');
    await syncSaves(false);
    try { await withTimeout(Promise.resolve(dosProps && dosProps.stop && dosProps.stop()), 3000); } catch (_) { /* 무시 */ }
    location.reload();
  });

  document.addEventListener('visibilitychange', () => {
    if (document.hidden) syncSaves(false);
    else if (!$('#play').hidden) requestWake();
  });
  window.addEventListener('pagehide', () => syncSaves(false));
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
    $('#tip-home').hidden = !(isIOS() && !isStandalone());
  }

  async function init() {
    try {
      state.game = (await idbGet('game')) || null;
      const s = await idbGet('saves');
      if (s) state.saves = { files: s.files || {}, zip: s.zip || null, updated: s.updated || 0 };
    } catch (e) {
      showError('이 브라우저에서는 저장 공간을 쓸 수 없어요. 개인정보 보호 브라우징을 끄고 다시 열어주세요.');
    }
    renderLauncher();
  }
  init();
})();
