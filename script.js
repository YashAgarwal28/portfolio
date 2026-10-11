/* Portfolio interactions: full-viewport head tracking, cursor ring, and one shared motion system
   (reveal, stagger, 3D tilt, spotlight, scroll progress) used by every section.

   Performance model
   - Static by default. Effects (class .fx on <html>) turn on only after a device check, and a runtime
     guard turns them off again if frames keep dropping. Visitors can also flip them with the
     "Effects" switch. Overrides: ?fx=high, ?fx=low, ?lite (this visit only), ?debug (window.__ya).
   - ONE requestAnimationFrame loop for head, ring and hero parallax; it sleeps when nothing moves,
     when the hero is off-screen, or when the tab is hidden.
   - Frames are decoded off the main thread (createImageBitmap); the canvas is redrawn only when the
     displayed frame changes. Reveals, tilt and spotlight touch only transform/opacity. */
(function () {
  "use strict";

  var doc = document, root = doc.documentElement;
  var qs = location.search;
  var reduceMotion = window.matchMedia("(prefers-reduced-motion: reduce)").matches;
  var finePointer = window.matchMedia("(hover: hover) and (pointer: fine)").matches;
  var conn = navigator.connection || {};
  var lite = /[?&]lite(?![a-z])/.test(qs);
  var force = (qs.match(/[?&]fx=(high|low)/) || [])[1] || "";

  function store(k, v) { try { if (v === null) localStorage.removeItem(k); else localStorage.setItem(k, v); } catch (e) {} }
  function read(k) { try { return localStorage.getItem(k) || ""; } catch (e) { return ""; } }
  if (force === "high") store("ya-fx", null);
  if (force === "low") store("ya-fx", "low");

  var weakDevice =
    conn.saveData === true ||
    /(^|-)2g$/.test(conn.effectiveType || "") ||
    (navigator.deviceMemory && navigator.deviceMemory < 2) ||
    (navigator.hardwareConcurrency && navigator.hardwareConcurrency < 2);
  var forcedOn = force === "high";
  var allowFx = !lite && !reduceMotion && force !== "low" && (forcedOn || (!weakDevice && !/^(low|off)$/.test(read("ya-fx"))));

  /* ---------- reveal system (shared by every section) ---------- */
  doc.querySelectorAll("[data-stagger]").forEach(function (g) {
    var i = 0;
    Array.prototype.forEach.call(g.children, function (c) {
      if (c.hasAttribute("data-reveal") || c.tagName === "LI") { c.style.setProperty("--i", i); i++; }
    });
  });
  doc.querySelectorAll("[data-reveal]").forEach(function (el, n) { if (!el.style.getPropertyValue("--i")) el.style.setProperty("--i", 0); });

  var revealEls = doc.querySelectorAll("[data-reveal]");
  if ("IntersectionObserver" in window) {
    var revealIO = new IntersectionObserver(function (entries) {
      entries.forEach(function (e) { if (e.isIntersecting) { e.target.classList.add("in"); revealIO.unobserve(e.target); } });
    }, { threshold: 0.1, rootMargin: "0px 0px -6% 0px" });
    revealEls.forEach(function (el) { revealIO.observe(el); });
    var liveIO = new IntersectionObserver(function (entries) {
      entries.forEach(function (e) { e.target.classList.toggle("on", e.isIntersecting); });
    });
    doc.querySelectorAll(".marquee").forEach(function (el) { liveIO.observe(el); });
  } else {
    revealEls.forEach(function (el) { el.classList.add("in"); });
  }
  /* stagger children inherit their group's order; list items reveal with their list */
  doc.querySelectorAll("ul[data-reveal] > li").forEach(function (li) { li.setAttribute("data-reveal", ""); });
  var liObs = "IntersectionObserver" in window ? new IntersectionObserver(function (entries) {
    entries.forEach(function (e) { if (e.isIntersecting) { e.target.classList.add("in"); liObs.unobserve(e.target); } });
  }, { threshold: 0.1, rootMargin: "0px 0px -6% 0px" }) : null;
  doc.querySelectorAll("ul[data-reveal] > li").forEach(function (li) { if (liObs) liObs.observe(li); else li.classList.add("in"); });

  /* ---------- state ---------- */
  var hero = doc.getElementById("top");
  var canvas = doc.getElementById("stage-canvas");
  stageEl = canvas ? canvas.parentElement : null;
  var poster = doc.getElementById("stage-poster");
  var badge = doc.getElementById("eye-badge");
  var heroWrap = hero ? hero.querySelector(".wrap") : null;
  var progressEl = doc.getElementById("progress");
  var toggle = doc.getElementById("fx-toggle");
  var CW = 1280, CH = 720, TOTAL = 64;
  var ENTER = 0.12, EXIT = 0.15;

  var mouse = { x: -200, y: -200, seen: false };
  var ring = { x: -200, y: -200, s: 1, target: 1, base: 1 };
  var par = { x: 0, y: 0 };
  var ringEl = null, tiltOn = false, pressed = false;
  var rafId = 0, lastT = 0, heroVisible = true;
  var frames = new Array(TOTAL), center = null, ctx = null, drawn = "", downImg = null, wDown = 0, lastBase = null, lastBaseKey = "c";
  var angle = 0, inDead = true, face = { x: 0, y: 0, ok: false }, faceDirty = true, objPos = { x: 0.5, y: 0.3 };
  /* per-frame calibration (assets/char/map.json): where the eyes are and which way the head looks.
     The source video is not a uniform orbit around one point, so we never assume one. */
  var MAP = null, geo = { l: 0, t: 0, ox: 0, oy: 0, dw: 1, dh: 1 };
  var cur = -1, lastSwitch = 0, hm = { x: -200, y: -200 }, pickErr = 0, LOOK_LIMIT = 80, pose = { rx: 0, ry: 0, ty: 0 }, stageEl = null;
  var started = false, enabled = false, touchActive = false, userOn = false;
  var tier = "?", calibMs = -1, slowScore = 0, guardFrom = 0;

  function kick() { if (enabled && !rafId && !doc.hidden) { lastT = performance.now(); rafId = requestAnimationFrame(tick); } }

  function readObjPos() {
    var p = (getComputedStyle(canvas).objectPosition || "50% 30%").split(" ");
    objPos.x = parseFloat(p[0]) / 100 || 0.5; objPos.y = parseFloat(p[1]) / 100 || 0.3;
  }
  /* screen geometry of the cover-fitted canvas; recomputed after scroll/resize */
  function updateFace() {
    var r = (stageEl || canvas).getBoundingClientRect(), vw = r.width, vh = r.height;
    if (!vw || !vh) { face.ok = false; return; }
    var sc = Math.min(vw / CW, vh / CH);
    geo.dw = CW * sc; geo.dh = CH * sc;
    geo.l = r.left; geo.t = r.top;
    geo.ox = (vw - geo.dw) * objPos.x; geo.oy = (vh - geo.dh) * objPos.y;
    var c = MAP ? MAP.center : [0.5, 0.42];
    face.x = geo.l + geo.ox + c[0] * geo.dw;
    face.y = geo.t + geo.oy + c[1] * geo.dh;
    face.ok = true; faceDirty = false;
  }
  function adiff(a, b) { return Math.abs(((a - b + 540) % 360) - 180); }

  /* choose the frame whose real gaze best matches the real direction from ITS OWN eyes to the cursor */
  function pickFrame(px, py, now) {
    var best = -1, bestE = 1e9, curE = 1e9;
    for (var i = 0; i < TOTAL; i++) {
      if (!frames[i]) continue;
      var ax = geo.l + geo.ox + MAP.ax[i] * geo.dw, ay = geo.t + geo.oy + MAP.ay[i] * geo.dh;
      var t = Math.atan2(py - ay, px - ax) * 57.29578; if (t < 0) t += 360;
      var e = adiff(t, MAP.th[i]);
      if (i === cur) curE = e;
      if (e < bestE - 0.01) { bestE = e; best = i; }
    }
    if (best < 0) return -1;
    pickErr = bestE;
    if (cur >= 0 && frames[cur] && best !== cur) {
      var needed = MAP.seg[best] !== MAP.seg[cur] ? 14 : 5;        /* hysteresis: avoid flicker at pose boundaries */
      if (bestE > curE - needed) { pickErr = curE; return cur; }
      if (MAP.seg[best] !== MAP.seg[cur] && now - lastSwitch < 140) { pickErr = curE; return cur; }
    }
    return best;
  }

  function nearest(i) {
    for (var d = 0; d < TOTAL / 2; d++) {
      var a = frames[(i + d) % TOTAL]; if (a) return { img: a, key: (i + d) % TOTAL };
      var b = frames[(i - d + TOTAL) % TOTAL]; if (b) return { img: b, key: (i - d + TOTAL) % TOTAL };
    }
    return null;
  }
  /* base frame (cursor tracking) + the looking-down still, faded in by how far the page is scrolled toward
     the skills strip, so he looks down at it as you scroll */
  function draw(img, key) {
    if (img) { lastBase = img; lastBaseKey = key; } else img = lastBase;
    if (!img) return;
    var w = downImg ? wDown : 0, k = lastBaseKey + "|" + Math.round(w * 200);
    if (k === drawn) return; drawn = k;
    ctx.globalAlpha = 1; ctx.drawImage(img, 0, 0);
    if (w > 0.004) { ctx.globalAlpha = w; ctx.drawImage(downImg, 0, 0); ctx.globalAlpha = 1; }
  }
  function sm(a, b, x) { var t = x < a ? 0 : x > b ? 1 : (x - a) / (b - a); return t * t * (3 - 2 * t); }

  function setBadge(dead) {
    if (!badge) return;
    badge.classList.toggle("eye", dead);
    badge.lastChild.textContent = dead ? " Eye contact" : " Following your cursor";
  }
  function syncToggle() {
    if (!toggle) return;
    toggle.setAttribute("aria-pressed", enabled ? "true" : "false");
    toggle.textContent = enabled ? "Effects: On" : "Effects: Off";
  }

  /* switch every effect off; the static portrait stays. why = "user" or a runtime reason */
  function degrade(why) {
    if (!enabled && tier === "low") return;
    enabled = false; tier = "low";
    store("ya-fx", why === "user" ? "off" : "low");
    if (rafId) { cancelAnimationFrame(rafId); rafId = 0; }
    root.classList.remove("fx", "fx-track", "fx-tilt");
    if (ringEl) { ringEl.remove(); ringEl = null; }
    if (heroWrap) heroWrap.style.transform = "";
    if (canvas) canvas.style.transform = "";
    if (ctx && center) { drawn = ""; draw(center, "c"); }
    if (window.__ya) window.__ya.why = why;
    syncToggle();
  }

  function tick(t) {
    rafId = 0;
    var raw = t - lastT;
    var dt = Math.min(0.05, Math.max(0.001, raw / 1000)); lastT = t;
    var moving = false;

    /* runtime guard: sustained slow frames => turn effects off (not when the user forced them on) */
    if (!userOn && t > guardFrom && raw > 34) { slowScore += 1; if (slowScore >= 14) { degrade("runtime: slow frames"); return; } }
    else if (slowScore > 0 && raw < 24) slowScore -= 0.25;

    if (ringEl) {
      var k = 1 - Math.exp(-dt / 0.026);
      ring.x += (mouse.x - ring.x) * k;
      ring.y += (mouse.y - ring.y) * k;
      ring.s += (ring.target - ring.s) * (1 - Math.exp(-dt / 0.06));
      ringEl.style.transform = "translate3d(" + ring.x.toFixed(1) + "px," + ring.y.toFixed(1) + "px,0) scale(" + ring.s.toFixed(3) + ")";
      if (Math.abs(mouse.x - ring.x) > 0.15 || Math.abs(mouse.y - ring.y) > 0.15 || Math.abs(ring.target - ring.s) > 0.004) moving = true;
    }

    if (center && heroVisible) {
      if (faceDirty) { readObjPos(); updateFace(); }
      if (face.ok) {
        /* light smoothing of the tracked point (removes hand jitter) without adding perceptible lag */
        var kh = 1 - Math.exp(-dt / 0.012);
        hm.x += (mouse.x - hm.x) * kh; hm.y += (mouse.y - hm.y) * kh;
        if (Math.abs(mouse.x - hm.x) > 0.4 || Math.abs(mouse.y - hm.y) > 0.4) moving = true; else { hm.x = mouse.x; hm.y = mouse.y; }

        /* scroll-driven look-down: eased in time so it never jumps; reaches full at about a quarter screen of scroll */
        var tDown = sm(innerHeight * 0.05, innerHeight * 0.3, window.scrollY || 0), kd = 1 - Math.exp(-dt / 0.1);
        wDown += (tDown - wDown) * kd;
        if (Math.abs(tDown - wDown) > 0.003) moving = true; else wDown = tDown;

        var dx = hm.x - face.x, dy = hm.y - face.y, dist = Math.hypot(dx, dy);
        var m = Math.min(innerWidth, innerHeight), was = inDead;
        if (!mouse.seen) inDead = true;
        else if (inDead) { if (dist > m * EXIT) inDead = false; }
        else if (dist < m * ENTER) inDead = true;
        if (inDead !== was) setBadge(inDead);

        if (inDead || !MAP) { cur = -1; draw(center, "c"); }
        else {
          var pick = pickFrame(hm.x, hm.y, t);
          /* if no frame in the footage looks anywhere near the cursor's direction (the video has no
             "looking down" poses), look at the visitor instead of turning the wrong way */
          if (pick >= 0 && pickErr > (cur < 0 ? LOOK_LIMIT - 6 : LOOK_LIMIT)) { cur = -1; draw(center, "c"); pick = -1; }
          else if (pick >= 0) {
            if (pick !== cur) { if (cur >= 0 && MAP.seg[pick] !== MAP.seg[cur]) lastSwitch = t; cur = pick; }
            angle = MAP.th[pick] * 0.0174533; draw(frames[pick], pick);
          }
        }
        if (downImg) draw(null, lastBaseKey);
      }

      /* depth: the hero copy drifts slightly against the pointer (compositor-only transform) */
      if (heroWrap && finePointer && mouse.seen) {
        var tx = -(mouse.x / innerWidth - 0.5) * 16, ty = -(mouse.y / innerHeight - 0.5) * 9, kp = 1 - Math.exp(-dt / 0.09);
        par.x += (tx - par.x) * kp; par.y += (ty - par.y) * kp;
        heroWrap.style.transform = "translate3d(" + par.x.toFixed(2) + "px," + par.y.toFixed(2) + "px,0)";
        if (Math.abs(tx - par.x) > 0.05 || Math.abs(ty - par.y) > 0.05) moving = true;
      }

      /* 3D response the footage cannot provide on its own: the head layer pitches forward when the cursor
         is below the face (and back when above), with a slight yaw and drop. Compositor-only transform. */
      if (face.ok && (finePointer || touchActive)) {
        var vy = Math.max(-1, Math.min(1, (hm.y - face.y) / (innerHeight * 0.45)));
        var vx = Math.max(-1, Math.min(1, (hm.x - face.x) / (innerWidth * 0.45)));
        var trx = mouse.seen ? -vy * 8 : 0, try_ = mouse.seen ? vx * 3 : 0, tty = mouse.seen ? vy * 7 : 0, kn = 1 - Math.exp(-dt / 0.07);
        pose.rx += (trx - pose.rx) * kn; pose.ry += (try_ - pose.ry) * kn; pose.ty += (tty - pose.ty) * kn;
        canvas.style.transform = "perspective(1300px) rotateX(" + pose.rx.toFixed(2) + "deg) rotateY(" + pose.ry.toFixed(2) + "deg) translate3d(0," + pose.ty.toFixed(2) + "px,0) scale(1.06)";
        if (Math.abs(trx - pose.rx) > 0.02 || Math.abs(try_ - pose.ry) > 0.02 || Math.abs(tty - pose.ty) > 0.05) moving = true;
      }
    }
    if (moving) rafId = requestAnimationFrame(tick);
  }

  function onMove(e) {
    mouse.x = e.clientX; mouse.y = e.clientY;
    if (!mouse.seen) { mouse.seen = true; ring.x = mouse.x; ring.y = mouse.y; }
    if (ringEl && !ringEl.classList.contains("show")) ringEl.classList.add("show");
    kick();
  }

  /* ---------- assets ---------- */
  function bitReversalOrder() {
    var out = [], bits = Math.log2(TOTAL);
    for (var i = 0; i < TOTAL; i++) { var r = 0; for (var b = 0; b < bits; b++) if (i & (1 << b)) r |= 1 << (bits - 1 - b); out.push(r); }
    return out;              /* coarse-to-fine so every angle has a near frame early */
  }
  function toBitmap(blob) {
    if (window.createImageBitmap) return createImageBitmap(blob);
    return new Promise(function (res, rej) { var im = new Image(); im.onload = function () { res(im); }; im.onerror = rej; im.src = URL.createObjectURL(blob); });
  }
  function loadOne(name) { return fetch("assets/char/" + name + ".webp").then(function (r) { return r.blob(); }).then(toBitmap); }

  /* how long this device takes to draw one frame into the canvas (what we do on every head change) */
  function calibrate(bmp) {
    try {
      var c = doc.createElement("canvas"); c.width = CW; c.height = CH;
      var x = c.getContext("2d", { alpha: false });
      x.drawImage(bmp, 0, 0); x.getImageData(0, 0, 1, 1);
      var t0 = performance.now();
      for (var i = 0; i < 8; i++) x.drawImage(bmp, 0, 0);
      x.getImageData(0, 0, 1, 1);
      return (performance.now() - t0) / 8;
    } catch (e) { return 99; }
  }

  var fOrder = null, fIdx = 0, fActive = 0, fStarted = false;
  function startFrames() {
    if (fStarted) return; fStarted = true; fOrder = bitReversalOrder();
    (function pump() {
      while (enabled && fActive < 4 && fIdx < fOrder.length) {
        (function (i) {
          fActive++;
          loadOne("f" + i).then(function (b) { frames[i] = b; if (!inDead) kick(); }).catch(function () {}).then(function () { fActive--; pump(); });
        })(fOrder[fIdx++]);
      }
    })();
  }

  function begin() {
    if (started || !canvas || !hero || !allowFx) return;
    started = true;
    ctx = canvas.getContext("2d", { alpha: false });
    Promise.all([
      loadOne("center"),
      fetch("assets/char/map.json").then(function (r) { return r.json(); }).catch(function () { return null; })
    ]).then(function (res) {
      var img = res[0]; center = img;
      MAP = res[1] && res[1].th && res[1].th.length === TOTAL ? res[1] : null;
      calibMs = calibrate(img);
      if (window.__ya) window.__ya.calibMs = +calibMs.toFixed(2);
      if (calibMs > 6 && !forcedOn && !userOn) { tier = "low"; store("ya-fx", "low"); started = false; syncToggle(); return; }

      tier = "high"; enabled = true; slowScore = 0;
      root.classList.add("fx");
      if (finePointer || touchActive) root.classList.add("fx-track");
      if (finePointer) root.classList.add("fx-tilt");
      readObjPos();
      draw(center, "c"); canvas.classList.add("ready");
      if (poster) setTimeout(function () { poster.classList.add("gone"); }, 60);
      setBadge(true); syncToggle();
      guardFrom = performance.now() + 2500;           /* ignore start-up hitches while frames stream in */

      if (finePointer) {
        ringEl = doc.createElement("div"); ringEl.className = "cursor-ring"; ringEl.setAttribute("aria-hidden", "true");
        doc.body.appendChild(ringEl);
        if (mouse.seen) { ring.x = mouse.x; ring.y = mouse.y; ringEl.classList.add("show"); }
        wireCursor();
        wireCards();
      }

      loadOne("down").then(function (b) { downImg = b; kick(); }).catch(function () {});
      /* the 63 turning frames are only needed for cursor / drag tracking: desktop loads them now, touch
         devices wait for the first drag (scrolling only needs the centre and looking-down images) */
      if (finePointer || touchActive) startFrames();
      kick();
    }).catch(function () { started = false; });
  }

  /* cursor ring states: hover grows, press squeezes (listeners added once) */
  var cursorWired = false;
  function wireCursor() {
    if (cursorWired) return; cursorWired = true;
    doc.addEventListener("pointerover", function (e) {
      if (!ringEl) return;
      var hit = e.target.closest && e.target.closest("a,button");
      ring.base = hit ? 1.65 : 1; ring.target = pressed ? ring.base * 0.8 : ring.base;
      ringEl.classList.toggle("hot", !!hit); kick();
    }, { passive: true });
    doc.addEventListener("pointerdown", function () { pressed = true; ring.target = ring.base * 0.8; kick(); }, { passive: true });
    doc.addEventListener("pointerup", function () { pressed = false; ring.target = ring.base; kick(); }, { passive: true });
    doc.documentElement.addEventListener("mouseleave", function () { if (ringEl) ringEl.classList.remove("show"); });
    doc.documentElement.addEventListener("mouseenter", function () { if (ringEl && mouse.seen) ringEl.classList.add("show"); });
  }

  /* cards: spotlight + 3D tilt on the hovered card only, throttled to one update per frame */
  var cardsWired = false;
  function wireCards() {
    if (cardsWired) return; cardsWired = true;
    var el = null, x = 0, y = 0, raf = 0, last = null;
    function reset(c) {
      if (!c) return;
      c.style.setProperty("--rx", "0deg"); c.style.setProperty("--ry", "0deg");
      setTimeout(function () { if (c !== el) c.classList.remove("tilting"); }, 400);
    }
    doc.addEventListener("pointermove", function (e) {
      var c = enabled && e.target.closest ? e.target.closest(".card") : null;
      if (c !== last) { reset(last); last = c; }
      el = c; if (!c) return;
      x = e.clientX; y = e.clientY;
      if (!raf) raf = requestAnimationFrame(function () {
        raf = 0; if (!el || !enabled) return;
        var r = el.getBoundingClientRect(), px = (x - r.left) / r.width, py = (y - r.top) / r.height;
        el.style.setProperty("--mx", (x - r.left) + "px"); el.style.setProperty("--my", (y - r.top) + "px");
        if (el.hasAttribute("data-tilt")) {
          el.classList.add("tilting");
          var amp = Math.min(1, 460 / r.width);
          el.style.setProperty("--ry", ((px - 0.5) * 9 * amp).toFixed(2) + "deg");
          el.style.setProperty("--rx", (-(py - 0.5) * 7 * amp).toFixed(2) + "deg");
        }
      });
    }, { passive: true });
    doc.documentElement.addEventListener("mouseleave", function () { reset(last); last = null; el = null; });
  }

  /* ---------- scroll progress bar ---------- */
  if (progressEl) {
    var sRaf = 0;
    var upd = function () {
      sRaf = 0;
      var h = doc.documentElement.scrollHeight - innerHeight;
      progressEl.style.transform = "scaleX(" + (h > 0 ? Math.min(1, Math.max(0, scrollY / h)) : 0).toFixed(4) + ")";
    };
    window.addEventListener("scroll", function () { if (enabled && !sRaf) sRaf = requestAnimationFrame(upd); }, { passive: true });
  }

  /* ---------- wiring ---------- */
  if (canvas && hero) {
    if ("ResizeObserver" in window) new ResizeObserver(function () { faceDirty = true; kick(); }).observe(stageEl || canvas);
    /* Scrolling moves the face on screen while the mouse stands still (no pointermove fires), so the
       tracker must wake on scroll too, otherwise the head keeps looking at where the cursor WAS. */
    window.addEventListener("scroll", function () { faceDirty = true; if (heroVisible) kick(); }, { passive: true });
    window.addEventListener("resize", function () { faceDirty = true; kick(); }, { passive: true });
    if ("IntersectionObserver" in window) {
      new IntersectionObserver(function (e) { heroVisible = e[0].isIntersecting; if (heroVisible) { faceDirty = true; kick(); } }).observe(hero);
    }
    doc.addEventListener("visibilitychange", function () { if (!doc.hidden) kick(); });

    if (finePointer) {
      window.addEventListener("pointermove", onMove, { passive: true });
      var go = function () { begin(); };
      if (doc.readyState === "complete") setTimeout(go, 200);
      else window.addEventListener("load", function () { setTimeout(go, 200); }, { once: true });
    } else {
      /* touch: nothing is downloaded or animated until the first touch on the portrait */
      hero.addEventListener("pointerdown", function (e) {
        touchActive = true; mouse.seen = true; mouse.x = e.clientX; mouse.y = e.clientY;
        begin(); if (enabled) startFrames(); kick();
      }, { passive: true });
      /* scrolling alone starts the (light) look-down effect: centre + looking-down images only */
      window.addEventListener("scroll", function () { if (!started && heroVisible) begin(); }, { passive: true, once: false });
      hero.addEventListener("pointermove", function (e) { if (!touchActive) return; mouse.x = e.clientX; mouse.y = e.clientY; kick(); }, { passive: true });
      var release = function () { touchActive = false; mouse.seen = false; kick(); };
      hero.addEventListener("pointerup", release, { passive: true });
      hero.addEventListener("pointercancel", release, { passive: true });
    }
  }

  /* ---------- visitor switch ---------- */
  if (toggle && canvas && !lite && !reduceMotion) {
    toggle.hidden = false; syncToggle();
    toggle.addEventListener("click", function () {
      if (enabled) { degrade("user"); return; }
      store("ya-fx", null); allowFx = true; userOn = true; forcedOn = true; started = false;
      if (!finePointer) touchActive = true;
      begin();
    });
  }

  /* diagnostics for testing only: add ?debug to the URL */
  if (/[?&]debug(?![a-z])/.test(qs)) {
    window.__ya = {
      get drawn() { return drawn; },
      get loaded() { return frames.filter(Boolean).length + (center ? 1 : 0); },
      get raf() { return !!rafId; },
      get dead() { return inDead; },
      get angle() { return angle; },
      get ring() { return !!ringEl; },
      get enabled() { return enabled; },
      get tier() { return tier; },
      get allowFx() { return allowFx; },
      get fxClass() { return root.classList.contains("fx"); },
      get stored() { return read("ya-fx"); },
      get lite() { return lite; },
      get face() { return { x: face.x, y: face.y }; },
      get frame() { return cur; },
      get wDown() { return wDown; },
      get pose() { return pose; },
      get pickErr() { return pickErr; },
      get hasMap() { return !!MAP; },
      get geo() { return geo; },
      get map() { return MAP; },
      calibMs: -1, why: ""
    };
  }
})();
