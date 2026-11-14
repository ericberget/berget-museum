/* The rock: a 3D model of the ground around the Berget farm in Nes.
   Heights come from data/terrain.js (Kartverket survey data, read from the open Terrain Tiles set).
   World units are metres. x is east, z is south, y is up. The origin is the registered Berget farm point. */
(function () {
  'use strict';
  var R = window.ROCK = {}, T = window.TERRAIN;
  var started = false, running = false, failed = false, raf = 0;
  var el, cv, lab, renderer, scene, camera;
  var LAT0 = 60.54615, LON0 = 9.1973, MPP, FBX, FBY, PX0, PY0, base, patch;
  var cam = { p: null, t: null }, orbit = null, tween = null, chapter = 0, labels = [], free = false;
  var meshB, meshP, TEX = {}, mode = 'sat';

  function tx(lon, z) { return (lon + 180) / 360 * Math.pow(2, z); }
  function ty(lat, z) { var r = lat * Math.PI / 180; return (1 - Math.log(Math.tan(r) + 1 / Math.cos(r)) / Math.PI) / 2 * Math.pow(2, z); }
  function u16(b64, n) { var s = atob(b64), a = new Float32Array(n); for (var i = 0; i < n; i++) a[i] = (s.charCodeAt(2 * i) | s.charCodeAt(2 * i + 1) << 8) / 10; return a; }
  function clamp(v, a, b) { return v < a ? a : v > b ? b : v; }
  function bil(a, w, h, x, y) {
    x = clamp(x, 0, w - 1.001); y = clamp(y, 0, h - 1.001);
    var i = Math.floor(x), j = Math.floor(y), fx = x - i, fy = y - j, o = j * w + i;
    return a[o] * (1 - fx) * (1 - fy) + a[o + 1] * fx * (1 - fy) + a[o + w] * (1 - fx) * fy + a[o + w + 1] * fx * fy;
  }
  function hBase(bx, by) { return bil(base, T.w, T.h, bx, by); }
  /* how far inside the detailed patch a point is, in patch cells (negative: outside) */
  function inPatch(bx, by) { var pi = (bx - PX0) * 4, pj = (by - PY0) * 4; return Math.min(pi, pj, T.pw - 1 - pi, T.ph - 1 - pj); }
  function hGrid(bx, by) {
    var d = inPatch(bx, by), b = hBase(bx, by);
    if (d <= 0) return b;
    var w = clamp(d / 16, 0, 1);
    return b + (bil(patch, T.pw, T.ph, (bx - PX0) * 4, (by - PY0) * 4) - b) * w;
  }
  function hAt(x, z) { return hGrid(x / MPP + FBX, z / MPP + FBY); }
  function world(lat, lon) { return [((tx(lon, 12) - T.x0) * 256 - FBX) * MPP, ((ty(lat, 12) - T.y0) * 256 - FBY) * MPP]; }
  function V(lat, lon, alt, lift) { var w = world(lat, lon); return new THREE.Vector3(w[0], alt == null ? hAt(w[0], w[1]) + (lift || 0) : alt, w[1]); }

  /* a shaded relief picture of a height grid: tint by height, light from the north-west, rock where it is steep, contour lines */
  function relief(w, h, sample, cell, minor, major, fine, photo) {
    var c = document.createElement('canvas'); c.width = w; c.height = h;
    var g = c.getContext('2d'), im, d, hh = new Float32Array(w * h), x, y, ph = null;
    if (photo) { g.drawImage(photo, 0, 0, w, h); ph = g.getImageData(0, 0, w, h).data; }
    im = g.createImageData(w, h); d = im.data;
    for (y = 0; y < h; y++) for (x = 0; x < w; x++) hh[y * w + x] = sample(x / (w - 1), y / (h - 1));
    for (y = 0; y < h; y++) for (x = 0; x < w; x++) {
      var o = y * w + x, v = hh[o];
      var l = hh[y * w + Math.max(0, x - 1)], r = hh[y * w + Math.min(w - 1, x + 1)], u = hh[Math.max(0, y - 1) * w + x], dn = hh[Math.min(h - 1, y + 1) * w + x];
      var gx = (r - l) / (2 * cell), gy = (dn - u) / (2 * cell), len = Math.sqrt(gx * gx + gy * gy + 1);
      var sh = clamp((gx * .62 + gy * .62 + .48) / len, 0, 1), k = .38 + .8 * sh;
      if (ph) { k = .5 + .72 * sh; d[o * 4] = Math.min(255, ph[o * 4] * k); d[o * 4 + 1] = Math.min(255, ph[o * 4 + 1] * k); d[o * 4 + 2] = Math.min(255, ph[o * 4 + 2] * k); d[o * 4 + 3] = 255; continue; }
      var t = clamp((v - 150) / 850, 0, 1), cr, cg, cb;
      if (t < .45) { var a = t / .45; cr = 188 + (150 - 188) * a; cg = 176 + (152 - 176) * a; cb = 136 + (112 - 136) * a; }
      else { var b = (t - .45) / .55; cr = 150 + (232 - 150) * b; cg = 152 + (224 - 152) * b; cb = 112 + (204 - 112) * b; }
      var steep = clamp((Math.atan(Math.sqrt(gx * gx + gy * gy)) * 57.3 - 30) / 14, 0, 1);
      cr += (126 - cr) * steep * .8; cg += (116 - cg) * steep * .8; cb += (108 - cb) * steep * .8;
      if (Math.floor(v / major) !== Math.floor(r / major) || Math.floor(v / major) !== Math.floor(dn / major)) k *= .52;
      else if (Math.floor(v / minor) !== Math.floor(r / minor) || Math.floor(v / minor) !== Math.floor(dn / minor)) k *= .76;
      else if (fine && (Math.floor(v / fine) !== Math.floor(r / fine) || Math.floor(v / fine) !== Math.floor(dn / fine))) k *= .9;
      d[o * 4] = cr * k; d[o * 4 + 1] = cg * k; d[o * 4 + 2] = cb * k; d[o * 4 + 3] = 255;
    }
    g.putImageData(im, 0, 0);
    var tex = new THREE.CanvasTexture(c); tex.anisotropy = 8; return tex;
  }
  function grid(nx, ny, pos, tex, off) {
    var g = new THREE.BufferGeometry(), P = new Float32Array(nx * ny * 3), U = new Float32Array(nx * ny * 2), I = new Uint32Array((nx - 1) * (ny - 1) * 6), i, j, k = 0;
    for (j = 0; j < ny; j++) for (i = 0; i < nx; i++) { var o = j * nx + i, p = pos(i, j); P[o * 3] = p[0]; P[o * 3 + 1] = p[1]; P[o * 3 + 2] = p[2]; U[o * 2] = i / (nx - 1); U[o * 2 + 1] = 1 - j / (ny - 1); }
    for (j = 0; j < ny - 1; j++) for (i = 0; i < nx - 1; i++) { var a = j * nx + i; I[k++] = a; I[k++] = a + nx; I[k++] = a + 1; I[k++] = a + 1; I[k++] = a + nx; I[k++] = a + nx + 1; }
    g.setAttribute('position', new THREE.BufferAttribute(P, 3)); g.setAttribute('uv', new THREE.BufferAttribute(U, 2)); g.setIndex(new THREE.BufferAttribute(I, 1));
    var m = new THREE.MeshBasicMaterial({ map: tex }); if (off) { m.polygonOffset = true; m.polygonOffsetFactor = -2; m.polygonOffsetUnits = -2; }
    return new THREE.Mesh(g, m);
  }
  /* a flat ribbon laid on the ground along a list of [x, z] points */
  function ribbon(pts, width, color, opacity, closed, dash) {
    var P = [], I = [], n = pts.length, i;
    for (i = 0; i < n; i++) {
      var a = pts[(i - 1 + n) % n], b = pts[(i + 1) % n];
      if (!closed) { a = pts[Math.max(0, i - 1)]; b = pts[Math.min(n - 1, i + 1)]; }
      var dx = b[0] - a[0], dz = b[1] - a[1], l = Math.sqrt(dx * dx + dz * dz) || 1, ox = -dz / l * width / 2, oz = dx / l * width / 2;
      var x1 = pts[i][0] + ox, z1 = pts[i][1] + oz, x2 = pts[i][0] - ox, z2 = pts[i][1] - oz;
      P.push(x1, hAt(x1, z1) + 2.5, z1, x2, hAt(x2, z2) + 2.5, z2);
    }
    var m = closed ? n : n - 1;
    for (i = 0; i < m; i++) { if (dash && i % dash >= dash / 2) continue; var p = i * 2, q = ((i + 1) % n) * 2; I.push(p, p + 1, q, q, p + 1, q + 1); }
    var g = new THREE.BufferGeometry(); g.setAttribute('position', new THREE.BufferAttribute(new Float32Array(P), 3)); g.setIndex(I);
    return new THREE.Mesh(g, new THREE.MeshBasicMaterial({ color: color, transparent: true, opacity: opacity, side: THREE.DoubleSide, depthWrite: false, polygonOffset: true, polygonOffsetFactor: -6, polygonOffsetUnits: -6 }));
  }
  function ring(lat, lon, radius, width) {
    var c = world(lat, lon), pts = [];
    for (var i = 0; i < 72; i++) { var a = i / 72 * Math.PI * 2; pts.push([c[0] + Math.cos(a) * radius, c[1] + Math.sin(a) * radius]); }
    return ribbon(pts, width, 0xff7a4f, .95, true, 0);
  }

  var PLACES = {
    berget: { ll: [60.54615, 9.1973], n: 'Berget', s: '509 m', lift: 45 },
    skriu: { ll: [60.54807, 9.19789], n: 'Skriu', s: 'the name means scree', lift: 30 },
    anker: { ll: [60.5477, 9.19599], n: 'Ankerbråten', lift: 30 },
    espe: { ll: [60.54513, 9.19689], n: 'Espelund', lift: 25 },
    ovre: { ll: [60.54209, 9.19343], n: 'Øvre Storeli', lift: 40 },
    nedre: { ll: [60.53847, 9.19045], n: 'Nedre Storeli', lift: 40 },
    stave: { ll: [60.5701, 9.0971], n: 'The stave church', s: 'stood about here until 1864', lift: 120 },
    kirke: { ll: [60.56692, 9.10354], n: 'Nes church', s: 'built 1862', lift: 70 },
    s1: { ll: [60.5493, 9.1984], n: '1  The face above Skriu', s: '80 m high, up to 48°', lift: 70, hot: 1 },
    s2: { ll: [60.54631, 9.20474], n: '2  The top', s: '677 m', lift: 40, hot: 1 },
    s3: { ll: [60.54066, 9.19078], n: '3  Hallandnatten', s: 'the only named height', lift: 60, hot: 1 },
    s4: { ll: [60.54585, 9.1969], n: '4  The yard itself', lift: 18, hot: 1 }
  };
  var ALL = Object.keys(PLACES);
  var CH = [
    { h: 'The word', t: 'In 1839 the priest at Nes wrote the family’s name as Berget. It means the rock. It was the name of their farm. Nobody in the family knows which rock.',
      p: [60.528, 9.105, 2700], l: [60.556, 9.165, 250], show: ['stave', 'berget'], dur: 2600,
      pics: [['ole-birth-1839', 'The 1839 entry', 'The Nes church book, 1839. Entry 39: Ole, born 6 August, son of Amund Halvorsen Berget.']] },
    { h: 'The church', t: 'The valley floor at Nes, 164 metres above the sea. The stave church stood about here. The family’s names were written in its book.',
      p: [60.5625, 9.111, 520], l: [60.5701, 9.0971, 170], show: ['stave', 'kirke'], dur: 4200,
      pics: [['gude-nes-church', 'The church, painted in 1845', 'The stave church at Nes, watercolour by Hans Gude, June 1845. Hallingdal Museum.'], ['nesbyen1910', 'Nes in 1910', 'Nesbyen and the hills above it, 1910.']] },
    { h: 'The climb', t: 'Today’s map has one farm called Berget in Nes. It is 3.8 miles (6 km) east of the church and 1,130 feet (345 m) higher.',
      p: [60.5745, 9.094, 760], l: [60.552, 9.17, 330], show: ['stave', 'berget'], dur: 4200, path: 1 },
    { h: 'The neighbours', t: 'Ole’s birth entry names his witnesses. Two are called Braaten and one is Guri Storelie. The farms beside this Berget are Ankerbråten and the two Storeli farms.',
      p: [60.5452, 9.1835, 800], l: [60.5445, 9.1955, 470], show: ['berget', 'skriu', 'anker', 'espe', 'ovre', 'nedre'], dur: 4600,
      pics: [['ole-birth-1839', 'The witnesses\u2019 names', 'The Nes church book, 1839. The lower strip is the witnesses\u2019 column: Braaten, Dybedal, Berget and Storelie, as we read it.']] },
    { h: 'The yard', t: 'The yard is at 509 metres. The ground falls away to the west. This is the view from it, down to the valley and across to the hills on the far side.',
      p: [60.54615, 9.1976, null, 16], l: [60.556, 9.13, 420], show: [], dur: 4600 },
    { h: 'Four suspects', t: 'Which rock? There are four candidates within a kilometre of the door. Turn the model and judge for yourself.',
      p: [60.5458, 9.1895, 700], l: [60.5474, 9.2005, 575], show: ['berget', 'skriu', 's1', 's2', 's3', 's4'], dur: 4200, rings: 1, free: 1 },
    { h: 'The walk to church', t: '3.8 miles in a straight line and 1,130 feet down. On foot that is well over an hour down and about two hours back up. Their real path is not known, and it was longer than this line. If this is the farm, Ole was born up here in August 1839 and his name was written down there.',
      pics: [['gude-nes-church', 'The church, painted in 1845', 'The stave church at Nes, watercolour by Hans Gude, June 1845. Hallingdal Museum.'], ['ole-birth-1839', 'Ole\u2019s entry, 1839', 'The Nes church book, 1839. Entry 39: Ole, born 6 August, son of Amund Halvorsen Berget.']],
      walk: 1, show: ['stave', 'berget'], dur: 26000, path: 1 }
  ];

  function fail(msg) { failed = true; var f = el.querySelector('.rk-fail'); f.textContent = msg; f.hidden = false; el.querySelector('.rk-card').hidden = true; }

  function init() {
    started = true; el = document.getElementById('rk'); if (!el) return;
    if (!window.THREE || !T) { fail('The 3D model could not load here. It needs WebGL and a connection for its drawing library.'); return; }
    cv = el.querySelector('canvas'); lab = el.querySelector('.rk-labels');
    try { renderer = new THREE.WebGLRenderer({ canvas: cv, antialias: true, alpha: true }); } catch (e) { fail('This browser could not start WebGL, so the 3D model is not shown.'); return; }
    renderer.setPixelRatio(Math.min(2, window.devicePixelRatio || 1)); renderer.setClearColor(0x000000, 0);
    MPP = 40075016.686 * Math.cos(LAT0 * Math.PI / 180) / 4096 / 256;
    FBX = (tx(LON0, 12) - T.x0) * 256; FBY = (ty(LAT0, 12) - T.y0) * 256;
    PX0 = (T.px0 / 4 - T.x0) * 256; PY0 = (T.py0 / 4 - T.y0) * 256;
    base = u16(T.b, T.w * T.h); patch = u16(T.pb, T.pw * T.ph);
    scene = new THREE.Scene(); scene.fog = new THREE.Fog(0x15191c, 3500, 15000);
    camera = new THREE.PerspectiveCamera(50, 1, 2, 30000);
    /* the whole valley, one vertex per 19 m; sunk out of sight under the detailed patch */
    var TW = renderer.capabilities.maxTextureSize >= 2048 ? 2048 : 1024;
    var tb = TEX.bs = relief(TW, Math.round(TW * T.h / T.w), function (u, v) { return hBase(u * (T.w - 1), v * (T.h - 1)); }, MPP * (T.w - 1) / (TW - 1), 50, 250);
    scene.add(meshB = grid(T.w, T.h, function (i, j) { return [(i - FBX) * MPP, hBase(i, j) - (inPatch(i, j) > 2 ? 40 : 0), (j - FBY) * MPP]; }, tb, false));
    /* the farm and the slope behind it, one vertex per 4.7 m */
    var tp = TEX.ps = relief(768, 768, function (u, v) { return hGrid(PX0 + u * (T.pw - 1) / 4, PY0 + v * (T.ph - 1) / 4); }, MPP / 4 * (T.pw - 1) / 767, 50, 250, 10);
    scene.add(meshP = grid(T.pw, T.ph, function (i, j) { var bx = PX0 + i / 4, by = PY0 + j / 4; return [(bx - FBX) * MPP, hGrid(bx, by) + .3, (by - FBY) * MPP]; }, tp, true));
    /* suspects */
    R.rings = new THREE.Group();
    R.rings.add(ring(60.5493, 9.1984, 95, 7)); R.rings.add(ring(60.54631, 9.20474, 60, 7)); R.rings.add(ring(60.54066, 9.19078, 70, 7)); R.rings.add(ring(60.54585, 9.1969, 34, 4));
    scene.add(R.rings);
    /* straight line from the farm to the church site */
    var a = world(60.54615, 9.1973), b = world(60.5701, 9.0971), pts = [];
    for (var i = 0; i <= 320; i++) pts.push([a[0] + (b[0] - a[0]) * i / 320, a[1] + (b[1] - a[1]) * i / 320]);
    R.line = pts; R.path = ribbon(pts, 26, 0xff7a4f, .9, false, 4); scene.add(R.path);
    /* labels with a thin post down to the ground */
    var posts = [];
    ALL.forEach(function (k) {
      var p = PLACES[k], w = world(p.ll[0], p.ll[1]), g = hAt(w[0], w[1]);
      p.v = new THREE.Vector3(w[0], g + p.lift, w[1]); posts.push(w[0], g, w[1], w[0], g + p.lift, w[1]);
      var d = document.createElement('div'); d.className = 'rk-l' + (p.hot ? ' hot' : ''); d.innerHTML = '<b></b>' + (p.s ? '<small></small>' : '');
      d.querySelector('b').textContent = p.n; if (p.s) d.querySelector('small').textContent = p.s;
      lab.appendChild(d); p.el = d; labels.push(p);
    });
    var pg = new THREE.BufferGeometry(); pg.setAttribute('position', new THREE.BufferAttribute(new Float32Array(posts), 3));
    scene.add(new THREE.LineSegments(pg, new THREE.LineBasicMaterial({ color: 0xedf3f5, transparent: true, opacity: .55 })));

    cam.p = V(60.50, 9.07, 5200); cam.t = V(60.556, 9.165, 250);
    size(); if (window.ResizeObserver) new ResizeObserver(size).observe(el); else window.addEventListener('resize', size);
    controls(); inset(); go(0, true);
    /* satellite pictures, shaded with the same light as the survey map so the hills keep their shape */
    var left = 2, imB = new Image(), imP = new Image();
    function got() { if (--left) return;
      TEX.bp = relief(TW, Math.round(TW * T.h / T.w), function (u, v) { return hBase(u * (T.w - 1), v * (T.h - 1)); }, MPP * (T.w - 1) / (TW - 1), 50, 250, 0, imB);
      TEX.pp = relief(768, 768, function (u, v) { return hGrid(PX0 + u * (T.pw - 1) / 4, PY0 + v * (T.ph - 1) / 4); }, MPP / 4 * (T.pw - 1) / 767, 50, 250, 0, imP);
      R.mode(mode); }
    imB.onload = imP.onload = got; imB.onerror = imP.onerror = function () { R.mode('survey'); el.querySelector('.rk-modes').hidden = true; };
    imB.src = 'img/sat-valley.jpg'; imP.src = 'img/sat-farm.jpg';
  }
  function size() { var w = el.clientWidth, h = el.clientHeight; if (!w || !h) return; renderer.setSize(w, h, false); camera.aspect = w / h; camera.updateProjectionMatrix(); }

  function pics(list) {
    var box = document.getElementById('rk-pics'); if (!box) return; box.textContent = '';
    (list || []).forEach(function (p) {
      var b = document.createElement('button'); b.type = 'button'; b.className = 'rk-pic'; b.setAttribute('data-lbsrc', 'img/' + p[0] + '.jpg'); b.setAttribute('data-lbcap', p[2]);
      var im = document.createElement('img'); im.src = 'img/' + p[0] + '.jpg'; im.alt = ''; var sp = document.createElement('span'); sp.textContent = p[1];
      b.appendChild(im); b.appendChild(sp); box.appendChild(b);
    });
  }
  /* a small map of Norway with Nes marked, drawn from the outline the crossing map already uses */
  function inset() {
    var A = window.ATLAS, box = el.querySelector('.rk-inset'); if (!box || !A || !A.land || !A.pts || A.pts.length < 3) return;
    var n = A.pts[0], c = A.pts[1], k = A.pts[2], uy = Math.abs(k[1] - n[1]) / 2.42, ux = Math.abs(c[0] - n[0]) / 1.65;
    if (!(ux > 0) || !(uy > 0)) return;
    var w = 11 * ux, h = 7.6 * uy, x0 = n[0] - 5.6 * ux, y0 = n[1] - 4.6 * uy;
    box.innerHTML = '<svg viewBox="' + [x0, y0, w, h].join(' ') + '" aria-hidden="true"><path d="' + A.land + '"/><circle cx="' + n[0] + '" cy="' + n[1] + '" r="' + w * .05 + '"/></svg><b>Nes, southern Norway</b><small>120 km north-west of Oslo</small>';
    box.hidden = false;
  }
  function go(i, first) {
    chapter = clamp(i, 0, CH.length - 1); var c = CH[chapter]; free = !!c.free;
    document.getElementById('rk-step').textContent = (chapter + 1) + ' of ' + CH.length;
    document.getElementById('rk-h').textContent = c.h; document.getElementById('rk-p').textContent = c.t;
    document.getElementById('rk-back').disabled = chapter === 0;
    document.getElementById('rk-next').textContent = chapter === CH.length - 1 ? 'Start again' : 'Next';
    document.getElementById('rk-alt').textContent = ''; pics(c.pics);
    R.rings.visible = !!c.rings; R.path.visible = !!c.path;
    labels.forEach(function (p) { p.on = false; }); c.show.forEach(function (k) { PLACES[k].on = true; });
    orbit = null;
    if (c.walk) { tween = { walk: 1, t0: performance.now() + 900, dur: c.dur }; return; }
    var P = c.p[2] == null ? V(c.p[0], c.p[1], null, c.p[3]) : V(c.p[0], c.p[1], c.p[2]), L = V(c.l[0], c.l[1], c.l[2]);
    tween = { p0: cam.p.clone(), t0v: cam.t.clone(), p1: P, t1: L, t0: performance.now(), dur: first ? 3400 : c.dur };
  }
  R.fly = function (k) {
    var p = PLACES[k]; if (!p || !started || failed) return;
    var c = CH[5]; chapter = 5; free = true; R.rings.visible = true; R.path.visible = false;
    labels.forEach(function (q) { q.on = false; }); c.show.forEach(function (q) { PLACES[q].on = true; });
    document.getElementById('rk-step').textContent = '6 of ' + CH.length; document.getElementById('rk-h').textContent = p.n.replace(/^\d\s+/, ''); document.getElementById('rk-p').textContent = p.s || '';
    document.getElementById('rk-back').disabled = false; document.getElementById('rk-next').textContent = 'Next'; document.getElementById('rk-alt').textContent = ''; pics(null);
    var w = world(p.ll[0], p.ll[1]), g = hAt(w[0], w[1]), f = world(60.54615, 9.1973);
    var dx = f[0] - w[0], dz = f[1] - w[1], l = Math.sqrt(dx * dx + dz * dz); if (l < 60) { dx = -1; dz = .3; l = 1.05; }
    var dist = k === 's4' ? 150 : 430, P = new THREE.Vector3(w[0] + dx / l * dist, 0, w[1] + dz / l * dist); P.y = Math.max(hAt(P.x, P.z) + 45, g + (k === 's4' ? 60 : 110));
    orbit = null; tween = { p0: cam.p.clone(), t0v: cam.t.clone(), p1: P, t1: new THREE.Vector3(w[0], g + 10, w[1]), t0: performance.now(), dur: 3000 };
    el.scrollIntoView({ block: 'center', behavior: 'smooth' });
  };

  function controls() {
    document.getElementById('rk-next').addEventListener('click', function () { go(chapter === CH.length - 1 ? 0 : chapter + 1); });
    document.getElementById('rk-back').addEventListener('click', function () { go(chapter - 1); });
    el.querySelectorAll('.rk-zoom button').forEach(function (b, i) { b.addEventListener('click', function () { grab(); orbit.r = clamp(orbit.r * (i ? 1.3 : .77), 40, 12000); }); });
    var ptrs = {}, last = null, pinch = 0, active = false;
    function grab() { if (tween && tween.walk) { /* leave the walk where it is */ } tween = null; if (!orbit) { var d = cam.p.clone().sub(cam.t), r = d.length(); orbit = { r: r, th: Math.atan2(d.x, d.z), ph: Math.acos(clamp(d.y / r, -1, 1)) }; } }
    R.grab = grab;
    cv.addEventListener('pointerdown', function (e) { cv.setPointerCapture(e.pointerId); ptrs[e.pointerId] = [e.clientX, e.clientY]; last = [e.clientX, e.clientY]; active = true; grab(); });
    cv.addEventListener('pointermove', function (e) {
      if (!ptrs[e.pointerId]) return; ptrs[e.pointerId] = [e.clientX, e.clientY];
      var ids = Object.keys(ptrs);
      if (ids.length === 2) { var a = ptrs[ids[0]], b = ptrs[ids[1]], d = Math.hypot(a[0] - b[0], a[1] - b[1]); if (pinch) orbit.r = clamp(orbit.r * pinch / d, 40, 12000); pinch = d; return; }
      orbit.th -= (e.clientX - last[0]) * .006; orbit.ph = clamp(orbit.ph - (e.clientY - last[1]) * .005, .12, 1.56); last = [e.clientX, e.clientY];
    });
    function up(e) { delete ptrs[e.pointerId]; pinch = 0; }
    cv.addEventListener('pointerup', up); cv.addEventListener('pointercancel', up);
    cv.addEventListener('mouseleave', function () { active = false; });
    cv.addEventListener('wheel', function (e) { if (!active) return; e.preventDefault(); grab(); orbit.r = clamp(orbit.r * Math.exp(e.deltaY * .0012), 40, 12000); }, { passive: false });
  }

  function ease(k) { return k < .5 ? 4 * k * k * k : 1 - Math.pow(-2 * k + 2, 3) / 2; }
  function frame(now) {
    if (tween && tween.walk) {
      var k = clamp((now - tween.t0) / tween.dur, 0, 1), s = k * k * (3 - 2 * k) * .985, L = R.line, n = L.length - 1;
      var at = function (q) { q = clamp(q, 0, 1) * n; var i = Math.min(n - 1, Math.floor(q)), f = q - i; return [L[i][0] + (L[i + 1][0] - L[i][0]) * f, L[i][1] + (L[i + 1][1] - L[i][1]) * f]; };
      var a = at(s), b = at(s + .07), top = 0;
      for (var q = -2; q <= 6; q++) { var c = at(s + q * .006); top = Math.max(top, hAt(c[0], c[1])); }
      cam.p.set(a[0], top + 38, a[1]); cam.t.set(b[0], hAt(b[0], b[1]) + 12, b[1]);
      var left = Math.hypot(L[n][0] - a[0], L[n][1] - a[1]) / 1609.34;
      document.getElementById('rk-alt').textContent = left.toFixed(1) + ' miles to the church \u00b7 ' + Math.round(hAt(a[0], a[1]) * 3.28084 / 10) * 10 + ' ft above the sea';
      if (k >= 1) tween = null;
    } else if (tween) {
      var e = ease(clamp((now - tween.t0) / tween.dur, 0, 1));
      cam.p.lerpVectors(tween.p0, tween.p1, e); cam.t.lerpVectors(tween.t0v, tween.t1, e);
      if (e >= 1) tween = null;
    } else if (orbit) {
      var sp = Math.sin(orbit.ph); cam.p.set(cam.t.x + orbit.r * sp * Math.sin(orbit.th), cam.t.y + orbit.r * Math.cos(orbit.ph), cam.t.z + orbit.r * sp * Math.cos(orbit.th));
    }
    var floor = hAt(cam.p.x, cam.p.z) + 5; if (cam.p.y < floor) cam.p.y = floor;
    camera.position.copy(cam.p); camera.lookAt(cam.t); camera.updateMatrixWorld();
    renderer.render(scene, camera);
    var w = el.clientWidth, h = el.clientHeight, v = new THREE.Vector3();
    labels.forEach(function (p) {
      var show = p.on || (free && !tween && orbit && p.hot);
      if (show) { v.copy(p.v).project(camera); show = v.z < 1 && v.z > -1 && Math.abs(v.x) < 1.05 && Math.abs(v.y) < 1.05; }
      if (show) { p.el.style.transform = 'translate(' + ((v.x + 1) / 2 * w).toFixed(1) + 'px,' + ((1 - v.y) / 2 * h).toFixed(1) + 'px) translate(-50%,-100%)'; p.el.style.opacity = 1; }
      else p.el.style.opacity = 0;
    });
  }
  function loop() { cancelAnimationFrame(raf); (function tick(now) { if (!running || failed) return; frame(now); raf = requestAnimationFrame(tick); })(performance.now()); }
  R.mode = function (m) {
    mode = m; if (!el) return;
    var sat = m === 'sat' && TEX.bp;
    el.classList.toggle('sat', !!sat);
    el.querySelectorAll('.rk-modes button').forEach(function (b) { b.setAttribute('aria-pressed', b.dataset.mode === m ? 'true' : 'false'); });
    if (!meshB) return;
    meshB.material.map = sat ? TEX.bp : TEX.bs; meshP.material.map = sat ? TEX.pp : TEX.ps; meshB.material.needsUpdate = meshP.material.needsUpdate = true;
    scene.fog.color.set(sat ? 0xc4cfd7 : 0x15191c); scene.fog.near = sat ? 2500 : 3500; scene.fog.far = sat ? 14000 : 15000;
  };
  R.show = function (on) { if (on) { if (!started) init(); if (failed) return; running = true; size(); loop(); } else { running = false; cancelAnimationFrame(raf); } };
})();
