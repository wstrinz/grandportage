"""Standalone Three.js campaign explorer generation.

The explorer embeds a non-authoritative projection.  It never reads or writes
the campaign graph in the browser and has no route back into the kernel.
"""

import json
import re


THREE_VERSION = "0.185.1"
DEFAULT_THREE_ROOT = (
    "https://cdn.jsdelivr.net/npm/three@%s/" % THREE_VERSION
)


def _embedded_json(value):
    # A graph record may contain prose with HTML-looking text.  Keep it data,
    # even inside a script tag.
    return json.dumps(
        value, sort_keys=True, separators=(",", ":"), ensure_ascii=True
    ).replace("<", "\\u003c")


def render(projection, title="Grand Portage campaign", three_root=None):
    root = (three_root or DEFAULT_THREE_ROOT).rstrip("/") + "/"
    imports = {
        "three": root + "build/three.module.js",
        "three/addons/": root + "examples/jsm/",
    }
    values = {
        "TITLE": _html_text(title),
        "IMPORT_MAP": _embedded_json({"imports": imports}),
        "PROJECTION": _embedded_json(projection),
        "THREE_VERSION": THREE_VERSION,
    }
    # Substitute once. Project prose and titles are data even if they happen to
    # contain one of the template marker strings.
    return re.sub(
        r"__(TITLE|IMPORT_MAP|PROJECTION|THREE_VERSION)__",
        lambda match: values[match.group(1)],
        _HTML,
    )


def _html_text(value):
    return (str(value).replace("&", "&amp;").replace("<", "&lt;")
            .replace(">", "&gt;").replace('"', "&quot;"))


_HTML = r'''<!doctype html>
<html lang="en">
<head>
  <meta charset="utf-8">
  <meta name="viewport" content="width=device-width,initial-scale=1">
  <title>__TITLE__</title>
  <style>
    :root {
      color-scheme: dark;
      --ink: #eef5ff; --muted: #8492a8; --panel: rgba(9,14,24,.88);
      --line: rgba(133,157,190,.23); --accent: #73d7ff;
    }
    * { box-sizing: border-box }
    html, body { width: 100%; height: 100%; margin: 0; overflow: hidden;
      background: radial-gradient(circle at 50% 30%, #17253a 0, #080c14 52%, #030508 100%);
      color: var(--ink); font: 13px/1.45 Inter, ui-sans-serif, system-ui, sans-serif }
    #stage { position: fixed; inset: 0 }
    canvas { display: block }
    .glass { background: var(--panel); border: 1px solid var(--line);
      box-shadow: 0 18px 70px rgba(0,0,0,.38); backdrop-filter: blur(16px) }
    #top { position: fixed; z-index: 5; top: 18px; left: 18px; right: 18px;
      min-height: 58px; border-radius: 16px; display: flex; align-items: center;
      gap: 18px; padding: 10px 14px }
    #brand { min-width: 230px }
    #brand strong { display: block; font-size: 15px; letter-spacing: .02em }
    #brand span, #stats { color: var(--muted); font-size: 11px }
    #search { flex: 1; position: relative }
    input { width: 100%; border: 1px solid var(--line); color: var(--ink);
      background: rgba(2,7,13,.72); border-radius: 11px; padding: 10px 13px;
      outline: none }
    input:focus { border-color: rgba(115,215,255,.65); box-shadow: 0 0 0 3px rgba(115,215,255,.08) }
    button { border: 1px solid var(--line); color: var(--ink); background: rgba(22,32,49,.84);
      border-radius: 10px; padding: 8px 10px; cursor: pointer }
    button:hover { border-color: rgba(115,215,255,.55); background: rgba(31,48,71,.94) }
    #left { position: fixed; z-index: 4; left: 18px; top: 92px; bottom: 18px;
      width: 230px; border-radius: 16px; padding: 14px; overflow: auto }
    #right { position: fixed; z-index: 4; right: 18px; top: 92px; bottom: 18px;
      width: min(390px, 34vw); border-radius: 16px; padding: 15px; overflow: auto }
    h2 { margin: 0 0 10px; font-size: 12px; color: #a9bdd5; letter-spacing: .12em; text-transform: uppercase }
    #kindFilters label { display: flex; align-items: center; gap: 8px; padding: 4px 0; cursor: pointer }
    #kindFilters i { width: 9px; height: 9px; border-radius: 50%; display: inline-block }
    #kindFilters small { margin-left: auto; color: var(--muted) }
    .section { padding: 12px 0; border-top: 1px solid var(--line) }
    .section:first-child { border-top: 0; padding-top: 0 }
    #selection h1 { font-size: 18px; margin: 2px 0 3px; overflow-wrap: anywhere }
    .pill { display: inline-block; padding: 3px 7px; margin: 2px 4px 2px 0;
      border-radius: 999px; background: rgba(115,215,255,.1); color: #bdeeff;
      border: 1px solid rgba(115,215,255,.2); font-size: 10px; letter-spacing: .04em }
    pre { white-space: pre-wrap; overflow-wrap: anywhere; color: #b8c5d6; margin: 10px 0 0;
      font: 11px/1.5 ui-monospace, SFMono-Regular, Consolas, monospace }
    #neighbors button { display: block; width: 100%; text-align: left; margin: 5px 0;
      overflow: hidden; text-overflow: ellipsis; white-space: nowrap }
    #neighbors button small { display: block; color: var(--muted); font-size: 9px;
      overflow: hidden; text-overflow: ellipsis }
    select { width: 100%; border: 1px solid var(--line); color: var(--ink);
      background: rgba(2,7,13,.9); border-radius: 10px; padding: 8px; outline: none }
    .tour-controls { display: grid; grid-template-columns: auto 1fr auto; gap: 6px; margin: 8px 0 }
    .tour-controls button { min-width: 0 }
    #tourProgress { color: var(--muted); font-size: 10px; letter-spacing: .06em;
      text-transform: uppercase; margin: 8px 0 3px }
    #tourStory strong { display: block; color: var(--ink); font-size: 14px; margin-bottom: 5px }
    #tourStory p { margin: 5px 0; color: #b8c5d6 }
    #tourStory .why { color: #ffd38a }
    #trail { display: flex; gap: 6px }
    #trail button { flex: 1 }
    #hint { position: fixed; z-index: 3; left: 264px; bottom: 20px; color: var(--muted);
      background: rgba(3,7,12,.62); border: 1px solid var(--line); padding: 7px 10px; border-radius: 9px }
    #tooltip { position: fixed; z-index: 8; pointer-events: none; display: none;
      padding: 6px 8px; border-radius: 8px; background: rgba(2,6,11,.93);
      border: 1px solid rgba(150,180,215,.25); max-width: 280px }
    .warning { color: #ffd38a }
    @media (max-width: 900px) {
      #left { width: 180px } #right { width: 310px } #hint { left: 210px }
      #brand { min-width: 160px }
    }
  </style>
  <script type="importmap">__IMPORT_MAP__</script>
</head>
<body>
  <div id="stage"></div>
  <header id="top" class="glass">
    <div id="brand"><strong>__TITLE__</strong><span>derived campaign projection · Three.js __THREE_VERSION__</span></div>
    <div id="search"><input id="query" autocomplete="off" placeholder="Search IDs and text — press / to focus"></div>
    <div id="stats"></div>
    <button id="reset">Reset view</button>
  </header>
  <aside id="left" class="glass">
    <div class="section"><h2>Entity layers</h2><div id="kindFilters"></div></div>
    <div class="section"><h2>Display</h2>
      <label><input id="labels" type="checkbox" checked> Labels</label><br>
      <label><input id="relations" type="checkbox" checked> Relations</label><br>
      <label><input id="context" type="checkbox" checked> Focus selected context</label><br>
      <label><input id="isolate" type="checkbox"> Hide outside context</label><br>
      <label for="contextDepth">Context depth</label>
      <select id="contextDepth"><option value="1">1 hop</option><option value="2" selected>2 hops</option><option value="3">3 hops</option><option value="4">4 hops</option></select>
    </div>
    <div class="section"><h2>Authority</h2>
      <div><span class="pill">cyan</span> declared</div>
      <div><span class="pill">green</span> verified</div>
      <div><span class="pill">amber</span> stale / debt</div>
      <div><span class="pill">red</span> refused / unsound</div>
    </div>
  </aside>
  <aside id="right" class="glass">
    <div id="tour" class="section">
      <h2>Argument tour</h2>
      <select id="tourSelect" aria-label="Choose an argument tour"></select>
      <div class="tour-controls"><button id="tourPrev" title="Previous stop">&#8592;</button><button id="tourGo">Start tour</button><button id="tourNext" title="Next stop">&#8594;</button></div>
      <div id="tourProgress">Choose a tour</div>
      <div id="tourStory"><p>Walk the campaign by inference, audit finding, transformation, or claim.</p></div>
    </div>
    <div id="selection" class="section"><h2>Selection</h2><p>Click a node to inspect its exact projected record.</p></div>
    <div class="section"><h2>Trail</h2><div id="trail"><button id="trailBack" disabled>&#8592; Back</button><button id="trailForward" disabled>Forward &#8594;</button></div></div>
    <div class="section"><h2>Related by</h2><div id="neighbors"><span class="warning">Nothing selected.</span></div></div>
  </aside>
  <div id="hint">drag orbit &middot; click inspect &middot; [ ] tour &middot; F frame &middot; Esc clear</div>
  <div id="tooltip"></div>
  <script id="projection" type="application/json">__PROJECTION__</script>
  <script type="module">
    import * as THREE from 'three';
    import { OrbitControls } from 'three/addons/controls/OrbitControls.js';

    const data = JSON.parse(document.getElementById('projection').textContent);
    const stage = document.getElementById('stage');
    const renderer = new THREE.WebGLRenderer({antialias: true, alpha: true});
    renderer.setPixelRatio(Math.min(devicePixelRatio, 2));
    renderer.setSize(innerWidth, innerHeight);
    renderer.outputColorSpace = THREE.SRGBColorSpace;
    renderer.toneMapping = THREE.ACESFilmicToneMapping;
    renderer.toneMappingExposure = 1.15;
    stage.appendChild(renderer.domElement);

    const scene = new THREE.Scene();
    scene.fog = new THREE.FogExp2(0x060a11, .0065);
    const camera = new THREE.PerspectiveCamera(48, innerWidth / innerHeight, .1, 1200);
    camera.position.set(18, 28, 72);
    const controls = new OrbitControls(camera, renderer.domElement);
    controls.enableDamping = true;
    controls.dampingFactor = .075;
    controls.minDistance = 8;
    controls.maxDistance = 260;
    controls.target.set(2, 0, 0);

    scene.add(new THREE.HemisphereLight(0xcde9ff, 0x172033, 2.1));
    const keyLight = new THREE.DirectionalLight(0xffffff, 2.2);
    keyLight.position.set(18, 32, 26); scene.add(keyLight);
    const rim = new THREE.PointLight(0x36c8ff, 80, 120); rim.position.set(-22, -16, 28); scene.add(rim);

    const palette = {
      model: 0x46b3ff, edge: 0x9278ff, partition: 0xce72ff, alias: 0x7d8aa6,
      claim: 0x4ee6b1, family: 0x76d997, inference: 0xffb45f,
      evidence: 0x47d6d0, verdict: 0x62e56d, finding: 0xff5f68,
      doubt: 0xff7c55, citation: 0x70a2d8, certificate: 0x9be36c,
      note: 0x8491a5, tombstone: 0x586273
    };
    const columns = {
      model: -28, edge: -16, partition: -16, alias: -16,
      claim: -3, family: -3, inference: 10,
      evidence: 23, verdict: 23, certificate: 23, citation: 23,
      finding: 35, doubt: 35, note: 35, tombstone: 35
    };
    const layerOrder = Object.keys(columns);
    const root = new THREE.Group(); scene.add(root);
    const relationRoot = new THREE.Group(); root.add(relationRoot);
    const nodeRoot = new THREE.Group(); root.add(nodeRoot);
    const labelRoot = new THREE.Group(); root.add(labelRoot);
    const meshByKey = new Map(), labelByKey = new Map(), nodeByKey = new Map();

    function statusColor(node) {
      const status = String(node.status || '').toUpperCase();
      if (/REFUT|UNSOUND|ERROR|WITHDRAW/.test(status)) return 0xff5260;
      if (/STALE|DEBT|UNVERIFIED|UNSUPPORTED|SUPERSEDED|REQUIRES/.test(status)) return 0xffc15a;
      if (/VERIFIED|CHECKED|PROVED/.test(status)) return 0x58e483;
      return palette[node.kind] || 0x8ea2bb;
    }
    function geometry(kind) {
      if (kind === 'model') return new THREE.SphereGeometry(1.25, 20, 14);
      if (kind === 'claim') return new THREE.IcosahedronGeometry(1.18, 1);
      if (kind === 'inference') return new THREE.OctahedronGeometry(1.22, 0);
      if (kind === 'edge') return new THREE.BoxGeometry(1.5, 1.5, 1.5);
      if (kind === 'partition') return new THREE.TetrahedronGeometry(1.35, 0);
      if (kind === 'finding') return new THREE.DodecahedronGeometry(1.2, 0);
      return new THREE.SphereGeometry(.82, 14, 10);
    }
    function sprite(text, color, scale=1) {
      const canvas = document.createElement('canvas'); canvas.width = 512; canvas.height = 80;
      const ctx = canvas.getContext('2d'); ctx.font = '600 25px system-ui';
      ctx.fillStyle = 'rgba(3,8,14,.76)'; ctx.roundRect(4, 5, 504, 66, 15); ctx.fill();
      ctx.strokeStyle = 'rgba(150,190,225,.24)'; ctx.stroke();
      ctx.fillStyle = color; ctx.textAlign = 'center'; ctx.textBaseline = 'middle';
      const clipped = text.length > 36 ? text.slice(0, 34) + '…' : text;
      ctx.fillText(clipped, 256, 39);
      const texture = new THREE.CanvasTexture(canvas); texture.colorSpace = THREE.SRGBColorSpace;
      const material = new THREE.SpriteMaterial({map: texture, transparent: true, depthWrite: false});
      const result = new THREE.Sprite(material); result.scale.set(8.4*scale, 1.32*scale, 1);
      return result;
    }
    function positionNodes(nodes) {
      const buckets = new Map();
      for (const node of nodes) {
        const bucket = buckets.get(node.kind) || []; bucket.push(node); buckets.set(node.kind, bucket);
      }
      for (const [kind, bucket] of buckets) {
        bucket.sort((a,b) => a.id.localeCompare(b.id));
        const x = columns[kind] ?? 42;
        const rows = Math.max(1, Math.ceil(Math.sqrt(bucket.length)));
        bucket.forEach((node, index) => {
          const row = index % rows, band = Math.floor(index / rows);
          const y = (row - (rows-1)/2) * 4.2;
          const z = (band - (Math.ceil(bucket.length/rows)-1)/2) * 5.2 + Math.sin(index*1.7)*.45;
          node.position = new THREE.Vector3(x, y, z);
        });
      }
    }
    positionNodes(data.nodes);

    for (const node of data.nodes) {
      nodeByKey.set(node.key, node);
      const color = statusColor(node);
      const material = new THREE.MeshStandardMaterial({
        color, emissive: color, emissiveIntensity: .22, roughness: .42, metalness: .22,
        transparent: true, opacity: .96
      });
      const mesh = new THREE.Mesh(geometry(node.kind), material);
      mesh.position.copy(node.position); mesh.userData.key = node.key;
      nodeRoot.add(mesh); meshByKey.set(node.key, mesh);
      const halo = new THREE.Mesh(new THREE.SphereGeometry(1.58, 12, 8),
        new THREE.MeshBasicMaterial({color, transparent: true, opacity: .055, depthWrite: false}));
      mesh.add(halo);
      const label = sprite(node.id, '#eaf5ff'); label.position.copy(node.position).add(new THREE.Vector3(0, 2.15, 0));
      labelRoot.add(label); labelByKey.set(node.key, label);
    }

    const relationObjects = [];
    for (const relation of data.relations) {
      const source = meshByKey.get(relation.source), target = meshByKey.get(relation.target);
      if (!source || !target) continue;
      const points = [source.position, target.position];
      const geometry = new THREE.BufferGeometry().setFromPoints(points);
      const color = relation.kind.includes('finding') ? 0xff6472 :
                    relation.kind.includes('verdict') ? 0x65e787 : 0x7f9aba;
      const line = new THREE.Line(geometry, new THREE.LineBasicMaterial({
        color, transparent: true, opacity: .28, depthWrite: false
      }));
      line.userData = {relation}; relationRoot.add(line); relationObjects.push(line);
    }

    // Column guides turn the z/y cloud into a semantic coordinate system.
    const guideKinds = [...new Set(data.nodes.map(n => n.kind))].sort((a,b) =>
      (columns[a] ?? 42) - (columns[b] ?? 42) || a.localeCompare(b));
    for (const kind of guideKinds) {
      const x = columns[kind] ?? 42;
      const guide = new THREE.GridHelper(52, 13, palette[kind] || 0x607088, 0x1a2636);
      guide.rotation.z = Math.PI/2; guide.position.x = x; guide.material.opacity = .12;
      guide.material.transparent = true; root.add(guide);
      const title = sprite(kind.toUpperCase(), '#91a8c3', .9);
      title.position.set(x, 26, -21); labelRoot.add(title);
    }

    const raycaster = new THREE.Raycaster(), pointer = new THREE.Vector2();
    let selected = null, hovered = null;
    let selectionTrail = [], trailIndex = -1, tourIndex = -1;
    const adjacency = new Map(data.nodes.map(node => [node.key, new Set()]));
    const incident = new Map(data.nodes.map(node => [node.key, []]));
    for (const relation of data.relations) {
      if (!adjacency.has(relation.source) || !adjacency.has(relation.target)) continue;
      adjacency.get(relation.source).add(relation.target);
      adjacency.get(relation.target).add(relation.source);
      incident.get(relation.source).push({other: relation.target, direction: 'out', relation});
      incident.get(relation.target).push({other: relation.source, direction: 'in', relation});
    }

    function clipped(value, limit=520) {
      const text = String(value || '').trim().replace(/\s+/g, ' ');
      return text.length > limit ? text.slice(0, limit - 1) + '...' : text;
    }
    function recordFor(node) {
      if (Object.prototype.hasOwnProperty.call(node, 'record')) return node.record;
      const ref = node.record_ref || {};
      const collection = data.collections?.[ref.collection];
      let record;
      if (Object.prototype.hasOwnProperty.call(ref, 'id') && collection && !Array.isArray(collection)) {
        record = collection[ref.id];
      } else if (Number.isInteger(ref.index) && Array.isArray(collection)) {
        record = collection[ref.index];
      }
      if (ref.field !== undefined) record = record?.[ref.field];
      return record || {};
    }
    function readingFor(node) {
      const r = recordFor(node);
      if (node.kind === 'inference') {
        const route = (r.path || []).map(step => `${step[0]} ${step[1]}`).join(', ') || 'no transport edge';
        return {
          headline: `${r.concludes_kind || 'claim'} at ${r.concludes_at || 'declared endpoint'}`,
          summary: clipped(r.asserted || `Inference ${node.id}`),
          why: `This is a transport step for ${r.claim || 'its premise'} via ${route}. Its authority depends on the claim scope, edge contracts, direction, and evidence shown nearby.`
        };
      }
      if (node.kind === 'finding') return {
        headline: `${node.status}: ${node.id}`,
        summary: clipped(r.detail || r.reason || 'The checker found unresolved semantic debt.'),
        why: clipped(r.discharge || 'Inspect the connected claim, inference, and edge to see what authority is missing.')
      };
      if (node.kind === 'edge') return {
        headline: `${r.src || '?'} -> ${r.dst || '?'} (${r.type || 'transformation'})`,
        summary: clipped(r.why || r.desc || `Transformation ${node.id}`),
        why: r.drops?.length ? `Recorded loss: ${r.drops.join('; ')}` : 'No recorded loss is shown; inspect the operation contract and evidence before treating this as exact.'
      };
      if (node.kind === 'claim') return {
        headline: `${r.kind || 'Claim'} on ${r.model || 'a model'}`,
        summary: clipped(r.statement || node.id),
        why: `Scope: ${r.scope || 'unspecified'}. Certificate: ${r.certificate || 'none declared'}. Follow related inference and certificate nodes to see what may be concluded.`
      };
      if (node.kind === 'model') return {
        headline: `Model ${node.id}`,
        summary: clipped(r.desc || r.describes || node.id),
        why: 'Models are presentations in the campaign. Incoming and outgoing transformations state what changes and what information may be lost.'
      };
      if (node.kind === 'certificate') return {
        headline: `Certificate ${node.id}`,
        summary: `Registered certificate; base_changes=${String(r.base_changes)}; source=${r.registry_source || 'unknown'}.`,
        why: 'A certificate is evidence metadata, not the proposition itself. Connected claims show where its authority is being used.'
      };
      return {
        headline: `${node.kind} ${node.id}`,
        summary: clipped(r.text || r.desc || r.statement || r.why || node.id),
        why: 'This is a projected campaign record. Its exact JSON remains available below.'
      };
    }
    function contextKeys(key, depth) {
      const keep = new Set(key ? [key] : []);
      let frontier = key ? new Set([key]) : new Set();
      for (let step = 0; step < depth && frontier.size; step++) {
        const next = new Set();
        for (const item of frontier) for (const neighbor of adjacency.get(item) || []) {
          if (!keep.has(neighbor)) next.add(neighbor);
        }
        for (const item of next) keep.add(item);
        frontier = next;
      }
      return keep;
    }
    function updateTrailButtons() {
      document.getElementById('trailBack').disabled = trailIndex <= 0;
      document.getElementById('trailForward').disabled = trailIndex < 0 || trailIndex >= selectionTrail.length - 1;
    }
    function showStory(reading) {
      const story = document.getElementById('tourStory'); story.replaceChildren();
      const title = document.createElement('strong'); title.textContent = reading.headline;
      const summary = document.createElement('p'); summary.textContent = reading.summary;
      const why = document.createElement('p'); why.className = 'why'; why.textContent = reading.why;
      story.append(title, summary, why);
    }
    function inspect(key, frame=false, recordTrail=true) {
      const node = nodeByKey.get(key); if (!node) return;
      selected = key;
      const kindBox = [...document.querySelectorAll('#kindFilters input')].find(input => input.value === node.kind);
      if (kindBox) kindBox.checked = true;
      if (recordTrail && selectionTrail[trailIndex] !== key) {
        selectionTrail = selectionTrail.slice(0, trailIndex + 1);
        selectionTrail.push(key); trailIndex = selectionTrail.length - 1;
      }
      updateTrailButtons();
      history.replaceState(null, '', '#' + encodeURIComponent(key));
      if (tourIndex >= 0) {
        const tour = activeTour();
        if (tour?.keys[tourIndex] !== key) {
          document.getElementById('tourProgress').textContent = `${tour.label} / paused while browsing`;
          showStory(readingFor(node));
        }
      }
      document.getElementById('selection').innerHTML =
        `<h2>Selection</h2><h1></h1><span class="pill"></span><span class="pill"></span><p class="selectionSummary"></p><pre></pre>`;
      const panel = document.getElementById('selection');
      panel.querySelector('h1').textContent = node.id;
      const pills = panel.querySelectorAll('.pill'); pills[0].textContent = node.kind; pills[1].textContent = node.status;
      panel.querySelector('.selectionSummary').textContent = readingFor(node).summary;
      panel.querySelector('pre').textContent = JSON.stringify(recordFor(node), null, 2);
      const neighbors = document.getElementById('neighbors'); neighbors.replaceChildren();
      const items = [...(incident.get(key) || [])].sort((a,b) => a.other.localeCompare(b.other));
      for (const item of items) {
        const button = document.createElement('button');
        const title = document.createElement('span');
        title.textContent = `${item.direction === 'out' ? '->' : '<-'} ${item.other}`;
        const detail = document.createElement('small');
        detail.textContent = `${item.relation.kind}${item.relation.label ? ' / ' + item.relation.label : ''}`;
        button.append(title, detail);
        button.onclick = () => inspect(item.other, true); neighbors.appendChild(button);
      }
      if (!neighbors.children.length) neighbors.textContent = 'No projected relations.';
      updateAppearance();
      if (frame) frameNode(node);
    }
    function clearSelection() {
      selected = null;
      history.replaceState(null, '', location.pathname + location.search);
      document.getElementById('selection').innerHTML = '<h2>Selection</h2><p>Click a node or start a tour to inspect its projected record.</p>';
      document.getElementById('neighbors').innerHTML = '<span class="warning">Nothing selected.</span>';
      updateAppearance();
    }
    function frameNode(node) {
      const direction = camera.position.clone().sub(controls.target).normalize();
      controls.target.copy(node.position); camera.position.copy(node.position).add(direction.multiplyScalar(18));
    }
    function updateAppearance() {
      const enabled = new Set([...document.querySelectorAll('#kindFilters input:checked')].map(i => i.value));
      const search = document.getElementById('query').value.trim().toLowerCase();
      const context = document.getElementById('context').checked;
      const isolate = document.getElementById('isolate').checked;
      const depth = Number(document.getElementById('contextDepth').value);
      const neighborhood = selected ? contextKeys(selected, depth) : null;
      for (const [key, mesh] of meshByKey) {
        const node = nodeByKey.get(key);
        const matches = !search || key.toLowerCase().includes(search) || JSON.stringify(recordFor(node)).toLowerCase().includes(search);
        const outside = neighborhood && !neighborhood.has(key);
        mesh.visible = enabled.has(node.kind) && matches && !(isolate && outside);
        const dim = context && outside;
        mesh.material.opacity = dim ? .08 : .96;
        mesh.material.emissiveIntensity = key === selected ? 1.15 : (dim ? .015 : .22);
        mesh.scale.setScalar(key === selected ? 1.45 : 1);
        const label = labelByKey.get(key); label.visible = mesh.visible && document.getElementById('labels').checked;
        label.material.opacity = dim ? .08 : 1;
      }
      relationRoot.visible = document.getElementById('relations').checked;
      for (const line of relationObjects) {
        const {source,target} = line.userData.relation;
        line.visible = relationRoot.visible && meshByKey.get(source)?.visible && meshByKey.get(target)?.visible;
        const active = selected && (source === selected || target === selected);
        const within = !neighborhood || (neighborhood.has(source) && neighborhood.has(target));
        line.material.opacity = active ? .95 : (context && !within ? .035 : .3);
      }
      const visible = [...meshByKey.values()].filter(mesh => mesh.visible).length;
      document.getElementById('stats').textContent = `${visible}/${data.nodes.length} nodes / ${data.relations.length} relations`;
    }

    const inferenceKeys = (data.orders?.inferences || []).map(id => `inference:${id}`).filter(key => nodeByKey.has(key));
    const severityRank = {UNSOUND_CONCLUSION: 0, UNSOUND_PREMISE: 1, DEBT: 2, CARRIED: 3};
    const findingKeys = data.nodes.filter(node => node.kind === 'finding')
      .sort((a,b) => (severityRank[a.status] ?? 9) - (severityRank[b.status] ?? 9) || a.id.localeCompare(b.id)).map(node => node.key);
    const edgeKeys = data.nodes.filter(node => node.kind === 'edge').sort((a,b) => a.id.localeCompare(b.id)).map(node => node.key);
    const claimKeys = data.nodes.filter(node => node.kind === 'claim').sort((a,b) => a.id.localeCompare(b.id)).map(node => node.key);
    const tours = [
      {id: 'argument', label: 'Argument spine', keys: inferenceKeys},
      {id: 'audit', label: 'Soundness audit', keys: findingKeys},
      {id: 'models', label: 'Model transformations', keys: edgeKeys},
      {id: 'claims', label: 'Claims and certificates', keys: claimKeys},
    ].filter(tour => tour.keys.length);
    const tourSelect = document.getElementById('tourSelect');
    for (const tour of tours) {
      const option = document.createElement('option'); option.value = tour.id;
      option.textContent = `${tour.label} (${tour.keys.length})`; tourSelect.appendChild(option);
    }
    function activeTour() { return tours.find(tour => tour.id === tourSelect.value) || tours[0]; }
    function renderTourStop() {
      const tour = activeTour(), key = tour?.keys[tourIndex];
      if (!tour || !key) return;
      const node = nodeByKey.get(key), reading = readingFor(node);
      document.getElementById('tourProgress').textContent = `${tour.label} / stop ${tourIndex + 1} of ${tour.keys.length}`;
      showStory(reading);
      document.getElementById('tourGo').textContent = 'Restart tour';
      document.getElementById('tourPrev').disabled = tourIndex <= 0;
      document.getElementById('tourNext').disabled = tourIndex >= tour.keys.length - 1;
      document.getElementById('query').value = '';
      document.getElementById('context').checked = true;
      inspect(key, true);
    }
    function goTour(index) {
      const tour = activeTour(); if (!tour?.keys.length) return;
      tourIndex = Math.max(0, Math.min(index, tour.keys.length - 1)); renderTourStop();
    }
    document.getElementById('tourGo').onclick = () => goTour(0);
    document.getElementById('tourPrev').onclick = () => goTour(tourIndex < 0 ? 0 : tourIndex - 1);
    document.getElementById('tourNext').onclick = () => goTour(tourIndex < 0 ? 0 : tourIndex + 1);
    tourSelect.onchange = () => {
      tourIndex = -1;
      document.getElementById('tourProgress').textContent = `${activeTour().label} / ${activeTour().keys.length} stops`;
      document.getElementById('tourStory').innerHTML = '<p>Press Start tour to follow this derived reading.</p>';
      document.getElementById('tourGo').textContent = 'Start tour';
    };

    const kinds = [...new Set(data.nodes.map(node => node.kind))].sort((a,b) =>
      (columns[a] ?? 42) - (columns[b] ?? 42) || a.localeCompare(b));
    const filters = document.getElementById('kindFilters');
    for (const kind of kinds) {
      const count = data.nodes.filter(node => node.kind === kind).length;
      const label = document.createElement('label');
      label.innerHTML = `<input type="checkbox" checked><i></i><span></span><small></small>`;
      const input = label.querySelector('input'); input.value = kind; input.onchange = updateAppearance;
      label.querySelector('i').style.background = '#' + (palette[kind] || 0x8ea2bb).toString(16).padStart(6,'0');
      label.querySelector('span').textContent = kind; label.querySelector('small').textContent = count;
      filters.appendChild(label);
    }
    for (const id of ['labels','relations','context','isolate','contextDepth']) document.getElementById(id).onchange = updateAppearance;
    document.getElementById('query').oninput = updateAppearance;
    document.getElementById('trailBack').onclick = () => {
      if (trailIndex > 0) { trailIndex--; inspect(selectionTrail[trailIndex], true, false); updateTrailButtons(); }
    };
    document.getElementById('trailForward').onclick = () => {
      if (trailIndex < selectionTrail.length - 1) { trailIndex++; inspect(selectionTrail[trailIndex], true, false); updateTrailButtons(); }
    };
    document.getElementById('reset').onclick = () => {
      controls.target.set(2,0,0); camera.position.set(18,28,72);
      document.getElementById('isolate').checked = false; clearSelection();
    };

    renderer.domElement.addEventListener('pointermove', event => {
      pointer.x = event.clientX / innerWidth * 2 - 1; pointer.y = -(event.clientY / innerHeight) * 2 + 1;
      raycaster.setFromCamera(pointer, camera);
      const hit = raycaster.intersectObjects([...meshByKey.values()].filter(mesh => mesh.visible), false)[0];
      hovered = hit?.object.userData.key || null;
      renderer.domElement.style.cursor = hovered ? 'pointer' : 'grab';
      const tip = document.getElementById('tooltip');
      if (hovered) { tip.style.display='block'; tip.style.left=`${event.clientX+13}px`; tip.style.top=`${event.clientY+13}px`; tip.textContent=hovered; }
      else tip.style.display='none';
    });
    renderer.domElement.addEventListener('click', () => hovered ? inspect(hovered) : clearSelection());
    addEventListener('keydown', event => {
      if (event.key === '/' && document.activeElement !== document.getElementById('query')) {
        event.preventDefault(); document.getElementById('query').focus();
      } else if (event.key === 'Escape') { document.getElementById('query').value=''; clearSelection(); updateAppearance(); }
      else if ((event.key === 'f' || event.key === 'F') && selected) frameNode(nodeByKey.get(selected));
      else if (event.key === ']' && document.activeElement?.tagName !== 'INPUT') goTour(tourIndex < 0 ? 0 : tourIndex + 1);
      else if (event.key === '[' && document.activeElement?.tagName !== 'INPUT') goTour(tourIndex < 0 ? 0 : tourIndex - 1);
    });
    addEventListener('resize', () => {
      camera.aspect = innerWidth/innerHeight; camera.updateProjectionMatrix(); renderer.setSize(innerWidth,innerHeight);
    });
    function animate() { requestAnimationFrame(animate); controls.update(); renderer.render(scene,camera); }
    updateAppearance();
    if (location.hash) {
      const linked = decodeURIComponent(location.hash.slice(1));
      if (nodeByKey.has(linked)) inspect(linked, true);
    }
    animate();
  </script>
</body>
</html>
'''
