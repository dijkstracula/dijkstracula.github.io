// FRP widget runtime — combinators, graph substrate, and timing renderer.
//
// Signals are sample-based: each node's `compute(t, ctx)` returns its value
// at time `t`. `ctx.at(name, t)` reads other nodes' values from a shared
// cache managed by `evaluate(N)`, so stateful combinators like `scan` don't
// re-walk history on each sample.
(function () {
  // Wave step duration — shared between renderGraph (animation timing)
  // and renderTiming (auto-computed playSpeed).
  const ANIM_MS = 400;

  function graph() {
    const nodes = {};
    const order = [];

    function add(name, deps, compute, kind, meta) {
      if (nodes[name]) throw new Error(`FRP: duplicate node "${name}"`);
      nodes[name] = { name, deps, compute, kind, meta: meta || {} };
      order.push(name);
      return { name };
    }

    return {
      nodes, order,

      // Sources: functions of `t` only, no deps.
      sig(name, fn, meta)   { return add(name, [], (t) => fn(t), 'source', meta); },
      const(name, v, meta)  { return add(name, [], () => v,      'source', meta); },
      clock(name, meta)     { return add(name, [], (t) => t,     'source', meta); },

      // Pointwise combinators.
      map(name, f, a, meta) {
        return add(name, [a.name],
                   (t, ctx) => f(ctx.at(a.name, t)), 'derived', meta);
      },
      map2(name, f, a, b, meta) {
        return add(name, [a.name, b.name],
                   (t, ctx) => f(ctx.at(a.name, t), ctx.at(b.name, t)),
                   'derived', meta);
      },
      // Variadic: f is called with an array of dep values at the current
      // tick. Mirrors `Signal (List α)` via `List.mapA id sigs` in the
      // Lean prose.
      mapN(name, f, sigs, meta) {
        const depNames = sigs.map(s => s.name);
        return add(name, depNames,
                   (t, ctx) => f(depNames.map(d => ctx.at(d, t))),
                   'derived', meta);
      },

      // Time-shifting.
      advance(name, a, k, meta) {
        return add(name, [a.name],
                   (t, ctx) => ctx.at(a.name, t + k), 'derived', meta);
      },
      delay(name, a, k, meta) {
        // Lean uses Nat subtraction (truncates at 0). Mirror that.
        return add(name, [a.name],
                   (t, ctx) => ctx.at(a.name, Math.max(0, t - k)),
                   'derived', meta);
      },

      // Stateful: folds `step` over its own history. Self-references via
      // ctx.at(name, t-1); the shared cache guarantees O(N) total.
      scan(name, step, init, meta) {
        return add(name, [], (t, ctx) => {
          if (t <= 0) return init;
          return step(ctx.at(name, t - 1));
        }, 'derived', Object.assign({ stateful: true }, meta || {}));
      },

      // Events: `Time → Option α`, encoded as `null | value`. Note that any
      // signal value being null would collide with the "no fire" sentinel,
      // so signals must not produce null; use undefined-behavior only for
      // event-typed nodes.
      event(name, fn, meta) {
        return add(name, [], (t) => fn(t), 'source',
                   Object.assign({ type: 'event' }, meta || {}));
      },
      // Convenience: fires with `true` (or the given `value`) at each tick
      // in `times`. Interactive: cells become clickable in the timing view;
      // clicks toggle the fire at that tick.
      eventAt(name, times, value, meta) {
        const set = new Set(times);
        const v = value === undefined ? true : value;
        return add(name, [], (t) => set.has(t) ? v : null, 'source',
          Object.assign({
            type: 'event',
            interactive: true,
            toggleAt: (t) => {
              if (set.has(t)) set.delete(t);
              else set.add(t);
            },
          }, meta || {}));
      },

      // Event.merge: e1 wins ties (mirrors <|> / orElse in Lean).
      merge(name, e1, e2, meta) {
        return add(name, [e1.name, e2.name], (t, ctx) => {
          const v1 = ctx.at(e1.name, t);
          return v1 !== null && v1 !== undefined ? v1 : ctx.at(e2.name, t);
        }, 'derived', Object.assign({ type: 'event' }, meta || {}));
      },

      // Event.latch: signal that remembers the latest fire, `init` before
      // the first fire.
      latch(name, init, e, meta) {
        return add(name, [e.name], (t, ctx) => {
          const ev = ctx.at(e.name, t);
          if (ev !== null && ev !== undefined) return ev;
          if (t <= 0) return init;
          return ctx.at(name, t - 1);
        }, 'derived', Object.assign({ stateful: true }, meta || {}));
      },

      // accumulate init onNone onSome ev — event-driven stateful signal.
      // Convention: at t=0 the signal shows `init` unconditionally
      // (ev@0 is not consulted). For t>0 the value is switch(t)(prev),
      // dispatching on ev@t. This matches the Lean pedagogy where init
      // is "the value at t=0" and events transition the state from
      // t-1 to t. Event sources that feed only into accumulate can set
      // `meta.noT0Click: true` so the timing view doesn't render a
      // clickable t=0 cell that has no observable effect.
      accumulate(name, init, onNone, onSome, e, meta) {
        return add(name, [e.name], (t, ctx) => {
          if (t <= 0) return init;
          const prev = ctx.at(name, t - 1);
          const ev = ctx.at(e.name, t);
          if (ev === null || ev === undefined) return onNone(prev);
          return onSome(ev, prev);
        }, 'derived', Object.assign({ stateful: true }, meta || {}));
      },

      evaluate(N) {
        const values = {};
        for (const name of order) values[name] = new Array(N);
        const ctx = {
          at(name, t) {
            const row = values[name];
            if (row && t >= 0 && t < N && row[t] !== undefined) return row[t];
            // Lookahead beyond [0, N) — recompute without caching. Fine for
            // sources; derived-with-lookahead is rare and still terminates.
            return nodes[name].compute(t, ctx);
          },
        };
        for (const name of order) {
          for (let t = 0; t < N; t++) {
            values[name][t] = nodes[name].compute(t, ctx);
          }
        }
        return values;
      },
    };
  }

  function defaultFormat(v, name, t, node) {
    const isEvent = node && node.meta && node.meta.type === 'event';
    if (isEvent) {
      if (v === null || v === undefined) return '';
      if (v === true) return '●';
      return '● ' + String(v);
    }
    if (v === null || v === undefined) return '·';
    if (typeof v === 'number') {
      return Number.isInteger(v) ? String(v) : v.toFixed(2);
    }
    if (typeof v === 'boolean') return v ? '✓' : '·';
    return String(v);
  }

  function renderTiming(container, g, opts) {
    opts = opts || {};
    const ticks  = opts.ticks  || 16;
    const format = opts.format || defaultFormat;
    const hasControls = !!opts.controls;
    // Auto-compute play speed from graph depth so a wave finishes within
    // one tick interval. Widget can still override via opts.playSpeed.
    const maxDepth = Math.max(0, ...Object.values(computeRanks(g)));
    const playSpeed = opts.playSpeed || Math.max(400, maxDepth * ANIM_MS);

    // Focus is active when either a subscriber is listening OR the widget
    // has controls of its own. Otherwise no column is highlighted and
    // header cells aren't clickable.
    let focus = hasControls ? 0 : null;
    const subscribers = [];
    function notify() { for (const cb of subscribers) cb(focus); }

    container.classList.add('frp-widget');

    let gridEl = null;
    function render() {
      const values = g.evaluate(ticks);
      const grid = document.createElement('div');
      grid.className = 'frp-timing';
      grid.style.setProperty('--frp-cols', ticks);

      const focusable = subscribers.length > 0 || hasControls;

      const corner = document.createElement('div');
      corner.className = 'frp-corner';
      grid.appendChild(corner);
      for (let t = 0; t < ticks; t++) {
        const th = document.createElement('div');
        let cls = 'frp-th';
        if (focusable) cls += ' frp-th-focusable';
        if (t === focus) cls += ' frp-focused';
        th.className = cls;
        th.textContent = t;
        if (focusable) {
          const tickAt = t;
          th.addEventListener('click', () => {
            focus = tickAt;
            render();
            notify();
          });
        }
        grid.appendChild(th);
      }

      for (const name of g.order) {
        const node = g.nodes[name];
        const isEvent = node.meta.type === 'event';
        const interactive = isEvent && node.meta.interactive && node.meta.toggleAt;

        const label = document.createElement('div');
        label.className = 'frp-label' + (isEvent ? ' frp-label-event' : '');
        label.textContent = name;
        grid.appendChild(label);

        const row = values[name];
        for (let t = 0; t < ticks; t++) {
          const cell = document.createElement('div');
          // Event sources feeding only into Convention-A `accumulate` can
          // opt out of the t=0 click affordance via meta.noT0Click, since
          // toggling ev@0 there has no observable effect.
          const cellDisabled = interactive && node.meta.noT0Click && t === 0;
          const cellInteractive = interactive && !cellDisabled;
          let cls = 'frp-cell';
          if (isEvent) cls += ' frp-cell-event';
          if (cellInteractive) cls += ' frp-cell-interactive';
          if (focus !== null && t === focus) cls += ' frp-focused';
          const formatted = format(row[t], name, t, node);
          if (formatted && typeof formatted === 'object') {
            cell.textContent = formatted.text != null ? formatted.text : '';
            if (formatted.className) cls += ' ' + formatted.className;
          } else {
            cell.textContent = formatted;
          }
          cell.className = cls;
          if (cellInteractive) {
            const tickAt = t;
            cell.addEventListener('click', () => {
              node.meta.toggleAt(tickAt);
              if (focus !== null) {
                focus = tickAt;
                bumpPlayTimer();
              }
              render();
              notify();
            });
          }
          grid.appendChild(cell);
        }
      }

      if (gridEl) gridEl.replaceWith(grid);
      else        container.appendChild(grid);
      gridEl = grid;
    }

    render();

    // VCR-style play/pause/reset bar, opt-in via opts.controls.
    let playing = false;
    let playTimer = null;
    let playBtn = null;
    function playStep() {
      focus = focus == null ? 0 : (focus + 1) % ticks;
      render();
      notify();
    }
    function play() {
      if (playing) return;
      playing = true;
      if (playBtn) playBtn.textContent = '⏸';
      playTimer = setInterval(playStep, playSpeed);
    }
    function pause() {
      if (!playing) return;
      playing = false;
      if (playBtn) playBtn.textContent = '▶';
      clearInterval(playTimer);
      playTimer = null;
    }
    function reset() { pause(); focus = 0; render(); notify(); }
    // Reset the play interval so the next tick fires `playSpeed` from
    // now — used after an event-toggle jump so the toggled tick gets a
    // full interval on screen instead of being cut short.
    function bumpPlayTimer() {
      if (!playing) return;
      clearInterval(playTimer);
      playTimer = setInterval(playStep, playSpeed);
    }

    if (hasControls) {
      const controls = document.createElement('div');
      controls.className = 'frp-controls';
      playBtn = document.createElement('button');
      playBtn.className = 'frp-ctrl-btn';
      playBtn.type = 'button';
      playBtn.textContent = '▶';
      playBtn.title = 'Play';
      playBtn.addEventListener('click', () => playing ? pause() : play());
      controls.appendChild(playBtn);
      const resetBtn = document.createElement('button');
      resetBtn.className = 'frp-ctrl-btn';
      resetBtn.type = 'button';
      resetBtn.textContent = '⏮';
      resetBtn.title = 'Reset to t=0';
      resetBtn.addEventListener('click', reset);
      controls.appendChild(resetBtn);
      container.appendChild(controls);
    }

    return {
      setTick(t) { focus = t; render(); notify(); },
      play, pause, reset,
      subscribe(cb) {
        const wasEmpty = subscribers.length === 0;
        subscribers.push(cb);
        if (wasEmpty && focus === null) {
          focus = opts.initialTick != null ? opts.initialTick : 0;
          render();
        }
        cb(focus);
      },
    };
  }

  const STYLES = `
    .frp-widget {
      font-family: 'JetBrains Mono', monospace;
      font-size: 0.85em;
      margin: 1.5em 0;
      overflow-x: auto;
      border: 1px solid var(--rule);
      background: var(--paper);
    }
    .frp-timing {
      display: grid;
      grid-template-columns: auto repeat(var(--frp-cols), minmax(3ch, 1fr));
      width: max-content;
      min-width: 100%;
    }
    .frp-corner, .frp-th, .frp-label, .frp-cell {
      padding: 0.25em 0.5em;
      border-right: 1px solid var(--rule);
      border-bottom: 1px solid var(--rule);
      text-align: center;
      background: var(--paper);
    }
    .frp-th    { color: var(--mute); font-size: 0.85em; }
    .frp-label { text-align: right; color: var(--ink); font-weight: 500; }
    .frp-cell  { color: var(--ink); }
    .frp-corner, .frp-th, .frp-label { background: var(--paper-2); }
    .frp-cell-event  { color: var(--accent); font-weight: 600; }
    .frp-label-event { font-style: italic; }
    .frp-cell-interactive {
      cursor: pointer;
      user-select: none;
    }
    .frp-cell-interactive:hover {
      background: var(--paper-2);
      box-shadow: inset 0 0 0 1px var(--accent);
    }
    .frp-th-focusable { cursor: pointer; }
    .frp-th-focusable:hover:not(.frp-focused) {
      background: var(--paper);
    }
    .frp-controls {
      display: flex;
      gap: 0.4em;
      padding: 0.4em 0.5em;
      border-top: 1px solid var(--rule);
      background: var(--paper-2);
    }
    .frp-ctrl-btn {
      padding: 0.15em 0.6em;
      border: 1px solid var(--rule);
      background: var(--paper);
      color: var(--ink);
      font-family: 'JetBrains Mono', monospace;
      font-size: 0.9em;
      line-height: 1.4;
      cursor: pointer;
    }
    .frp-ctrl-btn:hover {
      border-color: var(--accent);
      color: var(--accent);
    }
    .frp-focused {
      background: var(--paper-2);
      box-shadow: inset 0 -2px 0 var(--accent);
    }
    .frp-corner, .frp-label {
      position: sticky;
      left: 0;
      z-index: 1;
      border-right: 1px solid var(--rule);
    }
    @media (max-width: 600px) {
      .frp-widget { font-size: 0.75em; }
      .frp-corner, .frp-th, .frp-label, .frp-cell {
        padding: 0.2em 0.35em;
      }
    }

    /* Graph view — pure SVG. */
    .frp-graph-svg {
      display: block;
      margin: 0 auto;
      font-family: 'JetBrains Mono', monospace;
      font-size: 13px;
    }
    .frp-gnode rect       { fill: var(--paper);  stroke: var(--rule);  stroke-width: 1; }
    .frp-gnode text       { fill: var(--ink); }
    .frp-gnode-event rect { stroke: var(--accent); }
    .frp-gnode-event text { fill: var(--accent); font-style: italic; }
    .frp-gedge            { fill: none; stroke: var(--mute); stroke-width: 1.5; }
    .frp-gbadge-c         { fill: var(--paper); stroke: var(--accent); stroke-width: 1; }
    .frp-gbadge-t         { fill: var(--accent); font-size: 12px; }
    .frp-gnode-value      { fill: var(--ink-2); font-size: 12px; font-weight: 600; }
    .frp-gnode-event .frp-gnode-value { fill: var(--accent); }
    .frp-gparticle        { fill: var(--accent); }
    .frp-arrow            { fill: var(--mute); }
  `;
  if (!document.getElementById('frp-styles')) {
    const style = document.createElement('style');
    style.id = 'frp-styles';
    style.textContent = STYLES;
    document.head.appendChild(style);
  }

  // Topological rank = length of longest dependency chain from a source.
  function computeRanks(g) {
    const ranks = {};
    function rank(name) {
      if (name in ranks) return ranks[name];
      const deps = g.nodes[name].deps;
      const r = deps.length === 0 ? 0 : Math.max(...deps.map(rank)) + 1;
      ranks[name] = r;
      return r;
    }
    for (const name of g.order) rank(name);
    return ranks;
  }

  // Unique marker id per graph so multiple widgets on a page don't clash.
  let __graphN = 0;

  function renderGraph(container, g, opts) {
    opts = opts || {};
    const isSpatial = opts.layout === 'spatial';
    // Depth from any source — used for wave-staggered animation, so
    // rank-2 edges fire after rank-1 edges have started.
    const depths = computeRanks(g);
    const markerId = `frp-arrow-${__graphN++}`;

    // Layout constants (SVG user units = px, no viewBox scaling).
    const CELL_W = opts.cellWidth  || 130;
    const CELL_H = opts.cellHeight || 84;
    const NODE_H = 30;
    const VAL_GAP = 14;
    const PAD    = 18;
    const CH_W   = 8.2; // approx monospace char width at 13px

    const pos = {};
    let width, height;

    if (isSpatial) {
      // Explicit {row, col} in each node's meta.
      let maxRow = 0, maxCol = 0;
      for (const name of g.order) {
        const m = g.nodes[name].meta;
        maxRow = Math.max(maxRow, m.row || 0);
        maxCol = Math.max(maxCol, m.col || 0);
      }
      width  = (maxCol + 1) * CELL_W + PAD * 2;
      height = (maxRow + 1) * CELL_H + PAD * 2;
      for (const name of g.order) {
        const m = g.nodes[name].meta;
        const row = m.row || 0, col = m.col || 0;
        const cx = PAD + col * CELL_W + CELL_W / 2;
        const cy = PAD + row * CELL_H + CELL_H / 2;
        const w  = Math.max(64, name.length * CH_W + 20);
        pos[name] = { cx, cy, x: cx - w/2, y: cy - NODE_H/2, w, h: NODE_H };
      }
    } else {
      // Topological rank + barycenter reorder (existing behavior).
      const ranks = computeRanks(g);
      const byRank = [];
      for (const name of g.order) {
        const r = ranks[name];
        (byRank[r] = byRank[r] || []).push(name);
      }
      const colOf = {};
      byRank.forEach(names => names.forEach((n, c) => { colOf[n] = c; }));
      for (let r = 1; r < byRank.length; r++) {
        const row = byRank[r];
        const scored = row.map((name, i) => {
          const deps = g.nodes[name].deps;
          const b = deps.length === 0
            ? colOf[name]
            : deps.reduce((s, d) => s + colOf[d], 0) / deps.length;
          return { name, b, orig: i };
        });
        scored.sort((a, b) => a.b - b.b || a.orig - b.orig);
        byRank[r] = scored.map(x => x.name);
        byRank[r].forEach((n, c) => { colOf[n] = c; });
      }
      const numRanks = byRank.length;
      const maxCols  = Math.max(...byRank.map(r => r.length));
      width  = maxCols  * CELL_W + PAD * 2;
      height = numRanks * CELL_H + PAD * 2;
      byRank.forEach((names, row) => {
        const rowStart = PAD + (maxCols - names.length) * CELL_W / 2;
        names.forEach((name, col) => {
          const cx = rowStart + col * CELL_W + CELL_W / 2;
          const cy = PAD + row * CELL_H + CELL_H / 2;
          const w  = Math.max(64, name.length * CH_W + 20);
          pos[name] = { cx, cy, x: cx - w/2, y: cy - NODE_H/2, w, h: NODE_H };
        });
      });
    }

    container.classList.add('frp-widget');
    const SVGNS = 'http://www.w3.org/2000/svg';
    const svg   = document.createElementNS(SVGNS, 'svg');
    svg.setAttribute('class', 'frp-graph-svg');
    svg.setAttribute('width',  width);
    svg.setAttribute('height', height);

    // Arrow marker for directed edges.
    const defs = document.createElementNS(SVGNS, 'defs');
    const marker = document.createElementNS(SVGNS, 'marker');
    marker.setAttribute('id', markerId);
    marker.setAttribute('viewBox', '0 0 10 10');
    marker.setAttribute('refX', '10');
    marker.setAttribute('refY', '5');
    marker.setAttribute('markerWidth', '6');
    marker.setAttribute('markerHeight', '6');
    marker.setAttribute('orient', 'auto');
    const markerPath = document.createElementNS(SVGNS, 'path');
    markerPath.setAttribute('d', 'M0,0 L10,5 L0,10 Z');
    markerPath.setAttribute('class', 'frp-arrow');
    marker.appendChild(markerPath);
    defs.appendChild(marker);
    svg.appendChild(defs);

    // Compute where a line from (sx, sy) toward the center (dx, dy) enters
    // the destination rect. `inset` pushes the point outward along the
    // source-to-dest vector so the arrow head sits just outside the border.
    function entryPoint(sx, sy, dx, dy, w, h, inset) {
      const ex = sx - dx, ey = sy - dy;
      const absEx = Math.abs(ex), absEy = Math.abs(ey);
      const tx = absEx > 0 ? (w / 2) / absEx : Infinity;
      const ty = absEy > 0 ? (h / 2) / absEy : Infinity;
      const t = Math.min(tx, ty);
      const bx = dx + t * ex, by = dy + t * ey;
      const len = Math.hypot(ex, ey) || 1;
      return { x: bx + (ex / len) * inset, y: by + (ey / len) * inset };
    }

    // Edges first so nodes render on top. Each edge also gets a particle
    // that animates along its path when the source value changes.
    const animations = [];
    for (const name of g.order) {
      const dp = pos[name];
      for (const dep of g.nodes[name].deps) {
        const sp = pos[dep];
        let pathD;
        if (isSpatial) {
          // Straight line from source boundary to just-outside-dest boundary
          // so the arrow head sits in the gap between nodes.
          const s = entryPoint(dp.cx, dp.cy, sp.cx, sp.cy, sp.w, sp.h, 0);
          const d = entryPoint(sp.cx, sp.cy, dp.cx, dp.cy, dp.w, dp.h, 4);
          pathD = `M${s.x},${s.y} L${d.x},${d.y}`;
        } else {
          // Bezier from parent bottom to just above child top.
          const x1 = sp.cx, y1 = sp.y + sp.h;
          const x2 = dp.cx, y2 = dp.y - 4;
          const midY = (y1 + y2) / 2;
          pathD = `M${x1},${y1} C${x1},${midY} ${x2},${midY} ${x2},${y2}`;
        }

        const path = document.createElementNS(SVGNS, 'path');
        path.setAttribute('d', pathD);
        path.setAttribute('class', 'frp-gedge');
        path.setAttribute('marker-end', `url(#${markerId})`);
        svg.appendChild(path);

        const particle = document.createElementNS(SVGNS, 'circle');
        particle.setAttribute('r', 5);
        particle.setAttribute('class', 'frp-gparticle');
        particle.setAttribute('opacity', 0);
        svg.appendChild(particle);

        animations.push({
          path, particle,
          depName: dep,
          destDepth: depths[name] || 1,
        });
      }
    }

    let animGen = 0;

    function writeValue(name, v, t) {
      const formatted = format(v, name, t, g.nodes[name]);
      const text = typeof formatted === 'string'
        ? formatted
        : (formatted && formatted.text) || '';
      valueEls[name].textContent = text;
    }

    // Wave-driven: each node's value updates when the wave arrives at it,
    // which is `depths[name] * ANIM_MS` after the tick boundary. An edge
    // from a source at depth `du` fires from `du * ANIM_MS` to
    // `(du+1) * ANIM_MS` — so the destination sees its value update at
    // exactly the moment the incoming particle reaches it.
    function fireAnimations(oldT, newT, values) {
      // Generation was already bumped by setTick; capture it here so all
      // scheduled callbacks close over the same value.
      const gen = animGen;

      // Value updates at each node's arrival time. Depth-0 nodes update
      // synchronously so the tick boundary paints in the same frame.
      for (const name of g.order) {
        const d = depths[name] || 0;
        if (d === 0) {
          writeValue(name, values[name][newT], newT);
        } else {
          setTimeout(() => {
            if (gen !== animGen) return;
            writeValue(name, values[name][newT], newT);
          }, d * ANIM_MS);
        }
      }

      // Edge animations, starting when the source has updated.
      for (const { path, particle, depName } of animations) {
        if (Object.is(values[depName][oldT], values[depName][newT])) continue;
        const startDelay = (depths[depName] || 0) * ANIM_MS;
        setTimeout(() => {
          if (gen !== animGen) return;
          const total = path.getTotalLength();
          const startTime = performance.now();
          const step = (now) => {
            if (gen !== animGen) return;
            const t = Math.min(1, (now - startTime) / ANIM_MS);
            const p = path.getPointAtLength(t * total);
            particle.setAttribute('cx', p.x);
            particle.setAttribute('cy', p.y);
            const op = t < 0.15 ? t / 0.15
                     : t > 0.85 ? (1 - t) / 0.15
                     : 1;
            particle.setAttribute('opacity', op);
            if (t < 1) requestAnimationFrame(step);
            else       particle.setAttribute('opacity', 0);
          };
          requestAnimationFrame(step);
        }, startDelay);
      }
    }

    // Nodes.
    const valueEls = {};
    for (const name of g.order) {
      const p    = pos[name];
      const node = g.nodes[name];
      const gEl  = document.createElementNS(SVGNS, 'g');
      let cls = 'frp-gnode';
      if (node.meta.type === 'event') cls += ' frp-gnode-event';
      if (node.meta.stateful)         cls += ' frp-gnode-stateful';
      gEl.setAttribute('class', cls);

      const rect = document.createElementNS(SVGNS, 'rect');
      rect.setAttribute('x', p.x);
      rect.setAttribute('y', p.y);
      rect.setAttribute('width',  p.w);
      rect.setAttribute('height', p.h);
      if (node.meta.type === 'event') {
        rect.setAttribute('rx', p.h / 2);
        rect.setAttribute('ry', p.h / 2);
      }
      gEl.appendChild(rect);

      const text = document.createElementNS(SVGNS, 'text');
      text.setAttribute('x', p.cx);
      text.setAttribute('y', p.cy);
      text.setAttribute('text-anchor', 'middle');
      text.setAttribute('dominant-baseline', 'central');
      text.textContent = name;
      gEl.appendChild(text);

      // Value badge for the currently focused tick, rendered below the box.
      const valEl = document.createElementNS(SVGNS, 'text');
      valEl.setAttribute('x', p.cx);
      valEl.setAttribute('y', p.y + p.h + VAL_GAP);
      valEl.setAttribute('text-anchor', 'middle');
      valEl.setAttribute('dominant-baseline', 'central');
      valEl.setAttribute('class', 'frp-gnode-value');
      gEl.appendChild(valEl);
      valueEls[name] = valEl;

      // Stateful self-reference badge.
      if (node.meta.stateful) {
        const bx = p.x + p.w - 4, by = p.y + 4;
        const bc = document.createElementNS(SVGNS, 'circle');
        bc.setAttribute('cx', bx);
        bc.setAttribute('cy', by);
        bc.setAttribute('r', 8);
        bc.setAttribute('class', 'frp-gbadge-c');
        gEl.appendChild(bc);
        const bt = document.createElementNS(SVGNS, 'text');
        bt.setAttribute('x', bx);
        bt.setAttribute('y', by);
        bt.setAttribute('text-anchor', 'middle');
        bt.setAttribute('dominant-baseline', 'central');
        bt.setAttribute('class', 'frp-gbadge-t');
        bt.textContent = '↻';
        gEl.appendChild(bt);
      }

      svg.appendChild(gEl);
    }

    container.appendChild(svg);

    const ticks  = opts.ticks  || 16;
    const format = opts.format || defaultFormat;

    let lastTick = null;
    function setTick(t) {
      const values = g.evaluate(ticks);
      // Cancel any in-flight wave: bump generation so pending setTimeouts
      // and RAF callbacks bail, and clear residual particle opacity from
      // an animation that was mid-flight when this call arrived.
      animGen++;
      for (const { particle } of animations) {
        particle.setAttribute('opacity', 0);
      }
      if (lastTick === null || lastTick === t) {
        // Initial render (or same tick): snap all values immediately.
        for (const name of g.order) writeValue(name, values[name][t], t);
      } else {
        // A previous wave may have been canceled, leaving deeper nodes
        // still showing pre-lastTick values. Snap everything to
        // lastTick's state before launching the new wave.
        for (const name of g.order) {
          if ((depths[name] || 0) > 0) {
            writeValue(name, values[name][lastTick], lastTick);
          }
        }
        fireAnimations(lastTick, t, values);
      }
      lastTick = t;
    }

    setTick(opts.initialTick != null ? opts.initialTick : 0);
    return { setTick };
  }

  window.FRP = { graph, renderTiming, renderGraph, defaultFormat, computeRanks };
})();
