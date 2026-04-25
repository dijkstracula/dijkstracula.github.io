// Atkinson dithering — applied to <img class="dither"> on page load.
//
// Two modes:
//   1. Default: one-shot dither, replaces img.src with the dithered data URL.
//   2. data-dither-interactive: replaces the <img> with a <canvas> and runs
//      an animation loop where cursor motion injects force into a 2D velocity
//      field; each frame the source image is warped by that field before
//      being re-dithered. The result reads like a viscous fluid pushing the
//      dither pattern around the cursor; the field decays back to zero so
//      the image "settles" after you stop moving.
//
// Atkinson recipe: each pixel is thresholded to black or white; 1/8 of the
// quantization error is distributed to each of six neighbors (right, +2-right,
// below-left, below, below-right, +2-below). 2/8 of the error is dropped,
// which preserves highlights and gives Atkinson its distinctive bright look.
(function () {
  const NEIGHBORS = [
    [1, 0], [2, 0],
    [-1, 1], [0, 1], [1, 1],
    [0, 2],
  ];

  function atkinson(buf, w, h) {
    for (let y = 0; y < h; y++) {
      for (let x = 0; x < w; x++) {
        const idx = y * w + x;
        const old = buf[idx];
        const v = old < 128 ? 0 : 255;
        buf[idx] = v;
        const err = (old - v) / 8;
        for (let n = 0; n < 6; n++) {
          const dx = NEIGHBORS[n][0], dy = NEIGHBORS[n][1];
          const nx = x + dx, ny = y + dy;
          if (nx >= 0 && nx < w && ny >= 0 && ny < h) {
            buf[ny * w + nx] += err;
          }
        }
      }
    }
  }

  function readGrayscale(ctx, w, h) {
    const data = ctx.getImageData(0, 0, w, h).data;
    const gray = new Float32Array(w * h);
    for (let i = 0, j = 0; i < data.length; i += 4, j++) {
      gray[j] = 0.2126 * data[i] + 0.7152 * data[i + 1] + 0.0722 * data[i + 2];
    }
    return gray;
  }

  function writeMonoToCanvas(ctx, buf, w, h) {
    const imgData = ctx.getImageData(0, 0, w, h);
    const data = imgData.data;
    for (let i = 0, j = 0; i < data.length; i += 4, j++) {
      const v = buf[j] > 127 ? 255 : 0;
      data[i] = data[i + 1] = data[i + 2] = v;
      data[i + 3] = 255;
    }
    ctx.putImageData(imgData, 0, 0);
  }

  // ----- One-shot dither (default) -------------------------------------
  function ditherStatic(img) {
    if (img.dataset.dithered === "true") return;
    const scale = Math.max(1, parseInt(img.dataset.ditherScale || "1", 10));
    const w = Math.max(1, Math.round(img.naturalWidth / scale));
    const h = Math.max(1, Math.round(img.naturalHeight / scale));
    const canvas = document.createElement("canvas");
    canvas.width = w;
    canvas.height = h;
    const ctx = canvas.getContext("2d", { willReadFrequently: true });
    ctx.imageSmoothingEnabled = false;
    ctx.drawImage(img, 0, 0, w, h);
    const gray = readGrayscale(ctx, w, h);
    atkinson(gray, w, h);
    writeMonoToCanvas(ctx, gray, w, h);
    img.src = canvas.toDataURL("image/png");
    img.dataset.dithered = "true";
    img.style.imageRendering = "pixelated";
  }

  // ----- Interactive (cursor-driven warp + redither) -------------------
  function ditherInteractive(img) {
    if (img.dataset.dithered === "true") return;

    // Tunables — exposed as data-dither-* attributes so they can be tweaked
    // from markup without touching JS.
    const scale  = Math.max(1, parseInt(img.dataset.ditherScale || "2", 10));
    const decay  = parseFloat(img.dataset.ditherDecay  || "0.86");
    const force  = parseFloat(img.dataset.ditherForce  || "0.45");
    const radius = parseFloat(img.dataset.ditherRadius || "26");

    // Build an offscreen canvas at the dither resolution. We replace the <img>
    // with a <canvas> sized to the original so CSS layout is unchanged.
    const w = Math.max(1, Math.round(img.naturalWidth / scale));
    const h = Math.max(1, Math.round(img.naturalHeight / scale));

    const src = document.createElement("canvas");
    src.width = w; src.height = h;
    const sctx = src.getContext("2d", { willReadFrequently: true });
    sctx.imageSmoothingEnabled = false;
    sctx.drawImage(img, 0, 0, w, h);
    const grayBase = readGrayscale(sctx, w, h);

    // Display canvas — the one users see and that receives mouse events.
    const view = document.createElement("canvas");
    view.width = w; view.height = h;
    view.className = img.className;
    view.style.cssText = img.style.cssText;
    view.style.width  = "100%";
    view.style.height = "100%";
    view.style.objectFit = "cover";
    view.style.imageRendering = "pixelated";
    view.style.display = "block";
    img.parentNode.replaceChild(view, img);
    const vctx = view.getContext("2d");

    // Per-pixel velocity field — units are source pixels per frame.
    const vx = new Float32Array(w * h);
    const vy = new Float32Array(w * h);
    const work = new Float32Array(w * h);

    // Cursor state.
    let mx = -1, my = -1, pmx = -1, pmy = -1, mIn = false;

    function imgCoords(e) {
      const r = view.getBoundingClientRect();
      return [
        ((e.clientX - r.left) * w) / r.width,
        ((e.clientY - r.top)  * h) / r.height,
      ];
    }
    view.addEventListener("pointerenter", (e) => {
      mIn = true;
      [mx, my] = imgCoords(e);
      pmx = mx; pmy = my;
    });
    view.addEventListener("pointerleave", () => { mIn = false; });
    view.addEventListener("pointermove", (e) => {
      pmx = mx; pmy = my;
      [mx, my] = imgCoords(e);
    });

    const r2max = radius * radius;
    const sigma = (radius * radius) / 2.5;

    function frame() {
      // Decay the velocity field. Tiny values get clamped to 0 so we can
      // bail early once everything has settled.
      let active = mIn;
      for (let i = 0; i < vx.length; i++) {
        vx[i] *= decay; vy[i] *= decay;
        if (Math.abs(vx[i]) < 0.01) vx[i] = 0;
        if (Math.abs(vy[i]) < 0.01) vy[i] = 0;
        if (vx[i] !== 0 || vy[i] !== 0) active = true;
      }

      // Inject cursor force — Gaussian-falloff stamp of the cursor's
      // velocity into the field around the cursor's current position.
      if (mIn) {
        const dx = mx - pmx, dy = my - pmy;
        const cx = Math.round(mx), cy = Math.round(my);
        for (let oy = -radius; oy <= radius; oy++) {
          for (let ox = -radius; ox <= radius; ox++) {
            const r2 = ox * ox + oy * oy;
            if (r2 > r2max) continue;
            const px = cx + ox, py = cy + oy;
            if (px < 0 || px >= w || py < 0 || py >= h) continue;
            const f = Math.exp(-r2 / sigma) * force;
            const i = py * w + px;
            vx[i] += dx * f;
            vy[i] += dy * f;
          }
        }
      }

      // Skip the heavy work entirely when there's nothing to do.
      if (!active) {
        requestAnimationFrame(frame);
        return;
      }

      // Sample warped grayscale: for each output pixel, look up the source
      // at (x - vx, y - vy). Negative warp = pixels appear "pulled" toward
      // the cursor's recent direction of travel.
      for (let y = 0; y < h; y++) {
        for (let x = 0; x < w; x++) {
          const i = y * w + x;
          let sx = x - vx[i] | 0;
          let sy = y - vy[i] | 0;
          if (sx < 0) sx = 0; else if (sx >= w) sx = w - 1;
          if (sy < 0) sy = 0; else if (sy >= h) sy = h - 1;
          work[i] = grayBase[sy * w + sx];
        }
      }

      atkinson(work, w, h);
      writeMonoToCanvas(vctx, work, w, h);
      requestAnimationFrame(frame);
    }

    img.dataset.dithered = "true";

    // Paint the resting state once before the loop kicks in, so the canvas
    // doesn't flash blank on first paint.
    work.set(grayBase);
    atkinson(work, w, h);
    writeMonoToCanvas(vctx, work, w, h);
    requestAnimationFrame(frame);
  }

  // ----- Bootstrap ----------------------------------------------------
  function ditherImage(img) {
    if (img.dataset.ditherInteractive !== undefined) {
      ditherInteractive(img);
    } else {
      ditherStatic(img);
    }
  }

  function process() {
    document.querySelectorAll("img.dither").forEach((img) => {
      if (img.complete && img.naturalWidth > 0) {
        ditherImage(img);
      } else {
        img.addEventListener("load", () => ditherImage(img), { once: true });
      }
    });
  }

  if (document.readyState === "loading") {
    document.addEventListener("DOMContentLoaded", process);
  } else {
    process();
  }
})();
