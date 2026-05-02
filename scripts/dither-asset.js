#!/usr/bin/env node
/**
 * Pre-compute Atkinson dithering for an image asset.
 *
 * Usage:
 *   node scripts/dither-asset.js <input.jpg> <output.png> [scale]
 *
 * Defaults: scale = 2 (matches the homepage's data-dither-scale="2").
 *
 * Requires `sharp` as a dev dependency:
 *   npm install --save-dev sharp
 */
const sharp = require("sharp");
const path = require("path");

const NEIGHBORS = [
  [1, 0], [2, 0],
  [-1, 1], [0, 1], [1, 1],
  [0, 2],
];

// Rec. 601 luma — same as Sharp's `.toColorspace("b-w")` and what feels
// right for portraits. Match this in dither.js so the in-browser warp
// re-quantizes to the same surface as the precomputed PNG.
function toGrayscale(data, width, height, channels) {
  const out = new Float32Array(width * height);
  if (channels === 1) {
    for (let i = 0; i < out.length; i++) out[i] = data[i];
  } else {
    for (let i = 0, j = 0; i < data.length; i += channels, j++) {
      out[j] = 0.299 * data[i] + 0.587 * data[i + 1] + 0.114 * data[i + 2];
    }
  }
  return out;
}

function atkinson(buf, w, h) {
  for (let y = 0; y < h; y++) {
    for (let x = 0; x < w; x++) {
      const idx = y * w + x;
      const old = buf[idx];
      const v = old < 128 ? 0 : 255;
      buf[idx] = v;
      const err = (old - v) / 8;
      for (let n = 0; n < 6; n++) {
        const nx = x + NEIGHBORS[n][0];
        const ny = y + NEIGHBORS[n][1];
        if (nx >= 0 && nx < w && ny >= 0 && ny < h) {
          buf[ny * w + nx] += err;
        }
      }
    }
  }
}

async function main() {
  const [, , inPath, outPath, scaleArg] = process.argv;
  if (!inPath || !outPath) {
    console.error("usage: node scripts/dither-asset.js <input> <output> [scale]");
    process.exit(1);
  }
  const scale = Math.max(1, parseInt(scaleArg || "2", 10));

  const meta = await sharp(inPath).metadata();
  const w = Math.max(1, Math.round(meta.width / scale));
  const h = Math.max(1, Math.round(meta.height / scale));

  const { data, info } = await sharp(inPath)
    .resize(w, h, { kernel: "nearest" })
    .removeAlpha()
    .raw()
    .toBuffer({ resolveWithObject: true });

  const buf = toGrayscale(data, w, h, info.channels);
  atkinson(buf, w, h);

  // Pack into a 1-channel grayscale PNG. Each pixel is now exactly 0 or 255.
  const out = Buffer.alloc(w * h);
  for (let i = 0; i < buf.length; i++) {
    out[i] = buf[i] > 127 ? 255 : 0;
  }
  await sharp(out, { raw: { width: w, height: h, channels: 1 } })
    .png({ compressionLevel: 9, palette: true })
    .toFile(outPath);

  console.log(`wrote ${outPath} (${w}x${h}, dither scale ${scale})`);
}

main().catch((e) => {
  console.error(e);
  process.exit(1);
});
