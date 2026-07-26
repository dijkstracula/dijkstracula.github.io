// scripts/subset-math.js
//
// Produces a tiny subset of a math font containing only the glyphs that
// Computer Modern Serif and JetBrains Mono lack — currently the white curly
// brackets ⦃ ⦄ used for Hoare-triple notation in the Lean posts. Without this,
// the browser falls back per-glyph to some arbitrary system font that renders
// them far too small.
//
// The source is NewComputerModern Math (the modern successor to Computer
// Modern), chosen because it both contains U+2983/U+2984 *and* matches the body
// font. (Note: plain Latin Modern Math does NOT contain these codepoints.)
//
// The ~KB output is committed at
//   src/assets/fonts/math-brackets.woff2
// and referenced from a unicode-range @font-face in src/css/site.css. Because
// unicode-range only gates *whether* the file is fetched (not its size), we
// subset rather than shipping the full ~680 KB face for two glyphs.
//
// Regenerate:  npm run fonts:subset
//
// Source font: place a full math face containing the target glyphs at
//   scripts/fonts-src/NewCMMath-Book.woff2   (git-ignored; not committed)
// or pass a path:  node scripts/subset-math.js path/to/font.otf
// Canonical source: NewComputerModern on CTAN —
//   https://ctan.org/pkg/newcomputermodern
// (STIX Two Math, XITS Math, and Asana Math also contain these glyphs if you
//  want a different look — just drop one in and re-run.)
//
// To cover more glyphs later, add them to GLYPHS and re-run; the script prints
// the matching `unicode-range` line to paste into site.css so the two can't drift.

const fs = require("fs");
const path = require("path");

// Single source of truth for which glyphs to keep.
const GLYPHS = "⦃⦄"; // U+2983 LEFT / U+2984 RIGHT WHITE CURLY BRACKET

const SRC = process.argv[2]
  ? path.resolve(process.cwd(), process.argv[2])
  : path.resolve(__dirname, "fonts-src/NewCMMath-Book.woff2");

const OUT = path.resolve(__dirname, "../src/assets/fonts/math-brackets.woff2");

async function main() {
  if (!fs.existsSync(SRC)) {
    console.error(
      `Source font not found:\n  ${SRC}\n\n` +
        `Download a math face containing ${GLYPHS} and place it there, or pass a path:\n` +
        `  https://ctan.org/pkg/newcomputermodern  (NewCMMath-Book.otf)\n` +
        `  node scripts/subset-math.js path/to/font.otf\n`
    );
    process.exit(1);
  }

  // subset-font is ESM-only; dynamic import works from this CommonJS script.
  const subsetFont = (await import("subset-font")).default;

  const input = fs.readFileSync(SRC);
  const output = await subsetFont(input, GLYPHS, { targetFormat: "woff2" });

  // Guard against the silent failure that bit us with Latin Modern Math: if the
  // source lacks the glyphs, subset-font emits a notdef-only font and the fix
  // does nothing. A real 2-glyph subset is comfortably larger than that.
  if (output.length < 1200) {
    console.error(
      `Output is only ${output.length} bytes — the source font probably does\n` +
        `not contain ${GLYPHS}. Pick a font that does (NewCM / STIX / XITS / Asana).`
    );
    process.exit(1);
  }

  fs.mkdirSync(path.dirname(OUT), { recursive: true });
  fs.writeFileSync(OUT, output);

  const range = [...GLYPHS]
    .map((ch) => "U+" + ch.codePointAt(0).toString(16).toUpperCase())
    .join(", ");

  console.log(`Subset ${[...GLYPHS].length} glyph(s): ${GLYPHS}`);
  console.log(`  in : ${SRC} (${input.length.toLocaleString()} bytes)`);
  console.log(`  out: ${OUT} (${output.length.toLocaleString()} bytes)`);
  console.log(`\nMatching @font-face descriptor:\n  unicode-range: ${range};`);
}

main().catch((err) => {
  console.error(err);
  process.exit(1);
});
