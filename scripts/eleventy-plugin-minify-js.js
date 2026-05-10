// Minify JS files in the build output. Walks the output dir after Eleventy
// finishes writing, runs each .js file through terser, and rewrites it in
// place. Skipped during `eleventy --serve` so dev rebuilds stay fast.
const fs = require("fs");
const path = require("path");
const { minify } = require("terser");

async function collectJsFiles(dir, files = []) {
  const entries = await fs.promises.readdir(dir, { withFileTypes: true });
  for (const entry of entries) {
    const p = path.join(dir, entry.name);
    if (entry.isDirectory()) {
      await collectJsFiles(p, files);
    } else if (entry.isFile() && p.endsWith(".js")) {
      files.push(p);
    }
  }
  return files;
}

module.exports = function (eleventyConfig, options = {}) {
  const outputDir = options.outputDir || "_site";
  const terserOptions = options.terser || { compress: true, mangle: true };

  eleventyConfig.on("eleventy.after", async ({ runMode }) => {
    if (runMode === "serve" || runMode === "watch") return;

    const root = path.resolve(outputDir);
    if (!fs.existsSync(root)) return;

    const files = await collectJsFiles(root);
    if (!files.length) return;

    let beforeBytes = 0;
    let afterBytes = 0;
    for (const file of files) {
      const original = await fs.promises.readFile(file, "utf8");
      try {
        const result = await minify(original, terserOptions);
        if (typeof result.code === "string") {
          beforeBytes += Buffer.byteLength(original);
          afterBytes += Buffer.byteLength(result.code);
          await fs.promises.writeFile(file, result.code);
        }
      } catch (err) {
        const rel = path.relative(root, file);
        console.warn(`[minify-js] skipped ${rel}: ${err.message}`);
      }
    }

    const saved = beforeBytes - afterBytes;
    const pct = beforeBytes ? ((saved / beforeBytes) * 100).toFixed(1) : "0.0";
    console.log(
      `[minify-js] ${files.length} file(s): ${(beforeBytes / 1024).toFixed(1)} KB → ${(afterBytes / 1024).toFixed(1)} KB (-${pct}%)`
    );
  });
};
