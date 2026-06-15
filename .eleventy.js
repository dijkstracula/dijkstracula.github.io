const syntaxHighlight = require("@11ty/eleventy-plugin-syntaxhighlight");
const rssPlugin = require("@11ty/eleventy-plugin-rss");
const minifyJsPlugin = require("./scripts/eleventy-plugin-minify-js");
const markdownIt = require("markdown-it");
const markdownItFootnote = require("markdown-it-footnote");
const markdownItContainer = require("markdown-it-container");
const Prism = require("prismjs");

global.Prism = Prism;
require('./src/js/prism-lean.js');
require('./src/js/prism-dafny.js');

module.exports = function(eleventyConfig) {
  // Configure markdown-it with footnote support and callouts
  const md = markdownIt({
    html: true,
    linkify: false,
    typographer: true
  });

  md.use(markdownItFootnote);

  // Add callout containers (inline)
  const calloutTypes = ['note', 'warning', 'tip', 'info', 'danger'];
  calloutTypes.forEach(type => {
    md.use(markdownItContainer, type, {
      render: function (tokens, idx) {
        if (tokens[idx].nesting === 1) {
          // opening tag
          return `<div class="callout callout-${type}">\n`;
        } else {
          // closing tag
          return '</div>\n';
        }
      }
    });
  });

  // Add margin callout containers (appear on the right)
  const marginCalloutTypes = ['margin-note', 'margin-warning', 'margin-tip', 'margin-info', 'margin-danger'];
  marginCalloutTypes.forEach(type => {
    md.use(markdownItContainer, type, {
      render: function (tokens, idx) {
        const baseType = type.replace('margin-', '');
        if (tokens[idx].nesting === 1) {
          // opening tag
          return `<div class="callout callout-margin callout-${baseType}">\n`;
        } else {
          // closing tag
          return '</div>\n';
        }
      }
    });
  });

  // Inline code highlighting: opt in via `inlineCodeLang` frontmatter
  md.renderer.rules.code_inline = function(tokens, idx, options, env) {
    const lang = env && env.inlineCodeLang;
    const code = tokens[idx].content;
    if (!lang || !Prism.languages[lang]) {
      return `<code>${md.utils.escapeHtml(code)}</code>`;
    }
    const html = Prism.highlight(code, Prism.languages[lang], lang);
    return `<code class="language-${lang}">${html}</code>`;
  };

  eleventyConfig.setLibrary("md", md);

  // Add syntax highlighting (Lean 4 language is registered above via global Prism)
  eleventyConfig.addPlugin(syntaxHighlight);

  // Post-process lean4 code blocks to visually separate proof code from proof state
  eleventyConfig.addTransform("lean-proof-state", function(content) {
    if (!this.page.outputPath || !this.page.outputPath.endsWith(".html")) {
      return content;
    }

    return content.replace(
      /<pre class="language-(diff-lean4|lean4)"><code class="language-(?:diff-lean4|lean4)">([\s\S]*?)<\/code><\/pre>/g,
      function(match, lang, codeContent) {
        // For diff-lean4, the diff-highlight plugin wraps each contiguous run of
        // same-type source lines in a single `<span class="token X language-lean4">`.
        // Re-wrap so each source line gets its own wrapper, then split('\n') yields
        // complete wrapped lines.
        if (lang === 'diff-lean4') {
          codeContent = codeContent.replace(
            /<span (class="token (?:unchanged|deleted-sign deleted|inserted-sign inserted) language-lean4")>([\s\S]*?\n)<\/span>/g,
            function (match, classAttr, inner) {
              // `inner` always ends with `\n` (the source-line terminator). Strip it,
              // split on remaining `\n`s, and re-wrap each line.
              const lines = inner.slice(0, -1).split('\n');
              const open = '<span ' + classAttr + '>';
              return lines.map(function (l) { return open + l + '</span>'; }).join('\n') + '\n';
            }
          );
        }
        const htmlLines = codeContent.split('\n');
        const plainLines = htmlLines.map(l => l.replace(/<[^>]*>/g, ''));
        // Drop leading diff prefix (+/-/space) so structural matchers still work.
        const semanticLines = lang === 'diff-lean4'
          ? plainLines.map(l => l.replace(/^[-+ ]/, ''))
          : plainLines;

        // Find goal boundary: line matching "N goal(s)" or "unsolved goals"
        const goalLineIdx = semanticLines.findIndex(
          l => /^\d+ goals?$/.test(l.trim()) || /^unsolved goals$/.test(l.trim())
        );

        if (goalLineIdx < 0) return match;

        // Exclude the blank separator line before the goal marker
        const splitIdx = (goalLineIdx > 0 && semanticLines[goalLineIdx - 1].trim() === '')
          ? goalLineIdx - 1
          : goalLineIdx;

        const proofHtml = htmlLines.slice(0, splitIdx).join('\n');

        // Parse state lines into goal blocks, each with optional case header, hypotheses, and goal
        const stateLines = htmlLines.slice(goalLineIdx);
        const statePlain = semanticLines.slice(goalLineIdx);

        // Pick the goal-count badge. In diff blocks both `-old goals` and `+new goals`
        // may appear; prefer the non-deleted line (the current state).
        let goalCountText = statePlain[0].trim();
        if (lang === 'diff-lean4') {
          for (let i = 0; i < statePlain.length; i++) {
            const trimmedSem = statePlain[i].trim();
            if (!(/^\d+ goals?$/.test(trimmedSem) || /^unsolved goals$/.test(trimmedSem))) {
              if (trimmedSem !== '') break; // stop at first real state line
              continue;
            }
            if (!plainLines[goalLineIdx + i].startsWith('-')) {
              goalCountText = trimmedSem;
              break;
            }
          }
        }

        // Group lines into goal blocks: { caseHeader?, hyps[], goalLines[] }
        const goalBlocks = [];
        let current = { caseHeader: null, hyps: [], goalLines: [] };
        let inGoal = false;

        for (let i = 1; i < stateLines.length; i++) {
          const plain = statePlain[i];
          if (plain.trim() === '') continue;
          // Skip any additional goal-count lines (diff blocks may carry both `-N goals` and `+M goals`)
          if (/^\d+ goals?$/.test(plain.trim()) || /^unsolved goals$/.test(plain.trim())) continue;

          const startsWithTurnstile = /^⊢/.test(plain);
          const isCase = /^case /.test(plain);
          const isContinuation = inGoal && /^ /.test(plain);

          if (isCase) {
            // Start a new goal block; save the previous one if it has content
            if (current.hyps.length > 0 || current.goalLines.length > 0) {
              goalBlocks.push(current);
            }
            inGoal = false;
            current = { caseHeader: stateLines[i], hyps: [], goalLines: [] };
          } else if (startsWithTurnstile) {
            if (inGoal) {
              // Multiple turnstile lines — shouldn't normally happen, but handle it
              current.goalLines.push(stateLines[i]);
            } else {
              inGoal = true;
              current.goalLines.push(stateLines[i]);
            }
          } else if (isContinuation) {
            current.goalLines.push(stateLines[i]);
          } else {
            if (inGoal) {
              // We left the goal area — this shouldn't happen within a single block,
              // but treat it as starting a new implicit block
              goalBlocks.push(current);
              inGoal = false;
              current = { caseHeader: null, hyps: [], goalLines: [] };
            }
            current.hyps.push(stateLines[i]);
          }
        }
        if (current.hyps.length > 0 || current.goalLines.length > 0) {
          goalBlocks.push(current);
        }

        // Build structured HTML
        let stateHtml = '<div class="proof-state">';
        stateHtml += '<div class="proof-state-header">';
        stateHtml += '<span class="proof-goal-badge">' + goalCountText + '</span>';
        stateHtml += '</div>';

        goalBlocks.forEach(function(block) {
          stateHtml += '<div class="proof-goal-block">';

          if (block.caseHeader) {
            stateHtml += '<div class="proof-case-header"><code class="language-' + lang + '">' + block.caseHeader + '</code></div>';
          }

          if (block.hyps.length > 0) {
            stateHtml += '<div class="proof-hypotheses">';
            block.hyps.forEach(function(h) {
              stateHtml += '<div class="proof-hyp"><code class="language-' + lang + '">' + h + '</code></div>';
            });
            stateHtml += '</div>';
          }

          if (block.goalLines.length > 0) {
            stateHtml += '<div class="proof-goal"><code class="language-' + lang + '">' + block.goalLines.join('\n') + '</code></div>';
          }

          stateHtml += '</div>';
        });

        stateHtml += '</div>';

        return '<div class="lean-proof-block">' +
          '<pre class="language-' + lang + ' proof-code"><code class="language-' + lang + '">' + proofHtml + '</code></pre>' +
          stateHtml + '</div>';
      }
    );
  });

  // Add RSS plugin
  eleventyConfig.addPlugin(rssPlugin);

  // Minify JS in the output dir (skipped in --serve / --watch).
  eleventyConfig.addPlugin(minifyJsPlugin);

  // Add global metadata for RSS
  eleventyConfig.addGlobalData("metadata", {
    url: "https://dijkstracula.github.io"
  });

  // Copy static assets
  eleventyConfig.addPassthroughCopy("src/css");
  eleventyConfig.addPassthroughCopy("src/js");
  eleventyConfig.addPassthroughCopy("src/assets");
  eleventyConfig.addPassthroughCopy("src/robots.txt");
  eleventyConfig.addPassthroughCopy("src/CNAME");

  // Resume submodule (dijkstracula/resume) — served at /resume/ as-is.
  eleventyConfig.addPassthroughCopy("src/resume");
  eleventyConfig.ignores.add("src/resume");

  // Add date filter for displaying dates nicely
  eleventyConfig.addFilter("readableDate", dateObj => {
    return new Date(dateObj).toLocaleDateString('en-CA', {
      year: 'numeric',
      month: 'long',
      day: 'numeric'
    });
  });

  // Add ISO date filter for datetime attributes
  eleventyConfig.addFilter("isoDate", dateObj => {
    return new Date(dateObj).toISOString().split('T')[0];
  });

  // Add current year filter for copyright
  eleventyConfig.addFilter("currentYear", () => {
    return new Date().getFullYear();
  });

  // Add striptags filter to remove HTML tags
  eleventyConfig.addFilter("striptags", (content) => {
    return content.replace(/<[^>]*>/g, '');
  });

  // Add truncate filter to limit text length
  eleventyConfig.addFilter("truncate", (text, length = 200) => {
    if (text.length <= length) return text;
    return text.substr(0, length).trim() + '...';
  });

  // Add limit filter to limit array length
  eleventyConfig.addFilter("limit", (array, limit) => {
    return array.slice(0, limit);
  });

  // Reading time (approx, 220 wpm) from rendered HTML
  eleventyConfig.addFilter("readingTime", (html) => {
    if (!html) return 1;
    const text = String(html).replace(/<[^>]*>/g, " ");
    const words = text.split(/\s+/).filter(Boolean).length;
    return Math.max(1, Math.round(words / 220));
  });

  // Compact tag label for the homepage changelog — up to two real tags joined with " · "
  eleventyConfig.addFilter("postTagLabel", (tags) => {
    if (!Array.isArray(tags)) return "";
    return tags.filter(t => t && t !== "post").slice(0, 2).join(" · ");
  });

  // Filter posts belonging to a series, sorted by date (oldest first)
  eleventyConfig.addFilter("seriesPosts", (posts, seriesId) => {
    return posts
      .filter(p => p.data.series === seriesId)
      .sort((a, b) => a.date - b.date);
  });

  // Sort posts by date (newest first)
  eleventyConfig.addCollection("posts", function(collectionApi) {
    return collectionApi.getFilteredByGlob("src/posts/*.md")
      .sort((a, b) => {
        return b.date - a.date;
      });
  });

  // Published posts only (no drafts)
  eleventyConfig.addCollection("publishedPosts", function(collectionApi) {
    return collectionApi.getFilteredByGlob("src/posts/*.md")
      .filter(post => !post.data.draft)
      .sort((a, b) => {
        return b.date - a.date;
      });
  });

  // Drafts only — used by the "Writing" row of the homepage Now panel
  eleventyConfig.addCollection("draftPosts", function(collectionApi) {
    return collectionApi.getFilteredByGlob("src/posts/*.md")
      .filter(post => post.data.draft)
      .sort((a, b) => b.date - a.date);
  });

  // Series list for the blog index
  eleventyConfig.addCollection("seriesList", function(collectionApi) {
    const posts = collectionApi.getFilteredByGlob("src/posts/*.md")
      .filter(p => !p.data.draft);
    const seriesMap = {};
    posts.forEach(post => {
      const id = post.data.series;
      if (!id) return;
      if (!seriesMap[id]) seriesMap[id] = [];
      seriesMap[id].push(post);
    });
    // Sort each series by date (oldest first), then sort series by most recent post (newest first)
    return Object.entries(seriesMap)
      .map(([id, seriesPosts]) => ({
        id,
        posts: seriesPosts.sort((a, b) => a.date - b.date)
      }))
      .sort((a, b) => b.posts[b.posts.length - 1].date - a.posts[a.posts.length - 1].date);
  });

  // Tag list with counts
  eleventyConfig.addCollection("tagList", function(collectionApi) {
    const tagCounts = {};
    collectionApi.getFilteredByGlob("src/posts/*.md")
      .filter(post => !post.data.draft)
      .forEach(post => {
        if (post.data.tags) {
          post.data.tags.forEach(tag => {
            if (tag !== "post") {
              tagCounts[tag] = (tagCounts[tag] || 0) + 1;
            }
          });
        }
      });

    return Object.keys(tagCounts)
      .sort()
      .map(tag => ({
        tag: tag,
        count: tagCounts[tag]
      }));
  });

  return {
    dir: {
      input: "src",
      output: "_site",
      includes: "_includes",
      layouts: "_layouts"
    },
    markdownTemplateEngine: "njk",
    htmlTemplateEngine: "njk",
    templateFormats: ["md", "njk", "html"]
  };
};
