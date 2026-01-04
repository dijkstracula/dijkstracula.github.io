const syntaxHighlight = require("@11ty/eleventy-plugin-syntaxhighlight");
const rssPlugin = require("@11ty/eleventy-plugin-rss");
const markdownIt = require("markdown-it");
const markdownItFootnote = require("markdown-it-footnote");
const markdownItContainer = require("markdown-it-container");

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

  eleventyConfig.setLibrary("md", md);

  // Add syntax highlighting with custom Lean 4 support
  eleventyConfig.addPlugin(syntaxHighlight, {
    init: function({ Prism }) {
      // Load custom Lean 4 language definition
      const leanDef = require('./src/js/prism-lean.js');
      if (typeof leanDef === 'function') {
        leanDef(Prism);
      }
    }
  });

  // Add RSS plugin
  eleventyConfig.addPlugin(rssPlugin);

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
