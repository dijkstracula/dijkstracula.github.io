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

  // Add syntax highlighting
  eleventyConfig.addPlugin(syntaxHighlight);

  // Add RSS plugin
  eleventyConfig.addPlugin(rssPlugin);

  // Add global metadata for RSS
  eleventyConfig.addGlobalData("metadata", {
    url: "https://yourblog.com"
  });

  // Copy static assets
  eleventyConfig.addPassthroughCopy("src/css");
  eleventyConfig.addPassthroughCopy("src/js");
  eleventyConfig.addPassthroughCopy("src/assets");
  eleventyConfig.addPassthroughCopy("src/robots.txt");
  eleventyConfig.addPassthroughCopy("src/CNAME");

  // Add date filter for displaying dates nicely
  eleventyConfig.addFilter("readableDate", dateObj => {
    return new Date(dateObj).toLocaleDateString('en-US', {
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

  // Sort posts by date (newest first), exclude drafts
  eleventyConfig.addCollection("posts", function(collectionApi) {
    return collectionApi.getFilteredByGlob("src/posts/*.md")
      .filter(item => !item.data.draft)
      .sort((a, b) => {
        return b.date - a.date;
      });
  });

  return {
    dir: {
      input: "src",
      output: "_site",
      includes: "_includes",
      layouts: "_layouts"
    },
    pathPrefix: "/website/",
    markdownTemplateEngine: "njk",
    htmlTemplateEngine: "njk",
    templateFormats: ["md", "njk", "html"]
  };
};
