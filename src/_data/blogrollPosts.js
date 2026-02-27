const EleventyFetch = require("@11ty/eleventy-fetch");
const RssParser = require("rss-parser");
const blogroll = require("./blogroll.json");

const parser = new RssParser();

module.exports = async function () {
  const posts = [];

  for (const entry of blogroll) {
    if (!entry.feed) continue;

    try {
      const xml = await EleventyFetch(entry.feed, {
        duration: "1d",
        type: "text",
      });
      const feed = await parser.parseString(xml);

      for (const item of feed.items) {
        posts.push({
          title: item.title,
          url: item.link,
          date: new Date(item.isoDate || item.pubDate),
          source: entry.name,
          sourceUrl: entry.url,
        });
      }
    } catch (err) {
      console.warn(`[blogroll] Failed to fetch feed for ${entry.name}: ${err.message}`);
    }
  }

  posts.sort((a, b) => b.date - a.date);
  return posts.slice(0, 20);
};
