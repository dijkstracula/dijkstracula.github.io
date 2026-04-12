const RssParser = require("rss-parser");
const fs = require("fs");
const path = require("path");

const blogroll = require("../src/_data/blogroll.json");
const parser = new RssParser();

const OUTPUT = path.join(__dirname, "../src/_data/blogrollPosts.json");

async function fetchFeeds() {
  // Load existing posts so we can preserve them for feeds that fail
  let existing = [];
  try {
    existing = JSON.parse(fs.readFileSync(OUTPUT, "utf-8"));
  } catch {
    // No existing file, that's fine
  }

  const posts = [];
  const failedSources = new Set();

  for (const entry of blogroll) {
    if (!entry.feed) continue;

    try {
      const res = await fetch(entry.feed, {
        headers: {
          "User-Agent": "Mozilla/5.0 (compatible; BlogrollFetcher/1.0)",
        },
      });
      if (!res.ok) throw new Error(`${res.status} ${res.statusText}`);
      const xml = await res.text();
      const feed = await parser.parseString(xml);

      for (const item of feed.items) {
        posts.push({
          title: item.title,
          url: item.link,
          date: item.isoDate || item.pubDate,
          source: entry.name,
        });
      }
      console.log(`[blogroll] Fetched ${feed.items.length} posts from ${entry.name}`);
    } catch (err) {
      console.warn(`[blogroll] Failed to fetch feed for ${entry.name}: ${err.message}`);
      failedSources.add(entry.name);
    }
  }

  // Preserve existing posts from feeds that failed
  for (const post of existing) {
    if (failedSources.has(post.source)) {
      posts.push(post);
    }
  }

  posts.sort((a, b) => new Date(b.date) - new Date(a.date));
  const top = posts.slice(0, 40);

  fs.writeFileSync(OUTPUT, JSON.stringify(top, null, 2) + "\n");
  console.log(`[blogroll] Wrote ${top.length} posts to ${OUTPUT}`);
  if (failedSources.size) {
    console.warn(`[blogroll] Preserved existing posts for: ${[...failedSources].join(", ")}`);
  }
}

fetchFeeds();
