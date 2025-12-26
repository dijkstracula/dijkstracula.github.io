module.exports = {
  layout: "post.njk",
  tags: ["post"],
  eleventyComputed: {
    permalink: (data) => {
      // Don't generate pages for draft posts
      if (data.draft) {
        return false;
      }
      // Use default permalink structure for published posts
      return data.permalink;
    }
  }
};
