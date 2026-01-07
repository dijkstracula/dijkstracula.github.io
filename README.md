# Website 2.0

## Getting Started

### Prerequisites

- Node.js (v16 or higher)
- npm

### Installation

```bash
npm install
```

### Development

Start the development server with live reload:

```bash
npm start
```

Visit `http://localhost:8080` to see your blog.

### Build

Build the site for production:

```bash
npm run build
```

The built site will be in the `_site` directory.

## Project Structure

```
.
├── src/
│   ├── _layouts/        # Layout templates
│   │   ├── base.njk     # Base layout with header/footer
│   │   └── post.njk     # Blog post layout
│   ├── posts/           # Blog posts (Markdown)
│   ├── index.njk        # Homepage
│   └── about.md         # About page
├── .eleventy.js         # 11ty configuration
└── package.json
```

## Writing Posts

Create a new Markdown file in `src/posts/` with the following frontmatter:

```markdown
---
layout: post.njk
title: Your Post Title
date: 2025-01-15
tags: [post, your-tags]
excerpt: A short description of your post.
---

Your post content here...
```

## Customization

### Change Site Name

Edit `src/_layouts/base.njk` and update the site name in the header and title.

### Add Your Info

Edit `src/about.md` to add your bio and contact information.

### Custom Styles

Add custom CSS in the `<style>` block of `src/_layouts/base.njk`.

## Deployment

This blog generates static files that can be hosted anywhere:

- **Netlify** - Drop `_site` folder or connect your Git repo
- **Vercel** - Import project and deploy
- **GitHub Pages** - Push `_site` to gh-pages branch
- **Any static host** - Upload the `_site` directory

## Tech Stack

- [11ty](https://www.11ty.dev/) - Static site generator
- [Pico.css](https://picocss.com/) - Minimal CSS framework

## License

MIT
