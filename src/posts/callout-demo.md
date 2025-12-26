---
layout: post.njk
title: "Callout Blocks Demo"
date: 2024-01-20T00:00:00.000Z
tags: [post, demo]
excerpt: "A demonstration of how to use callout blocks in your blog posts."
draft: true
---

# Callout Blocks Demo

This post demonstrates the different types of callout blocks available in your blog.

## Note Callout

::: note
This is a note callout. Use it for general information or supplementary details that might be helpful to readers.
:::

## Info Callout

::: info
This is an info callout. Use it for factual information or explanations that provide additional context.
:::

## Tip Callout

::: tip
This is a tip callout. Use it to share helpful advice, best practices, or pro tips with your readers.
:::

## Warning Callout

::: warning
This is a warning callout. Use it to alert readers about potential issues, gotchas, or things they should be careful about.
:::

## Danger Callout

::: danger
This is a danger callout. Use it for critical warnings about things that could break or cause serious problems.
:::

## Margin Callouts

::: margin-note
This is a margin note! It appears to the right of the main content on wide screens. On mobile, it displays inline.
:::

You can also have callouts appear in the right margin instead of inline. This is great for side notes, additional context, or commentary that supplements the main text without interrupting the flow.

::: margin-tip
Margin callouts are perfect for tips that don't need to break up your main narrative!
:::

## Usage in Markdown

To use **inline callouts**, wrap your content with triple colons and the callout type:

```markdown
::: note
Your note content here
:::

::: warning
Your warning content here
:::
```

To use **margin callouts**, prefix the type with `margin-`:

```markdown
::: margin-note
This appears in the right margin!
:::

::: margin-tip
Another margin callout!
:::
```

You can include any markdown inside callouts:

::: tip
**Pro tip**: You can use:
- Lists
- **Bold** and *italic* text
- [Links](https://example.com)
- `Code snippets`
- And more!
:::
