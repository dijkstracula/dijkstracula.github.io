#!/usr/bin/env python3
import re
import sys
from pathlib import Path

def convert_hugo_to_11ty(content):
    """Convert Hugo frontmatter and syntax to 11ty format"""

    # Check if already converted (has layout: post.njk)
    if re.search(r'^layout: post\.njk$', content, re.MULTILINE):
        return content

    # Extract Hugo frontmatter (handles both quoted and unquoted oneliner)
    frontmatter_pattern = (
        r'^---\n'
        r'title: "(.*?)"\n'
        r'date: (.*?)\n'
        r'(?:slug: .*?\n)?'
        r'(?:draft: .*?\n)?'
        r'tags: \[(.*?)\]\n'
        r'(?:categories: .*?\n)?'
        r'(?:oneliner: "?(.*?)"?\n)?'
        r'---'
    )

    frontmatter_match = re.match(frontmatter_pattern, content, re.MULTILINE)

    if frontmatter_match:
        title = frontmatter_match.group(1)
        date = frontmatter_match.group(2)
        tags = frontmatter_match.group(3)
        oneliner = frontmatter_match.group(4) if frontmatter_match.lastindex >= 4 else ""

        # Build new frontmatter
        new_frontmatter = f'''---
layout: post.njk
title: "{title}"
date: {date}
tags: [post, {tags}]
excerpt: "{oneliner}"
---'''

        # Replace frontmatter
        content = re.sub(
            r'^---\n.*?---',
            new_frontmatter,
            content,
            count=1,
            flags=re.MULTILINE | re.DOTALL
        )

    # Convert Hugo shortcodes to HTML
    content = re.sub(r'\{\{< manualcode >\}\}\n?', '<div class="dafny-code">\n', content)
    content = re.sub(r'\n?\{\{< /manualcode >\}\}', '\n</div>', content)

    return content

def main():
    posts_dir = Path('/Users/ntaylor/code/blog/src/posts')

    for post_file in posts_dir.glob('*.md'):
        print(f"Converting {post_file.name}...")

        content = post_file.read_text()
        converted = convert_hugo_to_11ty(content)

        if content != converted:
            post_file.write_text(converted)
            print(f"  ✓ Converted")
        else:
            print(f"  - No changes needed")

if __name__ == '__main__':
    main()
