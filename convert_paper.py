#!/usr/bin/env python3
"""
Convert the Solvent paper from Pandoc markdown with BibTeX citations
to 11ty-compatible markdown with a bibliography section.
"""

import re
from datetime import datetime
from pathlib import Path

# The markdown content
markdown_content = """[MARKDOWN_CONTENT_PLACEHOLDER]"""

# Simple BibTeX parser - extracts key fields we care about
def parse_bibtex_entry(entry):
    """Parse a single BibTeX entry into a dict."""
    result = {}

    # Extract entry type and key
    match = re.search(r'@(\w+)\{([^,]+),', entry)
    if match:
        result['type'] = match.group(1)
        result['key'] = match.group(2)

    # Extract fields
    for field in ['title', 'author', 'year', 'journal', 'booktitle', 'publisher', 'url', 'howpublished']:
        pattern = rf'{field}\s*=\s*[{"{"]([^}}"]+)[}}"]'
        match = re.search(pattern, entry, re.IGNORECASE)
        if match:
            result[field] = match.group(1).strip()

    return result

def format_bibliography_entry(entry):
    """Format a bibliography entry in a readable way."""
    parts = []

    if 'author' in entry:
        # Clean up author names (remove extra braces, etc.)
        authors = entry['author'].replace('{', '').replace('}', '')
        parts.append(authors)

    if 'title' in entry:
        title = entry['title'].replace('{', '').replace('}', '').replace('\\', '')
        parts.append(f'"{title}"')

    if 'booktitle' in entry:
        parts.append(f"*{entry['booktitle']}*")
    elif 'journal' in entry:
        parts.append(f"*{entry['journal']}*")

    if 'year' in entry:
        parts.append(f"({entry['year']})")

    if 'url' in entry:
        url = entry['url'].replace('\\', '')
        parts.append(f"[Link]({url})")
    elif 'howpublished' in entry:
        hp = entry['howpublished'].replace('\\url{', '').replace('}', '')
        parts.append(f"[Link]({hp})")

    return '. '.join(parts) + '.'

# Parse the BibTeX file (simplified - just extract the entries we need)
bibtex_content = """[BIBTEX_CONTENT_PLACEHOLDER]"""

# Extract all BibTeX entries
bibtex_entries = {}
for entry in re.split(r'\n(?=@)', bibtex_content):
    if entry.strip():
        parsed = parse_bibtex_entry(entry)
        if 'key' in parsed:
            bibtex_entries[parsed['key']] = parsed

# Find all citations in the markdown
citations = re.findall(r'\[@([^\]]+)\]', markdown_content)
unique_citations = []
seen = set()
for cite in citations:
    if cite not in seen:
        unique_citations.append(cite)
        seen.add(cite)

# Build citation map
citation_map = {}
for i, cite_key in enumerate(unique_citations, 1):
    citation_map[cite_key] = i

# Replace citations with superscript numbers
def replace_citation(match):
    cite_key = match.group(1)
    if cite_key in citation_map:
        return f'[^{citation_map[cite_key]}]'
    else:
        return f'[{cite_key}]'  # Keep as-is if not found

markdown_with_refs = re.sub(r'\[@([^\]]+)\]', replace_citation, markdown_content)

# Build bibliography section
bibliography_lines = ['\n## References\n']
for cite_key in unique_citations:
    num = citation_map[cite_key]
    if cite_key in bibtex_entries:
        formatted = format_bibliography_entry(bibtex_entries[cite_key])
        bibliography_lines.append(f'[^{num}]: {formatted}')
    else:
        bibliography_lines.append(f'[^{num}]: {cite_key} (reference not found)')

bibliography_section = '\n'.join(bibliography_lines)

# Add frontmatter
frontmatter = f"""---
layout: post.njk
title: "Liquid Types: Unifying Type Theory and Model Checking"
date: {datetime.now().isoformat()}
tags: [post, types, formal-methods, verification, liquid-types, smt]
excerpt: "A deep dive into refinement types and the Liquid Types paper, exploring how SMT solvers can enable decidable dependent type inference"
---

*This is a paper/report on the [Liquid Types](https://github.com/dijkstracula/solvent) system, exploring how refinement types unify type-theoretic and model-checking approaches to program verification.*

---

"""

# Combine everything
final_content = frontmatter + markdown_with_refs + '\n' + bibliography_section

# Write output
output_path = Path('/Users/ntaylor/code/blog/src/posts/liquid-types-paper.md')
with open(output_path, 'w') as f:
    f.write(final_content)

print(f"Converted paper written to {output_path}")
print(f"Found {len(unique_citations)} unique citations")
