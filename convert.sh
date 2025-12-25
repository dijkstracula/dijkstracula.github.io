#!/bin/bash
# Script to convert Hugo posts to 11ty format

cd ~/code/old-blog/content/blog

for file in Proving-The-Coding-Interview.md Proving-The-Coding-Interview-2.md Proving-The-Coding-Interview-3.md Ivy-In-Python3.md; do
    # Read the file and do basic conversions
    # Note: This is a simplified conversion - manual cleanup may be needed
    sed 's|https://www.cs.utexas.edu/~ntaylor/blog/proving/|/posts/proving-the-coding-interview/|g' "$file" | \
    sed 's|https://www.cs.utexas.edu/~ntaylor/blog/proving-2/|/posts/proving-the-coding-interview-2/|g' | \
    sed 's|https://www.cs.utexas.edu/~ntaylor/blog/proving-3/|/posts/proving-the-coding-interview-3/|g' > /tmp/"$file"
done

echo "Converted files are in /tmp/"
