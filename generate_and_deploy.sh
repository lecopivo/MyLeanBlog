#!/usr/bin/env bash
lake exe generate-blog
cd site
git init
git add -A
git commit -m "deploy"
git push -f git@github.com:lecopivo/MyLeanBlog.git HEAD:gh-pages
