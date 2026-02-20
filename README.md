# My Lean Blog


Build with
```
lake exe generate-blog
```

View with
```
./server.py 8000
```
and go to `http://localhost:8000/`

This directory contains a blog written in Verso, in the spirit of personal sites built with static
site generators like Jekyll.

Most of the posts include code examples that are in the current version of Lean; however, there is
[one post](Blog/Posts/Comparison.lean) that instead loads its example code from files in separate
Lean projects. This means its examples will not need updating as the blog's software is updated.

