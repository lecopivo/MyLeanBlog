import VersoBlog

import Blog
import Blog.Theme

open Verso Genre Blog Site Syntax

def blog : Site := site Blog.FrontPage /
  static "static" ← "static_files"
  "about" Blog.About
  "blog" Blog.Posts with
    Blog.Posts.VisionForSciLean
    -- Blog.Posts.ThoughtsOnFiniteArithmetics
    Blog.Posts.NumLeanIntro
    -- Blog.Posts.CSG

def main := blogMain theme blog
