import VersoBlog
import Blog.Meta

open Verso Genre Blog Site Syntax

open Output Html Template Theme in
def theme : Theme := { Theme.default with
  primaryTemplate := do
    let isRoot := (← currentPath).isEmpty
    let postList :=
      match (← param? "posts") with
      | none => Html.empty
      | some html => html
    let catList :=
      match (← param? (α := Post.Categories) "categories") with
      | none => Html.empty
      | some ⟨cats⟩ =>
        if cats.isEmpty then Html.empty else {{
          <div class="category-directory">
            <h2> "Categories" </h2>
            <ul>
            {{ cats.map fun (target, cat) =>
              {{<li><a href={{target}}>{{Post.Category.name cat}}</a></li>}}
            }}
            </ul>
          </div>
        }}
    return {{
      <html>
        <head>
          <meta charset="utf-8"/>
          <meta name="viewport" content="width=device-width, initial-scale=1"/>
          {{ if isRoot then {{<meta http-equiv="refresh" content="0; url=/blog/"/>}} else .empty }}
          <link rel="preconnect" href="https://fonts.googleapis.com"/>
          <link rel="preconnect" href="https://fonts.gstatic.com" crossorigin="anonymous"/>
          <link href="https://fonts.googleapis.com/css?family=Alata" rel="stylesheet"/>
          <title>{{ (← param (α := String) "title") }} " — Tomáš Skřivan"</title>
          <link rel="stylesheet" href="/static/style.css"/>
          {{← builtinHeader }}
        </head>
        <body>
          <header class="site-header">
            <div class="inner-wrap nav-wrap">
              <a class="navbar-brand" href="https://lecopivo.github.io/">"🐳 "<span class="light">"Tomáš"</span> " Skřivan"</a>
              <nav class="site-nav" aria-label="Main navigation">
                <a href="/blog/">"Blog"</a>
                <a href="/about/">"About"</a>
              </nav>
            </div>
          </header>
          <main>
            <div class="wrap">
              {{← breadcrumbs 2}}
              {{← param "content" }}
              {{ postList }}
              {{ catList }}
            </div>
          </main>
        </body>
      </html>
    }}
  }
  |>.override #[] {
    template := do
      return {{<div class="frontpage">{{← param "content"}}</div>}},
    params := id
  }
