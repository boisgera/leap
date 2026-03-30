#!/usr/bin/env python3
"""
Build pipeline: .lean -> .lean.md -> .lean.html 
"""

import subprocess
import sys
from pathlib import Path

SHIKI_SCRIPT = r"""\
<script type="module">
import { codeToHtml } from "https://esm.sh/shiki@3";

const lean4Grammar = await fetch(
  "https://raw.githubusercontent.com/leanprover/vscode-lean4/master/vscode-lean4/syntaxes/lean4.json"
).then(r => r.json());

for (const block of document.querySelectorAll("pre[class] > code")) {
  const lang = block.className.match(/language-(\w+)/)?.[1]
             ?? block.parentElement.className.match(/(\w+)/)?.[1]
             ?? "text";
  const parent = block.parentElement;
  parent.outerHTML = await codeToHtml(block.textContent, {
    lang,
    theme: "github-dark",
    langs: [{ ...lean4Grammar, name: "lean4" }],
  });
}
</script>"""


def run(cmd: list[str]) -> None:
    subprocess.run(cmd, check=True)


def inject_shiki(html_path: Path) -> None:
    content = html_path.read_text(encoding="utf-8")
    content = content.replace("</body>", f"{SHIKI_SCRIPT}\n</body>", 1)
    html_path.write_text(content, encoding="utf-8")


def build(lean_file: str, title: str) -> None:
    src = Path(lean_file)
    md = src.with_suffix(".lean.md")
    html = src.with_suffix(".lean.html")

    run(["mol", str(src)])  # -> .lean.md

    run([
        "pandoc", "-s",
        "--metadata", f"title={title}",
        "--no-highlight",
        "--mathjax=https://cdn.jsdelivr.net/npm/mathjax@3/es5/tex-chtml.js",
        "-o", str(html),
        str(md),
    ])

    inject_shiki(html)


if __name__ == "__main__":
    build(
        lean_file=sys.argv[1] if len(sys.argv) > 1 else "Chapter12.lean",
        title=sys.argv[2] if len(sys.argv) > 2 else "LoVe – Chapter 12",
    )