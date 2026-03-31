#!/usr/bin/env -S uv run --script
# /// script
# dependencies = [
#   "lxml",
# ]
# ///

# Python Standard Library
from lxml import etree
import subprocess
import sys
from pathlib import Path


def run(cmd: list[str]) -> None:
    subprocess.run(cmd, check=True)


def build(lean_file: str) -> None:
    src = Path(lean_file)
    md = src.with_suffix(".lean.md")
    html = src.with_suffix(".lean.html")

    run(["mol", str(src)])  # -> .lean.md

    run(
        [
            "pandoc",
            "--standalone",
            "--toc",
            "--css=index.css",
            "--syntax-definition=lean4.xml",
            "--mathjax=https://cdn.jsdelivr.net/npm/mathjax@3/es5/tex-chtml.js",
            "--bibliography=bib.json",
            "--citeproc",
            "-o",
            str(html),
            str(md),
        ]
    )

    # Post-processing
    with html.open("rb") as f:
        tree = etree.parse(f, etree.HTMLParser())

    root = tree.getroot()


if __name__ == "__main__":
    build(
        lean_file=sys.argv[1] if len(sys.argv) > 1 else "Chapter12.lean",
        # title=sys.argv[2] if len(sys.argv) > 2 else "LoVe – Chapter 12",
    )
