#!/usr/bin/env python3
"""
Build pipeline: .lean -> .lean.md -> .lean.html
"""

# Python Standard Library
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
            "-s",
            "--syntax-definition=lean4.xml",
            "--mathjax=https://cdn.jsdelivr.net/npm/mathjax@3/es5/tex-chtml.js",
            "-o",
            str(html),
            str(md),
        ]
    )


if __name__ == "__main__":
    build(
        lean_file=sys.argv[1] if len(sys.argv) > 1 else "Chapter12.lean",
        # title=sys.argv[2] if len(sys.argv) > 2 else "LoVe – Chapter 12",
    )
