#!/usr/bin/env python3
"""Count *live* `sorry`s in the Lean sources at a given git revision.

A "live" sorry is one that is real proof-term code, NOT a `sorry` token that
merely appears inside a comment (line `--`, block `/- -/`, or doc `/-- -/`) or
a string literal. The naive `git grep sorry` count is badly inflated by prose.

Usage:
    python3 scripts/count_live_sorries.py [REV]      # default REV = HEAD
    python3 scripts/count_live_sorries.py REV --per-file
"""
import argparse
import re
import subprocess
import sys

import os
LEAN_PATHSPECS = [os.environ.get("LEAN_PATH", "analysis/Analysis/")]


def git(*args):
    return subprocess.run(["git", *args], capture_output=True, text=True).stdout


def list_files(rev):
    out = git("ls-tree", "-r", "--name-only", rev, "--", *LEAN_PATHSPECS)
    return [f for f in out.splitlines() if f.endswith(".lean")]


def strip_comments_and_strings(src):
    """Remove Lean block comments (nestable), line comments, and string
    literals, replacing them with spaces so column counts are preserved."""
    out = []
    i, n = 0, len(src)
    depth = 0          # block-comment nesting depth
    in_str = False
    in_line = False
    while i < n:
        c = src[i]
        two = src[i:i+2]
        if in_line:
            out.append(c)
            if c == "\n":
                in_line = False
            i += 1
        elif depth > 0:
            if two == "/-":
                depth += 1
                out.append("  "); i += 2
            elif two == "-/":
                depth -= 1
                out.append("  "); i += 2
            else:
                out.append(" " if c != "\n" else "\n"); i += 1
        elif in_str:
            out.append(" ")
            if c == "\\" and i + 1 < n:
                out.append(" "); i += 2
            else:
                if c == '"':
                    in_str = False
                i += 1
        else:
            if two == "/-":
                depth += 1
                out.append("  "); i += 2
            elif two == "--":
                in_line = True
                out.append(two); i += 2
            elif c == '"':
                in_str = True
                out.append(" "); i += 1
            else:
                out.append(c); i += 1
    return "".join(out)


SORRY_RE = re.compile(r"\bsorry\b")


def count_in_blob(src):
    code = strip_comments_and_strings(src)
    # Drop line-comment tails too (we kept the leading `--`).
    lines = []
    for line in code.split("\n"):
        idx = line.find("--")
        if idx != -1:
            line = line[:idx]
        lines.append(line)
    return len(SORRY_RE.findall("\n".join(lines)))


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("rev", nargs="?", default="HEAD")
    ap.add_argument("--per-file", action="store_true")
    args = ap.parse_args()

    total = 0
    per = {}
    for f in list_files(args.rev):
        blob = git("show", f"{args.rev}:{f}")
        c = count_in_blob(blob)
        if c:
            per[f] = c
            total += c

    if args.per_file:
        for f in sorted(per, key=lambda k: -per[k]):
            print(f"{per[f]:4d}  {f}")
        print("-" * 30)
    print(f"{total} live sorries at {args.rev}")


if __name__ == "__main__":
    main()
