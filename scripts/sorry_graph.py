#!/usr/bin/env python3
"""Generate a graph of open `sorry` count over the project's git history.

Walks every commit (oldest first), counts `sorry` tokens in the Lean sources
under analysis/Analysis/, and plots the count over time.

Usage:
    python3 scripts/sorry_graph.py            # writes sorries_over_time.png + .csv
    python3 scripts/sorry_graph.py --out foo  # custom output prefix
"""
import argparse
import csv
import datetime
import subprocess
import sys

LEAN_PATHSPECS = ["analysis/Analysis/*.lean", "analysis/Analysis/**/*.lean"]


def git(*args):
    return subprocess.run(
        ["git", *args], capture_output=True, text=True, check=True
    ).stdout


def count_sorries(sha):
    """Count `sorry` word-tokens in the Lean sources at a given revision."""
    try:
        out = subprocess.run(
            ["git", "grep", "-h", "-o", r"\bsorry\b", sha, "--", *LEAN_PATHSPECS],
            capture_output=True,
            text=True,
        ).stdout
    except subprocess.CalledProcessError:
        return 0
    return sum(1 for _ in out.splitlines())


def collect():
    log = git("log", "--reverse", "--format=%H %cI").splitlines()
    rows = []
    for i, line in enumerate(log):
        sha, date = line.split(" ", 1)
        rows.append((date, sha, count_sorries(sha)))
        if i % 100 == 0:
            print(f"  ...{i}/{len(log)} commits", file=sys.stderr)
    return rows


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--out", default="sorries_over_time", help="output file prefix")
    args = ap.parse_args()

    rows = collect()

    csv_path = f"{args.out}.csv"
    with open(csv_path, "w", newline="") as f:
        w = csv.writer(f)
        w.writerow(["date", "commit", "sorries"])
        w.writerows(rows)
    print(f"wrote {csv_path}")

    import matplotlib

    matplotlib.use("Agg")
    import matplotlib.pyplot as plt

    dates = [datetime.datetime.fromisoformat(r[0]) for r in rows]
    vals = [r[2] for r in rows]

    fig, ax = plt.subplots(figsize=(12, 6))
    ax.plot(dates, vals, lw=1.2, color="#c0392b")
    ax.fill_between(dates, vals, alpha=0.15, color="#c0392b")
    ax.set_title("Sorries over time — analysis project")
    ax.set_ylabel("open sorries")
    ax.set_xlabel("date")
    ax.grid(alpha=0.3)
    peak = max(vals)
    ax.annotate(
        f"peak {peak}",
        xy=(dates[vals.index(peak)], peak),
        xytext=(10, -20),
        textcoords="offset points",
        fontsize=9,
    )
    ax.annotate(
        f"now {vals[-1]}",
        xy=(dates[-1], vals[-1]),
        xytext=(-40, 15),
        textcoords="offset points",
        fontsize=9,
    )
    fig.autofmt_xdate()
    fig.tight_layout()
    png_path = f"{args.out}.png"
    fig.savefig(png_path, dpi=130)
    print(f"wrote {png_path}")


if __name__ == "__main__":
    main()
