#!/usr/bin/env python3
"""Custody share (post-G4 decision 8; rule agreed 2026-10-07). Builder's non-merge commits only.
custody-only: every changed path is CI, snapshot/publication manifest, pin, or custody receipt;
governance: every changed path is a record (decisions, status, TCB, docs, reports) or custody;
work: anything touching code, proofs, tests or tools. Campaign-agent commits are excluded."""
import subprocess, sys
CUSTODY = (".github/", "public-snapshot", "KERNEL-PIN.json", "oracle/PIN.json", "reports/ALPHA", "reports/REVIEWER", "reports/DK-V4-RECEIPT")
GOV = ("DECISIONS.md", "STATUS.md", "TCB.md", "README", "AGENTS.md", "docs/", "reports/", "LIMITS.md")


def tally(args):
    out = subprocess.run(["git", "log", "--no-merges", "--format=%h"] + args, capture_output=True, text=True).stdout.split()
    t = {"custody": 0, "governance": 0, "work": 0}
    for h in out:
        files = subprocess.run(["git", "show", "--name-only", "--format="] + [h], capture_output=True, text=True).stdout.split()
        if all(f.startswith("campaigns/3p-matroids/") for f in files):
            continue
        k = ("custody" if all(f.startswith(CUSTODY) for f in files)
             else "governance" if all(f.startswith(GOV + CUSTODY) for f in files) else "work")
        t[k] += 1
    return t


if __name__ == "__main__":
    # usage: custody-share.py <git log arguments selecting the window>, e.g. --since=2026-10-04 3bd0bf0
    t = tally(sys.argv[1:])
    n = sum(t.values())
    print(f"{t['custody']} of {n} builder commits custody-only ({100 * t['custody'] / max(n, 1):.0f}%); "
          f"{t['governance']} governance; {t['work']} work")
