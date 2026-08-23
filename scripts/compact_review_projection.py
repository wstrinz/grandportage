#!/usr/bin/env python3
"""Prototype a bounded content-addressed review index over a large JSONL."""

import argparse
from pathlib import Path

from grandportage import projection


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("source", type=Path)
    parser.add_argument("output", type=Path)
    parser.add_argument("--max-records", type=int, default=2000)
    args = parser.parse_args(argv)
    if args.output.exists():
        parser.error("output already exists: %s" % args.output)
    value = projection.compact_review_projection(
        args.source, max_records=args.max_records)
    with args.output.open("w", encoding="utf-8", newline="\n") as stream:
        stream.write(projection.canonical_json(value))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
