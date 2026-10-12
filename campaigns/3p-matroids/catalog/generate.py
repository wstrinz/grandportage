"""Catalog of simple rank-3 matroids on 3..N elements, up to isomorphism (3P stage F2).

TRUSTED generator: GP does not check it. Catalog completeness is an OPEN premise
(CATALOG-COMPLETE); `check.py` is an independent cross-check, not a proof.

A simple rank-3 matroid on [n] is given by its lines: subsets of size >= 3, pairwise meeting
in at most one point, not all points on one line.  Every simple rank-3 matroid on n+1 points
has a single-element deletion that is a simple matroid of rank 3, or the rank-2 line U(2,n).
So the classes on n+1 points are the rank-3 single-point extensions of the classes on n points
and of U(2,n), deduplicated by a canonical form.

A new point p extends some pairwise disjoint lines L (to L + p) and joins some pairs {a, b}
not on a common line (to new lines {a, b, p}); the chosen lines and pairs are pairwise
disjoint, since every point lies on at most one line through p.

usage: python generate.py [N] [--write]   (N defaults to 8; --write emits matroids/*.json)
"""
from itertools import permutations, product
import hashlib
import json
from math import factorial
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
CAMPAIGN = HERE.parent


def invariants(n, lines):
    """An isomorphism invariant per point: line sizes through it, refined once by neighbours."""
    through = [[L for L in lines if p in L] for p in range(n)]
    inv1 = [tuple(sorted(len(L) for L in through[p])) for p in range(n)]
    return [(inv1[p], tuple(sorted((len(L), tuple(sorted(inv1[q] for q in L if q != p))) for L in through[p])))
            for p in range(n)]


def relabelings(n, lines):
    """Every bijection sending points to labels in the order of their invariant (ties all ways)."""
    inv = invariants(n, lines)
    cells = []
    for v in sorted(set(inv)):
        cells.append([p for p in range(n) if inv[p] == v])
    starts, s = [], 0
    for c in cells:
        starts.append(s)
        s += len(c)
    for choice in product(*[permutations(c) for c in cells]):
        sigma = [0] * n
        for start, perm in zip(starts, choice):
            for i, p in enumerate(perm):
                sigma[p] = start + i
        yield sigma


def apply(sigma, lines):
    return tuple(sorted(tuple(sorted(sigma[p] for p in L)) for L in lines))


def canonical(n, lines):
    """The least relabelled line set over invariant-respecting bijections: equal iff isomorphic."""
    return min(apply(s, lines) for s in relabelings(n, lines))


def automorphisms(n, lines):
    """|Aut(M)|: every automorphism preserves the invariant, so search only those bijections."""
    target = apply(list(range(n)), lines)
    inv = invariants(n, lines)
    cells = [[p for p in range(n) if inv[p] == v] for v in sorted(set(inv))]
    count = 0
    for choice in product(*[permutations(c) for c in cells]):
        tau = [0] * n
        for cell, perm in zip(cells, choice):
            for p, q in zip(cell, perm):
                tau[p] = q
        count += apply(tau, lines) == target
    return count


def rank3(n, lines):
    return not any(len(L) == n for L in lines) and n >= 3


def extensions(n, lines):
    """All single-point extensions (point n) of a simple matroid on [n] given by its lines."""
    lines = [tuple(L) for L in lines]
    covered = set()
    for L in lines:
        for a in L:
            for b in L:
                covered.add((a, b))
    out = []

    def go(a, used, ext, pairs):
        while a < n and a in used:
            a += 1
        if a == n:
            new = [L + (n,) if L in ext else L for L in lines] + [(x, y, n) for x, y in pairs]
            out.append([tuple(sorted(L)) for L in new])
            return
        go(a + 1, used | {a}, ext, pairs)  # a lies on no line through the new point
        for L in lines:
            if a in L and not (set(L) & used):
                go(a + 1, used | set(L), ext | {L}, pairs)
        for b in range(a + 1, n):
            if b not in used and (a, b) not in covered:
                go(a + 1, used | {a, b}, ext, pairs + [(a, b)])

    go(0, frozenset(), frozenset(), [])
    return out


def generate(N):
    classes = {3: {canonical(3, [])}}
    for n in range(3, N):
        seeds = list(classes[n]) + [((tuple(range(n))),)]  # rank-3 classes and the line U(2,n)
        found = set()
        for lines in seeds:
            for ext in extensions(n, lines):
                if rank3(n + 1, ext):
                    found.add(canonical(n + 1, ext))
        classes[n + 1] = found
    return classes


def order_key(lines):
    return (len(lines), tuple(sorted((-len(L) for L in lines))), lines)


def as_matroid(name, n, lines):
    els = [str(i + 1) for i in range(n)]
    return {"name": name, "elements": els, "lines": [[els[p] for p in L] for L in lines]}


F1_NAMES = ["F7", "F7-", "MK4", "U36", "AG23-e", "AG23", "Pappus", "NonPappus"]


def f1_forms():
    """Canonical forms of the F1 matroids with at most 9 elements, for isomorphism records."""
    out = {}
    for name in F1_NAMES:
        m = json.loads((CAMPAIGN / "matroids" / f"{name}.json").read_text(encoding="utf-8"))
        idx = {e: i for i, e in enumerate(m["elements"])}
        lines = [tuple(sorted(idx[e] for e in L)) for L in m["lines"]]
        n = len(m["elements"])
        out[(n, canonical(n, lines))] = (name, m, lines)
    return out


def iso_map(n, lines_a, lines_b):
    """A bijection sigma with sigma(lines_a) == lines_b, by brute force (n <= 9)."""
    target = apply(list(range(n)), lines_b)
    for sigma in permutations(range(n)):
        if apply(sigma, lines_a) == target:
            return list(sigma)
    return None


def main():
    N = int(next((a for a in sys.argv[1:] if a.isdigit()), 8))
    write = "--write" in sys.argv
    digest = hashlib.sha256((HERE / "generate.py").read_bytes()).hexdigest()
    classes = generate(N)
    f1 = f1_forms()
    catalog = {"schema": "gp-3p-catalog/v0", "generator": "campaigns/3p-matroids/catalog/generate.py",
               "generator_sha256": digest, "trust": "trusted (unchecked by GP)",
               "premise": "CATALOG-COMPLETE (OPEN): every simple rank-3 matroid on 3..%d elements is "
                          "isomorphic to exactly one entry" % N,
               "counts": {}, "entries": []}
    for n in range(3, N + 1):
        ordered = sorted(classes[n], key=order_key)
        catalog["counts"][str(n)] = len(ordered)
        for i, lines in enumerate(ordered, 1):
            name = f"C{n}-{i:02d}"
            entry = {"name": name, "n": n, "index": i, "lines": [list(L) for L in lines],
                     "aut": automorphisms(n, lines)}
            hit = f1.get((n, lines))
            if hit:
                f1name, m, f1lines = hit
                sigma = iso_map(n, list(lines), f1lines)  # catalog point i -> F1 element index sigma[i]
                entry["isomorphic_to"] = {"matroid": f1name,
                                          "map": {str(i + 1): m["elements"][sigma[i]] for i in range(n)}}
            catalog["entries"].append(entry)
            if write:
                mat = as_matroid(name, n, lines)
                mat["source"] = {"generator": catalog["generator"], "generator_sha256": digest,
                                 "catalog_index": [n, i], "trust": "trusted generator",
                                 "premise": "catalog completeness OPEN (CATALOG-COMPLETE)"}
                if hit:
                    mat["source"]["isomorphic_to"] = entry["isomorphic_to"]
                (CAMPAIGN / "matroids" / f"{name}.json").write_bytes(
                    (json.dumps(mat, indent=1, ensure_ascii=False) + "\n").encode("utf-8"))
    print("counts", catalog["counts"])
    if write:
        (HERE / "catalog.json").write_bytes((json.dumps(catalog, indent=1, ensure_ascii=False) + "\n").encode("utf-8"))
    return catalog


if __name__ == "__main__":
    main()
