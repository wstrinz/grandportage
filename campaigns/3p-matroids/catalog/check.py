"""Independent cross-check of catalog.json (evidence for CATALOG-COMPLETE, not a proof).

1. Each entry is a simple rank-3 matroid (lines of size >= 3 meeting pairwise in <= 1 point,
   not all points on one line), and no two entries of the same size are isomorphic.
2. Orbit counting: the number of labelled simple rank-3 matroids on [n], counted directly,
   equals the sum of n!/|Aut(M)| over the catalog entries on n points.  A missing class would
   make the catalog sum too small.

The direct count does not use the generator's extension step: it builds every linear space on
[n] by choosing the line through the least uncovered pair, so each is built exactly once.
"""
from itertools import combinations
from fractions import Fraction
import json
from math import factorial
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parent))
from generate import canonical  # noqa: E402

HERE = Path(__file__).resolve().parent


def labelled_count(n):
    """Labelled linear spaces on [n] with no line through all n points."""
    pairs = [(a, b) for a in range(n) for b in range(a + 1, n)]
    bit = {p: 1 << i for i, p in enumerate(pairs)}
    full = (1 << len(pairs)) - 1

    def pbits(S):
        m = 0
        for a, b in combinations(sorted(S), 2):
            m |= bit[(a, b)]
        return m

    total = 0

    def go(cov, big):
        nonlocal total
        if cov == full:
            total += not big
            return
        a, b = next(p for p in pairs if not cov & bit[p])
        # the line through {a, b}: {a, b} plus any set T whose pairs with a, b and inside T are uncovered
        cand = [c for c in range(n) if c not in (a, b) and not cov & (bit[tuple(sorted((a, c)))] |
                                                                      bit[tuple(sorted((b, c)))])]

        def ext(i, T, m):
            if i == len(cand):
                L = {a, b} | set(T)
                go(cov | m, big or len(L) == n)
                return
            ext(i + 1, T, m)
            c = cand[i]
            add = pbits({a, b, c})
            for t in T:
                add |= bit[tuple(sorted((t, c)))]
            if not cov & add & ~m and all(not cov & bit[tuple(sorted((t, c)))] for t in T):
                ext(i + 1, T + [c], m | add)

        ext(0, [], bit[(a, b)])

    go(0, False)
    return total


def aut_brute(n, lines):
    """|Aut(M)| by exhaustive backtracking over bijections (independent of the generator's
    invariant pruning): a bijection is an automorphism iff it maps every line onto a line."""
    L = {frozenset(l) for l in lines}
    closing = {i: [l for l in L if max(l) == i] for i in range(n)}
    count = 0

    def go(i, sigma, used):
        nonlocal count
        if i == n:
            count += 1
            return
        for q in range(n):
            if q in used:
                continue
            sigma[i] = q
            if all(frozenset(sigma[p] for p in l) in L for l in closing[i]):
                go(i + 1, sigma, used | {q})
        sigma[i] = None

    go(0, [None] * n, frozenset())
    return count


def main():
    cat = json.loads((HERE / "catalog.json").read_text(encoding="utf-8"))
    ok = True
    by_n = {}
    for e in cat["entries"]:
        n, lines = e["n"], [tuple(L) for L in e["lines"]]
        simple = all(len(L) >= 3 for L in lines) and all(len(set(A) & set(B)) <= 1 for A, B in combinations(lines, 2))
        rank3 = not any(len(L) == n for L in lines)
        if not (simple and rank3):
            print("BAD entry", e["name"]); ok = False
        by_n.setdefault(n, []).append((e, canonical(n, lines)))
    for n, es in sorted(by_n.items()):
        forms = [f for _, f in es]
        distinct = len(set(forms)) == len(forms)
        auts = [aut_brute(n, e["lines"]) for e, _ in es]
        same_aut = auts == [e["aut"] for e, _ in es]
        orbit_sum = sum(Fraction(factorial(n), a) for a in auts)
        direct = labelled_count(n)
        print(f"n={n}: entries {len(es)}, pairwise non-isomorphic {distinct}, "
              f"generator |Aut| agrees {same_aut}, sum n!/|Aut| = {orbit_sum}, labelled count = {direct}, match {orbit_sum == direct}")
        ok &= distinct and same_aut and orbit_sum == direct
    # 3. Each isomorphism record maps the entry's lines exactly onto the F1 matroid's lines.
    for e in cat["entries"]:
        iso = e.get("isomorphic_to")
        if not iso:
            continue
        f1 = json.loads((HERE.parent / "matroids" / f"{iso['matroid']}.json").read_text(encoding="utf-8"))
        image = sorted(sorted(iso["map"][str(p + 1)] for p in L) for L in e["lines"])
        good = (image == sorted(sorted(L) for L in f1["lines"]) and
                sorted(iso["map"].values()) == sorted(f1["elements"]))
        print(f"{e['name']} -> {iso['matroid']}: isomorphism {'verified' if good else 'FAILS'}")
        ok &= good
    print("CHECK", "PASS" if ok else "FAIL")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
