"""External search for the Fano realization fixtures of the 3a reach slice (post-G2 §3.6).

usage: python tools/search-fano-certificate.py [--out tmp/fano-search]
The fixtures it produced were taken into the corpus as GP-X413-X415 (Fano intake, 2026-10-03); its
output is provenance for that search and is never written over corpus cases.
Glue only (Addendum A1): sympy searches; GP's Lean checker replays and computes reach.

Encoding: points 1..7, lines 124 235 346 457 561 672 713. Points 1, 2, 3, 6 form a projective
frame, (1,0,0), (0,1,0), (0,0,1), (1,1,1); no three are collinear in the Fano plane. The other
points use affine charts p4 = (1, y4, z4), p5 = (x5, 1, z5), p7 = (1, y7, z7), which contain
the characteristic-2 realization. Equations: the seven incidence determinants. Guards: the
nonconstant determinants of the non-line triples that involve a chart point (nondegeneracy).
"""
import argparse
from itertools import combinations
import json
from pathlib import Path
import time

import sympy as sp

ROOT = Path(__file__).resolve().parents[1]
x5, y4, z4, z5, y7, z7 = sp.symbols("x5 y4 z4 z5 y7 z7")
VARS = [x5, y4, z4, z5, y7, z7]
POINTS = {1: (1, 0, 0), 2: (0, 1, 0), 3: (0, 0, 1), 6: (1, 1, 1),
          4: (1, y4, z4), 5: (x5, 1, z5), 7: (1, y7, z7)}
LINES = [(1, 2, 4), (2, 3, 5), (3, 4, 6), (4, 5, 7), (5, 6, 1), (6, 7, 2), (7, 1, 3)]
WITNESS_F2 = {x5: 0, y4: 1, z4: 0, z5: 1, y7: 0, z7: 1}


def det(triple):
    return sp.expand(sp.Matrix([POINTS[i] for i in triple]).det())


def text(poly):
    return str(sp.expand(poly)).replace("**", "^")


def system():
    eqs = [det(line) for line in LINES]
    lines = {tuple(sorted(l)) for l in LINES}
    guards = [det(t) for t in combinations(range(1, 8), 3)
              if t not in lines and set(t) & {4, 5, 7}]
    # A nonzero constant determinant is already nondegenerate; it adds no guard.
    guards = [g for g in guards if not g.is_number]
    return eqs, guards


def certificate(eqs):
    """Cofactors q with sum(q_i * eq_i) = 1 over Q, or None."""
    basis = sp.groebner(eqs, *VARS, order="lex", domain="QQ")
    if list(basis.exprs) != [1]:
        return None
    # The six linear incidences have distinct leading variables, so they form a lex Groebner
    # basis; reducing the remaining cubic by them leaves a constant r != 0.
    linear = [e for e in eqs if sp.Poly(e, *VARS).total_degree() == 1]
    cubic = [e for e in eqs if sp.Poly(e, *VARS).total_degree() > 1]
    assert len(cubic) == 1
    quotients, r = sp.reduced(cubic[0], linear, *VARS, order="lex")
    assert r.is_number and r != 0, r
    cof = {id(e): sp.expand(-q / r) for e, q in zip(linear, quotients)}
    cof[id(cubic[0])] = sp.Rational(1) / r
    q = [cof[id(e)] for e in eqs]
    assert sp.expand(sum(qi * ei for qi, ei in zip(q, eqs)) - 1) == 0
    return q, r


def case(case_id, title, situation, inputs, conclusion, verdict, reason):
    return {"schema_version": 1, "id": case_id, "seed": None, "title": title,
            "situation": situation, "inputs": inputs, "attempted_conclusion": conclusion,
            "expected": {"verdict": verdict, "reason": reason}, "scope_or_region": "SCOPE",
            "sources": [{"repository": "post-g2-handoff", "path": "docs/GP-0.50-POST-G2-HANDOFF.md",
                         "line": 263, "anchor": "**Fano cases (new, authorized).**"}],
            "provisional": "slice fixture; formal corpus intake at post-G2 §3.7"}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--out", default=str(ROOT / "tmp/fano-search"))
    out = Path(parser.parse_args().out)
    start = time.time()
    eqs, guards = system()
    found = certificate(eqs)
    elapsed = round(time.time() - start, 2)
    if found is None:
        raise SystemExit("certificate search failed: report it; do not weaken the case")
    q, r = found
    for g in guards:
        assert g.subs(WITNESS_F2) % 2 != 0, g
    for e in eqs:
        assert e.subs(WITNESS_F2) % 2 == 0, e
    base = {"variables": [str(v) for v in VARS], "generators": [text(e) for e in eqs],
            "guards": [text(g) for g in guards]}
    c1 = dict(base, cofactors=[text(x) for x in q])
    situation = ("Fano plane realization system: projective frame on points 1, 2, 3, 6; affine charts "
                 f"for points 4, 5, 7; seven incidence equations; {len(guards)} nondegeneracy guards.")
    fixtures = {
        "fano-c1-char0.json": case("GP-FANO-C1", "Fano plane is not realizable in characteristic 0",
            situation, dict(c1, characteristic=0), "Hold EMPTY in characteristic 0 by the C1 certificate.",
            "ACCEPT", "The rational unit certificate replays; its reach must exclude 2."),
        "fano-c1-char2.json": case("GP-FANO-C1-CHAR2", "Fano C1 certificate used in characteristic 2",
            situation, dict(c1, characteristic=2), "Hold EMPTY in characteristic 2 by the same certificate.",
            "REFUSE", "The certificate has denominator 2, so its reach excludes characteristic 2."),
        "fano-witness-f2.json": case("GP-FANO-F2", "Fano plane is realizable over F_2",
            situation, dict(base, point={str(v): str(WITNESS_F2[v]) for v in VARS}, characteristic=2),
            "Hold NONEMPTY at characteristic 2 by an F_2 witness.", "ACCEPT",
            "The witness satisfies every incidence and no guard vanishes modulo 2."),
    }
    out.mkdir(parents=True, exist_ok=True)
    for name, value in fixtures.items():
        (out / name).write_text(json.dumps(value, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({"search_seconds": elapsed, "remainder": str(r), "guards": len(guards),
                      "cofactors": [text(x) for x in q]}, indent=2))


if __name__ == "__main__":
    main()
