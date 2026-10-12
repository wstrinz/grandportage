"""Encode a simple rank-3 matroid as a 3a realization system (post-G3a handoff §4.3).

usage: python tools/encode-matroid.py <matroid.json> [-o <encoding.json>]

The input names the ground set and the lines (maximal dependent flats with at least three points):
  {"name": "F7", "elements": ["1", ..., "7"], "lines": [["1", "2", "4"], ...]}

Each element becomes a column (x_i, y_i, z_i). The non-bases (3-subsets of a line) give the
equations det = 0 and the bases give the guards det != 0, so the system is nonempty over a field
K exactly when M is realizable over K, given one normalization: a frame. The first basis in
lexicographic order is fixed to e1, e2, e3 and, when one exists, the first later element in general
position with it to (1, 1, 1). That a realization exists iff a framed one does (PGL3 acts
transitively on frames) is the named premise ENCODING-FRAME, OPEN until discharged in Lean.

The output is deterministic, and its SHA-256 over canonical JSON is the digest every claim binds.
"""
import argparse
from itertools import combinations
import hashlib
import json
from pathlib import Path
import sys

SCHEMA = "gp-matroid-encoding/v1"
PREMISE = {
    "name": "ENCODING-FRAME",
    "status": "OPEN",
    "statement": "M is realizable over K iff the framed system is nonempty over K: a realization can be "
                 "moved by an element of PGL3(K) so that the frame columns are e1, e2, e3 (and 1, 1, 1)."
}


def canonical(matroid):
    """Validate a simple rank-3 matroid given by its lines; return it in canonical order."""
    elements = [str(e) for e in matroid["elements"]]
    if len(set(elements)) != len(elements):
        raise ValueError("elements must be distinct")
    index = {e: i for i, e in enumerate(elements)}
    lines = []
    for line in matroid["lines"]:
        pts = sorted({index[str(p)] for p in line})
        if len(pts) != len(line) or len(pts) < 3:
            raise ValueError(f"line {line} must list at least three distinct elements")
        lines.append(pts)
    lines.sort()
    for a, b in combinations(lines, 2):
        if len(set(a) & set(b)) > 1:
            raise ValueError("two lines share two points: not a simple rank-3 matroid")
    nonbases = {t for line in lines for t in combinations(line, 3)}
    if all(t in nonbases for t in combinations(range(len(elements)), 3)):
        raise ValueError("no basis: rank is below 3")
    return {"name": matroid["name"], "elements": elements,
            "lines": [[elements[i] for i in line] for line in lines]}, nonbases


# Polynomials: {exponent tuple: int}, over the variable list of one encoding.
def add(p, q, sign=1):
    r = dict(p)
    for m, c in q.items():
        r[m] = r.get(m, 0) + sign * c
        if r[m] == 0:
            del r[m]
    return r


def mul(p, q):
    r = {}
    for m1, c1 in p.items():
        for m2, c2 in q.items():
            m = tuple(a + b for a, b in zip(m1, m2))
            r[m] = r.get(m, 0) + c1 * c2
            if r[m] == 0:
                del r[m]
    return r


def det3(cols):
    (a, b, c), (d, e, f), (g, h, i) = cols  # columns; det of the 3x3 with these columns
    t1 = mul(a, add(mul(e, i), mul(h, f), -1))
    t2 = mul(d, add(mul(b, i), mul(h, c), -1))
    t3 = mul(g, add(mul(b, f), mul(e, c), -1))
    return add(add(t1, t2, -1), t3)


def show(p, names):
    if not p:
        return "0"
    terms = sorted(p.items(), key=lambda mc: (-sum(mc[0]), [-e for e in mc[0]]))
    out = ""
    for k, (m, c) in enumerate(terms):
        factors = [n if e == 1 else f"{n}^{e}" for n, e in zip(names, m) if e]
        body = "*".join(factors)
        mag = abs(c)
        text = body if mag == 1 and body else (f"{mag}*{body}" if body else str(mag))
        out += (("-" if c < 0 else "") if k == 0 else (" - " if c < 0 else " + ")) + text
    return out


def encode(matroid):
    m, nonbases = canonical(matroid)
    n = len(m["elements"])
    bases = [t for t in combinations(range(n), 3) if t not in nonbases]
    base = bases[0]
    fourth = next((j for j in range(n) if j not in base and
                   all(t in bases for t in (tuple(sorted(s + (j,))) for s in combinations(base, 2)))), None)
    frame = list(base) + ([fourth] if fourth is not None else [])
    free = [j for j in range(n) if j not in frame]
    names = [f"{c}{j + 1}" for j in free for c in "xyz"]
    nv = len(names)
    const = lambda k: {(0,) * nv: k} if k else {}
    var = lambda v: {tuple(1 if i == v else 0 for i in range(nv)): 1}
    fixed = {base[0]: (1, 0, 0), base[1]: (0, 1, 0), base[2]: (0, 0, 1)}
    if fourth is not None:
        fixed[fourth] = (1, 1, 1)
    cols = {}
    for j in range(n):
        if j in fixed:
            cols[j] = tuple(const(k) for k in fixed[j])
        else:
            v = 3 * free.index(j)
            cols[j] = (var(v), var(v + 1), var(v + 2))
    equations, nonzero = [], []
    for t in combinations(range(n), 3):
        d = det3([cols[j] for j in t])
        if t in nonbases:
            if not d:
                continue  # identically zero: no condition
            if all(sum(mo) == 0 for mo in d):
                raise ValueError(f"non-basis {t} is a frame basis")
            equations.append(show(d, names))
        else:
            if not d:
                raise ValueError(f"basis {t} has identically zero determinant")
            if all(sum(mo) == 0 for mo in d):
                continue  # a nonzero constant: no condition
            nonzero.append(show(d, names))
    body = {"schema": SCHEMA, "matroid": m, "premise": PREMISE,
            "frame": [m["elements"][j] for j in frame], "variables": names,
            "equations": equations, "nonzero": nonzero}
    body["digest"] = hashlib.sha256(json.dumps(body, sort_keys=True, separators=(",", ":"),
                                               ensure_ascii=False).encode("utf-8")).hexdigest()
    return body


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("matroid")
    ap.add_argument("-o", "--output")
    args = ap.parse_args()
    out = json.dumps(encode(json.loads(Path(args.matroid).read_text(encoding="utf-8"))), indent=2,
                     ensure_ascii=False) + "\n"
    if args.output:
        Path(args.output).write_bytes(out.encode("utf-8"))
    else:
        sys.stdout.write(out)
    return 0


if __name__ == "__main__":
    sys.exit(main())
