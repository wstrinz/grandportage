"""Encode a graph as its unit-distance system (Highway 61 Revisited G-4, for G-1 and G-2).

usage: python tools/encode-udg.py (<graph.json> | --g6 GRAPH6) [--gauge] [-o <encoding.json>]

The input is a graph on vertices 0, ..., n-1, either JSON
  {"name": "K4", "n": 4, "edges": [[0, 1], [0, 2], ...]}
or a graph6 string (--g6). The output is GP's `--system` JSON:

- variables x1, y1, x2, y2, ... (vertex i owns x{i+1}, y{i+1});
- one equation (x_i - x_j)^2 + (y_i - y_j)^2 - 1 per edge i < j, in lexicographic order;
- no constraint on non-edges: extra unit distances are allowed (M5 pitfall 4);
- all C(n, 2) distinctness guards (x_i - x_j)^2 + (y_i - y_j)^2 != 0, pairs i < j in order;
- no gauge by default. With --gauge, the first edge a < b is pinned by the equations x_a, y_a,
  x_b - 1, y_b, placed before the edge equations. A rotation and a translation move any point
  there and keep every squared distance, so no embedding is lost (GPBinding.UDG.udg_gauge_iff).

The system has a real point exactly when the graph has an injective unit-distance embedding into
EuclideanSpace R (Fin 2) (GPBinding.UDG.udg_frame_iff, over the Lean encoder
`GPProfile.UDG.Data.system`, which this script mirrors term for term). The output is deterministic,
and its SHA-256 over canonical JSON is the digest a claim binds.
"""
import argparse
import hashlib
import json
from pathlib import Path
import sys

SCHEMA = "gp-udg-encoding/v1"
PREMISE = {
    "name": "ENCODING-FRAME",
    "status": "OPEN",
    "theorem": "GPBinding.UDG.udg_frame_iff",
    "statement": "G has an injective unit-distance embedding into the Euclidean plane iff its unit-distance "
                 "system (edge equations, all pair guards, optional gauge) has a real point. Discharged for a "
                 "claim once the Lean encoder re-derives the claim's system."
}


def graph6_decode(s):
    """Vertices and edges (i < j) of a graph6 string (optional '>>graph6<<' header)."""
    s = s.strip()
    if s.startswith(">>graph6<<"):
        s = s[len(">>graph6<<"):]
    data = [ord(c) - 63 for c in s]
    if not data or any(d < 0 or d > 63 for d in data):
        raise ValueError("not a graph6 string")
    if data[0] < 63:
        n, rest = data[0], data[1:]
    elif len(data) > 1 and data[1] < 63:
        if len(data) < 4:
            raise ValueError("truncated graph6 size")
        n, rest = (data[1] << 12) | (data[2] << 6) | data[3], data[4:]
    else:
        if len(data) < 8:
            raise ValueError("truncated graph6 size")
        n = 0
        for d in data[2:8]:
            n = (n << 6) | d
        rest = data[8:]
    need = (n * (n - 1) // 2 + 5) // 6
    if len(rest) != need:
        raise ValueError(f"graph6 body has {len(rest)} bytes, expected {need}")
    bits = [(d >> (5 - k)) & 1 for d in rest for k in range(6)]
    edges, k = [], 0
    for j in range(1, n):
        for i in range(j):
            if bits[k]:
                edges.append([i, j])
            k += 1
    if any(bits[k:]):
        raise ValueError("graph6 padding bits are not zero")
    return n, edges


def canonical(graph):
    """Validate a simple graph; return n and its edges (i < j), sorted and deduplicated."""
    n = graph["n"]
    if not isinstance(n, int) or n < 0:
        raise ValueError("n must be a nonnegative integer")
    edges = set()
    for e in graph["edges"]:
        if len(e) != 2 or not all(isinstance(v, int) for v in e):
            raise ValueError(f"edge {e} must be two integers")
        i, j = e
        if not (0 <= i < n and 0 <= j < n):
            raise ValueError(f"edge {e} is out of range")
        if i == j:
            raise ValueError(f"edge {e} is a loop")
        edges.add((min(i, j), max(i, j)))
    return n, sorted(edges)


# Polynomials: {exponent tuple: int}, over the 2n variables of one encoding.
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


def polys(n, edges, gauge=False):
    """The encoding's variable names, equations and guards as polynomial dicts (the Lean encoder's
    `Data.eqPolys` and `Data.guardPolys`, in the same order)."""
    nv = 2 * n
    names = [f"{c}{i + 1}" for i in range(n) for c in "xy"]
    const = lambda k: {(0,) * nv: k} if k else {}
    var = lambda v: {tuple(1 if i == v else 0 for i in range(nv)): 1}

    def sq(i, j):
        dx = add(var(2 * i), var(2 * j), -1)
        dy = add(var(2 * i + 1), var(2 * j + 1), -1)
        return add(mul(dx, dx), mul(dy, dy))

    eqs = []
    if gauge and edges:
        a, b = edges[0]
        eqs += [var(2 * a), var(2 * a + 1), add(var(2 * b), const(1), -1), var(2 * b + 1)]
    eqs += [add(sq(i, j), const(1), -1) for i, j in edges]
    guards = [sq(i, j) for i in range(n) for j in range(i + 1, n)]
    return names, eqs, guards


def encode(graph, gauge=False):
    n, edges = canonical(graph)
    names, eqs, guards = polys(n, edges, gauge)
    body = {"schema": SCHEMA, "graph": {"name": graph.get("name"), "n": n, "edges": [list(e) for e in edges]},
            "premise": PREMISE, "gauge": list(edges[0]) if gauge and edges else None,
            "variables": names, "equations": [show(p, names) for p in eqs],
            "nonzero": [show(p, names) for p in guards]}
    body["digest"] = hashlib.sha256(json.dumps(body, sort_keys=True, separators=(",", ":"),
                                               ensure_ascii=False).encode("utf-8")).hexdigest()
    return body


def main():
    ap = argparse.ArgumentParser()
    src = ap.add_mutually_exclusive_group(required=True)
    src.add_argument("graph", nargs="?")
    src.add_argument("--g6")
    ap.add_argument("--gauge", action="store_true", help="pin the first edge at (0, 0), (1, 0)")
    ap.add_argument("-o", "--output")
    args = ap.parse_args()
    if args.g6:
        n, edges = graph6_decode(args.g6)
        graph = {"name": args.g6, "n": n, "edges": edges}
    else:
        graph = json.loads(Path(args.graph).read_text(encoding="utf-8"))
    out = json.dumps(encode(graph, args.gauge), indent=2, ensure_ascii=False) + "\n"
    if args.output:
        Path(args.output).write_bytes(out.encode("utf-8"))
    else:
        sys.stdout.write(out)
    return 0


if __name__ == "__main__":
    sys.exit(main())
