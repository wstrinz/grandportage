"""Untrusted proposer for census `extcover` receipts (HW61 G-5).

For a base graph H on n vertices, a degree k and a pattern list, the extensions of H are the graphs
H + v where the new vertex v (numbered n) is adjacent to exactly the k-set S of H's vertices. For
each S in the order of the Lean generator `GPCensus.Extension.combos n k` this script proposes one
hit: a pattern index p and an injective map from p's vertices into 0..n that sends every pattern
edge to an edge and every required non-edge to a non-edge. The lowest pattern index wins, so with
the forbidden graphs listed before the TU gadgets an F-hit is preferred. Nothing here is trusted:
the Lean checker re-verifies every hit and generates the list of S itself.

usage: gp50_extcover.py hits <base g6> <k> <patterns.json> <out.hits>
       gp50_extcover.py run <bases.g6> <k> <patterns.json> <patterns sha256> <outdir> [--batch B]

`hits` writes one base's hits file (exit 3 when some extension has no hit; the neighbourhoods are
printed on stderr). `run` refuses a patterns file whose SHA-256 differs from the pin, proposes hits
for every base, builds one NONE claim per base (scope [n + 1]) with an `extcover` certificate, runs
the census runner on ledgers of B claims and writes `summary.json`: per-base survivors, witness
counts per pattern and hold status, and the runner's wall time and peak working set.
"""
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[1]
RUNNER = ROOT / ("census/.lake/build/bin/gp_census" + (".exe" if os.name == "nt" else ""))


def g6decode(s):
    s = s.strip()
    d = [ord(c) - 63 for c in s]
    n = d[0]
    if n >= 63:
        raise ValueError("graph6 with n >= 63 is not supported")
    bits = []
    for x in d[1:]:
        bits += [(x >> (5 - i)) & 1 for i in range(6)]
    edges, t = [], 0
    for j in range(1, n):
        for i in range(j):
            if bits[t]:
                edges.append((i, j))
            t += 1
    return n, edges


def combos(n, k, memo={}):
    """The Lean generator's order: combos (n+1) (k+1) = combos n (k+1) ++ map (n :: ·) (combos n k)."""
    if k == 0:
        return [[]]
    if n == 0:
        return []
    if (n, k) not in memo:
        memo[(n, k)] = combos(n - 1, k) + [[n - 1] + t for t in combos(n - 1, k - 1)]
    return memo[(n, k)]


def monos(pv, padj, pnon, adj, n):
    """Injective maps of pattern vertices `pv` into range(n) sending edges to edges and required
    non-edges to non-edges. `padj`/`pnon` give each pattern vertex's neighbours / required
    non-neighbours."""
    order, seen = [], set()
    for s in pv:  # BFS order: each vertex's candidates are constrained by mapped neighbours
        if s in seen:
            continue
        queue = [s]
        seen.add(s)
        while queue:
            u = queue.pop(0)
            order.append(u)
            for w in sorted(padj[u]):
                if w in pv and w not in seen:
                    seen.add(w)
                    queue.append(w)
    full = (1 << n) - 1
    phi = {}

    def rec(i, used):
        if i == len(order):
            yield dict(phi)
            return
        u = order[i]
        cand = full & ~used
        for w in padj[u]:
            if w in phi:
                cand &= adj[phi[w]]
        for w in pnon[u]:
            if w in phi:
                cand &= ~adj[phi[w]]
        while cand:
            low = cand & -cand
            cand ^= low
            phi[u] = low.bit_length() - 1
            yield from rec(i + 1, used | low)
            del phi[u]

    yield from rec(0, 0)


def hit_table(n, edges, k, patterns):
    """For each pattern and each choice of the pattern vertex x placed on the new vertex (or none),
    the demands on S: T (x's neighbours, must lie in S) and A (x's required non-neighbours, must
    avoid S), with one witness map per (T, A). Keyed by T."""
    adj = [0] * n
    for a, b in edges:
        adj[a] |= 1 << b
        adj[b] |= 1 << a
    table = {}
    for p, pat in enumerate(patterns):
        m = pat["n"]
        padj = {u: set() for u in range(m)}
        pnon = {u: set() for u in range(m)}
        for a, b in pat["edges"]:
            padj[a].add(b)
            padj[b].add(a)
        for a, b in pat.get("non_edges", []):
            pnon[a].add(b)
            pnon[b].add(a)
        for x in [None] + list(range(m)):
            if x is not None and len(padj[x]) > k:
                continue
            pv = [u for u in range(m) if u != x]
            best = {}
            for phi in monos(pv, {u: padj[u] - {x} for u in range(m)}, {u: pnon[u] - {x} for u in range(m)},
                             adj, n):
                T = 0 if x is None else sum(1 << phi[w] for w in padj[x])
                A = 0 if x is None else sum(1 << phi[w] for w in pnon[x])
                if (T, A) not in best:
                    best[(T, A)] = [n if u == x else phi[u] for u in range(m)]
            for (T, A), mp in best.items():
                table.setdefault(T, []).append((p, A, mp))
    for T in table:
        table[T].sort()
    return table


def find_hits(n, edges, k, patterns):
    table = hit_table(n, edges, k, patterns)
    hits, survivors = [], []
    for S in combos(n, k):
        smask = sum(1 << s for s in S)
        best = None
        sub = smask
        while True:  # every subset T of S, including the empty set
            for p, A, mp in table.get(sub, ()):
                if A & smask == 0:
                    if best is None or p < best[0]:
                        best = (p, mp)
                    break
            if sub == 0:
                break
            sub = (sub - 1) & smask
        if best is None:
            survivors.append(S)
            hits.append((S, None, None))
        else:
            hits.append((S, best[0], best[1]))
    return hits, survivors


def write_hits(path, hits):
    with open(path, "w", encoding="utf-8", newline="\n") as f:
        for S, p, mp in hits:
            tail = ";" if p is None else str(p) + ";" + ",".join(map(str, mp))
            f.write(",".join(map(str, S)) + ";" + tail + "\n")


def claim(key, g6, k, patterns, hits_path, pins):
    n, _ = g6decode(g6)
    spec = {"base_g6": g6, "k": k, "patterns": patterns}
    return {"key": key, "kind": "NONE", "colors": 1, "scope": [n + 1], "extension": dict(spec, **pins),
            "certificate": dict(spec, type="extcover", n=n + 1, hits_file=str(hits_path))}


def run_ledger(path):
    """Run the census runner on a ledger: its claims, wall seconds and peak working set in MB."""
    start = time.time()
    try:
        import psutil  # optional: priority and peak memory; CI runs without it
    except ImportError:
        run = subprocess.run([str(RUNNER), "run", str(path)], capture_output=True)
        if run.returncode != 0:
            raise RuntimeError(run.stderr.decode())
        return json.loads(run.stdout)["claims"], time.time() - start, 0.0
    proc = psutil.Popen([str(RUNNER), "run", str(path)], stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    try:
        proc.nice(psutil.BELOW_NORMAL_PRIORITY_CLASS if os.name == "nt" else 10)
    except psutil.Error:
        pass
    peak = 0
    while proc.poll() is None:
        try:
            info = proc.memory_info()
            peak = max(peak, getattr(info, "peak_wset", info.rss))
        except psutil.Error:
            pass
        time.sleep(0.05)
    out, err = proc.communicate()
    if proc.returncode != 0:
        raise RuntimeError(err.decode())
    return json.loads(out)["claims"], time.time() - start, peak / 2 ** 20


def run(bases_path, k, pats_path, pin, outdir, batch=10):
    raw = Path(pats_path).read_bytes()
    if hashlib.sha256(raw).hexdigest() != pin:
        raise SystemExit(f"pattern-hash mismatch: {pats_path} is not {pin}")
    pats = json.loads(raw)
    bases = [l for l in Path(bases_path).read_text(encoding="utf-8").splitlines() if l.strip()]
    outdir = Path(outdir)
    outdir.mkdir(parents=True, exist_ok=True)
    pins = {"patterns_sha256": pin, "bases_sha256": hashlib.sha256(Path(bases_path).read_bytes()).hexdigest()}
    rows, claims = [], []
    for i, g6 in enumerate(bases):
        t0 = time.time()
        n, edges = g6decode(g6)
        hits, survivors = find_hits(n, edges, k, pats)
        hp = outdir / f"b{i:03d}.hits"
        write_hits(hp, hits)
        counts = {}
        for _, p, _ in hits:
            if p is not None:
                name = pats[p].get("name", f"#{p}")
                counts[name] = counts.get(name, 0) + 1
        rows.append({"key": i, "g6": g6, "g6_sha256": hashlib.sha256(g6.encode()).hexdigest(),
                     "extensions": len(hits), "survivors": survivors, "per_pattern": counts,
                     "hits_sha256": hashlib.sha256(hp.read_bytes()).hexdigest(),
                     "search_seconds": round(time.time() - t0, 2)})
        claims.append(claim(i, g6, k, pats, hp, pins))
    runs = []
    for j in range(0, len(claims), batch):
        lp = outdir / f"ledger-{j // batch:03d}.json"
        lp.write_text(json.dumps({"claims": claims[j:j + batch]}), encoding="utf-8", newline="\n")
        out, wall, peak = run_ledger(lp)
        for c in out:
            rows[c["key"]].update(held=c["held"], reach=c["reach"])
        runs.append({"ledger": lp.name, "claims": len(out), "wall_seconds": round(wall, 2), "peak_mb": round(peak, 1)})
    summary = {"bases": str(bases_path), "k": k, "patterns_sha256": pin, "claims": len(rows),
               "held": sum(bool(r.get("held")) for r in rows), "extensions": sum(r["extensions"] for r in rows),
               "survivors": sum(len(r["survivors"]) for r in rows), "runner": runs, "rows": rows}
    (outdir / "summary.json").write_text(json.dumps(summary, indent=1) + "\n", encoding="utf-8", newline="\n")
    return summary


def main(argv):
    if len(argv) == 6 and argv[1] == "hits":
        pats = json.load(open(argv[4], encoding="utf-8"))
        n, edges = g6decode(argv[2])
        hits, survivors = find_hits(n, edges, int(argv[3]), pats)
        write_hits(argv[5], hits)
        counts = {}
        for _, p, _ in hits:
            if p is not None:
                name = pats[p].get("name", f"#{p}")
                counts[name] = counts.get(name, 0) + 1
        print(json.dumps({"extensions": len(hits), "survivors": len(survivors), "per_pattern": counts}))
        if survivors:
            print(json.dumps(survivors), file=sys.stderr)
            return 3
        return 0
    if len(argv) >= 7 and argv[1] == "run":
        batch = int(argv[argv.index("--batch") + 1]) if "--batch" in argv else 10
        s = run(argv[2], int(argv[3]), argv[4], argv[5], argv[6], batch)
        print(json.dumps({key: s[key] for key in ("claims", "held", "extensions", "survivors", "runner")}))
        return 0 if s["held"] == s["claims"] else 3
    print(__doc__, file=sys.stderr)
    return 2


if __name__ == "__main__":
    sys.exit(main(sys.argv))
