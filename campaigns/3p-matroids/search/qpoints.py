import json, random, subprocess, sys
from pathlib import Path
from realize import *
random.seed(1)
GP = Path(__file__).resolve().parents[3].as_posix() + "/"  # the repo root
def enc_of(name):
    return json.loads(subprocess.run(["python", GP+"tools/encode-matroid.py", GP+f"campaigns/3p-matroids/matroids/{name}.json"], capture_output=True, text=True).stdout)
K = F(0)
out = {}
for name in sys.argv[1:]:
    mat = json.load(open(GP+f"campaigns/3p-matroids/matroids/{name}.json")); enc = enc_of(name)
    best = None
    for t in range(int(400)):
        r = search(K, mat, enc, tries=1, R=2 + t % 3)
        if not r: continue
        co = clear_denoms_Q(enc, r[1]); eqs, gs = check(K, enc, co)
        assert all(K.iszero(x) for x in eqs) and not any(K.iszero(x) for x in gs)
        bp = bad_primes(gs); sc = (sum(bp), max(abs(x[0].numerator) for x in co.values()))
        if best is None or sc < best[0]: best = (sc, co, bp)
    if best is None: print(name, "no Q point found"); continue
    pt = {v: str(x[0]) for v, x in best[1].items()}
    out[name] = {"point": pt, "bad_primes": sorted(best[2])}
    print(name, "bad primes", sorted(best[2]), "max coord", best[0][1])
json.dump(out, open("qpoints.json", "w"), indent=1)
