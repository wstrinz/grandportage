import json, random, sys
from realize import *
from qpoints_lib import enc_of, GP
random.seed(2)
IRR = {2: [(1,), (1, 1, 1), (1, 1, 0, 1), (1, 1, 0, 0, 1), (1, 0, 1, 0, 0, 1)], 3: [(1,), (1, 0, 1), (1, 2, 0, 1)], 5: [(1,), (3, 0, 1)], 7: [(1,), (1, 0, 1)], 11: [(1,), (1, 0, 1)], 13: [(1,), (2, 0, 1)]}
res = {}
for job in sys.argv[1:]:
    name, p = job.split(":"); p = int(p)
    mat = json.load(open(GP+f"campaigns/3p-matroids/matroids/{name}.json")); enc = enc_of(name)
    for m in IRR[p]:
        K = F(p, m)
        r = search(K, mat, enc, tries=6000)
        if r:
            pt = {v: K.tostr(x) for v, x in r[1].items()}
            res[job] = {"p": p, "m": list(m), "point": pt}
            print(job, "point over F_%d^%d" % (p, max(K.k, 1)), "m =", m); break
    else:
        print(job, "NO point found up to degree", len(IRR[p][-1]) - 1)
old = {}
try: old = json.load(open("fpoints.json"))
except Exception: pass
old.update(res); json.dump(old, open("fpoints.json", "w"), indent=1)
