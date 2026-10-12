import json, re
import sympy as sp
from maproute import build, D
R = D + "receipts/"
def w(n, o): json.dump(o, open(R + n, "w", newline="\n"), indent=1)
Q = json.load(open("qpoints.json")); FP = json.load(open("fpoints.json"))
plan = {"MK4": [], "U36": [2, 3, 5, 7], "Pappus": [2, 3, 5], "Desargues": [2, 3, 5], "AG23": [3], "AG23-e": [3], "PG23": [3]}
cmds = []
for M, primes in plan.items():
    if M in Q:
        S = ",".join(map(str, Q[M]["bad_primes"]))
        w(f"{M}-point-q.json", {"certificate": {"type": "point", "point": Q[M]["point"]}})
        w(f"{M}-bridge-q.json", {"rule": {"type": "bridge"}, "premises": [f"{M}-nonempty-q"]})
        cmds += [f'claim {M}-nonempty-q --matroid {M} --kind NONEMPTY --outside "{S}"', f"submit {M}-nonempty-q $R/{M}-point-q.json",
                 f'claim {M}-in-chi --matroid {M} --kind NOT_IN_IDEAL --target 1 --outside "{S}"', f"submit {M}-in-chi $R/{M}-bridge-q.json"]
    for p in primes:
        job = f"{M}:{p}"
        if job not in FP: cmds.append(f"# MISSING {job}"); continue
        fp = FP[job]
        if len(fp["m"]) == 1:  # prime field: point + bridge
            pt = {v: str(int(sp.sympify(s.replace("^", "**")) if s != "0" else 0) % p) for v, s in fp["point"].items()}
            w(f"{M}-point-f{p}.json", {"certificate": {"type": "point", "point": pt, "characteristic": p}})
            w(f"{M}-bridge-{p}.json", {"rule": {"type": "bridge"}, "premises": [f"{M}-nonempty-{p}"]})
            cmds += [f"claim {M}-nonempty-{p} --matroid {M} --kind NONEMPTY --char {p}", f"submit {M}-nonempty-{p} $R/{M}-point-f{p}.json",
                     f"claim {M}-in-chi-{p} --matroid {M} --kind NOT_IN_IDEAL --target 1 --char {p}", f"submit {M}-in-chi-{p} $R/{M}-bridge-{p}.json"]
        else:
            if M == "U36" and p == 2: continue  # held already
            tag = f"F{p}^{len(fp['m'])-1}"
            build(job)
            cmds += [f"claim {M}-in-chi-{p} --matroid {M} --kind NOT_IN_IDEAL --target 1 --char {p}", f"submit {M}-in-chi-{p} $R/{M}-map-{tag}.json"]
            src = f"src-{tag}"
            if src not in " ".join(cmds) and tag != "F2^2":
                cmds[-2:-2] = [f"claim {src} --system $C/systems/{tag}.json --kind NOT_IN_IDEAL --target 1 --char {p}", f"submit {src} $R/{tag}-proper.json"]
open("real_cmds.txt", "w").write("\n".join(cmds) + "\n")
print("\n".join(cmds))
