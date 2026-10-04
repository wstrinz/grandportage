"""Write reports/PHASE-3A-EXPRESSIVENESS.json: every profile case's owner and outcome, and the A5
convergence summary of the 3a corpus run (post-G2 §3.7, Addendum A §5).

usage: python tools/gen-3a-expressiveness.py
Reads corpus/GATE-OWNERS.json and reports/PHASE-3A-SAFETY.json, and runs the 3a corpus once more
with the binder receipt (reports/PHASE-3A-BINDER.json) to count theorem warrants.
"""
from collections import Counter
import json
from pathlib import Path
import subprocess

EXE_SUFFIX = ".exe" if __import__("os").name == "nt" else ""
ROOT = Path(__file__).resolve().parents[1]
RUNNER = ROOT / ("profile/.lake/build/bin/gp_corpus_run" + EXE_SUFFIX)


def main():
    owners = {r["id"]: r for r in json.loads((ROOT / "corpus/GATE-OWNERS.json").read_text(encoding="utf-8"))["cases"]}
    safety = json.loads((ROOT / "reports/PHASE-3A-SAFETY.json").read_text(encoding="utf-8"))
    rows = []
    for c in safety["cases"]:
        base = c["id"].split("[")[0]
        rows.append({"id": c["id"], "owner": owners.get(base, {}).get("owner"), "expected": c["expected"],
                     "observed": c["observed"], "mechanism": c.get("mechanism", []),
                     "instantiated": c.get("instantiated", False),
                     "field_strengthened": c.get("field_strengthened")})
    by_owner = {}
    for r in rows:
        outcome = ("loss" if r["observed"] == "EXPRESSIVENESS_LOSS" else
                   "false ACCEPT" if r["observed"] == "ACCEPT" and r["expected"] != "ACCEPT" else
                   "agree" if r["observed"] == r["expected"] else "disagree")
        by_owner.setdefault(r["owner"], Counter())[outcome] += 1

    run = json.loads(subprocess.run(
        [str(RUNNER), str(ROOT), str(ROOT / "profile/slice/corpus-3a.json"), "--binder",
         str(ROOT / "reports/PHASE-3A-BINDER.json")], check=True, capture_output=True, text=True,
        encoding="utf-8").stdout)
    accepted = [c for c in run["cases"] if c.get("observed") == "ACCEPT"]
    held = [i for c in accepted for i in c["items"] if i["key"] in c["requested"] and i["held"]]
    warranted = [c["id"] for c in run["cases"] if any(t["supported"] for t in c.get("theorem_warrants", []))]
    convergence = {
        "accepting_rows": len(accepted),
        "held_requested_claims": len(held),
        "held_by_kind": dict(Counter(i["kind"] for i in held)),
        "held_by_support": dict(Counter(i["support"] for i in held)),
        "rows_with_widening": sum(1 for c in run["cases"] if c.get("widened")),
        "rows_with_theorem_warrants": warranted,
        "binder_refused": run.get("binder_refused"),
    }
    out = {"schema": "gp-3a-expressiveness/v2", "source": "corpus/GATE-OWNERS.json, reports/PHASE-3A-SAFETY.json",
           "outcomes_by_owner": {k: dict(v) for k, v in sorted(by_owner.items(), key=lambda kv: str(kv[0]))},
           "convergence": convergence, "cases": rows}
    (ROOT / "reports/PHASE-3A-EXPRESSIVENESS.json").write_text(json.dumps(out, indent=2, ensure_ascii=False) + "\n",
                                                               encoding="utf-8", newline="\n")
    print(json.dumps({"outcomes_by_owner": out["outcomes_by_owner"], "convergence": convergence}, indent=1))


if __name__ == "__main__":
    main()
