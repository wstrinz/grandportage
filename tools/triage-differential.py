"""Write reports/PHASE-3A-DIFFERENTIAL.json: the post-G2 §3.8 triage of the v0.37 oracle's
JC(2) and matroid inferences against the 3a profile. The triage itself is judgment recorded here;
this script checks it covers every inference and agrees with the oracle's clean/finding split.
"""
from collections import Counter
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
FIXTURES = ROOT / "oracle/checkout/fixtures"

TRIAGE = {
    # matroid
    "IM-ML8-BASE-EXT": ("finding", "inexpressible-3b", "claim over R by a square-class certificate; 3a scopes cannot separate R from C (field class, 3b)"),
    "IM-ML8-Q-BASE-EXT": ("finding", "inexpressible-3b", "a base-field-only EMPTY over Q is unstatable in 3a: a char-0 EMPTY claim covers every char-0 field, and no C1 certificate exists since ML8 is realizable over Q(sqrt -3)"),
    "IM-ML8-DESCENT": ("finding", "inexpressible-3b", "the NONEMPTY premise over C needs a number-field witness (3b)"),
    "IM-NF-SKIP-SAT": ("finding", "consistent-by-rule", "NONEMPTY moves tight->loose only (R2); the AGAINST step loose->tight is refused; models carry no polynomial data to execute"),
    "IM-U35-CLOSURE": ("finding", "consistent-by-rule", "3a has no image-closure relation; R3 never licenses NONEMPTY back from a closure"),
    "IM-ORIENT-TO-REAL": ("finding", "inexpressible-other", "combinatorial oriented-matroid model, no field"),
    "IM-MACLANE": ("clean", "inexpressible-other", "finite orientation exhaustion is a combinatorial certificate (census-style, Phase 4)"),
    "IM-FANO-CONTRAST": ("clean", "executed-agrees", "GP-FANO-C1: computed reach char 0 and every prime but 2 contains C (reports/PHASE-3A-SLICE.json)"),
    "IM-ML8-ASCEND": ("clean", "inexpressible-3b", "NONEMPTY over Q(sqrt -3) needs a number-field witness"),
    "IM-ML8-UP": ("clean", "inexpressible-3b", "frame-normalized realization over C needs a number-field witness"),
    "IM-U35-RANK": ("clean", "inexpressible-other", "PREDICATE claim along an image closure; no 3a kind"),
    "IM-FANO-NO-SAT": ("clean", "consistent-by-rule", "EMPTY moves loose->tight (R2): the unsaturated system's unit certificate empties the saturated one"),
    # jc2
    "INF-C08-HIST": ("finding", "inexpressible-3b", "square-class certificate over Q(sqrt 17)"),
    "INF-C20-HIST": ("finding", "inexpressible-3b", "square-class certificate over Q(sqrt 17)"),
    "INF-C08-CURRENT": ("clean", "inexpressible-3b", "square-class certificate over Q(sqrt 17)"),
    "INF-SLICEPHI": ("finding", "inexpressible-other", "PREDICATE along a necessary condition; no 3a kind"),
    "INF-SLICEPHI-KILL": ("clean", "consistent-by-rule", "EMPTY moves loose->tight (R2); unit certificate data not in the fixture"),
    "INF-SYZCOLL-DICT": ("clean", "inexpressible-other", "IDENTITY claim on a relaxation; campaign syzygy data"),
    "INF-SYZCOLL": ("clean", "inexpressible-campaign", "exact valuation collision certificate (campaign-op)"),
    "INF-KSYZ": ("clean", "consistent-by-rule", "EMPTY along an equivalence (R2 both ways); certificate data not in the fixture"),
    "INF-KSYZ-REV": ("clean", "inexpressible-other", "IDENTITY claim; campaign syzygy data"),
    "INF-POSSLICE": ("clean", "inexpressible-campaign", "nonzero-resultant certificate on an ordered slice (3b/campaign-op)"),
    "INF-G4-MONO": ("clean", "inexpressible-campaign", "nonzero-resultant certificate (campaign-op)"),
    "INF-A10-SURV": ("finding", "consistent-by-rule", "3a has no image-closure relation; NONEMPTY is never licensed back from a closure"),
    "INF-R9": ("clean", "inexpressible-campaign", "NONEMPTY by a campaign witness with no polynomial data"),
}


def main():
    fixture_of = {}
    problems = []
    for d in ("matroid", "jc2"):
        base = FIXTURES / d
        expect = json.loads((base / "expect.json").read_text(encoding="utf-8"))
        for line in (base / "graph.jsonl").read_text(encoding="utf-8").splitlines():
            if not line.strip() or line.startswith("#"):
                continue
            row = json.loads(line)
            if row.get("ev") != "inference":
                continue
            oracle = "clean" if row["id"] in expect["clean_inferences"] else "finding"
            fixture_of[row["id"]] = d
            if row["id"] not in TRIAGE:
                problems.append(f"untriaged {row['id']}")
            elif TRIAGE[row["id"]][0] != oracle:
                problems.append(f"{row['id']}: oracle says {oracle}")
    problems += [f"unknown {i}" for i in TRIAGE if i not in fixture_of]
    if problems:
        raise SystemExit("; ".join(problems))
    out = {"schema": "gp-3a-differential/v1", "authority": "post-G2 §3.8",
           "oracle": "v0.37.0 ac41557 (oracle/checkout)", "fixtures": ["fixtures/matroid", "fixtures/jc2"],
           "summary": ("No disagreements. The Fano contrast executes and agrees; other inferences are consistent "
                       "by the proved R2/R3 direction tables but carry no polynomial data to execute; the rest need "
                       "3b field classes or number fields, combinatorial certificates, or campaign operations. A "
                       "char-0 claim in 3a covers every char-0 field, so the base-field-only ML8 claims are not "
                       "statable in 3a at all (3b)."),
           "counts": dict(Counter(v[1] for v in TRIAGE.values())),
           "inferences": [{"id": i, "fixture": fixture_of[i], "oracle": TRIAGE[i][0], "triage": TRIAGE[i][1],
                           "note": TRIAGE[i][2]} for i in sorted(TRIAGE)]}
    (ROOT / "reports/PHASE-3A-DIFFERENTIAL.json").write_text(
        json.dumps(out, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
    print(json.dumps(out["counts"]))


if __name__ == "__main__":
    main()
