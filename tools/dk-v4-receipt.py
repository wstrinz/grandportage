#!/usr/bin/env python3
"""Write reports/DK-V4-RECEIPT.json: what GP held for the DK V4 slice, bound by digests.

The data (DK's type files, the n = 19 certificate, CNF and LRAT proof) stay in the private harvest
(corpus/harvest/dk-v4). The receipt binds them by SHA-256, with the verdicts the census runner
returned and the premises each claim carries.
"""
import hashlib
import importlib.util
import json
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location("dk_v4", ROOT / "tools/dk_v4.py")
dk = importlib.util.module_from_spec(spec)
spec.loader.exec_module(dk)
H = dk.HARVEST


def sha(path_or_bytes):
    data = path_or_bytes if isinstance(path_or_bytes, bytes) else Path(path_or_bytes).read_bytes()
    return hashlib.sha256(data).hexdigest()


def canon_json(obj):
    return json.dumps(obj, sort_keys=True, separators=(",", ":")).encode("utf-8")


def main(difftests):
    run19 = H / "run19"
    v19 = json.loads((run19 / "n19-verdict.json").read_text(encoding="utf-8"))
    cert19 = json.loads((run19 / "n19-cert.json").read_text(encoding="utf-8"))
    head = next(l for l in (run19 / "n19.cnf").open(encoding="utf-8") if l.startswith("p cnf")).strip()
    cells = dk.load_cells()
    v23 = json.loads((H / "run23/cells-verdict.json").read_text(encoding="utf-8"))
    n23 = {}
    for c, members in cells.items():
        meta, a0 = members[0]["cellmeta"], members[0]["perms"]
        reps = [dk.rep(23, t["lines"], t["perms"]) for t in members]
        stmt = dk.statement(23, a0, len(members), meta["bstar"], catalog=[r["witness"] for r in reps])
        n23[c] = {"count": len(members), "held": v23[c]["held"], "point_inventory": meta["b"],
                  "line_inventory": meta["bstar"], "statement_sha256": sha(canon_json(stmt)),
                  "catalog_digests_sha256": sha("\n".join(sorted(t["digest"] for t in members)).encode()),
                  "premise": "CELL-COMPLETE"}
    receipt = {
        "schema": "gp-dk-v4-receipt/v1",
        "design": "docs/DK-V4-DESIGN.md",
        "decision": "DECISIONS.md 2026-10-04 (G4's DK condition)",
        "sources": {
            "type_files": f"cfg23 commit {(H / 'SOURCE-COMMIT').read_text().strip()} artifacts/v4-cell-census-v1",
            "audit_lane": f"cfg23 commit {(H / 'AUDIT-SOURCE-COMMIT').read_text().strip()}",
            "custody": "the builder reran v4census.py: all 5,299 type files regenerated, JSON-equal to the commit "
                       "(bytes differ only by CRLF); per-cell staging from that rerun carries each cell's labelling",
        },
        "runner_sha256": sha(dk.RUNNER),
        "census_commit": subprocess.run(["git", "rev-parse", "HEAD"], cwd=ROOT, capture_output=True, text=True).stdout.strip(),
        "n19_control": {
            "claim": "V4_COUNT = 9 at n = 38 (19 points, 19 lines), DK's normal-form action Sys(19, [1,1,3], 3), "
                     "no line inventory (both admissible line cells)",
            "held": v19["held"], "reach": v19["reach"],
            "claim_sha256": sha(run19 / "n19-claim.json"), "certificate_sha256": sha(run19 / "n19-cert.json"),
            "models": len(cert19["models"]), "representatives": len(cert19["reps"]), "labels": len(cert19["labels"]),
            "cnf_header": head, "cnf_sha256": sha(run19 / "n19.cnf"),
            "lrat_sha256": sha(run19 / "n19.lrat"), "lrat_bytes": (run19 / "n19.lrat").stat().st_size,
            "premise": "none (V4-NORMAL-FORM bridges to DK's wording, outside the claim)",
        },
        "n23_cells": n23,
        "premises": {
            "V4-NORMAL-FORM": "a type admits a V4 action with point inventory I iff it is isomorphic to a member with "
                              "DK's normal-form action a0(I) (classification of V4-sets); standard, closable in principle",
            "CELL-COMPLETE": "DK's direct enumerator (v4census.py) and the audit lane's indep_enum.py agree; NOT "
                             "independent for the b12 cells, derived by duality in the shared join.py",
        },
        "difftests": difftests,
    }
    out = ROOT / "reports/DK-V4-RECEIPT.json"
    out.write_text(json.dumps(receipt, indent=1) + "\n", encoding="utf-8", newline="\n")
    print(out)


if __name__ == "__main__":
    main(json.loads(sys.argv[1]) if len(sys.argv) > 1 else {})
