#!/usr/bin/env python3
"""Compile the checked depth-six replay ledger through ``frontier/v1``.

The older generated status block remains a compatibility review surface. This
adapter is the second independent consumer of the general proof-frontier
compiler and preserves the ledger's five domain-specific status strings while
marking them explicitly open.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path

from grandportage import frontier as FRONT


ROOT = Path(__file__).resolve().parents[2]
DEFAULT_LEDGER = ROOT / "review" / "jc-h3-depth6-seam-replay-v2.json"
EXPECTED_LEDGER_SHA256 = (
    "327434f1a5fe4aa34b707e38139f8d15a8523c37d372142d71193b153a83ecac"
)
LEDGER_SCHEMA = "gp-jc-h3-depth6-milestone-replay/v2"
EXPECTED_VERDICT = "VERIFIED_TO_EXPLICIT_OPEN_OBLIGATION"


class Depth6FrontierError(ValueError):
    """The landed ledger drifted or lost its authority boundary."""


def _require(condition, message):
    if not condition:
        raise Depth6FrontierError(message)


def _sha256(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def _load(path):
    return json.loads(Path(path).read_text(encoding="utf-8"))


IDS = {
    "R5": "JC.H3.D6.R5.CUBIC_FACE",
    "R6": "JC.H3.D6.R6.NONMONOMIAL_FRAME",
    "R7": "JC.H3.D6.R7.75_125_IDENTIFICATION",
    "R6.Q_side_relocation": "JC.H3.D6.R6.Q_SIDE_RELOCATION",
    "target_pair_to_normalized_laurent_root": (
        "JC.H3.SOURCE.TARGET_PAIR_TO_NORMALIZED_LAURENT_ROOT"),
}

PREMISES = {
    "actual_pair": "JC.H3.SOURCE.ACTUAL_PAIR",
    "source_polynomiality": "JC.H3.SOURCE.POLYNOMIALITY",
    "gap5": "JC.H3.SOURCE.GAP5",
}

NEXT_ARTIFACTS = {
    "R5": "derive or bind the selected monic depressed-cubic face",
    "R6": "materialize the exact non-monomial eqq1-to-psi2 frame conversion",
    "R7": "supply a printed or independently derived (75,125) identification",
    "R6.Q_side_relocation": (
        "prove Q-side positive-j relocation from the three named premises"),
    "target_pair_to_normalized_laurent_root": (
        "materialize the coefficient-level map from the target polynomial "
        "pair to normalized Laurent-root data"),
}


def _scope(local_id):
    if local_id == "target_pair_to_normalized_laurent_root":
        return {
            "id": "JC.H3.SOURCE.TARGET_PAIR.SEAM",
            "description": (
                "the source-derived target polynomial pair before normalized "
                "Laurent-root materialization"),
        }
    return {
        "id": "JC.H3.D6.CONDITIONAL_NORMALIZED_ROOT",
        "description": (
            "the landed depth-six argument conditional on normalized "
            "Laurent-root input; no original-source or reverse-lift scope"),
    }


def _item(value, superseding_evidence):
    local_id = value["id"]
    _require(local_id in IDS, "unknown depth-six frontier id: %s" % local_id)
    premises = []
    for premise in value.get("premises", []):
        _require(premise in PREMISES,
                 "unknown depth-six premise id: %s" % premise)
        premises.append({"id": PREMISES[premise], "status": "OPEN"})
    return {
        "id": IDS[local_id],
        "proposition": value["why_open"],
        "status": value["status"],
        "frontier_state": "OPEN",
        "scope": _scope(local_id),
        "premises": premises,
        "blocked_downstream": list(value.get("blocks", [])),
        "superseding_evidence": list(superseding_evidence),
        "smallest_next_artifact": {
            "description": NEXT_ARTIFACTS[local_id],
        },
        "estimated_cost": None,
        "potential_impact": list(value.get("blocks", [])),
    }


def verify_ledger(path=DEFAULT_LEDGER):
    path = Path(path)
    _require(_sha256(path) == EXPECTED_LEDGER_SHA256,
             "depth-six seam ledger digest changed")
    ledger = _load(path)
    _require(ledger.get("schema") == LEDGER_SCHEMA,
             "unsupported depth-six ledger schema")
    _require(ledger.get("overall_verdict") == EXPECTED_VERDICT,
             "depth-six ledger verdict changed")
    _require(ledger.get("aggregate_graph_effect") == "NONE",
             "depth-six ledger widened graph authority")
    frontier = ledger.get("open_frontier")
    _require(isinstance(frontier, list) and len(frontier) == 5,
             "depth-six ledger must expose exactly five frontier items")
    _require(set(item.get("id") for item in frontier) == set(IDS),
             "depth-six ledger frontier ids changed")
    _require(ledger.get("first_missing_authority", {}).get("id") ==
             "target_pair_to_normalized_laurent_root",
             "depth-six first missing authority changed")

    items = [_item(item, ledger.get("superseded_by", []))
             for item in frontier]
    source = {
        "path": str(path.relative_to(ROOT)).replace("\\", "/"),
        "sha256": "sha256:" + EXPECTED_LEDGER_SHA256,
        "ledger_schema": ledger["schema"],
        "overall_verdict": ledger["overall_verdict"],
        "binding_digest_algo": ledger.get("binding_digest_algo"),
        "binding_count": len(ledger.get("bindings", {})),
    }
    projection = FRONT.build(items, sources=[source])
    _require(projection["authority"] == FRONT.AUTHORITY and
             projection["graph_effect"] == FRONT.GRAPH_EFFECT,
             "depth-six frontier projection widened authority")
    _require(set(projection["open_items"]) == set(IDS.values()),
             "depth-six frontier lost or closed an obligation")
    _require(projection["changes"] == [],
             "depth-six frontier invented a premise update")
    projection["consumer"] = "jc-h3-depth6-status-ledger"
    projection["source_overall_verdict"] = ledger["overall_verdict"]
    projection["source_authority_ceiling"] = ledger.get("authority_ceiling")
    return projection


def review_receipt(report):
    return {
        "schema": "gp-jc-h3-depth6-frontier-review/v1",
        "projection_schema": report["schema"],
        "authority": report["authority"],
        "graph_effect": report["graph_effect"],
        "consumer": report["consumer"],
        "history": report["history"],
        "source": report["sources"][0],
        "source_overall_verdict": report["source_overall_verdict"],
        "source_authority_ceiling": report["source_authority_ceiling"],
        "open_items": report["open_items"],
        "item_observations": FRONT.item_observations(report),
        "items": [{
            "id": item["id"],
            "status": item["effective_status"],
            "scope_id": item["scope"]["id"],
            "blocked_downstream": item["blocked_downstream"],
            "smallest_next_artifact": item["smallest_next_artifact"],
        } for item in report["items"]],
    }


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--ledger", type=Path, default=DEFAULT_LEDGER)
    parser.add_argument("--compact", action="store_true")
    args = parser.parse_args(argv)
    try:
        report = verify_ledger(args.ledger)
        print(FRONT.canonical_json(
            report, pretty=not args.compact), end="")
        return 0
    except (OSError, json.JSONDecodeError, ValueError) as exc:
        print(json.dumps({"status": "REFUSED", "error": str(exc)},
                         indent=2, sort_keys=True))
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
