#!/usr/bin/env python3
"""Compile the bounded H8/c7_9 proof state into ``frontier/v1``.

This adapter consumes frozen metadata by default.  ``--check-native-bindings``
also checks the exact sibling JC receipt bytes and their terminal verdicts.  It
does not run the sibling release suite and does not mutate either repository.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path

from grandportage import frontier as FRONT


ROOT = Path(__file__).resolve().parents[2]
DEFAULT_FIXTURE = ROOT / "fixtures" / "jc_frontier" / "h8_c79_v1.json"
EXPECTED_FIXTURE_SHA256 = (
    "73204a4cc3f8c12895beacf7f2f2e812f876833e7b98cf6faa473d21d204cfe8"
)
NATIVE_ROOT = ROOT.parent / "math-stuff"


class JCFrontierError(ValueError):
    """The frozen proof-state input or its native binding drifted."""


def _require(condition, message):
    if not condition:
        raise JCFrontierError(message)


def _sha256(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def _load(path):
    return json.loads(Path(path).read_text(encoding="utf-8"))


def _check_native_sources(fixture):
    checked = []
    for source in fixture["sources"]:
        path = NATIVE_ROOT / source["path"]
        _require(path.is_file(), "native source is absent: %s" % path)
        _require(_sha256(path) == source["sha256"],
                 "native source digest changed: %s" % source["path"])
        value = _load(path)
        _require(value.get("verdict") == source["verdict"],
                 "native verdict changed: %s" % source["path"])
        if source["path"].endswith(
                "f2_h3_c79_source_incidence_family_certificate.json"):
            _require(value.get("window", {}).get("scalar_faces", {}).get(
                "8,1") == "(5/4)*t**2",
                "native c7_9 family lost the exact unit face")
            _require(value.get("ring", {}).get("codimension") == 5,
                     "native c7_9 family scope changed")
        checked.append(source["path"])
    return checked


def verify_fixture(path=DEFAULT_FIXTURE, check_native_bindings=False):
    path = Path(path)
    _require(_sha256(path) == EXPECTED_FIXTURE_SHA256,
             "frontier fixture digest changed")
    fixture = _load(path)
    _require(fixture.get("schema") == "frontier-input/v1",
             "unsupported frontier fixture schema")
    _require(fixture.get("consumer") == "jc-h3-h8-c79-frontier",
             "frontier fixture consumer changed")

    native_checked = (
        _check_native_sources(fixture) if check_native_bindings else [])
    projection = FRONT.build_document(fixture)
    by_id = {item["id"]: item for item in projection["items"]}

    _require(projection["schema"] == FRONT.SCHEMA and
             projection["authority"] == FRONT.AUTHORITY and
             projection["graph_effect"] == FRONT.GRAPH_EFFECT,
             "frontier projection widened authority")
    _require(projection["history"]["immutable"] is True,
             "frontier projection did not retain immutable history")
    _require(by_id["JC.H3.H8"]["historical_status"] == "OPEN_PREMISE" and
             by_id["JC.H3.H8"]["effective_status"] == "DISCHARGED",
             "H8 premise update did not propagate")
    _require(by_id["JC.H3.OPERATOR_SCHEDULE.D8-15"]["effective_status"] ==
             "VERIFIED", "operator schedule remains H8-conditional")
    _require(by_id["JC.H3.D9.PAIRING.DEG34"]["effective_status"] ==
             "VERIFIED", "depth-9 pairing remains H8-conditional")
    _require(by_id["JC.H3.C79.SOURCE.FACE81.UNIT"]["effective_status"] ==
             "CLOSED", "c7_9 family source exclusion is not closed")
    _require(by_id["JC.H3.C79.SOURCE.FACE81.PIN_ABLATION"]
             ["effective_status"] == "OPEN",
             "pin ablation was silently closed")
    _require(by_id["JC.H3.B0.SOURCE.EXCLUSION"]["effective_status"] ==
             "OPEN", "family source exclusion widened to the b=0 branch")
    _require({"additive residual bodies", "actual-source membership", "H3"}
             <= set(projection["discharges"][0]["does_not_discharge"]),
             "H8 discharge lost its refusal boundary")

    projection["consumer"] = fixture["consumer"]
    projection["fixture"] = {
        "path": str(path.relative_to(ROOT)).replace("\\", "/"),
        "sha256": "sha256:" + EXPECTED_FIXTURE_SHA256,
    }
    projection["native_bindings_checked"] = native_checked
    return projection


def review_receipt(report):
    """Return the compact checked-in review surface for this consumer."""
    return {
        "schema": "gp-jc-h3-frontier-review/v1",
        "projection_schema": report["schema"],
        "authority": report["authority"],
        "graph_effect": report["graph_effect"],
        "consumer": report["consumer"],
        "fixture": report["fixture"],
        "history": report["history"],
        "changes": report["changes"],
        "open_items": report["open_items"],
        "item_observations": FRONT.item_observations(report),
        "source_bindings": report["sources"],
        "does_not_discharge": report["discharges"][0][
            "does_not_discharge"],
    }


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--fixture", type=Path, default=DEFAULT_FIXTURE)
    parser.add_argument("--check-native-bindings", action="store_true")
    parser.add_argument("--compact", action="store_true")
    args = parser.parse_args(argv)
    try:
        report = verify_fixture(
            args.fixture, check_native_bindings=args.check_native_bindings)
        print(FRONT.canonical_json(
            report, pretty=not args.compact), end="")
        return 0
    except (OSError, json.JSONDecodeError, ValueError) as exc:
        print(json.dumps({"status": "REFUSED", "error": str(exc)},
                         indent=2, sort_keys=True))
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
