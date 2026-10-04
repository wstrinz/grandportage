"""Offline replay of the bounded frozen D1/D3/X8-X10 guard snapshots.

This intentionally imports only the pinned oracle checkout's loader/checker.
It does not invoke the CAS or mutate the checkout.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import sys
from pathlib import Path


WORKSPACE = Path(__file__).resolve().parents[1]
ORACLE = WORKSPACE / "oracle" / "checkout"
FIXTURES = ORACLE / "tests" / "fixtures" / "dk_retrodiction"

BOUND_FILES = (
    "fixtures/D1-inference-on-family-claim/input.json",
    "fixtures/D3-inert-disposition/before.json",
    "fixtures/D3-inert-disposition/after.json",
    "transports/X8-X10.json",
)

CANDIDATE_VERDICTS = {
    "GP-X399": "REFUSE",
    "GP-X400": "REFUSE",
    "GP-X401": "ACCEPT",
    "GP-X402": "REFUSE",
    "GP-X403": "REFUSE",
}


def sha256_lf(path: Path) -> str:
    return hashlib.sha256(path.read_bytes().replace(b"\r\n", b"\n")).hexdigest()


def read_events(path: Path):
    return json.loads(path.read_text(encoding="utf-8"))


def run() -> dict:
    """Return the focused report after verifying frozen fixture bytes first."""
    manifest = read_events(FIXTURES / "manifest.json")
    fixture_hashes = {}
    for relative in BOUND_FILES:
        observed = sha256_lf(FIXTURES / relative)
        expected = manifest["files"][relative]
        fixture_hashes[relative] = {
            "expected_lf_sha256": expected,
            "observed_lf_sha256": observed,
            "matches": observed == expected,
        }
    mismatches = [relative for relative, item in fixture_hashes.items() if not item["matches"]]
    if mismatches:
        raise ValueError("frozen fixture digest mismatch: " + ", ".join(mismatches))

    # The frozen test imports helpers as a top-level module. Insert these paths
    # only after the fixture gate; the checkout remains read-only.
    sys.path[:0] = [str(ORACLE), str(ORACLE / "tests")]
    from grandportage import check as C  # pylint: disable=import-outside-toplevel
    from grandportage import store as S  # pylint: disable=import-outside-toplevel

    from jsonschema import Draft202012Validator  # pylint: disable=import-outside-toplevel

    case_schema = read_events(WORKSPACE / "corpus" / "case.schema.json")
    case_validator = Draft202012Validator(case_schema)
    candidate_validation = []
    for case_id, verdict in CANDIDATE_VERDICTS.items():
        path = WORKSPACE / "reports" / "guard-case-candidates" / (case_id + ".json")
        candidate = read_events(path)
        schema_errors = sorted(error.message for error in case_validator.iter_errors(candidate))
        source_paths_exist = all(
            (ORACLE / source["path"]).is_file()
            for source in candidate.get("sources", ())
        )
        source_anchors_match_lines = all(
            source["line"] <= len((ORACLE / source["path"]).read_text(encoding="utf-8").splitlines())
            and source["anchor"] in (ORACLE / source["path"]).read_text(encoding="utf-8").splitlines()[source["line"] - 1]
            for source in candidate.get("sources", ())
        )
        source_identity_matches_pin = all(
            source["repository"] == "gp-v037"
            and source.get("commit") == "ac4155787207e2847d248cffed7be871d5dcd577"
            for source in candidate.get("sources", ())
        )
        candidate_validation.append({
            "file": str(path.relative_to(WORKSPACE)),
            "id_matches_filename": candidate.get("id") == case_id,
            "schema_version": candidate.get("schema_version"),
            "schema_valid": not schema_errors,
            "schema_errors": schema_errors,
            "expected_verdict": candidate.get("expected", {}).get("verdict"),
            "expected_verdict_matches": candidate.get("expected", {}).get("verdict") == verdict,
            "source_paths_exist_in_pinned_checkout": source_paths_exist,
            "source_anchors_match_declared_lines": source_anchors_match_lines,
            "source_identity_matches_corpus_pin": source_identity_matches_pin,
        })

    def fold(events):
        graph = S.Graph()
        for line, event in enumerate(events, 1):
            graph.apply(event, source="<frozen-guard-fixture>", lineno=line)
        return graph.validate()

    def refusal(label, relative, markers):
        try:
            fold(read_events(FIXTURES / relative))
        except S.GraphError as exc:
            text = str(exc)
            return {
                "case": label,
                "fixture": relative,
                "outcome": "REFUSE",
                "error_type": type(exc).__name__,
                "error": text,
                "markers": list(markers),
                "markers_present": all(marker.lower() in text.lower() for marker in markers),
            }
        return {
            "case": label,
            "fixture": relative,
            "outcome": "UNEXPECTED_ACCEPT",
            "markers": list(markers),
            "markers_present": False,
        }

    d1 = refusal(
        "GP-X399", "fixtures/D1-inference-on-family-claim/input.json", ("DISCHARGE", "family")
    )
    d3_before = refusal(
        "GP-X400", "fixtures/D3-inert-disposition/before.json", ("PREDICATE", "COUNT")
    )
    d3_after_graph = fold(read_events(FIXTURES / "fixtures/D3-inert-disposition/after.json"))
    d3_after_findings = C.run(d3_after_graph)
    d3_after = {
        "case": "GP-X401",
        "fixture": "fixtures/D3-inert-disposition/after.json",
        "outcome": "ACCEPT_DECLARATION_WITH_DEBT",
        "finding_ids": [finding.fid for finding in d3_after_findings],
        "retains_family_c_split": "FAMILY:C-SPLIT" in {finding.fid for finding in d3_after_findings},
    }
    transport_events = read_events(FIXTURES / "transports/X8-X10.json")
    transport_graph = fold(transport_events)
    refused = {
        finding.subject: finding
        for finding in C.run(transport_graph)
        if finding.rule == C.R_TRANSPORT
    }
    clean = C.clean_inferences(transport_graph, C.run(transport_graph))
    missing_why = {
        event["id"]: next(
            premise["missing_why"]
            for premise in event["premises"]
            if "missing_why" in premise
        )
        for event in transport_events
        if event.get("ev") == "inference" and event["id"] in {"INF-X8", "INF-X10"}
    }
    x8 = {
        "case": "GP-X402",
        "fixture": "transports/X8-X10.json",
        "outcome": "REFUSE",
        "subject": "INF-X8",
        "present": "INF-X8" in refused,
        "validation_gate": "explicit required_kind open-premise slot reported by C.R_TRANSPORT",
        "missing_why": missing_why["INF-X8"],
        "discharge": refused.get("INF-X8").discharge if "INF-X8" in refused else None,
        "missing_premise_marker": "E5" in missing_why["INF-X8"],
    }
    x10 = {
        "case": "GP-X403",
        "fixture": "transports/X8-X10.json",
        "outcome": "REFUSE",
        "subject": "INF-X10",
        "present": "INF-X10" in refused,
        "validation_gate": "explicit required_kind open-premise slot reported by C.R_TRANSPORT",
        "missing_why": missing_why["INF-X10"],
        "discharge": refused.get("INF-X10").discharge if "INF-X10" in refused else None,
        "missing_premise_marker": "E5-gap" in missing_why["INF-X10"],
    }

    controls = [d1, d3_before, d3_after, x8, x10]
    passed = (
        all(item["matches"] for item in fixture_hashes.values())
        and all(
            item["id_matches_filename"]
            and item["schema_version"] == 1
            and item["schema_valid"]
            and item["expected_verdict_matches"]
            and item["source_paths_exist_in_pinned_checkout"]
            and item["source_anchors_match_declared_lines"]
            and item["source_identity_matches_corpus_pin"]
            for item in candidate_validation
        )
        and d1["outcome"] == "REFUSE" and d1["markers_present"]
        and d3_before["outcome"] == "REFUSE" and d3_before["markers_present"]
        and d3_after["retains_family_c_split"]
        and x8["present"] and x8["missing_premise_marker"]
        and x10["present"] and x10["missing_premise_marker"]
        and clean == ["INF-X9"]
    )
    report = {
        "schema_version": 1,
        "status": "focused_offline_frozen_guard_probe",
        "oracle_checkout": str(ORACLE),
        "fixture_manifest_source_commit": manifest["source_commit"],
        "fixture_hashes": fixture_hashes,
        "candidate_validation": candidate_validation,
        "controls": controls,
        "limited_contrast": {
            "clean_inferences": clean,
            "meaning": "INF-X9 is a clean inference in this frozen graph only; it carries the declared, unproved E5 premise and is not a family-bridge or source/parent-cover positive.",
        },
        "execution_limits": [
            "Offline Python loader/checker fold only.",
            "No CAS invocation.",
            "No oracle checkout writes.",
            "D3 declaration acceptance remains distinct from FAMILY:C-SPLIT debt.",
        ],
        "passed": passed,
    }
    return report


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    report = run()
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({"passed": report["passed"], "output": str(args.output)}, sort_keys=True))
    return 0 if report["passed"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
