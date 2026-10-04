"""Validate complete hash-bound layer metadata; unresolved kernel candidates block G2 selection."""
from __future__ import annotations
import argparse
from collections import Counter
import importlib.util
import json
from pathlib import Path
import re

REPO = Path(__file__).resolve().parents[1]
_spec = importlib.util.spec_from_file_location("layer_tag_generator", Path(__file__).with_name("tag-corpus-layers.py"))
_generator = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(_generator)
LAYERS = _generator.LAYERS

def pointer_exists(value, pointer):
    try:
        for token in pointer.split("/")[1:]:
            token = token.replace("~1", "/").replace("~0", "~")
            value = value[int(token)] if isinstance(value, list) else value[token]
        return True
    except (KeyError, IndexError, TypeError, ValueError):
        return False

def validate(registry, case_dir: Path, expected_count=462):
    if not isinstance(registry, dict) or (type(registry.get("schema_version")) is not int or registry.get("schema_version") != 1):
        raise ValueError("invalid registry schema")
    if registry.get("policy_version") != _generator.POLICY_VERSION:
        raise ValueError("unknown layer policy version")
    source = {case["id"]: (path, case, digest) for path, case, digest in _generator.read_cases(case_dir)}
    if expected_count is not None and len(source) != expected_count:
        raise ValueError("unexpected source case count")
    rows = registry.get("cases")
    if not isinstance(rows, list) or type(registry.get("case_count")) is not int or registry["case_count"] != len(source):
        raise ValueError("case_count or cases is invalid")
    seen = set()
    for row in rows:
        if not isinstance(row, dict):
            raise ValueError("tag row must be an object")
        required = {"id", "path", "sha256", "primary_layer", "candidate_layers",
                    "g2_kernel_eligible", "status", "rationale", "evidence_pointers",
                    "secondary_layers", "secondary_duties", "review_group", "full_contract_required"}
        if not required.issubset(row):
            raise ValueError("tag row is missing required fields")
        ident = row.get("id")
        if not isinstance(ident, str) or ident not in source or ident in seen:
            raise ValueError(f"unknown/duplicate row id: {ident!r}")
        seen.add(ident)
        path, case, digest = source[ident]
        if row.get("path") != f"corpus/must/{path.name}":
            raise ValueError(f"{ident}: wrong case path")
        if not isinstance(row.get("sha256"), str) or not re.fullmatch(r"[0-9a-f]{64}", row["sha256"]) or row["sha256"] != digest:
            raise ValueError(f"{ident}: stale/invalid byte hash")
        layer, candidates = row.get("primary_layer"), row.get("candidate_layers")
        if layer is not None and layer not in LAYERS:
            raise ValueError(f"{ident}: invalid primary layer")
        if not isinstance(candidates, list) or not candidates or any(x not in LAYERS for x in candidates) or len(set(candidates)) != len(candidates):
            raise ValueError(f"{ident}: invalid candidate layers")
        if not isinstance(row.get("rationale"), str) or not row["rationale"].strip():
            raise ValueError(f"{ident}: missing rationale")
        if layer is None:
            if row.get("status") != "unresolved" or len(candidates) < 2:
                raise ValueError(f"{ident}: ambiguity must be explicit")
            expected_g2 = None if "kernel" in candidates else False
        else:
            if row.get("status") != "resolved" or candidates != [layer]:
                raise ValueError(f"{ident}: resolved layer has conflicting candidates")
            expected_g2 = layer == "kernel"
        actual_g2 = row.get("g2_kernel_eligible", "missing")
        if actual_g2 is not None and type(actual_g2) is not bool:
            raise ValueError(f"{ident}: G2 eligibility must be boolean/null")
        if type(actual_g2) is not type(expected_g2) or actual_g2 != expected_g2:
            raise ValueError(f"{ident}: G2 eligibility hides or contradicts kernel candidacy")
        if row["full_contract_required"] is not True:
            raise ValueError(f"{ident}: complete unchanged fixture contract is required")
        if not isinstance(row["review_group"], str) or not row["review_group"].strip():
            raise ValueError(f"{ident}: missing review group")
        secondary, duties = row["secondary_layers"], row["secondary_duties"]
        if (not isinstance(secondary, list) or any(x not in LAYERS or x == layer for x in secondary)
                or len(set(secondary)) != len(secondary)):
            raise ValueError(f"{ident}: invalid secondary layers")
        if not isinstance(duties, list) or len(duties) != len(secondary):
            raise ValueError(f"{ident}: secondary duty coverage mismatch")
        duty_layers = []
        for duty in duties:
            if (not isinstance(duty, dict) or set(duty) != {"layer", "duty"}
                    or duty["layer"] not in secondary
                    or not isinstance(duty["duty"], str) or not duty["duty"].strip()):
                raise ValueError(f"{ident}: invalid secondary duty")
            duty_layers.append(duty["layer"])
        if duty_layers != secondary:
            raise ValueError(f"{ident}: secondary duties must match unique listed layers")
        policy = _generator.CATALOG.get(ident, _generator.decision(
            None, "Case is outside the finite reviewed catalog; Will must decide layer and possible G2 eligibility."))
        if any(row.get(field) != value for field, value in policy.items()):
            raise ValueError(f"{ident}: metadata contradicts reviewed full-contract policy")
        pointers = row.get("evidence_pointers")
        if not isinstance(pointers, list) or not pointers or any(not isinstance(p, str) or not p.startswith("/") or not pointer_exists(case, p) for p in pointers):
            raise ValueError(f"{ident}: invalid evidence pointer")
    if seen != set(source) or len(rows) != len(source):
        raise ValueError(f"missing case rows: {sorted(set(source) - seen)}")
    return {"case_count": len(rows), "layers": dict(Counter(r["primary_layer"] or "unresolved" for r in rows)),
            "unresolved": [r["id"] for r in rows if r["primary_layer"] is None],
            "g2_pending": [r["id"] for r in rows if r["g2_kernel_eligible"] is None]}

def kernel_case_ids(registry, case_dir, expected_count=462):
    summary = validate(registry, case_dir, expected_count)
    if summary["g2_pending"]:
        raise ValueError("G2 kernel selection blocked by unresolved kernel candidates: " + ", ".join(summary["g2_pending"]))
    return [r["id"] for r in registry["cases"] if r["g2_kernel_eligible"]]

def g2_result_eligible(row, *, full_fixture_passed, projection_only=False):
    """Check reviewed policy plus runner attestation; metadata alone is not a pass."""
    if type(full_fixture_passed) is not bool or type(projection_only) is not bool:
        raise ValueError("pass/projection flags must be boolean")
    policy = _generator.CATALOG.get(row.get("id"))
    if policy is None or any(row.get(field) != value for field, value in policy.items()):
        return False
    return (row.get("status") == "resolved" and row.get("primary_layer") == "kernel"
            and row.get("g2_kernel_eligible") is True
            and row.get("full_contract_required") is True
            and full_fixture_passed and not projection_only)

def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--case-dir", type=Path, default=REPO / "corpus/must")
    p.add_argument("--registry", type=Path, default=REPO / "corpus/LAYER-TAGS.json")
    p.add_argument("--kernel-ids", action="store_true", help="Fail closed while any kernel candidacy remains unresolved")
    args = p.parse_args()
    data = json.loads(args.registry.read_text(encoding="utf-8"))
    try:
        result = kernel_case_ids(data, args.case_dir) if args.kernel_ids else validate(data, args.case_dir)
    except ValueError as exc:
        p.exit(1, f"layer validation failed: {exc}\n")
    print(json.dumps(result, indent=2))
if __name__ == "__main__":
    main()
