"""ARR15 retrodiction gates for public-surface contract closure."""

import json
from pathlib import Path

from grandportage import check as C
from grandportage import format as F
from grandportage import kernel as K
from grandportage import mcp
from grandportage import store as S


ROOT = Path(__file__).resolve().parents[1]
MEMBERS_FIXTURE = ROOT / "fixtures" / "arr15" / "n14-nondivfree-member-keys-v1.json"


def _members():
    fixture = json.loads(MEMBERS_FIXTURE.read_text(encoding="utf-8"))
    assert fixture["source_export_sha256"] == (
        "8ed59e803848aaeb511a0500f131e30a58c17597e2533d61dc7e3b25d6af83ee")
    assert len(fixture["members"]) == len(set(fixture["members"])) == 173
    return fixture["members"]


def _events(asserts_count=173, evidence=True, family_enumeration=True):
    family = {
        "ev": "family", "id": "F-N14-NONDIVFREE-SEEDS", "count": 173,
        "desc": "rank-3, 14-atom representable integrally splitting "
                "non-divisionally-free matroids",
        "members": _members(),
    }
    if family_enumeration:
        family["enumeration"] = "C-N14-SEED-COUNT-173"
    events = [family, {
        "ev": "claim", "id": "C-N14-SEED-COUNT-173",
        "family": "F-N14-NONDIVFREE-SEEDS", "kind": K.PREDICATE,
        "statement": "the exact filtered seed family has 173 members",
        "asserts_count": asserts_count,
        "established_by": "RAN", "ladder": "exact-checked",
    }]
    if evidence:
        events.append({
            "ev": "evidence", "id": "EV-N14-MAC-DB-COUNT-REPLAY",
            "for": "C-N14-SEED-COUNT-173", "method": "ENUMERATION",
            "ran": "the pinned AQL count and full 173-object export",
            "what": "applied the exact deterministic predicate to the full "
                    "815107-document parent collection",
            "decides": "BOTH",
        })
    return events


def _family_findings(root):
    graph = S.load(S.graph_path(str(root)))
    return [finding for finding in C.run(graph) if finding.rule == C.R_FAMILY]


def test_n14_remediation_crosses_the_real_mcp_native_and_reload_boundary(tmp_path):
    result = mcp.h_portage_declare({"events": _events()}, str(tmp_path))
    assert not result.get("isError"), result
    assert _family_findings(tmp_path) == []
    graph = S.load(S.graph_path(str(tmp_path)))
    assert graph.families["F-N14-NONDIVFREE-SEEDS"]["members"] == _members()


def test_naked_family_count_remains_refused_after_public_round_trip(tmp_path):
    result = mcp.h_portage_declare(
        {"events": [_events(family_enumeration=False)[0]]}, str(tmp_path))
    assert not result.get("isError"), result
    findings = _family_findings(tmp_path)
    assert len(findings) == 1
    assert "names no claim" in findings[0].detail


def test_mismatched_enumeration_count_is_refused_for_the_intended_reason(tmp_path):
    result = mcp.h_portage_declare(
        {"events": _events(asserts_count=174)}, str(tmp_path))
    assert not result.get("isError"), result
    findings = _family_findings(tmp_path)
    assert len(findings) == 1
    assert "asserts count 174 rather than 173" in findings[0].detail


def test_enumeration_without_exact_evidence_does_not_self_certify(tmp_path):
    result = mcp.h_portage_declare(
        {"events": _events(evidence=False)}, str(tmp_path))
    assert not result.get("isError"), result
    findings = _family_findings(tmp_path)
    assert len(findings) == 1
    assert "decides: BOTH" in findings[0].detail


def test_native_and_mcp_declaration_fields_are_identical():
    schemas = {
        schema["properties"]["ev"]["enum"][0]: schema
        for schema in mcp.DECLARABLE_EVENT_SCHEMA["oneOf"]
    }
    for kind, fields in F.EVENT_FIELDS.items():
        if kind in ("meta", "verdict"):
            continue
        assert set(schemas[kind]["properties"]) == fields
        assert set(schemas[kind]["required"]) == F.AUTHOR_REQUIRED_FIELDS.get(
            kind, F.REQUIRED_FIELDS.get(kind, {"ev"}))
    assert "enumeration" in schemas["family"]["properties"]
