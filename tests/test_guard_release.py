"""v0.32 acceptance, written against the frozen DK inputs before repairs."""
import hashlib
import json
from pathlib import Path

import pytest

from grandportage import cas, check as C, cli, format as F, kernel as K
from grandportage import migration as MIG, store as S
from helpers import fold

ROOT = Path(__file__).parent / "fixtures" / "dk_retrodiction"


def events(name):
    return json.loads((ROOT / name).read_text(encoding="utf-8"))


def test_frozen_dk_inputs_keep_their_original_lf_hashes():
    manifest = events("manifest.json")
    for name, digest in manifest["files"].items():
        assert hashlib.sha256((ROOT / name).read_bytes().replace(
            b"\r\n", b"\n")).hexdigest() == digest, name


def test_family_premise_refuses_with_discharge_without_crashing():
    with pytest.raises(S.GraphError, match="DISCHARGE.*family"):
        fold(events("fixtures/D1-inference-on-family-claim/input.json"))


@pytest.mark.parametrize("kind", [K.EMPTY, K.NONEMPTY, K.COUNT])
def test_other_family_premises_also_refuse(kind):
    batch = [{"ev": "family", "id": "F", "count": 0, "desc": "members"},
             {"ev": "claim", "id": "C", "family": "F", "kind": kind,
              "statement": "a family statement"},
             {"ev": "inference", "id": "I", "claim": "C",
              "asserted": "a model conclusion"}]
    if kind == K.EMPTY:
        batch[1]["certificate"] = "UNIT_IDEAL_CERT"
    if kind == K.NONEMPTY:
        batch[1]["witness_kind"] = "ASSERTED"
    if kind == K.COUNT:
        batch[1].update(splits="F", groups=[{"id": "G", "settles": 0,
                         "verdict": "unsettled"}], method="count", proves=[], why="none")
    with pytest.raises(S.GraphError, match="DISCHARGE.*family"):
        fold(batch)


def test_inert_disposition_is_refused_but_count_control_keeps_coverage_debt():
    with pytest.raises(S.GraphError, match="PREDICATE.*COUNT|COUNT.*PREDICATE"):
        fold(events("fixtures/D3-inert-disposition/before.json"))
    graph = fold(events("fixtures/D3-inert-disposition/after.json"))
    assert "FAMILY:C-SPLIT" in {f.fid for f in C.run(graph)}


@pytest.mark.parametrize("field", ["splits", "groups", "method", "proves"])
def test_disposition_fields_are_not_silently_accepted_on_non_count(field):
    with pytest.raises(S.GraphError, match=field):
        fold([{"ev": "model", "id": "M"},
              {"ev": "claim", "id": "C", "model": "M", "kind": K.PREDICATE,
               "statement": "statement", field: [] if field in ("groups", "proves") else "x"}])


@pytest.mark.parametrize("field,before,after", [
    ("field", "Q", "R"), ("coefficient_domain", "Q", "F_2"),
    ("characteristic", 0, 2), ("point_universe", "BASE", "ALGEBRAIC_CLOSURE"),
    ("embedding", None, {"kind": "REAL"}), ("open_conditions", [], ["x"]),
    ("saturated_at", [], ["x"]), ("ideal_pending", True, False),
])
def test_semantic_model_changes_require_relicense(field, before, after):
    assert K.classify_supersession({field: before}, {field: after}, "model") == (
        K.RELICENSE, [field])


def test_ledger_and_open_slots_keep_their_original_obligations(tmp_path, capsys):
    graph = S.load(str(ROOT / "fixtures/ledger/graph.jsonl"))
    findings = C.run(graph)
    assert len(graph.claims) == 57
    assert findings[0].fid == "DOUBT:D-E5-GAP"
    assert "FAMILY:F-TRADE" not in {f.fid for f in findings}
    slot_graph = fold(events("transports/X8-X10.json"))
    refused = {f.subject: f for f in C.run(slot_graph) if f.rule == C.R_TRANSPORT}
    assert {"INF-X8", "INF-X10"} <= set(refused)
    assert "Do not close it by writing the claim as though it held" in refused["INF-X8"].discharge
    assert C.clean_inferences(slot_graph, C.run(slot_graph)) == ["INF-X9"]
    assert cli.main(["--root", str(tmp_path), "--graph",
                     str(ROOT / "fixtures/ledger/graph.jsonl"), "history"]) == 0
    history = capsys.readouterr().out
    assert "M-E1-RING --RELICENSE--> M-E1-RING-2" in history
    assert history.count("--") >= 12


def test_frozen_dk_ledger_migrates_with_explicit_certificate_reach():
    source = str(ROOT / "fixtures/ledger/graph.jsonl")
    report = MIG.migrate_kernel_epoch([source], dry_run=True)[0]
    converted = {
        change["event"]: change["actions"][0]["action"]
        for change in report["changes"]
        if change["kind"] == "certificate"
    }
    assert set(converted) == {
        "ORDER_CERTIFICATE", "TORUS_CERTIFICATE",
        "FORCED_INCIDENCE_COFACTOR", "BLAND_JENSEN_GF2_CONTRADICTION",
    }
    assert "mapped ORDER_CERTIFICATE to ORDERED" in converted[
        "ORDER_CERTIFICATE"]
    assert "mapped BLAND_JENSEN_GF2_CONTRADICTION to NONE" in converted[
        "BLAND_JENSEN_GF2_CONTRADICTION"]


def test_history_keeps_both_successors_of_a_model(tmp_path, capsys):
    S.append([{"ev": "model", "id": "A", "what": "old"},
              {"ev": "model", "id": "B", "what": "first", "supersedes": "A", "discharge_kind": "RESTATE"},
              {"ev": "model", "id": "C", "what": "second", "supersedes": "A", "discharge_kind": "RESTATE"}], str(tmp_path))
    assert cli.main(["--root", str(tmp_path), "history"]) == 0
    text = capsys.readouterr().out
    assert "A --RESTATE--> B" in text
    assert "A --RESTATE--> C" in text


@pytest.mark.live
@pytest.mark.parametrize("repeat", range(3))
@pytest.mark.parametrize("size", [96, 97])
def test_frozen_witness_boundary_three_repeats(size, repeat):
    name = "pass-96vars.json" if size == 96 else "fail-97vars.json"
    batch = events("fixtures/D2-witness-substitution-scaling/" + name)
    model = next(e for e in batch if e["ev"] == "model")
    claim = next(e for e in batch if e["ev"] == "claim")
    ok, detail = cas.check_witness(model["ring_vars"], model["generators"],
                                   claim["witness_point"], timeout=30)
    assert ok, detail


@pytest.mark.live
@pytest.mark.parametrize("size", [138, 174, 1024])
def test_large_witness_checks_true_and_false_points(size):
    variables = ["x%d" % n for n in range(size)]
    point = dict.fromkeys(variables, "1")
    point["x0"] = "0"
    assert cas.check_witness(variables, ["x0*x1"], point, timeout=30)[0]
    point["x0"] = "1"
    assert not cas.check_witness(variables, ["x0*x1"], point, timeout=30)[0]
