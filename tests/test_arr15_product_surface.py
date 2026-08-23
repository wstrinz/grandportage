"""ARR15 retrodictions for handoff, lane deltas, and safe merging."""

import hashlib
import json

from grandportage import cli
from grandportage import format as F
from grandportage import store as S
from tools import replay_arr15_e10 as REPLAY


def _family(fid, count=1, enumeration=None):
    event = {"ev": "family", "id": fid, "count": count,
             "desc": "a finite test index"}
    if enumeration:
        event["enumeration"] = enumeration
    return event


def test_check_since_classifies_all_four_lane_outcomes(tmp_path, capsys):
    assert cli.main(["--root", str(tmp_path), "init"]) == 0
    S.append([
        _family("F-UNCHANGED"),
        _family("F-CHANGED", enumeration="C-CHANGED"),
        _family("F-RESOLVED", enumeration="C-RESOLVED"),
    ], str(tmp_path))
    capsys.readouterr()

    assert cli.main(["--root", str(tmp_path), "check", "--json"]) == 1
    before = json.loads(capsys.readouterr().out)
    assert all(finding.get("fingerprint") for finding in before["findings"])
    receipt = tmp_path / "e10-check-receipt.json"
    receipt.write_text(json.dumps(before), encoding="utf-8")

    S.append([
        {"ev": "claim", "id": "C-CHANGED", "family": "F-CHANGED",
         "kind": "PREDICATE", "statement": "the count is complete",
         "asserts_count": 1},
        {"ev": "claim", "id": "C-RESOLVED", "family": "F-RESOLVED",
         "kind": "PREDICATE", "statement": "the count is complete",
         "asserts_count": 1},
        {"ev": "evidence", "id": "EV-RESOLVED", "for": "C-RESOLVED",
         "method": "ENUMERATION", "ran": "exact census",
         "what": "enumerated the complete index", "decides": "BOTH"},
        _family("F-NEW"),
    ], str(tmp_path))

    assert cli.main([
        "--root", str(tmp_path), "check", "--json", "--since", str(receipt),
    ]) == 1
    delta = json.loads(capsys.readouterr().out)["since"]
    assert delta["inherited_unchanged"] == ["FAMILY:F-UNCHANGED"]
    assert [item["id"] for item in delta["changed_inherited"]] == [
        "FAMILY:F-CHANGED"]
    assert delta["resolved"] == ["FAMILY:F-RESOLVED"]
    assert delta["new"] == ["FAMILY:F-NEW"]


def test_folded_events_expose_complete_handoff_state(tmp_path, capsys):
    assert cli.main(["--root", str(tmp_path), "init"]) == 0
    S.append([
        {"ev": "family", "id": "F", "count": 1,
         "desc": "a finite handoff index"},
        {"ev": "claim", "id": "C", "family": "F",
         "kind": "PREDICATE", "statement": "one member"},
        {"ev": "evidence", "id": "EV", "for": "C",
         "method": "ENUMERATION", "ran": "census", "what": "counted"},
        {"ev": "citation", "id": "CITE", "cites": "source",
         "resolves_to": "page 1", "why": "custody"},
        {"ev": "note", "id": "N", "text": "handoff note"},
    ], str(tmp_path))
    capsys.readouterr()
    assert cli.main(["--root", str(tmp_path), "events", "--folded"]) == 0
    state = json.loads(capsys.readouterr().out)
    assert state["families"]["F"]["count"] == 1
    assert state["evidence"]["EV"]["for"] == "C"
    assert state["citations"]["CITE"]["resolves_to"] == "page 1"
    assert state["named_notes"]["N"]["text"] == "handoff note"
    assert "verdicts" in state
    assert state["metadata"]["implementation"]


def test_coordinate_merge_diagnostic_requires_verified_presentation_map(
        tmp_path, capsys):
    paths = []
    for name, variables, generators in (
            ("a", ["x", "y"], ["x+y"]),
            ("b", ["u", "v"], ["u-v"])):
        path = tmp_path / (name + ".jsonl")
        path.write_text("".join(
            json.dumps(event, sort_keys=True) + "\n"
            for event in [
                F.meta_event(),
                {"ev": "model", "id": "PRESENTATION", "what": "a curve",
                 "ring_vars": variables, "generators": generators},
            ]), encoding="utf-8")
        paths.append(path)
    assert cli.main([
        "--graph", str(paths[0]), "--graph", str(paths[1]), "merge",
    ]) == 1
    output = capsys.readouterr().out
    assert "PRESENTATION CONFLICT: PRESENTATION" in output
    assert "mint separate presentation IDs" in output
    assert "mapped EQUIVALENCE" in output
    assert "gp verify" in output
    assert "Do not use `same_as`" in output


def test_e10_replay_harness_hashes_migrates_and_preserves_hard_merge(
        tmp_path, monkeypatch):
    sources = {}
    for lane, variables in (("windows", ["x"]), ("mac", ["u"])):
        path = tmp_path / (lane + ".jsonl")
        path.write_text("".join(
            json.dumps(event, sort_keys=True) + "\n"
            for event in [
                {"ev": "meta", "graph_format": 4, "kernel_epoch": 10,
                 "created_with": "grandportage/0.24.0"},
                {"ev": "model", "id": "P", "what": "presentation",
                 "ring_vars": variables, "generators": [variables[0]]},
            ]), encoding="utf-8")
        sources[lane] = path
        monkeypatch.setitem(
            REPLAY.EXPECTED, lane,
            hashlib.sha256(path.read_bytes()).hexdigest())
    before = {lane: path.read_bytes() for lane, path in sources.items()}
    report = REPLAY.replay(sources)
    assert report["sources_unchanged"] is True
    assert [lane["migrated_graph_format"] for lane in report["lanes"]] == [
        F.GRAPH_FORMAT, F.GRAPH_FORMAT]
    assert report["merge_conflicts"] == [{
        "kind": "model", "id": "P", "fields": ["generators", "ring_vars"],
    }]
    assert {lane: path.read_bytes() for lane, path in sources.items()} == before
