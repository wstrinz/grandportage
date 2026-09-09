"""Operational work never becomes graph authority or a full-check receipt."""
import json

import pytest

from grandportage import check as C, cli, store as S
from helpers import fold


def record():
    return {"id": "TRY-1", "family": "F", "locus": "cell-7",
            "disposition": "UNRESOLVED", "reason": "TIMEOUT",
            "budget": {"value": 75, "unit": "seconds"}}


def prepare(tmp_path):
    S.append([{"ev": "family", "id": "F", "count": 1, "desc": "cells"}], str(tmp_path))
    payload = tmp_path / "work-input.json"
    payload.write_text(json.dumps(record()), encoding="utf-8")
    return payload


def test_work_is_visible_under_its_family_and_does_not_change_graph(tmp_path, capsys):
    payload = prepare(tmp_path)
    before = (tmp_path / ".portage/graph.jsonl").read_bytes()
    assert cli.main(["--root", str(tmp_path), "work", "--file", str(payload)]) == 0
    capsys.readouterr()
    assert cli.main(["--root", str(tmp_path), "check", "--json"]) == 1
    result = json.loads(capsys.readouterr().out)
    assert result["unresolved"][0]["family"] == "F"
    assert result["unresolved"][0]["budget"] == {"value": 75, "unit": "seconds"}
    assert result["counts"]["claims"] == 0
    assert (tmp_path / ".portage/graph.jsonl").read_bytes() == before
    assert cli.main(["--root", str(tmp_path), "work", "--resolve", "TRY-1",
                     "--why", "Retried with a larger cap; see separate evidence."]) == 0
    capsys.readouterr()
    cli.main(["--root", str(tmp_path), "check", "--json"])
    assert json.loads(capsys.readouterr().out)["unresolved"] == []
    assert len((tmp_path / ".portage/work.jsonl").read_text().splitlines()) == 2


@pytest.mark.parametrize("change", [
    {"family": "MISSING"}, {"reason": "EMPTY"}, {"budget": {"value": -1, "unit": "seconds"}},
    {"budget": {"value": True, "unit": "seconds"}}, {"certificate": "UNIT_IDEAL_CERT"},
])
def test_bad_work_is_refused_transactionally(tmp_path, capsys, change):
    payload = prepare(tmp_path)
    data = record()
    data.update(change)
    payload.write_text(json.dumps(data), encoding="utf-8")
    assert cli.main(["--root", str(tmp_path), "work", "--file", str(payload)]) == 2
    assert not (tmp_path / ".portage/work.jsonl").exists()


def test_unchecked_mode_keeps_open_premises_but_never_reports_clean(tmp_path, capsys):
    from test_guard_release import events
    S.append(events("transports/X8-X10.json"), str(tmp_path))
    assert cli.main(["--root", str(tmp_path), "check", "--seam", "unchecked", "--json"]) == 1
    report = json.loads(capsys.readouterr().out)
    assert report["seam"] == "unchecked"
    assert report["clean"] == []
    assert {"INF-X8", "INF-X10"} <= {f["subject"] for f in report["findings"]}
    receipt = tmp_path / "receipt.json"
    receipt.write_text(json.dumps(report), encoding="utf-8")
    with pytest.raises(ValueError, match="unchecked"):
        cli._finding_delta([], str(receipt))
    cli.main(["--root", str(tmp_path), "check", "--seam", "unchecked", "--quiet"])
    assert "field-scope transports were not checked" in capsys.readouterr().out


def test_accounting_does_not_run_transport_checks(monkeypatch):
    from test_guard_release import events
    graph = fold(events("transports/X8-X10.json"))
    monkeypatch.setattr(C, "audit_inference", lambda *_: pytest.fail("transport was checked"))
    assert C.run_accounting(graph)


def test_work_duplicate_and_unknown_resolution_leave_log_unchanged(tmp_path, capsys):
    payload = prepare(tmp_path)
    argv = ["--root", str(tmp_path), "work", "--file", str(payload)]
    assert cli.main(argv) == 0
    path = tmp_path / ".portage/work.jsonl"
    before = path.read_bytes()
    assert cli.main(argv) == 2
    assert cli.main(["--root", str(tmp_path), "work", "--resolve", "unknown", "--why", "done"]) == 2
    assert path.read_bytes() == before


def test_mcp_reports_operational_work_and_unchecked_state(tmp_path, capsys):
    from grandportage import mcp
    payload = prepare(tmp_path)
    assert cli.main(["--root", str(tmp_path), "work", "--file", str(payload)]) == 0
    text = mcp.h_portage_check({"seam": "unchecked"}, str(tmp_path))["content"][0]["text"]
    assert "field-scope transports were not checked" in text
    assert "TRY-1" in text
    assert "clean inferences" not in text


def test_custom_graph_work_logs_do_not_mix(tmp_path, capsys):
    from grandportage import work
    first, second = tmp_path / "first.jsonl", tmp_path / "second.jsonl"
    for graph in (first, second):
        S.append([{"ev": "family", "id": "F", "count": 1, "desc": "cells"}], graph=str(graph))
    work.append(str(first), S.load(str(first)), record())
    assert work.unresolved([str(second)], S.load(str(second))) == []


def test_malformed_or_locked_work_log_is_not_silently_ignored(tmp_path, capsys):
    payload = prepare(tmp_path)
    lock = tmp_path / ".portage/work.jsonl.lock"
    lock.write_text("another writer", encoding="utf-8")
    assert cli.main(["--root", str(tmp_path), "work", "--file", str(payload)]) == 2
    assert lock.read_text() == "another writer"
    (tmp_path / ".portage/work.jsonl").write_text('{"truncated":', encoding="utf-8")
    assert cli.main(["--root", str(tmp_path), "check"]) == 2


def test_append_preserves_valid_log_without_final_newline(tmp_path, capsys):
    from grandportage import work
    payload = prepare(tmp_path)
    assert cli.main(["--root", str(tmp_path), "work", "--file", str(payload)]) == 0
    path = tmp_path / ".portage/work.jsonl"
    path.write_bytes(path.read_bytes().rstrip(b"\n"))
    assert cli.main(["--root", str(tmp_path), "work", "--resolve", "TRY-1", "--why", "retried"]) == 0
    records = work.read(str(path))
    assert len(records) == 2
    assert records[1]["resolves"] == records[0]["id"]
