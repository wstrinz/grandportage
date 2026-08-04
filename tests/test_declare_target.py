import json

from grandportage import cli
from grandportage import format as F
from grandportage import store as S


def _native(path, identifier):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text("\n".join([
        json.dumps(F.meta_event(), sort_keys=True),
        json.dumps({"ev": "model", "id": identifier,
                    "desc": identifier.lower()}, sort_keys=True),
        "",
    ]), encoding="utf-8")


def _payload(path, text="explicit write"):
    path.write_text(json.dumps({"ev": "note", "text": text}),
                    encoding="utf-8")


def test_declare_writes_the_single_explicit_graph_not_root(tmp_path, capsys):
    root_graph = tmp_path / ".portage" / "graph.jsonl"
    selected = tmp_path / ".portage" / "graph.epoch1.jsonl"
    payload = tmp_path / "event.json"
    _native(root_graph, "ROOT")
    _native(selected, "SELECTED")
    _payload(payload)
    root_before = root_graph.read_bytes()

    assert cli.main([
        "--root", str(tmp_path), "--graph", str(selected),
        "declare", "--file", str(payload),
    ]) == 0

    assert root_graph.read_bytes() == root_before
    assert any(note["text"] == "explicit write"
               for note in S.load(str(selected)).notes)
    assert str(selected.resolve()) in capsys.readouterr().out


def test_repeated_graph_write_target_refuses_before_reading_stdin(
        tmp_path, capsys, monkeypatch):
    first = tmp_path / "first.jsonl"
    second = tmp_path / "second.jsonl"
    _native(first, "FIRST")
    _native(second, "SECOND")
    before = (first.read_bytes(), second.read_bytes())

    class RefuseRead:
        def read(self):
            raise AssertionError("ambiguous target must refuse before stdin")

    monkeypatch.setattr("sys.stdin", RefuseRead())
    assert cli.main([
        "--graph", str(first), "--graph", str(second), "declare",
    ]) == 2
    assert (first.read_bytes(), second.read_bytes()) == before
    assert "exactly one write target" in capsys.readouterr().err


def test_explicit_epoch0_target_still_refuses_transactionally(tmp_path):
    graph = tmp_path / "legacy.jsonl"
    payload = tmp_path / "event.json"
    graph.write_text(json.dumps({"ev": "model", "id": "OLD",
                                 "desc": "old"}) + "\n",
                     encoding="utf-8")
    _payload(payload)
    before = graph.read_bytes()

    assert cli.main([
        "--graph", str(graph), "declare", "--file", str(payload),
    ]) == 2
    assert graph.read_bytes() == before


def test_literal_portage_declare_surface_uses_the_same_selected_graph(
        tmp_path):
    root_graph = tmp_path / ".portage" / "graph.jsonl"
    selected = tmp_path / ".portage" / "return.jsonl"
    payload = tmp_path / "event.json"
    _native(root_graph, "ROOT")
    _native(selected, "RETURN")
    _payload(payload, "literal surface")
    root_before = root_graph.read_bytes()

    assert cli.declare_main([
        "--root", str(tmp_path), "--graph", str(selected),
        "--file", str(payload),
    ]) == 0

    assert root_graph.read_bytes() == root_before
    assert any(note["text"] == "literal surface"
               for note in S.load(str(selected)).notes)
