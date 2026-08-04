import json
from pathlib import Path
from grandportage import check as C
from grandportage import cli
from grandportage import migration as MIG
from grandportage import projection as P
from grandportage import store as S
from grandportage import visualization as V

import helpers as H


def _projection():
    graph = H.load("jc2")
    return P.build(
        graph,
        sources=[H.graph_file("jc2")],
        findings=C.run(graph),
        accepted={"accepted": {}, "note": ""},
        package_version="test",
    )


def test_projection_is_complete_deterministic_and_non_authoritative():
    first = _projection()
    second = _projection()

    assert first == second
    assert P.canonical_json(first) == P.canonical_json(second)
    assert first["schema"] == "grand-portage-projection/v2"
    assert first["authority"] == "DERIVED_READ_MODEL_ONLY"
    assert first["source"]["graphs"][0]["fingerprint"].startswith("sha256:")
    assert first["counts"]["accepted_findings"] == 0

    graph = H.load("jc2")
    assert set(first["collections"]["models"]) == set(graph.models)
    assert set(first["collections"]["edges"]) == set(graph.edges)
    assert set(first["collections"]["claims"]) == set(graph.claims)
    assert list(first["collections"]["inferences"]) == graph.inference_order
    assert first["orders"]["inferences"] == graph.inference_order
    assert set(first["collections"]["certificates"]) == set(graph.certificates)
    assert set(first["collections"]["certificate_sources"]) == set(
        graph.cert_source)

    keys = [node["key"] for node in first["nodes"]]
    assert len(keys) == len(set(keys))
    key_set = set(keys)
    assert {node["id"] for node in first["nodes"]
            if node["kind"] == "certificate"} == set(graph.certificates)
    assert all(relation["source"] in key_set and relation["target"] in key_set
               for relation in first["relations"])
    assert all(P.resolve_record(first, node) is not None
               for node in first["nodes"])


def test_projection_v2_references_canonical_records_instead_of_copying_them():
    graph = S.Graph()
    marker = "projection-only-marker-" + "x" * 10_000
    graph.models["BIG"] = {
        "ev": "model",
        "id": "BIG",
        "characteristic": 0,
        "ring_vars": ["x"],
        "generators": [marker],
    }

    projected = P.build(graph, package_version="test")
    node = next(node for node in projected["nodes"]
                if node["key"] == "model:BIG")

    assert "record" not in node
    assert node["record_ref"] == {"collection": "models", "id": "BIG"}
    assert P.resolve_record(projected, node) == projected[
        "collections"]["models"]["BIG"]
    assert P.canonical_json(projected, pretty=False).count(marker) == 1


def test_relative_source_path_remains_portable(tmp_path, monkeypatch):
    source = tmp_path / "graph.jsonl"
    source.write_bytes(b"{}\n")
    monkeypatch.chdir(tmp_path)

    record = P._source_record("graph.jsonl")

    assert record["path"] == "graph.jsonl"
    assert record["bytes"] == 3


def test_focus_is_an_explicit_presentation_neighborhood():
    full = _projection()
    selected = P.focus(full, "claim:CL-C08", radius=1)

    assert selected["focus"] == {
        "selector": "claim:CL-C08",
        "resolved": "claim:CL-C08",
        "radius": 1,
        "semantics": "UNDIRECTED_PRESENTATION_NEIGHBORHOOD",
    }
    assert any(node["key"] == "claim:CL-C08" for node in selected["nodes"])
    assert len(selected["nodes"]) < len(full["nodes"])
    kept = {node["key"] for node in selected["nodes"]}
    assert all(relation["source"] in kept and relation["target"] in kept
               for relation in selected["relations"])


def test_visualization_is_standalone_read_only_and_escapes_embedded_data():
    projection = _projection()
    projection["collections"]["notes"].append({
        "text": "</script><b>owned</b> __TITLE__",
    })
    html = V.render(projection, title="Campaign <review> __PROJECTION__")

    assert "Campaign &lt;review&gt; __PROJECTION__" in html
    assert r'"text":"\u003c/script>\u003cb>owned\u003c/b> __TITLE__"' in html
    assert "</script><b>owned</b>" not in html
    assert r"\u003c/script>\u003cb>owned\u003c/b>" in html
    assert V.THREE_VERSION in html
    assert "OrbitControls" in html
    assert "DERIVED_READ_MODEL_ONLY" in html
    for control in ("tourSelect", "tourPrev", "tourNext", "contextDepth",
                    "isolate", "trailBack", "trailForward"):
        assert 'id="%s"' % control in html
    assert "Argument spine" in html
    assert "Soundness audit" in html
    assert "data.orders?.inferences" in html
    assert "readonly" not in html.lower() or "read-only" in html.lower()


def test_cli_project_and_visualize_write_only_derived_outputs(tmp_path):
    graph = H.graph_file("jc2")
    projected = tmp_path / "campaign.json"
    explorer = tmp_path / "campaign.html"

    assert cli.main([
        "--root", str(tmp_path), "--graph", graph, "project",
        "--output", str(projected),
    ]) == 0
    payload = json.loads(projected.read_text(encoding="utf-8"))
    assert payload["authority"] == "DERIVED_READ_MODEL_ONLY"
    assert payload["orders"]["inferences"]
    assert cli.main([
        "--root", str(tmp_path), "--graph", graph, "project",
        "--output", str(projected),
    ]) == 2
    assert cli.main([
        "--root", str(tmp_path), "--graph", graph, "project",
        "--output", graph, "--force",
    ]) == 2

    assert cli.main([
        "--root", str(tmp_path), "--graph", graph, "visualize",
        "--output", str(explorer), "--title", "JC2 review",
    ]) == 0
    html = explorer.read_text(encoding="utf-8")
    assert "JC2 review" in html
    assert "grand-portage-projection/v2" in html
    assert "graph.jsonl" in html
    assert "sha256:" in html


def test_certificate_verdict_projects_after_non_destructive_migration(tmp_path):
    root = Path(__file__).parents[1]
    source = (root / "review" / "v0.19" / "jc-p-axis" /
              ".portage" / "graph.jsonl")
    migrated = tmp_path / "jc-p-axis-format4.jsonl"
    MIG.migrate_kernel_epoch([str(source)], output=str(migrated))
    graph = S.load(str(migrated))
    projected = P.build(
        graph, sources=[str(migrated)], findings=C.run(graph),
        accepted={"accepted": {}, "note": ""}, package_version="test")
    keys = {node["key"] for node in projected["nodes"]}
    links = [relation for relation in projected["relations"]
             if relation["kind"] == "verdict-of"]

    assert links
    assert all(link["source"] in keys and link["target"] in keys
               for link in links)
    certificate_links = [
        link for link in links
        if projected["collections"]["verdicts"][
            link["source"].split(":", 1)[1]]["subject"] == "certificate"
    ]
    assert [link["target"] for link in certificate_links] == [
        "claim:JC-P-C9-AXIS-EMPTY"]
def test_every_verdict_subject_has_an_explicit_projection_target_kind():
    assert set(P.VERDICT_TARGET_KINDS) == set(S.Graph._VERDICTS)
    assert P.VERDICT_TARGET_KINDS["certificate"] == "claim"
    assert P.VERDICT_TARGET_KINDS["witness"] == "claim"
    assert P.VERDICT_TARGET_KINDS["ring_iso"] == "edge"