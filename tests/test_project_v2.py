from copy import deepcopy
from pathlib import Path
import json

from grandportage import project_v2 as I
from grandportage import store as S
from grandportage import verify as V
from grandportage import format as F
from scripts import check_interpreter_parity as parity


def graph():
    g = S.Graph()
    g.apply(F.meta_event())
    g.apply(dict(parity.fixture()["model"], ev="model", id="M"))
    g.apply({"ev": "claim", "id": "C", "model": "M", "kind": "EMPTY",
             "statement": "ordered example", "certificate": "ORDERED_SOS_CERT", "scope": "ANY_ORDERED"})
    return g.validate()


def test_projection_is_read_only_and_never_promotes_a_tag():
    g = graph()
    before = deepcopy(g.claims), deepcopy(g.models), dict(g.authority_receipts)
    report = I.project(g)
    assert report["graph_effect"] == "NONE"
    assert report["categories"]["claims"]["C"]["status"] == "PROJECTABLE"
    evidence = report["categories"]["evidence"]["certificate:C"]
    assert evidence["status"] == "UNPROJECTABLE"
    assert evidence["candidate"]["requirement_profile"] is None
    assert report["profile_from_tag"] == {"count": 1, "denominator": 1, "rate": 1.0}
    assert before == (g.claims, g.models, g.authority_receipts)


def test_missing_context_is_reported_without_inventing_about():
    g = graph()
    g.models["M"].pop("about")
    report = I.project(g)
    assert "context.about" in report["categories"]["claims"]["C"]["missing"]
    assert report["stop_for_missing_context"]
    assert "about" not in g.models["M"]


def test_stale_receipt_changes_projection_without_changing_graph_bytes(tmp_path):
    S.append([dict(parity.fixture()["model"], ev="model", id="M"),
              {"ev": "claim", "id": "C", "model": "M", "kind": "EMPTY",
               "statement": "ordered example", "certificate": "ORDERED_SOS_CERT", "scope": "ANY_ORDERED"}], str(tmp_path))
    V.verify_all(root=str(tmp_path), record=True, supplied_certificates={"C": parity.fixture()["certificate"]})
    path = Path(S.graph_path(str(tmp_path)))
    before = path.read_bytes()
    g = S.load(str(path))
    first = I.project(g)
    rid = next(iter(g.verdicts))
    assert first["categories"]["bindings"][rid]["candidate"]["current_under_loaded_state"]
    g.models["M"]["generators"] = ["x^2+2"]
    stale = I.project(g)
    assert not stale["categories"]["bindings"][rid]["candidate"]["current_under_loaded_state"]
    assert "binding.current_receipt" in stale["categories"]["bindings"][rid]["missing"]
    assert first["state_fingerprint"] != stale["state_fingerprint"]
    assert path.read_bytes() == before


def test_lean_type_dictionary_and_gate_references_are_checked():
    from grandportage import check as C
    expected = "import GrandPortage.IR\n\n" + "".join(
        "#check " + name + "\n" for name in sorted(I.LEAN_TYPES.values()))
    expected += "".join("#check GrandPortage.IR.ClaimKind." + name + "\n"
                        for name in sorted(I.LEAN_KINDS.values()))
    checkfile = Path(__file__).resolve().parents[1] / "lean/GrandPortage/IRChecks.lean"
    assert checkfile.read_text(encoding="utf-8") == expected
    for gates in I.GATES.values():
        for reference in gates:
            assert callable(getattr(C, reference.split(".", 1)[1]))


def test_integer_identity_projects_but_rational_syntax_is_a_named_gap():
    import pytest
    g = graph()
    g.claims["C"].update(kind="IDENTITY", lhs="x*x", rhs="x^2", identity_origin="AMBIENT")
    assert I.project(g)["categories"]["claims"]["C"]["status"] == "PROJECTABLE"
    with pytest.raises(ValueError, match="rational_expression_adapter"):
        I.expression("1/2", ["x"], 0)
    assert json.loads(I.canonical(I.expression("127", [], 0)))
    with pytest.raises(ValueError, match="expression_adapter_budget"):
        I.expression("510", [], 0)


def test_corpus_manifest_covers_available_inputs_and_pins_source_bytes(tmp_path):
    import hashlib
    from scripts import project_ir_corpus as corpus
    root = Path(__file__).resolve().parents[1]
    corpus.run(tmp_path)
    index = json.loads((tmp_path/"index.json").read_text(encoding="utf-8"))
    retained=json.loads((root/"review/ir-v2-projection/index.json").read_text(encoding="utf-8"))
    assert [(s["source"],s["source_sha256"],s["report_sha256"]) for s in index["sources"]] == [(s["source"],s["source_sha256"],s["report_sha256"]) for s in retained["sources"]]
    available = {p.relative_to(root).as_posix() for p, _, _ in
                 list(corpus.event_files()) + list(corpus.wrapped_fixtures())}
    assert {s["source"] for s in index["sources"]} == available
    assert index["recommendation"] is None
    for item in index["sources"]:
        report = json.loads((tmp_path / item["report"]).read_text(encoding="utf-8"))
        source = report["source"]
        assert hashlib.sha256((root/source["path"]).read_bytes().replace(b"\r\n", b"\n")).hexdigest() == source["sha256"]
        assert report["graph_effect"] == "NONE"
