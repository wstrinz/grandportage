from copy import deepcopy
from pathlib import Path
import json
from grandportage import explain as E, store as S, verify as V, cli
from tests.test_project_v2 import graph
from scripts import check_interpreter_parity as parity
from tests.test_epoch12_contract import _typed_graph, _family_events

def receipt_graph(tmp_path):
    S.append([dict(parity.fixture()["model"],ev="model",id="M"),
              {"ev":"claim","id":"C","model":"M","kind":"EMPTY","statement":"ordered",
               "certificate":"ORDERED_SOS_CERT","scope":"ANY_ORDERED"}],str(tmp_path))
    V.verify_all(root=str(tmp_path),record=True,supplied_certificates={"C":parity.fixture()["certificate"]})
    return S.load(S.graph_path(str(tmp_path)))

def test_ordered_receipt_reifies_conditional_rule_without_tag_inference(tmp_path):
    g=receipt_graph(tmp_path); before=deepcopy(g.models),deepcopy(g.claims),dict(g.authority_receipts)
    report=E.explain(g,"C")
    assert set(report["tree"]["obligations"])==set(E.OBLIGATIONS)
    assert report["tree"]["complete"]
    assert report["tree"]["lost"]["values"]==[]
    assert not report["tree"]["flags"]
    assert before==(g.models,g.claims,g.authority_receipts)
    assert E.explain(graph(),"C")["tree"]["obligations"]["interpreter_requirements"]["status"]=="DATA_GAP"

def test_removed_receipt_and_staled_binding_change_gap(tmp_path):
    g=receipt_graph(tmp_path); rid=next(iter(g.verdicts)); receipt=g.verdicts.pop(rid)
    result=E.explain(g,"C")
    assert result["tree"]["obligations"]["interpreter_requirements"]["missing"]=="retained interpreter receipt"
    g.verdicts[rid]=receipt;g.models["M"]["generators"]=["x^2+2"]
    result=E.explain(g,"C")
    assert result["tree"]["obligations"]["current_binding"]["status"]=="DATA_GAP"
    assert not result["tree"]["complete"]
    assert result["tree"]["lost"]["label"]=="unlicensed observations under available discharge"

def test_deleted_family_record_changes_nonlocal_composition_gap():
    inf={"ev":"inference","id":"I","premises":[{"claim":"C-FAMILY","path":[]},{"claim":"C-MODEL","path":[]}],
         "family_bridges":{"C-FAMILY":"B-E5"},"concludes_kind":"PREDICATE","asserted":"P"}
    g=_typed_graph(_family_events()+[inf])
    before=E.explain(g,"I")["tree"]
    assert before["node_kind"]=="family"
    assert before["obligations"]["composition"]["status"]=="REIFIED"
    del g.families["F"]
    after=E.explain(g,"I")["tree"]
    assert after["obligations"]["composition"]["missing"]=="family record F"

def test_cli_is_read_only_and_dictionary_is_in_aggregate(tmp_path,capsys):
    receipt_graph(tmp_path); path=Path(S.graph_path(str(tmp_path))); before=path.read_bytes()
    assert cli.main(["explain",str(path),"C","--json"])==0
    assert json.loads(capsys.readouterr().out)["graph_effect"]=="NONE"
    assert cli.main(["explain",str(path),"M","--kind","EMPTY"])==0
    assert "unlicensed observations under available discharge" in capsys.readouterr().out
    assert path.read_bytes()==before
    root=Path(__file__).resolve().parents[1]
    assert (root/"lean/GrandPortage/ExplainChecks.lean").read_text()==E.lean_checks()

def test_corpus_absence_never_substitutes_fixtures(tmp_path):
    from scripts.project_ir_corpus import run_campaign_corpus
    r=run_campaign_corpus(tmp_path/"missing",tmp_path/"reports")
    assert r["status"]=="BLOCKED-ON-CORPUS"
    assert r["campaigns"]=={} and r["recommendation"] is None
