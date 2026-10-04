"""Conditional premise fidelity, native refusals and source preservation."""
import copy
import importlib.util
import json
from pathlib import Path
import pytest
ROOT = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location("conditional",ROOT / "tools/run-phase2-conditional-cover-slice.py")
slice = importlib.util.module_from_spec(spec);spec.loader.exec_module(slice)
def fixture(case_id="GP-A16-covered"):
    return json.loads((ROOT / "corpus/must" / (case_id + ".json")).read_bytes())
def execute(case,label):
    return slice.execute((json.dumps(case) + "\n").encode("utf-8"),label)[0]
@pytest.mark.parametrize("branches,coverage",[(False,False),(False,True),(True,False),(True,True)])
def test_both_named_premises_required(branches,coverage):
    case=fixture();case["inputs"].update(all_listed_branches_empty=branches,checked_exhaustive_cover=coverage)
    out=execute(case,f"control-{branches}-{coverage}")
    assert out["conditional"] is True
    assert (3 in out["state"]["held"]) == (branches and coverage)
    assert out["given"] == (["all_listed_branches_empty"] if branches else []) + (["checked_exhaustive_cover"] if coverage else [])
@pytest.mark.parametrize("mutation",["unknown-input","unknown-case-field","nonboolean","uncommissioned"])
def test_malformed_inputs_refuse(mutation):
    case=fixture()
    if mutation=="unknown-input":case["inputs"]["success"]=True
    elif mutation=="unknown-case-field":case["success"]=True
    elif mutation=="nonboolean":case["inputs"]["checked_exhaustive_cover"]="true"
    else:case["id"]="GP-UNCOMMISSIONED"
    assert execute(case,"malformed-"+mutation)["status"]=="MALFORMED"
def test_expected_verdict_cannot_supply_authority():
    case=fixture("GP-A16-missing");case["expected"]["verdict"]="ACCEPT"
    assert 3 not in execute(case,"expected-not-authority")["state"]["held"]
def test_duplicate_raw_input_key_refuses():
    raw=json.dumps(fixture()).replace('"checked_exhaustive_cover": true','"checked_exhaustive_cover": false, "checked_exhaustive_cover": true')
    out,_=slice.execute(raw.encode("utf-8"),"duplicate-input-key")
    assert out["status"]=="MALFORMED"
def test_report_counts_only_original_conditional_cases_and_preserves_bytes():
    paths=[ROOT/"corpus/must"/(case+".json") for case in slice.CASES]
    before={p:p.read_bytes() for p in paths}
    report=slice.run(slice.SCRATCH/"test-report.json")
    assert report["case_count"]==2 and not report["production_profile_adoption"]
    assert not report["underlying_algebraic_truth_certified"]
    assert all(row["conditional_conclusion_only"] and row["full_fixture_contract"] for row in report["cases"])
    assert [row["observed"] for row in report["cases"]]==["REFUSE","ACCEPT"]
    assert all(p.read_bytes()==raw for p,raw in before.items())
