import copy, importlib.util, json
from pathlib import Path
import pytest
ROOT=Path(__file__).resolve().parents[1]
PATH=ROOT/"experiments"/"jc_h3_source_depth6"/"s2_lowjet_guard_peel_handback_adapter.py"
SPEC=importlib.util.spec_from_file_location("s2_guard",PATH); ADAPTER=importlib.util.module_from_spec(SPEC); SPEC.loader.exec_module(ADAPTER)
@pytest.fixture
def handback(): return ADAPTER.validate_handback_value(ADAPTER.load_fixture())
def by_id(r): return {x["id"]:x for x in r["items"]}
def test_s2_only_closeout_is_closed(handback):
 r=ADAPTER.build_report(handback); x=by_id(r)
 assert r["open_items"]==[]
 assert x[ADAPTER.SIGMA]["effective_status"]=="SIGMA_FULLY_SOURCE_EXCLUDED_INVARIANT_J"
 assert x[ADAPTER.COVER]["effective_status"]=="LOWJET_COVER_COMPLETE"
 assert r["source_authority_ceiling"]=="S2_LOWJET_SOURCE_EXCLUSION_ONLY"
@pytest.mark.parametrize("field",["source_sufficiency_licensed","global_b0_licensed","s1_s3_s4_licensed","h3_licensed","verdict_75125_licensed"])
def test_scope_promotions_refuse(handback,field):
 v=copy.deepcopy(handback); v["closeout"][field]=True
 with pytest.raises(ADAPTER.S2GuardPeelError,match="was promoted"): ADAPTER.validate_handback_value(v)
def test_native_bindings_match_current_sibling_checkout(handback): ADAPTER.check_native_bindings(handback)
def test_review_receipt_regenerates(handback):
 assert json.loads(ADAPTER.REVIEW_RECEIPT.read_text(encoding="utf-8"))==ADAPTER.review_receipt(ADAPTER.build_report(handback))
