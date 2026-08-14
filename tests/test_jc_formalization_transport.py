import copy
import importlib.util
import json
from pathlib import Path

import pytest


ROOT = Path(__file__).resolve().parents[1]
SCRIPT = (ROOT / "experiments" / "jc_formalization_transport" /
          "adapter.py")


def _load():
    spec = importlib.util.spec_from_file_location(
        "jc_formalization_transport_test", SCRIPT)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def _fixture(module):
    return json.loads(module.DEFAULT_FIXTURE.read_text(encoding="utf-8"))


def _by_id(records):
    return {record["id"]: record for record in records}


def test_current_ledger_is_derived_and_exercises_every_adversarial_case():
    module = _load()
    report = module.verify_fixture()

    assert report["schema"] == module.SCHEMA
    assert report["authority"] == "DERIVED_READ_MODEL_ONLY"
    assert report["graph_effect"] == "NONE"
    assert report["summary"] == {
        "objects": 18,
        "edges": 13,
        "formal_authorities": 6,
        "assays": 9,
        "licensed": 1,
        "refused": 7,
        "inexpressible": 1,
        "out_of_kernel_edges": report["summary"]["out_of_kernel_edges"],
        "unbound_landed_edges": [],
    }
    assert {item["case"] for item in report["assays"]} == set("ABCDEFGH")
    assert report["native_bindings_checked"] == []


def test_actual_provenance_forgets_forward_but_cannot_be_recovered():
    module = _load()
    assays = _by_id(module.verify_fixture()["assays"])

    assert assays["JC.ASSAY.A.FORWARD_FORGET"]["actual_verdict"] == "LICENSED"
    assert assays["JC.ASSAY.A.REVERSE_REALIZATION"]["actual_verdict"] == "REFUSED"
    assert assays["JC.ASSAY.H.ROWZERO_SCOPE_WIDENING"]["actual_verdict"] == "REFUSED"


def test_degree_five_credit_is_visible_as_a_real_expressibility_gap():
    module = _load()
    assays = _by_id(module.verify_fixture()["assays"])
    result = assays["JC.ASSAY.B.CODOMAIN_CREDIT"]

    assert result["actual_verdict"] == "INEXPRESSIBLE"
    assert "dimension/rank-credit claim kind" in result["reason"]


def test_non_affine_lifts_and_slice_reversal_fail_closed():
    module = _load()
    assays = _by_id(module.verify_fixture()["assays"])

    for assay_id in (
        "JC.ASSAY.C.FINITE_TO_FORMAL",
        "JC.ASSAY.D.INITIAL_TO_ACTUAL",
        "JC.ASSAY.F.DELETE_DISPLACEMENTS",
        "JC.ASSAY.G.SLICE_TO_FULL",
    ):
        assert assays[assay_id]["actual_verdict"] == "REFUSED"


def test_untyped_edge_remains_an_honest_refusal_not_a_transport_license():
    module = _load()
    value = _fixture(module)
    edge = _by_id(value["edges"])["JC.EDGE.FORMAL_ARC_TO_EXACT_WITNESS"]
    edge["relation"] = "UNTYPED"

    report = module.compile_ledger(value)
    assays = _by_id(report["assays"])
    assert assays["JC.ASSAY.C.FINITE_TO_FORMAL"]["actual_verdict"] == "REFUSED"
    assert "UNTYPED edge fails closed" in (
        assays["JC.ASSAY.C.FINITE_TO_FORMAL"]["reason"])


def test_block_one_binding_retains_every_formal_premise():
    module = _load()
    report = module.verify_fixture()
    edges = _by_id(report["edges"])
    authorities = _by_id(report["authorities"])
    wanted = [
        "JC.PREM.ORDER_EIGHT_BOUNDED",
        "JC.PREM.SLICE_IS_SOLUTION",
        "JC.PREM.ALL_ORDERS_GAUGE",
    ]

    assert edges["JC.EDGE.SLICE_TO_BLOCK_ONE_ZERO"]["premise_ids"] == wanted
    assert authorities["JC.AUTH.ACTUAL_BLOCK_ONE"]["premise_ids"] == wanted


def test_omitting_a_formal_premise_is_refused():
    module = _load()
    value = _fixture(module)
    edge = _by_id(value["edges"])["JC.EDGE.SLICE_TO_BLOCK_ONE_ZERO"]
    edge["premise_ids"].remove("JC.PREM.ORDER_EIGHT_BOUNDED")

    with pytest.raises(module.FormalizationLedgerError, match="EDG7"):
        module.compile_ledger(value)


def test_authority_cannot_be_rebound_to_different_semantic_endpoints():
    module = _load()
    value = _fixture(module)
    authority = _by_id(value["authorities"])["JC.AUTH.ACTUAL_BLOCK_ONE"]
    authority["target_object_id"] = "JC.SEM.RELAXED_SUMMIT_POINT"

    with pytest.raises(module.FormalizationLedgerError, match="EDG6"):
        module.compile_ledger(value)


def test_retyping_forgetting_as_equivalence_exposes_the_reverse_widening():
    module = _load()
    value = _fixture(module)
    edge = _by_id(value["edges"])["JC.EDGE.FORGET_ACTUAL_SUMMIT"]
    edge["relation"] = "EQUIVALENCE"

    with pytest.raises(module.FormalizationLedgerError, match="ASY8"):
        module.compile_ledger(value)


def test_field_relative_obstruction_cannot_be_relabelled_scheme_scoped():
    module = _load()
    value = _fixture(module)
    assay = _by_id(value["assays"])["JC.ASSAY.E.FIELD_WIDENING"]
    assay["scope"] = "SCHEME"

    with pytest.raises(module.FormalizationLedgerError, match="ASY8"):
        module.compile_ledger(value)


def test_lossy_edges_must_name_their_information_loss():
    module = _load()
    value = _fixture(module)
    edge = _by_id(value["edges"])["JC.EDGE.LOCAL7_TO_LOCAL5"]
    edge["losses"] = []

    with pytest.raises(module.FormalizationLedgerError, match="EDG9"):
        module.compile_ledger(value)


def test_live_jc_commit_sources_and_declarations_are_bound(
        explicit_jc_native_binding_check):
    module = _load()
    if not module.NATIVE_ROOT.exists():
        pytest.skip("sibling JC checkout is not present")

    report = module.verify_fixture(check_bindings=True)
    assert report["native_bindings_checked"] == sorted(
        source["id"] for source in report["sources"])


def test_declaration_and_digest_drift_are_refused_before_use(
        explicit_jc_native_binding_check):
    module = _load()
    if not module.NATIVE_ROOT.exists():
        pytest.skip("sibling JC checkout is not present")
    report = module.verify_fixture()

    changed_declaration = copy.deepcopy(report)
    changed_declaration["authorities"][0]["source_contains"] = (
        "theorem definitely_not_in_the_bound_module")
    with pytest.raises(module.FormalizationLedgerError, match="BND6"):
        module.check_native_bindings(changed_declaration)

    changed_digest = copy.deepcopy(report)
    changed_digest["sources"][0]["sha256"] = "0" * 64
    with pytest.raises(module.FormalizationLedgerError, match="BND4"):
        module.check_native_bindings(changed_digest)


def test_output_is_deterministic_and_input_order_independent():
    module = _load()
    value = _fixture(module)
    first = module.compile_ledger(value)
    value["objects"].reverse()
    value["edges"].reverse()
    value["authorities"].reverse()
    second = module.compile_ledger(value)

    # The input fingerprint preserves the authored source ordering, but every
    # projected semantic collection is canonical and stable.
    for field in ("objects", "edges", "authorities", "premises", "assays"):
        assert first[field] == second[field]
