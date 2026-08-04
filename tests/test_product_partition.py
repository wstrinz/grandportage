"""Checked product receipts compiled into first-class binary partitions."""

import json
from dataclasses import FrozenInstanceError
from pathlib import Path

import pytest

from grandportage import cli
from grandportage import contracts as OC
from grandportage import kernel as K
from grandportage import operations as O
from grandportage import store as S
from grandportage import verify as V


FIXTURE = (Path(__file__).parents[1] / "fixtures" / "jc_p_axis" /
           "product_split_v1.json")


def _spec():
    return json.loads(FIXTURE.read_text(encoding="utf-8"))


def _parent_equation():
    return _spec()["receipts"][0]["equation"]


def _operation(**overrides):
    args = {
        "src": "P_AXIS_BOTTOM",
        "ring_vars": _spec()["ring_vars"],
        "generators": [_parent_equation()],
        "receipt_spec": _spec(),
        "receipt_id": "E_2_0_bottom_split",
        "coefficient_domain": "Q",
        "point_universe": S.ALGEBRAIC_CLOSURE_POINT_UNIVERSE,
    }
    args.update(overrides)
    return O.product_split(**args)


def _fold(events):
    return S.Graph().apply_all(
        [(event, "product-partition", index)
         for index, event in enumerate(events)]
    ).validate()


def _init_campaign(root, equation=None):
    assert cli.main(["--root", str(root), "init"]) == 0
    S.append([{
        "ev": "model",
        "id": "P_AXIS_BOTTOM",
        "what": "JC bottom-block equation",
        "characteristic": 0,
        "ring_vars": _spec()["ring_vars"],
        "generators": [equation or _parent_equation()],
        "open_conditions": ["p"],
        "coefficient_domain": "Q",
        "point_universe": S.ALGEBRAIC_CLOSURE_POINT_UNIVERSE,
    }], str(root))


def test_partition_contract_is_nary_not_an_operation_contract():
    contract = OC.PRODUCT_SPLIT_PARTITION

    assert isinstance(contract, OC.PartitionContract)
    assert not isinstance(contract, OC.OperationContract)
    assert contract.branch_edge_type == K.NECESSARY_CONDITION
    assert "union" in contract.semantic_relation
    assert set(obligation.name for obligation
               in contract.checked_obligations) == {
        "binary_product_identity",
        "parent_equation_binding",
        "constant_unit_scalar",
        "partition_exhaustiveness",
    }
    assert OC.PARTITION_CONTRACTS["ProductSplit"] is contract


def test_partition_contract_is_immutable_audit_data():
    with pytest.raises(FrozenInstanceError):
        OC.PRODUCT_SPLIT_PARTITION.semantic_relation = "trust the factors"


def test_jc_product_receipt_mints_two_branch_models_and_one_partition():
    op = _operation(open_conditions=["p"])

    assert op.contract is OC.PRODUCT_SPLIT_PARTITION
    assert op.program is None
    assert [event["ev"] for event in op.events].count("model") == 2
    assert [event["ev"] for event in op.events].count("edge") == 2
    assert [event["ev"] for event in op.events].count("claim") == 1
    assert [event["ev"] for event in op.events].count("partition") == 1

    models = [event for event in op.events if event["ev"] == "model"]
    assert models[0]["generators"][:-1] == [_parent_equation()]
    assert models[0]["generators"][-1] == "p*c6_0+c8_0"
    assert models[1]["generators"][-1] == "p*c7_0+c9_0"
    assert all(model["open_conditions"] == ["p"] for model in models)
    assert all(model["component_of"] == "P_AXIS_BOTTOM" for model in models)


def test_branch_edges_run_from_each_tighter_branch_to_parent():
    op = _operation()
    edges = [event for event in op.events if event["ev"] == "edge"]

    assert all(edge["dst"] == "P_AXIS_BOTTOM" for edge in edges)
    assert all(edge["src"] != "P_AXIS_BOTTOM" for edge in edges)
    assert all(edge["type"] == K.NECESSARY_CONDITION for edge in edges)
    assert all(edge["built_by_operation"] == "ProductSplit" for edge in edges)


def test_partition_binds_the_exact_receipt_fingerprint():
    op = _operation()
    partition = next(event for event in op.events
                     if event["ev"] == "partition")

    assert partition["receipt_schema"] == "product_split_v1"
    assert partition["receipt_id"] == "E_2_0_bottom_split"
    assert partition["receipt_fingerprint"] == op.request[
        "receipt_fingerprint"]
    assert partition["exhaustive"] == next(
        event["id"] for event in op.events if event["ev"] == "claim")


def test_emitted_events_form_a_valid_graph_partition():
    parent = {
        "ev": "model", "id": "P_AXIS_BOTTOM", "what": "JC bottom block",
        "characteristic": 0, "ring_vars": _spec()["ring_vars"],
        "generators": [_parent_equation()],
        "coefficient_domain": "Q",
        "point_universe": S.ALGEBRAIC_CLOSURE_POINT_UNIVERSE,
    }
    graph = _fold([parent] + _operation().events)

    partition = graph.partitions[
        "P-P_AXIS_BOTTOM-E_2_0_bottom_split"]
    assert len(partition["branches"]) == 2
    assert partition["parent"] == "P_AXIS_BOTTOM"


def test_existing_exhaustiveness_verifier_consumes_the_emitted_partition():
    parent = {
        "ev": "model", "id": "P_AXIS_BOTTOM", "what": "JC bottom block",
        "characteristic": 0, "ring_vars": _spec()["ring_vars"],
        "generators": [_parent_equation()],
        "coefficient_domain": "Q",
        "point_universe": S.ALGEBRAIC_CLOSURE_POINT_UNIVERSE,
    }
    graph = _fold([parent] + _operation().events)

    class Backend:
        def membership(self, ring, expression, generators,
                       characteristic, timeout):
            assert expression == "1"
            return {"is_member": False}

        def partition_cover(self, ring, parent_generators, branch_generators,
                            characteristic, timeout):
            assert parent_generators == [_parent_equation()]
            assert len(branch_generators) == 2
            assert branch_generators[0][-1] == "p*c6_0+c8_0"
            assert branch_generators[1][-1] == "p*c7_0+c9_0"
            return True, {"why": "exact binary product"}

    verdict, why = V.partition_exhaustiveness(
        graph, "P-P_AXIS_BOTTOM-E_2_0_bottom_split", _backend=Backend())
    assert verdict == V.COVERS
    assert "COMPLETE" in why


@pytest.mark.live
def test_jc_product_partition_verifies_against_real_backend():
    parent = {
        "ev": "model", "id": "P_AXIS_BOTTOM", "what": "JC bottom block",
        "characteristic": 0, "ring_vars": _spec()["ring_vars"],
        "generators": [_parent_equation()],
        "coefficient_domain": "Q",
        "point_universe": S.ALGEBRAIC_CLOSURE_POINT_UNIVERSE,
    }
    graph = _fold([parent] + _operation().events)

    verdict, why = V.partition_exhaustiveness(
        graph, "P-P_AXIS_BOTTOM-E_2_0_bottom_split", timeout=120)
    assert verdict == V.COVERS, why

def test_variable_unit_receipt_remains_evidence_but_cannot_mint_cover():
    with pytest.raises(ValueError, match="constant-unit scalar"):
        _operation(receipt_id="E_4_0_bottom_split",
                   generators=[_spec()["receipts"][1]["equation"]])


def test_nonliteral_parent_membership_is_not_invented():
    with pytest.raises(ValueError, match="literal parent generator"):
        _operation(generators=["0"])


def test_receipt_ring_and_characteristic_must_match_parent():
    with pytest.raises(ValueError, match="ring_vars must equal"):
        _operation(ring_vars=list(reversed(_spec()["ring_vars"])))

    with pytest.raises(ValueError, match="characteristic must equal"):
        _operation(characteristic=5)


def test_receipt_id_and_branch_ids_fail_closed():
    with pytest.raises(ValueError, match="select one verified"):
        _operation(receipt_id="missing")

    with pytest.raises(ValueError, match="two distinct branch ids"):
        _operation(src="P_AXIS_BOTTOM0", produces="P_AXIS_BOTTOM")


def test_false_product_receipt_fails_before_any_events_are_minted():
    spec = _spec()
    spec["receipts"][0]["scalar"] = "9"

    with pytest.raises(ValueError, match="not scalar times"):
        _operation(receipt_spec=spec)


def test_cli_construct_product_split_dry_run_uses_source_algebra(
        tmp_path, capsys):
    _init_campaign(tmp_path)
    capsys.readouterr()

    rc = cli.main([
        "--root", str(tmp_path), "construct", "product-split",
        "--src", "P_AXIS_BOTTOM", "--spec", str(FIXTURE),
        "--receipt", "E_2_0_bottom_split", "--produces", "JC-F%d",
    ])

    assert rc == 0
    events = json.loads(capsys.readouterr().out)
    models = [event for event in events if event["ev"] == "model"]
    assert [model["id"] for model in models] == ["JC-F0", "JC-F1"]
    assert all(model["ring_vars"] == _spec()["ring_vars"] for model in models)
    assert all(model["open_conditions"] == ["p"] for model in models)
    assert any(event["ev"] == "partition" for event in events)
    assert "JC-F0" not in S.load(S.graph_path(str(tmp_path))).models


def test_cli_construct_product_split_declare_persists_valid_partition(
        tmp_path, capsys):
    _init_campaign(tmp_path)
    capsys.readouterr()

    rc = cli.main([
        "--root", str(tmp_path), "construct", "product-split",
        "--src", "P_AXIS_BOTTOM", "--spec", str(FIXTURE),
        "--receipt", "E_2_0_bottom_split", "--declare",
    ])

    assert rc == 0
    assert "declared 6 event(s)" in capsys.readouterr().out
    graph = S.load(S.graph_path(str(tmp_path))).validate()
    assert {"P_AXIS_BOTTOM_F0", "P_AXIS_BOTTOM_F1"} <= set(graph.models)
    partition = graph.partitions[
        "P-P_AXIS_BOTTOM-E_2_0_bottom_split"]
    assert partition["branches"] == [
        "P_AXIS_BOTTOM_F0", "P_AXIS_BOTTOM_F1"]


def test_cli_product_split_reports_missing_inputs_and_files(tmp_path, capsys):
    _init_campaign(tmp_path)
    capsys.readouterr()

    rc = cli.main([
        "--root", str(tmp_path), "construct", "product-split",
        "--src", "P_AXIS_BOTTOM",
    ])
    assert rc == 2
    assert "requires --spec and --receipt" in capsys.readouterr().err

    rc = cli.main([
        "--root", str(tmp_path), "construct", "product-split",
        "--src", "P_AXIS_BOTTOM", "--spec", str(tmp_path / "missing.json"),
        "--receipt", "E_2_0_bottom_split",
    ])
    assert rc == 2
    assert "missing.json" in capsys.readouterr().err


def test_cli_product_split_preserves_localization_refusal(tmp_path, capsys):
    equation = _spec()["receipts"][1]["equation"]
    _init_campaign(tmp_path, equation=equation)
    capsys.readouterr()

    rc = cli.main([
        "--root", str(tmp_path), "construct", "product-split",
        "--src", "P_AXIS_BOTTOM", "--spec", str(FIXTURE),
        "--receipt", "E_4_0_bottom_split",
    ])

    assert rc == 2
    assert "constant-unit scalar" in capsys.readouterr().err
