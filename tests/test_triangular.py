"""Ordered localized triangular-chain validation and refusal controls."""

import copy
import json
from pathlib import Path

import pytest

from grandportage import cli
from grandportage import triangular as TRI


FIXTURE = (Path(__file__).parents[1] / "fixtures" / "jc_source_ladder" /
           "localized_triangular_solve_chain_v1.json")
SECOND_FIXTURE = (Path(__file__).parents[1] / "fixtures" /
                  "jc_source_ladder" /
                  "localized_triangular_solve_chain_v2_second_face.json")


def _spec():
    return json.loads(FIXTURE.read_text(encoding="utf-8"))


def _initial_fingerprint(spec):
    return TRI.state_fingerprint(
        spec["characteristic"], spec["coefficient_domain"],
        spec["point_universe"], spec["ring_vars"],
        spec["unit_generators"], spec["initial_generators"],
    )


def test_jc_top_face_five_step_contract_pilot_verifies():
    report = TRI.verify(_spec())

    assert report["verdict"] == TRI.VERIFIED
    assert report["checked_steps"] == 5
    assert [step["id"] for step in report["steps"]] == [
        "top-r2", "top-r5", "top-r1", "top-r4", "top-r3",
    ]
    assert [step["pivot"] for step in report["steps"]] == [
        "I4", "c6_9", "c9_14", "I1", "Im1",
    ]
    assert report["source_receipt"]["id"] == "f2_h3_q_receipt_probe"
    assert _spec()["initial_generators"][2].count("I4") > 0
    assert _spec()["initial_generators"][2].count("c6_9") > 0
    assert len(report["final_generators"]) == 1


def test_jc_second_face_verifies_modulo_exact_scalar_gauge_receipts():
    spec = json.loads(SECOND_FIXTURE.read_text(encoding="utf-8"))
    report = TRI.verify(spec)

    assert report["schema"] == TRI.SCHEMA_V2
    assert report["checked_steps"] == 5
    assert report["normalization_generators"] == ["(15)*t^3+1"]
    assert report["licenses"] == [
        "exact_ordered_localized_triangular_substitution_chain_"
        "modulo_declared_normalization_generators",
    ]
    assert [step["id"] for step in report["steps"]] == [
        "second-r2", "second-r5", "second-r1", "second-r4", "second-r3",
    ]
    assert all(step["normalization_cofactors"]
               for step in report["steps"])


def test_changed_second_face_normalization_cofactor_is_rejected():
    spec = json.loads(SECOND_FIXTURE.read_text(encoding="utf-8"))
    spec["steps"][2]["normalization_cofactors"][0] += "+1"

    with pytest.raises(TRI.TriangularChainError,
                       match="declared normalization receipt"):
        TRI.verify(spec)


def test_second_face_context_is_state_fingerprint_bound():
    spec = json.loads(SECOND_FIXTURE.read_text(encoding="utf-8"))
    spec["normalization_generators"][0] = "15*t^3+2"

    with pytest.raises(TRI.TriangularChainError,
                       match="input_state_fingerprint"):
        TRI.verify(spec)


def test_normalization_context_may_not_depend_on_a_chain_pivot():
    spec = json.loads(SECOND_FIXTURE.read_text(encoding="utf-8"))
    spec["normalization_generators"][0] = "15*t^3+c3_4"

    with pytest.raises(TRI.TriangularChainError,
                       match="may not use chain pivot"):
        TRI.verify(spec)


def test_chain_report_preserves_semantic_debt():
    report = TRI.verify(_spec())

    assert report["licenses"] == [
        "exact_ordered_localized_triangular_substitution_chain",
    ]
    assert "bind the initial" in report["open_obligations"][0]
    boundary = report["authority_boundary"]
    assert "no graph model equivalence" in boundary
    assert "emptiness" in boundary
    assert "parent coverage" in boundary
    assert "source-membership" in boundary
    assert "H3" in boundary


def test_changed_step_order_is_rejected():
    spec = _spec()
    spec["steps"][0], spec["steps"][1] = spec["steps"][1], spec["steps"][0]

    with pytest.raises(TRI.TriangularChainError,
                       match="input_state_fingerprint"):
        TRI.verify(spec)


def test_missing_prior_substitution_is_rejected():
    spec = _spec()
    spec["steps"][0]["output_generators"][-1] = (
        spec["steps"][0]["output_generators"][-1] + "+I4"
    )

    with pytest.raises(TRI.TriangularChainError,
                       match="exact ordered substitution result"):
        TRI.verify(spec)


def test_changed_state_fingerprint_is_rejected():
    spec = _spec()
    spec["steps"][2]["input_state_fingerprint"] = "sha256:" + "0" * 64

    with pytest.raises(TRI.TriangularChainError,
                       match="input_state_fingerprint"):
        TRI.verify(spec)


def test_coordinate_bearing_pivot_coefficient_is_not_a_unit():
    spec = _spec()
    equation = "c3_5*(I4-5/2*c3_5)"
    spec["initial_generators"][0] = equation
    spec["steps"][0]["equation"] = equation
    spec["steps"][0]["coefficient"] = "c3_5"
    spec["steps"][0]["input_state_fingerprint"] = _initial_fingerprint(spec)

    with pytest.raises(TRI.TriangularChainError,
                       match="declared unit generators"):
        TRI.verify(spec)


def test_cross_chart_guard_list_is_rejected():
    spec = _spec()
    spec["unit_generators"] = ["q"]

    with pytest.raises(TRI.TriangularChainError,
                       match="distinct ring variables"):
        TRI.verify(spec)


def test_changed_normalized_output_polynomial_is_rejected():
    spec = _spec()
    spec["steps"][3]["output_generators"][0] += "+1"

    with pytest.raises(TRI.TriangularChainError,
                       match="exact ordered substitution result"):
        TRI.verify(spec)


def test_solution_may_not_reintroduce_another_chain_pivot():
    spec = _spec()
    equation = "2*t^2*(I4-c6_9)"
    spec["initial_generators"][0] = equation
    spec["steps"][0]["equation"] = equation
    spec["steps"][0]["solution"] = "c6_9"
    spec["steps"][0]["input_state_fingerprint"] = _initial_fingerprint(spec)

    with pytest.raises(TRI.TriangularChainError,
                       match="any chain pivot variable"):
        TRI.verify(spec)


def test_unmodelled_normalization_receipt_fails_closed():
    spec = _spec()
    spec["steps"][0]["denominator_clearing"] = {"power": 1}

    with pytest.raises(TRI.TriangularChainError, match="unknown field"):
        TRI.verify(spec)


def test_source_receipt_fingerprint_is_typed():
    spec = _spec()
    spec["source_receipt"]["sha256"] = "probably the same receipt"

    with pytest.raises(TRI.TriangularChainError,
                       match="source_receipt sha256"):
        TRI.verify(spec)


@pytest.mark.parametrize("field,value", [
    ("coefficient_domain", "R"),
    ("point_universe", "GENERIC"),
])
def test_domain_and_point_universe_are_typed(field, value):
    spec = _spec()
    spec[field] = value

    with pytest.raises(TRI.TriangularChainError, match=field):
        TRI.verify(spec)


def test_cli_reports_v2_normalization_without_graph_authority(capsys):
    assert cli.main([
        "verify-localized-triangular-chain", "--spec", str(SECOND_FIXTURE),
    ]) == 0
    output = capsys.readouterr().out
    assert "normalization generators: 1" in output
    assert "no graph equivalence" in output


def test_cli_states_no_graph_authority(capsys):
    assert cli.main([
        "verify-localized-triangular-chain", "--spec", str(FIXTURE),
    ]) == 0
    output = capsys.readouterr().out
    assert TRI.VERIFIED in output
    assert "no graph equivalence, emptiness, coverage, source, or H3 claim" in output


def test_cli_rejects_false_chain(tmp_path, capsys):
    spec = copy.deepcopy(_spec())
    spec["steps"][4]["coefficient"] = "t"
    path = tmp_path / "false-chain.json"
    path.write_text(json.dumps(spec), encoding="utf-8")

    assert cli.main([
        "verify-localized-triangular-chain", "--spec", str(path),
    ]) == 2
    assert "LOCALIZED TRIANGULAR CHAIN FAILED" in capsys.readouterr().err
