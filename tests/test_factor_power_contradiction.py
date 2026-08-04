"""Composition of a factor receipt with the landed JC affine consequence."""

import copy
import json
from pathlib import Path

import pytest

from grandportage import cli
from grandportage import factor_power_contradiction as FPC


FIXTURE = (Path(__file__).parents[1] / "fixtures" / "jc_p_axis" /
           "factor_power_affine_contradiction_v1.json")
FACTOR_FIXTURE = (Path(__file__).parents[1] / "fixtures" / "jc_p_axis" /
                  "factor_power_v1.json")


def _spec():
    return json.loads(FIXTURE.read_text(encoding="utf-8"))


def test_composition_binds_the_checked_in_factor_fixture_exactly():
    factor = json.loads(FACTOR_FIXTURE.read_text(encoding="utf-8"))
    assert _spec()["factor_power"] == factor


def test_landed_jc_axis_contradiction_pattern_verifies_exactly():
    report = FPC.verify(_spec())

    assert report["verdict"] == FPC.VERIFIED
    assert report["factor_receipt"] == "E_3_22_c9_axis"
    assert report["pivot"] == {
        "variable": "c9_11",
        "solution": "-p*t",
        "base": "p*t+c9_11",
    }
    assert report["consequence"]["id"] == "E_1_22_c9_axis"
    assert report["consequence"]["residual"] == "(5)*p*t^2"
    assert report["licenses"] == [
        "exact_factor_to_affine_declared_unit_contradiction_pattern",
    ]


def test_composition_preserves_model_and_semantic_debt():
    report = FPC.verify(_spec())

    assert report["open_obligations"] == [
        "the factor and consequence equations vanish in the same "
        "interpreted target",
        "the interpreted target has no zero divisors",
        "the nonzero scalar coefficients and declared unit generators "
        "remain units in that target",
    ]
    boundary = report["authority_boundary"]
    assert "no model binding" in boundary
    assert "emptiness" in boundary
    assert "claim-transport" in boundary


def test_selected_factor_receipt_must_exist():
    spec = _spec()
    spec["factor_receipt"] = "E_missing"

    with pytest.raises(FPC.FactorPowerContradictionError,
                       match="select one nested"):
        FPC.verify(spec)


def test_pivot_solution_must_solve_a_monic_affine_base():
    spec = _spec()
    spec["pivot"]["solution"] = "-2*p*t"

    with pytest.raises(FPC.FactorPowerContradictionError,
                       match="base must equal pivot - solution"):
        FPC.verify(spec)


def test_pivot_solution_cannot_be_self_referential():
    spec = _spec()
    spec["pivot"]["solution"] = "-p*t+c9_11"

    with pytest.raises(FPC.FactorPowerContradictionError,
                       match="may not contain the pivot"):
        FPC.verify(spec)


def test_consequence_residual_is_recomputed():
    spec = _spec()
    spec["consequence"]["residual"] = "6*p*t^2"

    with pytest.raises(FPC.FactorPowerContradictionError,
                       match="not the exact pivot substitution"):
        FPC.verify(spec)


@pytest.mark.parametrize("residual", ["c9_11", "p+t", "0"])
def test_consequence_must_reduce_to_one_declared_unit_monomial(residual):
    spec = _spec()
    spec["consequence"]["residual"] = residual

    with pytest.raises(FPC.FactorPowerContradictionError,
                       match="unit monomial|unit generators"):
        FPC.verify(spec)


def test_false_nested_factor_receipt_fails_before_composition():
    spec = _spec()
    spec["factor_power"]["receipts"][0]["exponent"] = 1

    with pytest.raises(FPC.FactorPowerContradictionError,
                       match="nested factor-power receipt"):
        FPC.verify(spec)


def test_unknown_fields_fail_closed():
    spec = _spec()
    spec["consequence"]["trust_domain"] = True

    with pytest.raises(FPC.FactorPowerContradictionError,
                       match="unknown field"):
        FPC.verify(spec)


def test_cli_states_compositional_authority_boundary(capsys):
    assert cli.main([
        "verify-factor-power-contradiction", "--spec", str(FIXTURE),
    ]) == 0
    output = capsys.readouterr().out
    assert FPC.VERIFIED in output
    assert "no model binding, emptiness, or claim transport" in output


def test_cli_rejects_false_composition(tmp_path, capsys):
    spec = copy.deepcopy(_spec())
    spec["consequence"]["equation"] = "10*t*c9_11 + 14*p*t^2"
    path = tmp_path / "false-composition.json"
    path.write_text(json.dumps(spec), encoding="utf-8")

    assert cli.main([
        "verify-factor-power-contradiction", "--spec", str(path),
    ]) == 2
    assert "FACTOR POWER CONTRADICTION FAILED" in capsys.readouterr().err
