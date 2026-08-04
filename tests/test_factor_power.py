"""Exact factor-power receipts and their deliberately narrow authority."""

import copy
import json
from pathlib import Path

import pytest

from grandportage import cli
from grandportage import factor_power as FP


FIXTURE = (Path(__file__).parents[1] / "fixtures" / "jc_p_axis" /
           "factor_power_v1.json")


def _spec():
    return json.loads(FIXTURE.read_text(encoding="utf-8"))


def test_landed_jc_p_axis_factor_receipts_verify():
    report = FP.verify(_spec())

    assert report["verdict"] == FP.VERIFIED
    assert [item["id"] for item in report["receipts"]] == [
        "E_3_22_c9_axis", "E_5_22_c9_axis",
    ]
    assert report["licenses"] == [
        "exact_declared_unit_monomial_times_positive_power_identity",
    ]
    assert len(report["spec_fingerprint"]) == 64


def test_report_preserves_semantic_debt_and_refuses_point_authority():
    report = FP.verify(_spec())

    assert report["open_obligations"] == [
        "equation vanishes in the interpreted target",
        "the interpreted target has no zero divisors",
        "the nonzero scalar coefficient and declared unit generators "
        "remain units in that target",
    ]
    boundary = report["authority_boundary"]
    assert "no base-vanishing" in boundary
    assert "emptiness" in boundary
    assert "claim-transport" in boundary


def test_wrong_factor_identity_is_rejected():
    spec = _spec()
    spec["receipts"][0]["equation"] = (
        "5*c9_11^2 + 9*c9_11*p*t + 5*p^2*t^2"
    )

    with pytest.raises(FP.FactorPowerError,
                       match="is not scalar times base"):
        FP.verify(spec)


@pytest.mark.parametrize("exponent", [0, -1, True, 65])
def test_exponent_must_be_bounded_and_strictly_positive(exponent):
    spec = _spec()
    spec["receipts"][0]["exponent"] = exponent

    with pytest.raises(FP.FactorPowerError, match="exponent must be"):
        FP.verify(spec)


@pytest.mark.parametrize("scalar", ["c9_11", "p+t"])
def test_scalar_must_be_a_declared_unit_monomial(scalar):
    spec = _spec()
    spec["receipts"][0]["scalar"] = scalar

    with pytest.raises(FP.FactorPowerError,
                       match="unit monomial|unit generators"):
        FP.verify(spec)


def test_duplicate_ids_and_unknown_fields_fail_closed():
    duplicate = _spec()
    duplicate["receipts"][1]["id"] = duplicate["receipts"][0]["id"]
    with pytest.raises(FP.FactorPowerError, match="ids must be unique"):
        FP.verify(duplicate)

    extra = _spec()
    extra["authority"] = "please trust me"
    with pytest.raises(FP.FactorPowerError, match="unknown field"):
        FP.verify(extra)


def test_cli_states_the_authority_boundary(capsys):
    assert cli.main([
        "verify-factor-power", "--spec", str(FIXTURE),
    ]) == 0
    output = capsys.readouterr().out
    assert FP.VERIFIED in output
    assert "no base-vanishing, emptiness, or claim transport" in output


def test_cli_rejects_a_false_receipt(tmp_path, capsys):
    spec = copy.deepcopy(_spec())
    spec["receipts"][1]["equation"] = "0"
    path = tmp_path / "false.json"
    path.write_text(json.dumps(spec), encoding="utf-8")

    assert cli.main([
        "verify-factor-power", "--spec", str(path),
    ]) == 2
    assert "FACTOR POWER FAILED" in capsys.readouterr().err
