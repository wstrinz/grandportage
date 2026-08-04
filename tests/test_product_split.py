"""Binary product-split receipts and refusal of premature branch authority."""

import copy
import json
from pathlib import Path

import pytest

from grandportage import cli
from grandportage import product_split as PS


FIXTURE = (Path(__file__).parents[1] / "fixtures" / "jc_p_axis" /
           "product_split_v1.json")


def _spec():
    return json.loads(FIXTURE.read_text(encoding="utf-8"))


def test_landed_jc_bottom_product_splits_verify():
    report = PS.verify(_spec())

    assert report["verdict"] == PS.VERIFIED
    assert [item["id"] for item in report["receipts"]] == [
        "E_2_0_bottom_split", "E_4_0_bottom_split",
    ]
    assert report["receipts"][0]["left"] == "p*c6_0+c8_0"
    assert report["receipts"][0]["right"] == "p*c7_0+c9_0"
    assert report["licenses"] == [
        "exact_declared_unit_monomial_times_binary_product_identity",
    ]


def test_product_identity_does_not_mint_branches_or_coverage():
    report = PS.verify(_spec())

    assert report["open_obligations"] == [
        "the equation vanishes in the interpreted target",
        "the interpreted target has no zero divisors",
        "the nonzero scalar coefficient and declared unit generators "
        "remain units in that target",
    ]
    boundary = report["authority_boundary"]
    assert "no factor disjunction" in boundary
    assert "branch creation" in boundary
    assert "coverage" in boundary
    assert "claim-transport" in boundary


def test_changed_equation_is_rejected():
    spec = _spec()
    spec["receipts"][0]["equation"] = (
        "10*c6_0*c7_0*p^2 + 9*c6_0*c9_0*p + "
        "10*c7_0*c8_0*p + 10*c8_0*c9_0"
    )

    with pytest.raises(PS.ProductSplitError,
                       match="is not scalar times left times right"):
        PS.verify(spec)


@pytest.mark.parametrize("scalar", ["c6_0", "p+c8_0", "0"])
def test_scalar_must_be_one_declared_unit_monomial(scalar):
    spec = _spec()
    spec["receipts"][0]["scalar"] = scalar

    with pytest.raises(PS.ProductSplitError,
                       match="unit monomial|unit generators"):
        PS.verify(spec)


@pytest.mark.parametrize("field", ["left", "right"])
def test_factors_must_be_nonzero(field):
    spec = _spec()
    spec["receipts"][0][field] = "0"

    with pytest.raises(PS.ProductSplitError, match="factors must be nonzero"):
        PS.verify(spec)


def test_identical_factors_are_not_a_binary_split():
    spec = _spec()
    spec["receipts"][0]["right"] = spec["receipts"][0]["left"]
    spec["receipts"][0]["equation"] = (
        "10*(c6_0*p+c8_0)^2"
    )

    with pytest.raises(PS.ProductSplitError, match="factors must be distinct"):
        PS.verify(spec)


def test_duplicate_ids_and_unknown_fields_fail_closed():
    duplicate = _spec()
    duplicate["receipts"][1]["id"] = duplicate["receipts"][0]["id"]
    with pytest.raises(PS.ProductSplitError, match="ids must be unique"):
        PS.verify(duplicate)

    extra = _spec()
    extra["receipts"][0]["create_branches"] = True
    with pytest.raises(PS.ProductSplitError, match="unknown field"):
        PS.verify(extra)


def test_cli_states_product_only_authority(capsys):
    assert cli.main([
        "verify-product-split", "--spec", str(FIXTURE),
    ]) == 0
    output = capsys.readouterr().out
    assert PS.VERIFIED in output
    assert "no factor disjunction, branch creation, coverage" in output


def test_cli_rejects_false_split(tmp_path, capsys):
    spec = copy.deepcopy(_spec())
    spec["receipts"][1]["scalar"] = "-9*p"
    path = tmp_path / "false-split.json"
    path.write_text(json.dumps(spec), encoding="utf-8")

    assert cli.main([
        "verify-product-split", "--spec", str(path),
    ]) == 2
    assert "PRODUCT SPLIT FAILED" in capsys.readouterr().err
