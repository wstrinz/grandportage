"""Coefficient-expansion translation validation and adversarial controls."""

import copy
import json

import pytest

from grandportage import coefficient_expansion as CE
from grandportage import cli
from grandportage import groebner as G


def _product_spec(coverage=CE.COMPLETE):
    coefficients = {
        "0": "a0*b0",
        "1": "a0*b1+a1*b0",
        "2": "a1*b1",
    }
    if coverage == CE.SELECTED:
        coefficients = {"0": coefficients["0"], "1": coefficients["1"]}
    return {
        "schema": CE.SCHEMA,
        "characteristic": 0,
        "parameter": "y",
        "coefficient_variables": ["a0", "a1", "b0", "b1"],
        "source_variables": ["p", "q"],
        "images": {
            "p": "a0+a1*y",
            "q": "b0+b1*y",
        },
        "bounded_variables": {
            "p": {"cap": 1, "coefficients": ["a0", "a1"]},
            "q": {"cap": 1, "coefficients": ["b0", "b1"]},
        },
        "equations": [{
            "id": "PRODUCT",
            "expression": "p*q",
            "degree": 2,
            "coverage": coverage,
            "coefficients": coefficients,
        }],
    }


def test_complete_expansion_checks_pack_and_every_coefficient():
    report = CE.verify(_product_spec())

    assert report["verdict"] == CE.VERIFIED_COMPLETE
    assert report["licenses"] == [
        "polynomial_identity_iff_all_rows_zero"
    ]
    assert report["equations"][0]["checked_coefficients"] == {
        "0": "a0*b0",
        "1": "a0*b1+a1*b0",
        "2": "a1*b1",
    }
    assert len(report["spec_fingerprint"]) == 64


def test_selected_coefficients_are_necessary_only():
    report = CE.verify(_product_spec(CE.SELECTED))

    assert report["verdict"] == CE.VERIFIED_SELECTED
    assert report["licenses"] == [
        "polynomial_identity_implies_selected_rows_zero"
    ]


def test_complete_expansion_rejects_an_omitted_overflow_row():
    spec = _product_spec()
    equation = spec["equations"][0]
    equation["degree"] = 1
    equation["coefficients"].pop("2")

    with pytest.raises(CE.CoefficientExpansionError,
                       match="omitted overflow coefficient y\\^2"):
        CE.verify(spec)


def test_selected_rows_may_omit_overflow_without_minting_equivalence():
    spec = _product_spec(CE.SELECTED)
    spec["equations"][0]["degree"] = 2

    assert CE.verify(spec)["verdict"] == CE.VERIFIED_SELECTED


def test_invented_or_wrong_coefficient_is_rejected():
    spec = _product_spec()
    spec["equations"][0]["coefficients"]["1"] = "a0*b1+a1*b0+1"

    with pytest.raises(CE.CoefficientExpansionError,
                       match="coefficient 1 is wrong"):
        CE.verify(spec)


@pytest.mark.parametrize("bad_key", ["01", "-1", "one"])
def test_coefficient_row_keys_are_canonical_nonnegative_integers(bad_key):
    spec = _product_spec()
    spec["equations"][0]["coefficients"][bad_key] = "0"

    with pytest.raises(CE.CoefficientExpansionError,
                       match="canonical nonnegative integers"):
        CE.verify(spec)


def test_cap_means_cap_plus_one_distinct_coordinates():
    spec = _product_spec()
    spec["bounded_variables"]["p"]["coefficients"] = ["a0"]

    with pytest.raises(CE.CoefficientExpansionError,
                       match="requires exactly 2 coefficient coordinates"):
        CE.verify(spec)


def test_pack_order_and_images_are_checked_not_declared():
    spec = _product_spec()
    spec["bounded_variables"]["p"]["coefficients"] = ["a1", "a0"]

    with pytest.raises(CE.CoefficientExpansionError,
                       match="does not exactly pack"):
        CE.verify(spec)


def test_one_coordinate_cannot_pack_two_bounded_polynomials():
    spec = _product_spec()
    spec["bounded_variables"]["q"]["coefficients"] = ["a0", "a1"]
    spec["images"]["q"] = "a0+a1*y"

    with pytest.raises(CE.CoefficientExpansionError,
                       match="cannot pack two bounded variables"):
        CE.verify(spec)


def test_recorded_rows_must_live_in_the_scalar_ring():
    spec = _product_spec()
    spec["equations"][0]["coefficients"]["0"] = "a0*b0+y"

    with pytest.raises(CE.CoefficientExpansionError,
                       match="must be a scalar-ring polynomial"):
        CE.verify(spec)


def test_images_cannot_retain_source_variables():
    spec = _product_spec()
    spec["images"]["p"] = "p+a0"

    with pytest.raises(CE.CoefficientExpansionError,
                       match="may not use a source variable"):
        CE.verify(spec)


def test_source_equation_cannot_smuggle_in_lowered_coordinates():
    spec = _product_spec()
    spec["equations"][0]["expression"] = "p*q+a0"

    with pytest.raises(CE.CoefficientExpansionError,
                       match="source expression may use only source variables"):
        CE.verify(spec)


def test_specification_is_closed_and_fingerprinted_deterministically():
    spec = _product_spec()
    first = CE.verify(spec)["spec_fingerprint"]
    second = CE.verify(copy.deepcopy(spec))["spec_fingerprint"]
    assert first == second

    spec["authority"] = "please trust me"
    with pytest.raises(CE.CoefficientExpansionError,
                       match="unknown field"):
        CE.verify(spec)


def test_cli_reports_the_authority_boundary(tmp_path, capsys):
    path = tmp_path / "coefficient.json"
    path.write_text(json.dumps(_product_spec()), encoding="utf-8")

    assert cli.main([
        "verify-coefficient-expansion", "--spec", str(path)
    ]) == 0
    output = capsys.readouterr().out
    assert CE.VERIFIED_COMPLETE in output
    assert "identity iff every recorded coefficient" in output

    path.write_text(json.dumps(_product_spec(CE.SELECTED)), encoding="utf-8")
    assert cli.main([
        "verify-coefficient-expansion", "--spec", str(path)
    ]) == 0
    output = capsys.readouterr().out
    assert CE.VERIFIED_SELECTED in output
    assert "no converse" in output


def test_large_sparse_image_survives_coefficient_lowering_without_infix_ast():
    terms = []
    for exponent in range(1200, -1, -1):
        powers = [["c", 1]]
        if exponent:
            powers.append(["y", exponent])
        terms.append({"coefficient": "1", "powers": powers})
    image = {"schema": G.SPARSE_POLYNOMIAL_SCHEMA, "terms": terms}
    spec = {
        "schema": CE.SCHEMA,
        "characteristic": 0,
        "parameter": "y",
        "coefficient_variables": ["c"],
        "source_variables": ["A"],
        "images": {"A": image},
        "bounded_variables": {},
        "equations": [{
            "id": "large-selected-row",
            "expression": "A",
            "degree": 1200,
            "coverage": CE.SELECTED,
            "coefficients": {"0": "c"},
        }],
    }

    report = CE.verify(spec)

    assert report["verdict"] == CE.VERIFIED_SELECTED
    assert report["equations"][0]["checked_coefficients"] == {"0": "c"}


def test_large_sparse_image_order_mutation_is_refused():
    spec = {
        "schema": G.SPARSE_POLYNOMIAL_SCHEMA,
        "terms": [
            {"coefficient": "1", "powers": [["x", 1]]},
            {"coefficient": "1", "powers": [["x", 2]]},
        ],
    }
    with pytest.raises(G.CertificateError, match="descending lexicographic"):
        G.parse_polynomial(spec, ["x"])
