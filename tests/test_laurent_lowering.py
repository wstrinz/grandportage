"""Finite Laurent lowering checks and the rows 7--8 chart control."""

import copy
import json
from pathlib import Path

import pytest

from grandportage import cli
from grandportage import coefficient_expansion as CE
from grandportage import laurent_coefficient_pipeline as LCP
from grandportage import laurent_lowering as LL


def _rows78_spec():
    return {
        "schema": LL.SCHEMA,
        "characteristic": 0,
        "series_variable": "y",
        "coefficient_variables": [
            "g5", "g2", "c0", "c210", "c27", "c24", "c21",
        ],
        "inputs": {
            "G": {"-5": "g5", "-2": "g2"},
            "F6": {"3": "-1/9", "0": "c0"},
            "F7": {"-2": "-g5/3", "1": "2*g2/3"},
            "C1": {
                "-10": "c210", "-7": "c27",
                "-4": "c24", "-1": "c21",
            },
            "F8": {
                "-10": "-2*c0*c210",
                "-7": "g5^2/21+13*c210/63-2*c0*c27",
                "-4": "g5*g2/6+7*c27/36-2*c0*c24",
                "-1": "g2^2/3+c24/9-2*c0*c21",
                "2": "5*c21/18",
            },
            "Y2": {"2": "1"},
            "ZERO": {},
        },
        "program": [
            {"id": "dF7", "op": "derivative", "arg": "F7"},
            {"id": "lhs7", "op": "scale", "arg": "dF7", "scalar": "9"},
            {"id": "y2G", "op": "multiply", "left": "Y2", "right": "G"},
            {"id": "rhs7", "op": "scale", "arg": "y2G", "scalar": "6"},
            {"id": "dF8", "op": "derivative", "arg": "F8"},
            {"id": "nine_dF8", "op": "scale", "arg": "dF8",
             "scalar": "9"},
            {"id": "dF6", "op": "derivative", "arg": "F6"},
            {"id": "C1_dF6", "op": "multiply",
             "left": "C1", "right": "dF6"},
            {"id": "twentyone_C1_dF6", "op": "scale",
             "arg": "C1_dF6", "scalar": "21"},
            {"id": "dC1", "op": "derivative", "arg": "C1"},
            {"id": "dC1_F6", "op": "multiply",
             "left": "dC1", "right": "F6"},
            {"id": "eighteen_dC1_F6", "op": "scale",
             "arg": "dC1_F6", "scalar": "18"},
            {"id": "lhs8a", "op": "add",
             "left": "nine_dF8", "right": "twentyone_C1_dF6"},
            {"id": "lhs8", "op": "add",
             "left": "lhs8a", "right": "eighteen_dC1_F6"},
            {"id": "G2", "op": "multiply", "left": "G", "right": "G"},
            {"id": "y2G2", "op": "multiply",
             "left": "Y2", "right": "G2"},
            {"id": "rhs8", "op": "scale", "arg": "y2G2",
             "scalar": "-3"},
        ],
        "equalities": [
            {"id": "depressed-x1", "left": "lhs7", "right": "rhs7"},
            {"id": "depressed-x0", "left": "lhs8", "right": "rhs8"},
        ],
        "exports": [
            {"id": "F7_polynomial", "node": "F7", "shift": 2},
            {"id": "F8_polynomial", "node": "F8", "shift": 10},
        ],
    }


def test_rows78_depressed_chart_receipts_verify_exactly():
    report = LL.verify(_rows78_spec())

    assert report["verdict"] == LL.VERIFIED
    assert report["licenses"] == [
        "declared_finite_laurent_equalities",
        "canonical_shifted_polynomial_exports",
    ]
    assert [item["id"] for item in report["equalities"]] == [
        "depressed-x1", "depressed-x0",
    ]
    assert len(report["spec_fingerprint"]) == 64


def test_export_is_directly_consumable_by_coefficient_expansion():
    report = LL.verify(_rows78_spec())
    exported = {item["id"]: item for item in report["exports"]}
    assert exported["F7_polynomial"]["support"] == [0, 3]
    assert exported["F7_polynomial"]["degree"] == 3
    assert exported["F8_polynomial"]["degree"] == 12

    coefficient_spec = {
        "schema": CE.SCHEMA,
        "characteristic": 0,
        "parameter": "y",
        "coefficient_variables": [
            "g5", "g2", "c0", "c210", "c27", "c24", "c21",
        ],
        "source_variables": ["F7source"],
        "images": {
            "F7source": exported["F7_polynomial"]["polynomial"],
        },
        "bounded_variables": {},
        "equations": [{
            "id": "F7-receipt",
            "expression": "F7source",
            "degree": 3,
            "coverage": CE.COMPLETE,
            "coefficients": {
                "0": "-g5/3", "1": "0", "2": "0", "3": "2*g2/3",
            },
        }],
    }

    lowered = CE.verify(coefficient_spec)
    assert lowered["verdict"] == CE.VERIFIED_COMPLETE


def test_export_refuses_an_incomplete_negative_power_clearing():
    spec = _rows78_spec()
    spec["exports"][1]["shift"] = 9

    with pytest.raises(LL.LaurentLoweringError,
                       match="does not clear every negative"):
        LL.verify(spec)


def _pipeline_spec():
    laurent = _rows78_spec()
    exports = {
        item["id"]: item for item in LL.verify(laurent)["exports"]
    }
    coefficient = {
        "schema": CE.SCHEMA,
        "characteristic": 0,
        "parameter": "y",
        "coefficient_variables": [
            "g5", "g2", "c0", "c210", "c27", "c24", "c21",
        ],
        "source_variables": ["F7source"],
        "images": {
            "F7source": exports["F7_polynomial"]["polynomial"],
        },
        "bounded_variables": {},
        "equations": [{
            "id": "F7-receipt",
            "expression": "F7source",
            "degree": 3,
            "coverage": CE.COMPLETE,
            "coefficients": {
                "0": "-g5/3", "1": "0", "2": "0", "3": "2*g2/3",
            },
        }],
    }
    return {
        "schema": LCP.SCHEMA,
        "laurent": laurent,
        "coefficient_expansion": coefficient,
        "bindings": [{
            "export": "F7_polynomial",
            "image": "F7source",
        }],
    }


def test_pipeline_binds_both_verified_passes():
    report = LCP.verify(_pipeline_spec())

    assert report["verdict"] == LCP.VERIFIED
    assert report["bindings"] == [{
        "export": "F7_polynomial", "image": "F7source",
    }]
    assert report["coefficient_report"]["verdict"] == CE.VERIFIED_COMPLETE


def test_pipeline_rejects_a_self_consistent_but_edited_intermediate():
    spec = _pipeline_spec()
    image = spec["coefficient_expansion"]["images"]["F7source"]
    assert image["terms"][0] == {
        "coefficient": "-1/3", "powers": [["g5", 1]],
    }
    image["terms"][0]["coefficient"] = "-2/3"
    spec["coefficient_expansion"]["equations"][0]["coefficients"]["0"] = (
        "-2*g5/3"
    )

    with pytest.raises(LCP.LaurentCoefficientPipelineError,
                       match="differs from the named Laurent export"):
        LCP.verify(spec)


def test_pipeline_requires_total_bindings():
    spec = _pipeline_spec()
    spec["bindings"] = []

    with pytest.raises(LCP.LaurentCoefficientPipelineError,
                       match="nonempty"):
        LCP.verify(spec)

def test_checked_in_jc_fixture_and_cli_authority_boundary(capsys):
    path = (Path(__file__).parents[1] / "fixtures" / "jc_rows78" /
            "laurent_lowering_v1.json")
    checked_in = json.loads(path.read_text(encoding="utf-8"))
    assert checked_in == _rows78_spec()

    assert cli.main([
        "verify-laurent-lowering", "--spec", str(path),
    ]) == 0
    output = capsys.readouterr().out
    assert LL.VERIFIED in output
    assert "no chart validity, integration, or claim transport" in output


def test_checked_in_bound_pipeline_and_cli(capsys):
    path = (Path(__file__).parents[1] / "fixtures" / "jc_rows78" /
            "laurent_coefficient_pipeline_v1.json")
    checked_in = json.loads(path.read_text(encoding="utf-8"))
    assert checked_in == _pipeline_spec()

    assert cli.main([
        "verify-laurent-coefficient-pipeline", "--spec", str(path),
    ]) == 0
    output = capsys.readouterr().out
    assert LCP.VERIFIED in output
    assert CE.VERIFIED_COMPLETE in output
    assert "no source derivation, chart validity, or claim transport" in output

def test_covered_chart_zero_rhs_is_rejected_for_symbolic_G():
    spec = _rows78_spec()
    spec["equalities"][0]["right"] = "ZERO"

    with pytest.raises(LL.LaurentLoweringError,
                       match="equality 0 is false"):
        LL.verify(spec)


def test_row8_coefficient_mutation_is_rejected():
    spec = _rows78_spec()
    node = next(item for item in spec["program"]
                if item["id"] == "twentyone_C1_dF6")
    node["scalar"] = "20"

    with pytest.raises(LL.LaurentLoweringError,
                       match="equality 1 is false"):
        LL.verify(spec)


def test_derivative_handles_negative_exponents_and_constant_term():
    spec = {
        "schema": LL.SCHEMA,
        "characteristic": 0,
        "series_variable": "y",
        "coefficient_variables": ["a", "b"],
        "inputs": {
            "F": {"-2": "a", "0": "b"},
            "EXPECTED": {"-3": "(-2)*a"},
        },
        "program": [
            {"id": "dF", "op": "derivative", "arg": "F"},
        ],
        "equalities": [
            {"id": "formal-derivative", "left": "dF",
             "right": "EXPECTED"},
        ],
    }

    assert LL.verify(spec)["program"][0]["terms"] == {"-3": "(-2)*a"}


def test_declared_monomial_shift_clears_negative_support():
    spec = {
        "schema": LL.SCHEMA,
        "characteristic": 0,
        "series_variable": "y",
        "coefficient_variables": ["a", "b"],
        "inputs": {
            "F": {"-3": "a", "1": "b"},
            "CLEARED": {"0": "a", "4": "b"},
        },
        "program": [
            {"id": "shifted", "op": "shift", "arg": "F",
             "exponent": 3},
        ],
        "equalities": [
            {"id": "clear-y-minus-three", "left": "shifted",
             "right": "CLEARED"},
        ],
    }

    report = LL.verify(spec)
    assert report["program"][0]["support"] == [0, 4]


def test_forward_references_and_unknown_fields_are_refused():
    spec = _rows78_spec()
    spec["program"][0]["arg"] = "later"
    with pytest.raises(LL.LaurentLoweringError,
                       match="reference an earlier value"):
        LL.verify(spec)

    spec = copy.deepcopy(_rows78_spec())
    spec["authority"] = "trust the producer"
    with pytest.raises(LL.LaurentLoweringError, match="unknown field"):
        LL.verify(spec)


def test_non_string_operation_and_equality_references_fail_closed():
    spec = _rows78_spec()
    spec["program"][0]["op"] = []
    with pytest.raises(LL.LaurentLoweringError, match="unsupported op"):
        LL.verify(spec)

    spec = _rows78_spec()
    spec["equalities"][0]["left"] = []
    with pytest.raises(LL.LaurentLoweringError,
                       match="reference computed values"):
        LL.verify(spec)

@pytest.mark.parametrize("key", ["01", "+1", "one"])
def test_laurent_exponents_must_be_canonical_integers(key):
    spec = _rows78_spec()
    spec["inputs"]["G"][key] = "1"

    with pytest.raises(LL.LaurentLoweringError,
                       match="canonical integers"):
        LL.verify(spec)
