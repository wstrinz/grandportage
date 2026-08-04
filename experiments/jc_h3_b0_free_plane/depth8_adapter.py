#!/usr/bin/env python3
"""Replay the transported JC b=0 depth-eight affine fiber block.

The native receipt exports nine raw coefficients and a transported 3x2 block,
but deliberately does not export the residual vector r8 or the three boundary
bodies. GP independently checks the raw commitments, pivot-absorbed transport,
rank, syzygy, and symbolic augmented determinant. The result is necessary-
condition evidence with graph effect NONE, not a depth-eight source model.
"""

from __future__ import annotations

import argparse
import contextlib
import copy
import hashlib
import importlib.util
import io
import json
import os
import subprocess
import sys
import tempfile
from fractions import Fraction
from pathlib import Path

from grandportage import evidence as EV
from grandportage import groebner as G


ROOT = Path(__file__).resolve().parents[2]
NATIVE_ROOT = ROOT.parent / "math-stuff" / "d2_plane_72_108"
DEFAULT_FIXTURE = ROOT / "fixtures" / "jc_b0_depth8_free_plane" / "v1.json"
DEFAULT_REVIEW = ROOT / "review" / "jc-h3-b0-depth8-free-plane-v1.json"
PREVIOUS_FIXTURE = ROOT / "fixtures" / "jc_b0_free_plane" / "v1.json"
PREVIOUS_ADAPTER = ROOT / "experiments" / "jc_h3_b0_free_plane" / "adapter.py"
SCHEMA = EV.AFFINE_FIBER_BLOCK_SCHEMA
EXPECTED_FIXTURE_SHA256 = (
    "7c26a7fdcfd12321997beb259f73388db654b3aff1cfbb83f30ccfa11017b82c")
EXPECTED_PREVIOUS_FIXTURE_SHA256 = (
    "b0bdca0a0b410d3510dd6b9285f9484c9c4462b42ebf3ff3439925a2326fac58")

NATIVE_BINDINGS = {
    "f2_h3_b0_depth8_free_plane_coefficients.json":
        "5cf9015b0065eb6fd5cd181be28f4c9e8004ca61786fafba1af463fddfc3024a",
    "f2_h3_b0_depth8_free_plane_coefficients.py":
        "75261cd6a03796bab720d1b95c0a012290e2722353801d7429ad19e059ee760c",
    "f2_h3_b0_free_plane_receipt.json":
        "e6c731f984d9c06d84aac014db8bff234bb15962d1ee6fac2ee80df7795e00da",
    "f2_h3_b0_compatibility_module.json":
        "944f95d762e05d3dec4ffa6599b4f0d1d2674e4127e5d168712a62de50291840",
    "f2_h3_source_depth6_receipt.json":
        "3dde87dd53b07c851ce78c27227b63660a9177860791cc2dca5bff5152db9c0d",
    "f2_h3_source_depth7_receipt.json":
        "2b50fc44669222a335697119c6221588e056cc32dfc1e1590e96162a4d301b86",
    "f2_h3_p_c6_1_receipt.json":
        "d971325110dcab38b25089c542c4cc5fd79ddb04342124ebf11c5d673ce4ee25",
    "f2_h3_source_depth6_chain_certificate.json.gz":
        "2280c88410667ce9c8ac5900c61b044f5cd7174540d859485c04bcca3a27eba0",
    "f2_h3_source_depth7_producer.py":
        "19bbf03fbc69b1d34054a2a6b1d590c062189e0a65917857c151dcc98244753f",
    "f2_h3_esystem_seam.py":
        "e21ecff0f9f389b620fa599820e95c93eb44343c44ff20e9d25879f330b39aca",
    "f2_h3_graded_eliminator_contract.py":
        "63da51c56475d39266f3fc74e6f5b0a2f70d05e0d7781d98791aa6bf12535965",
    "f2_target_root_support_data.py":
        "16eb77a98c9c02939cc48a9b7f0e9f1141234784013daf4a34ca375666a2f2d2",
}

ROWS = ("E[2,19]", "E[3,20]", "E[4,22]")
RAW_SLOTS = ("c7_4", "c8_5", "c9_7")
RING_VARS = (
    "c2_1", "c2_2", "c2_3", "c3_5", "c4_5", "c5_7", "c7_10",
    "c8_12", "t", "r8_1", "r8_2", "r8_3",
)


class Depth8BlockEvidenceError(ValueError):
    """The transported block, residual scope, or authority boundary drifted."""


def require(condition, check_id, message):
    if not condition:
        raise Depth8BlockEvidenceError("%s: %s" % (check_id, message))


def normalized_sha256(path):
    return hashlib.sha256(
        Path(path).read_bytes().replace(b"\r\n", b"\n")).hexdigest()


def encoded(value):
    return (json.dumps(value, indent=2, sort_keys=True,
                       ensure_ascii=True) + "\n").encode("utf-8")


def _native_bytes(value):
    return (json.dumps(value, sort_keys=True, separators=(",", ":"))
            + "\n").encode("utf-8")


def _series_to_sparse(value):
    require(isinstance(value, list), "P1", "native polynomial is not a list")
    terms = []
    seen = set()
    for entry in value:
        require(isinstance(entry, list) and len(entry) == 2, "P2",
                "native term is malformed")
        powers, coefficient = entry
        try:
            rational = Fraction(coefficient)
        except (ValueError, ZeroDivisionError, TypeError) as exc:
            raise Depth8BlockEvidenceError("P3: invalid coefficient") from exc
        require(str(rational) == coefficient and rational != 0, "P4",
                "coefficient is not canonical nonzero rational")
        power_map = {}
        for pair in powers:
            require(isinstance(pair, list) and len(pair) == 2 and
                    pair[0] in RING_VARS and type(pair[1]) is int and
                    pair[1] > 0 and pair[0] not in power_map, "P5",
                    "native variable power is invalid")
            power_map[pair[0]] = pair[1]
        monomial = tuple(power_map.get(name, 0) for name in RING_VARS)
        require(monomial not in seen, "P6", "duplicate native monomial")
        seen.add(monomial)
        terms.append({
            "coefficient": coefficient,
            "powers": [[name, exponent] for name, exponent in
                       zip(RING_VARS, monomial) if exponent],
        })
    terms.sort(key=lambda term: tuple(dict(term["powers"]).get(name, 0)
                                      for name in RING_VARS), reverse=True)
    return {"schema": G.SPARSE_POLYNOMIAL_SCHEMA, "terms": terms}


def _poly(value, budget=None):
    return G.parse_polynomial(
        _series_to_sparse(value), RING_VARS, _budget=budget)


def _q(expression, budget=None):
    return G.parse_polynomial(expression, RING_VARS, _budget=budget)


def _restriction(value, budget):
    images = dict((name, name) for name in RING_VARS)
    images.update({
        "c5_7": "0",
        "c8_12": "c2_3*c3_5^2",
        "c4_5": "c2_3^2/4",
    })
    sparse = G.substitute_polynomial(
        value, RING_VARS, images, _budget=budget, _preserve_sparse=True)
    return G.parse_polynomial(sparse, RING_VARS, _budget=budget)


def _expected_projection():
    return {
        "instance_id": "jc_h3_b0_depth8_transported_free_plane_block",
        "coefficient_domain": "K = QQ[t]/(15*t^3+1)",
        "semantic_layer": "NECESSARY_DEPTH8_EXTENSION_BLOCK",
        "base_model": "X_b with P1..P5, S2, pin, and declared guards",
        "transport": {
            "invariant_coordinate": "q7=c9_7+(3/2)*c2_3*c7_4",
            "D7": "d/dc7_4-(3/2)*c2_3*d/dc9_7",
            "D8": "d/dc8_5",
            "prerequisite": "verified depth-7 c9_7 affine pivot absorption",
        },
        "checked_block": {
            "rows": list(ROWS),
            "columns": ["D7", "D8"],
            "rank": 2,
            "left_syzygy": ["c2_3", "0", "2"],
            "determines": ["transported c7_4", "c8_5"],
            "symbolic_compatibility": "Psi8=c2_3*r8_1+2*r8_3",
            "residual_status": "NOT_EXPORTED",
            "excess_rows": 1,
        },
        "licenses": [
            "the nine raw boundary coefficients are the frozen exact coefficients",
            "the pivot-absorbed transported block is the declared exact 3x2 matrix",
            "the block has constant rank two under the audited localization units",
            "the two transported directions are determined in this necessary extension block",
            "for every symbolic residual, solvability is equivalent to one compatibility pairing Psi8=0",
        ],
        "consumed_frozen_semantics": [
            "the native derivative-table chain-rule assembly transports the raw columns through every earlier solved-coordinate sensitivity",
            "the derivative/support argument makes the depth-eight dependence affine in the transported directions",
            "the boundary triple is a necessary condition for actual-source extension under the named premises",
        ],
        "does_not_license": [
            "an explicit polynomial Psi8 before r8 is exported",
            "materialization of any depth-eight boundary body or the c9_6 rung",
            "equivalence with the complete depth-eight fiber or actual-source fiber",
            "sufficiency for extension past depth eight",
            "nonzerodivisor, component, irreducibility, point, or emptiness claims on Z(Psi8)",
            "depth nine, H8, H3, source membership, or a (75,125) verdict change",
            "any graph claim or transport authority",
        ],
        "first_open_obligation": (
            "export r8=(r8_1,r8_2,r8_3), the three boundary residuals after "
            "earlier legal solves on X_b, without promoting necessary to sufficient"),
        "graph_effect": "NONE",
    }


def _validate_native_certificate(certificate):
    require(certificate.get("id") ==
            "f2_h3_b0_depth8_free_plane_coefficients" and
            certificate.get("schema_version") == 1 and
            certificate.get("verdict") ==
            "RANK2_PLANE_DETERMINED_ONE_EXCESS_COMPATIBILITY", "N1",
            "native certificate identity, schema, or verdict changed")
    require(certificate.get("bindings") == {
        name: NATIVE_BINDINGS[name] for name in (
            "f2_h3_b0_compatibility_module.json",
            "f2_h3_b0_free_plane_receipt.json",
            "f2_h3_p_c6_1_receipt.json",
            "f2_h3_source_depth6_chain_certificate.json.gz",
            "f2_h3_source_depth6_receipt.json",
            "f2_h3_source_depth7_receipt.json",
        )}, "N2", "native receipt dependency custody changed")
    require(certificate.get("source_digests") == {
        name: NATIVE_BINDINGS[name] for name in (
            "f2_h3_esystem_seam.py",
            "f2_h3_graded_eliminator_contract.py",
            "f2_h3_source_depth7_producer.py",
            "f2_target_root_support_data.py",
        )}, "N3", "native source-code custody changed")
    require(certificate.get("M8", {}).get("rows") == list(ROWS) and
            certificate.get("M8", {}).get("columns") == ["D7", "D8"] and
            certificate.get("rank", {}).get("value") == 2 and
            certificate.get("rank", {}).get(
                "I2_is_unit_ideal_on_localization") is True, "N4",
            "native block or rank statement changed")
    require(certificate.get("left_syzygy", {}).get("generator") ==
            ["a", "0", "2"] and
            certificate.get("left_syzygy", {}).get("primitive") is True,
            "N5", "native left syzygy changed")
    residual = certificate.get("residual_vector_r8", {})
    require(residual.get("carried_as") == ["r8_1", "r8_2", "r8_3"] and
            residual.get("status", "").startswith("NOT EXPORTED"), "N6",
            "missing residual was silently materialized or renamed")
    grade = certificate.get("semantic_grade", {})
    require(grade.get("supplies", "").startswith("NECESSARY CONDITIONS ONLY")
            and "not an equivalent source fiber" in grade.get("is_not", "")
            and "NOT proved" in grade.get("missing_implication", ""), "N7",
            "native necessary-only semantic grade widened")
    require(any("no source sufficiency" in item for item in
                certificate.get("refusals", [])) and
            any("Psi8" in item for item in certificate.get("open", [])), "N8",
            "native source or residual refusal disappeared")


def _load_previous_adapter():
    spec = importlib.util.spec_from_file_location(
        "gp_depth8_previous_free_plane", PREVIOUS_ADAPTER)
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


def _check_previous_prerequisite(record):
    raw = PREVIOUS_FIXTURE.read_bytes()
    require(hashlib.sha256(raw).hexdigest() ==
            EXPECTED_PREVIOUS_FIXTURE_SHA256 and record == {
                "fixture": "fixtures/jc_b0_free_plane/v1.json",
                "sha256": EXPECTED_PREVIOUS_FIXTURE_SHA256,
                "required_result": "affine_round_trip and pivot-independent downstream",
            }, "C1", "previous GP affine-pivot prerequisite changed")
    checked = _load_previous_adapter().validate_fixture_value(
        json.loads(raw.decode("utf-8")))
    require(checked.get("affine_round_trip") is True and
            checked.get("downstream_equations") == 8, "C2",
            "previous affine-pivot replay no longer supplies its prerequisite")


def _capture_native(native_root):
    root = Path(native_root)
    script = root / "f2_h3_b0_depth8_free_plane_coefficients.py"
    old_argv, old_path = sys.argv[:], sys.path[:]
    try:
        sys.argv = [str(script), "--quiet"]
        sys.path.insert(0, str(root))
        spec = importlib.util.spec_from_file_location(
            "gp_depth8_block_fixture_native", script)
        module = importlib.util.module_from_spec(spec)
        with contextlib.redirect_stdout(io.StringIO()):
            try:
                spec.loader.exec_module(module)
            except SystemExit as exc:
                require(exc.code == 0, "B1", "native depth-eight checker failed")
        return module
    finally:
        sys.argv = old_argv
        sys.path[:] = old_path


def build_fixture(native_root=NATIVE_ROOT):
    root = Path(native_root)
    bindings = {name: normalized_sha256(root / name)
                for name in sorted(NATIVE_BINDINGS)}
    require(bindings == dict(sorted(NATIVE_BINDINGS.items())), "B2",
            "native depth-eight inputs drifted before freeze")
    module = _capture_native(root)
    certificate = json.loads((root /
        "f2_h3_b0_depth8_free_plane_coefficients.json").read_text(
            encoding="utf-8"))
    _validate_native_certificate(certificate)
    return {
        "schema": SCHEMA,
        "binding_digest_algo": "sha256-lf-normalized",
        "source_bindings": bindings,
        "gp_prerequisite": {
            "fixture": "fixtures/jc_b0_free_plane/v1.json",
            "sha256": EXPECTED_PREVIOUS_FIXTURE_SHA256,
            "required_result": "affine_round_trip and pivot-independent downstream",
        },
        "native_certificate": certificate,
        "raw_columns": {
            row: {slot: module.ser(module.RAW6[row, slot])
                  for slot in RAW_SLOTS} for row in ROWS
        },
        "transported_block": [
            [module.ser(module.M8[i][j]) for j in range(2)]
            for i in range(3)
        ],
        "projection": _expected_projection(),
        "authority_boundary": (
            "The exact coefficient block determines two coordinates only in "
            "the named necessary extension model. The residual r8 and thus "
            "the explicit Psi8 polynomial are absent; no sufficiency, source, "
            "geometric, verdict, or graph authority is minted."),
    }


def _det2(matrix, first, second):
    return (matrix[first][0] * matrix[second][1] -
            matrix[first][1] * matrix[second][0])


def _det3(matrix):
    return (matrix[0][0] * matrix[1][1] * matrix[2][2]
            + matrix[0][1] * matrix[1][2] * matrix[2][0]
            + matrix[0][2] * matrix[1][0] * matrix[2][1]
            - matrix[0][0] * matrix[1][2] * matrix[2][1]
            - matrix[0][1] * matrix[1][0] * matrix[2][2]
            - matrix[0][2] * matrix[1][1] * matrix[2][0])


def _validate_arithmetic(fixture):
    budget = G._ArithmeticBudget()
    raw_values = fixture["raw_columns"]
    require(tuple(raw_values) == ROWS and
            all(tuple(raw_values[row]) == RAW_SLOTS for row in ROWS), "A1",
            "nine-column raw ledger shape changed")
    raw = {(row, slot): _poly(raw_values[row][slot], budget)
           for row in ROWS for slot in RAW_SLOTS}
    certificate = fixture["native_certificate"]
    hashes = {
        "%s/%s" % (row, slot): hashlib.sha256(
            _native_bytes(raw_values[row][slot])).hexdigest()
        for row in ROWS for slot in RAW_SLOTS
    }
    require(hashes == certificate["coefficients_sha256"], "A2",
            "raw coefficient does not match native commitment")

    block_values = fixture["transported_block"]
    require(len(block_values) == 3 and all(len(row) == 2
            for row in block_values), "A3", "transported block shape changed")
    require(hashlib.sha256(_native_bytes(block_values)).hexdigest() ==
            certificate["block_sha256"], "A4",
            "transported block does not match native commitment")
    block = [[_poly(value, budget) for value in row] for row in block_values]

    transport = certificate["transport"]
    require(transport["D7"] ==
            "d/d c7_4 - (3/2)*a * d/d c9_7   (q7, base coords, guards and a held fixed)"
            and transport["D8"] == "d/d c8_5"
            and transport["invariant"] ==
            "q7 := c9_7 + (3/2)*a*c7_4"
            and transport["sign_convention"].startswith(
                "FORCED by D7(q7) = 0"), "A5",
            "pivot-absorbed transport or its forced sign changed")

    expected = [
        [_q("0", budget), _q("-5*c2_3*t", budget)],
        [_q("-(5/8)*c2_3^4*c3_5", budget), _q("0", budget)],
        [_q("0", budget), _q("(5/2)*c2_3^2*t", budget)],
    ]
    require(block == expected, "A6", "closed-form M8 changed")
    minors = [_det2(block, 0, 1), _det2(block, 0, 2),
              _det2(block, 1, 2)]
    require(minors == [
        _q("-(25/8)*c2_3^5*c3_5*t", budget), _q("0", budget),
        _q("-(25/16)*c2_3^6*c3_5*t", budget)], "A7",
        "rank-two minor calculation changed")

    syzygy = [_q("c2_3", budget), _q("0", budget), _q("2", budget)]
    require(all((syzygy[0] * block[0][column] +
                 syzygy[1] * block[1][column] +
                 syzygy[2] * block[2][column]).is_zero
                for column in range(2)), "A8",
            "left syzygy does not annihilate both columns")

    residuals = [_q("r8_1", budget), _q("r8_2", budget),
                 _q("r8_3", budget)]
    augmented = [block[i] + [residuals[i]] for i in range(3)]
    psi8 = _q("c2_3*r8_1+2*r8_3", budget)
    audited = _q("-(25/16)*c2_3^5*c3_5*t", budget)
    determinant = _det3(augmented)
    require(determinant == audited * psi8 and
            determinant.uses_any([RING_VARS.index("r8_1"),
                                  RING_VARS.index("r8_3")]) and
            not determinant.uses_any([RING_VARS.index("r8_2")]), "A9",
            "symbolic augmented determinant factorization changed")

    require(_restriction(raw["E[2,19]", "c8_5"], budget) ==
            _q("-5*c2_3*t", budget) and
            _restriction(raw["E[2,19]", "c9_7"], budget).is_zero and
            _restriction(raw["E[3,20]", "c8_5"], budget).is_zero and
            _restriction(raw["E[3,20]", "c9_7"], budget) == _q(
                "-5*c2_2*t-5*c2_3*c7_10-(5/2)*c2_3^3*c3_5", budget) and
            _restriction(raw["E[4,22]", "c8_5"], budget) ==
            _q("(5/2)*c2_3^2*t", budget) and
            _restriction(raw["E[4,22]", "c9_7"], budget).is_zero, "A10",
            "raw six-coefficient restriction changed")

    localization = certificate["localization_ledger"]
    require(localization["inverted"] == ["c2_3", "p", "det5"] and
            any(item.startswith("c3_5 (forced") for item in
                localization["derived_units"]) and
            any(item.startswith("t (15*t**3") for item in
                localization["derived_units"]) and
            localization["never_inverted"] ==
                ["c5_7", "mu*w", "R", "det6", "det5p"], "A11",
            "unit audit or never-inverted boundary changed")
    degree = certificate["degree_certificate"]
    require(degree["second_derivative_indices"] == {
        "(7,7)": -6, "(7,8)": -7, "(8,7)": -7, "(8,8)": -8,
    } and degree["no_body_formed"] is True and
            degree["nonlinear_block"].startswith("NONE"), "A12",
            "native affine-degree certificate changed")
    return {
        "raw_coefficients": 9,
        "transported_shape": [3, 2],
        "rank": 2,
        "unit_minor": "-(25/8)*c2_3^5*c3_5*t",
        "left_syzygy": ["c2_3", "0", "2"],
        "symbolic_compatibility": "Psi8=c2_3*r8_1+2*r8_3",
        "residual_exported": False,
    }


def validate_fixture_value(fixture):
    require(set(fixture) == {"schema", "binding_digest_algo",
            "source_bindings", "gp_prerequisite", "native_certificate",
            "raw_columns", "transported_block", "projection",
            "authority_boundary"}, "F1", "fixture shape changed")
    require(fixture["schema"] == SCHEMA and
            fixture["binding_digest_algo"] == "sha256-lf-normalized", "F2",
            "fixture schema or digest algorithm changed")
    require(fixture["source_bindings"] ==
            dict(sorted(NATIVE_BINDINGS.items())), "F3",
            "frozen native binding changed")
    require(fixture["projection"] == _expected_projection(), "M1",
            "transport, residual, authority, or graph scope changed")
    _check_previous_prerequisite(fixture["gp_prerequisite"])
    _validate_native_certificate(fixture["native_certificate"])
    return _validate_arithmetic(fixture)


def check_native_bindings(fixture, native_root=NATIVE_ROOT):
    root = Path(native_root)
    require(root.exists(), "B3", "sibling JC checkout is absent")
    for name, expected in fixture["source_bindings"].items():
        require((root / name).exists(), "B4", "native binding absent: " + name)
        require(normalized_sha256(root / name) == expected, "B5",
                "native binding changed: " + name)


def report_from_checked_fixture(fixture, checked):
    report = copy.deepcopy(fixture["projection"])
    report.update({
        "schema": SCHEMA,
        "verdict": "VERIFIED_RANK2_NECESSARY_AFFINE_BLOCK",
        "checked_instance": checked,
        "source_bindings": fixture["source_bindings"],
        "gp_prerequisite": fixture["gp_prerequisite"],
        "evidence_envelope": {
            "schema": SCHEMA,
            "checked_proposition": (
                "the pivot-transported depth-eight necessary block has "
                "constant rank two and one symbolic residual compatibility"),
            "licenses": fixture["projection"]["licenses"],
            "consumed_frozen_semantics": fixture["projection"][
                "consumed_frozen_semantics"],
            "first_open_obligation": fixture["projection"][
                "first_open_obligation"],
            "graph_effect": "NONE",
            "authority_boundary": fixture["authority_boundary"],
        },
    })
    return report


def verify_fixture(path=DEFAULT_FIXTURE, check_bindings=False,
                   native_root=NATIVE_ROOT):
    raw = Path(path).read_bytes()
    if EXPECTED_FIXTURE_SHA256 is not None:
        require(hashlib.sha256(raw).hexdigest() == EXPECTED_FIXTURE_SHA256,
                "F4", "frozen depth-eight block fixture digest changed")
    fixture = json.loads(raw.decode("utf-8"))
    checked = validate_fixture_value(fixture)
    if check_bindings:
        check_native_bindings(fixture, native_root)
    return report_from_checked_fixture(fixture, checked)


def native_replay(native_root=NATIVE_ROOT):
    completed = subprocess.run(
        [sys.executable, str(Path(native_root) /
         "f2_h3_b0_depth8_free_plane_coefficients.py"), "--quiet"],
        cwd=str(native_root), capture_output=True, text=True,
        timeout=180, check=False)
    require(completed.returncode == 0, "N9",
            "native depth-eight replay failed: " + completed.stderr.strip())
    require("40/40 checks passed" in completed.stdout and
            "RANK2_PLANE_DETERMINED_ONE_EXCESS_COMPATIBILITY" in
            completed.stdout, "N10", "native replay summary changed")
    return {"verdict": "VERIFIED_NATIVE_40_OF_40", "graph_effect": "NONE"}


def _atomic_write(path, value, force=False):
    path = Path(path)
    if path.exists() and not force:
        raise Depth8BlockEvidenceError(
            "output exists; pass --force to replace it: %s" % path)
    payload = encoded(value)
    path.parent.mkdir(parents=True, exist_ok=True)
    handle, temporary = tempfile.mkstemp(
        prefix=path.name + ".", suffix=".tmp", dir=str(path.parent))
    try:
        with os.fdopen(handle, "wb") as stream:
            stream.write(payload)
            stream.flush()
            os.fsync(stream.fileno())
        os.replace(temporary, path)
    except BaseException:
        try:
            os.unlink(temporary)
        except FileNotFoundError:
            pass
        raise
    return hashlib.sha256(payload).hexdigest()


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--fixture", type=Path, default=DEFAULT_FIXTURE)
    parser.add_argument("--native-root", type=Path, default=NATIVE_ROOT)
    parser.add_argument("--check-native-bindings", action="store_true")
    parser.add_argument("--native-replay", action="store_true")
    parser.add_argument("--write-fixture", action="store_true")
    parser.add_argument("--output", type=Path)
    parser.add_argument("--force", action="store_true")
    args = parser.parse_args(argv)
    if args.force and not (args.write_fixture or args.output):
        parser.error("--force requires --write-fixture or --output")
    try:
        if args.write_fixture:
            digest = _atomic_write(
                args.fixture, build_fixture(args.native_root), args.force)
            print(json.dumps({"fixture": str(args.fixture), "sha256": digest},
                             indent=2, sort_keys=True))
            return 0
        report = verify_fixture(
            args.fixture, args.check_native_bindings, args.native_root)
        if args.native_replay:
            report["native_replay"] = native_replay(args.native_root)
        if args.output:
            _atomic_write(args.output, report, args.force)
        else:
            print(json.dumps(report, indent=2, sort_keys=True))
        return 0
    except (Depth8BlockEvidenceError, G.CertificateError, OSError, ValueError,
            json.JSONDecodeError) as exc:
        print("REFUSED: %s" % exc, file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
