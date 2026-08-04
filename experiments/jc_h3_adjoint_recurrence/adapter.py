#!/usr/bin/env python3
"""Verify the corrected JC unilateral adjoint-recurrence boundary.

The adapter consumes a frozen native certificate but independently decodes its
padded operator matrices and recomputes the shift facts.  It checks the exact
premises used by the Lean theorem: the sequence is zero from depth 14, while
the depth-13 block is nonzero.  On the unilateral domain d >= 6 this makes the
constant-coefficient annihilator ideal exactly (S^8), with no nonzero constant
term and hence no reversible backward recurrence.

This is standalone evidence with graph effect NONE.  The native assumptions
P1..P5, S2, the pin, and H8 remain assumptions; no face body, source
membership, H3 conclusion, or verdict promotion is produced.
"""

from __future__ import annotations

import argparse
import copy
import hashlib
import json
import os
import subprocess
import sys
import tempfile
from fractions import Fraction
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
NATIVE_ROOT = ROOT.parent / "math-stuff" / "d2_plane_72_108"
DEFAULT_FIXTURE = ROOT / "fixtures" / "jc_adjoint_recurrence" / "v1.json"
SCHEMA = "parametric_recurrence_v1"
EXPECTED_FIXTURE_SHA256 = (
    "8b9cf56ca0faad4dbeeb57593c2612ed408521df3a9d62c34bcd838e8189cd58")

NATIVE_BINDINGS = {
    "f2_h3_adjoint_recurrence_certificate.json":
        "9a3f3854b19d5efe988c660f51babbb7b71eca00cf99b2fd88c8b6168ccb7ba4",
    "f2_h3_adjoint_recurrence.py":
        "9c99a96ee5c273ada10aae5d3beea4de0a0db980c78cf0570c4dd9dfc1244d64",
}

ROWS = (1, 2, 3, 4, 5)
COLUMNS = ("C7_fresh", "C8_lag1")
ZERO = {}
REGIME_SPEC = (
    ("R1", (6, 7), False, (2, 3), COLUMNS, 1),
    ("R2", (8, 9), False, (2, 3, 4), COLUMNS, 1),
    ("R3", (10, 11), False, (2, 3, 4, 5), COLUMNS, 2),
    ("R4", (12, 13), False, (2, 3, 4, 5), ("C8_lag1",), 3),
    ("R5", (14, 14), False, (2, 3, 4, 5), (), 4),
    ("R6", (15, 24), True, ROWS, (), 5),
)
JUMP_DEPTHS = (7, 9, 11, 13)
EXPECTED_ANNIHILATOR = {
    "within_regimes": "S - 1",
    "global_polynomial_coefficient": (
        "(d-7)*(d-9)*(d-11)*(d-13)*(S-1) on the padded sequence, d >= 6; "
        "each linear factor is necessary"),
    "constant_coefficient": (
        "on the unilateral domain d >= 6 the annihilator ideal is exactly "
        "(S^8): S^8 annihilates because padded B_d = 0 for d >= 14, S^7 "
        "fails at d = 6 because B_13 != 0, and backward induction shows every "
        "annihilator has lowest shift exponent >= 8; in particular no "
        "annihilator with nonzero constant term, and no reversible backward "
        "recurrence, exists"),
}


class RecurrenceEvidenceError(ValueError):
    """The frozen receipt, exact recurrence, or authority scope drifted."""


def require(condition, check_id, message):
    if not condition:
        raise RecurrenceEvidenceError("%s: %s" % (check_id, message))


def normalized_sha256(path):
    return hashlib.sha256(
        Path(path).read_bytes().replace(b"\r\n", b"\n")).hexdigest()


def encoded(value):
    return (json.dumps(value, indent=2, sort_keys=True,
                       ensure_ascii=True) + "\n").encode("utf-8")


def sparse_digest(value):
    canonical = json.dumps({
        "symbols": list(value["symbols"]),
        "terms": value["terms"],
    }, separators=(",", ":"))
    return hashlib.sha256(canonical.encode("utf-8")).hexdigest()


def _decode_entry(entry, where):
    require(isinstance(entry, dict) and set(entry) == {
        "sha256", "sparse", "terms"}, "P1", where + " entry shape changed")
    sparse = entry["sparse"]
    require(isinstance(sparse, dict) and set(sparse) == {"symbols", "terms"},
            "P2", where + " sparse shape changed")
    symbols = sparse["symbols"]
    terms = sparse["terms"]
    require(symbols == sorted(set(symbols)) and
            all(isinstance(name, str) and name for name in symbols), "P3",
            where + " symbols are not canonical")
    require(entry["terms"] == len(terms) and
            entry["sha256"] == sparse_digest(sparse), "P4",
            where + " term count or sparse digest changed")
    result = {}
    previous = None
    for term in terms:
        require(isinstance(term, list) and len(term) == 2 and
                isinstance(term[0], list) and isinstance(term[1], str), "P5",
                where + " term shape changed")
        monomial = []
        last = -1
        for factor in term[0]:
            require(isinstance(factor, list) and len(factor) == 2, "P5",
                    where + " support factor changed")
            index, exponent = factor
            require(type(index) is int and last < index < len(symbols), "P6",
                    where + " support indices are not canonical")
            require(type(exponent) is int and 0 < exponent <= 64, "P7",
                    where + " exponent is invalid")
            last = index
            monomial.append((symbols[index], exponent))
        monomial = tuple(monomial)
        require(previous is None or previous < monomial, "P8",
                where + " terms are not strictly ordered")
        previous = monomial
        coefficient = Fraction(term[1])
        require(coefficient and str(coefficient) == term[1], "P9",
                where + " coefficient is zero or noncanonical")
        result[monomial] = coefficient
    return result


def _add(left, right, scale=Fraction(1)):
    result = dict(left)
    for monomial, coefficient in right.items():
        result[monomial] = result.get(monomial, Fraction(0)) + scale * coefficient
        if not result[monomial]:
            del result[monomial]
    return result


def _decode_regimes(certificate):
    regimes = certificate.get("regimes")
    require(isinstance(regimes, list) and len(regimes) == len(REGIME_SPEC),
            "R1", "regime family changed")
    decoded = {}
    for record, expected in zip(regimes, REGIME_SPEC):
        name, depths, open_ended, rows, columns, cokernel_dimension = expected
        require(record.get("regime") == name and
                record.get("depths") == list(depths) and
                record.get("open_ended") is open_ended and
                record.get("rows") == list(rows) and
                record.get("columns") == list(columns) and
                record.get("cokernel_dimension") == cokernel_dimension,
                "R2", name + " regime metadata changed")
        require(len(record.get("left_cokernel_basis", [])) ==
                cokernel_dimension, "R3", name + " cokernel dimension drifted")
        for basis_index, vector in enumerate(record["left_cokernel_basis"]):
            require(set(map(int, vector)) <= set(rows), "R4",
                    name + " cokernel vector has an out-of-regime row")
            for row, entry in vector.items():
                _decode_entry(entry, "%s cokernel[%d,%s]" % (
                    name, basis_index, row))
        matrix = {}
        for item in record.get("matrix", []):
            key = (item.get("row"), item.get("column"))
            require(key[0] in rows and key[1] in columns and key not in matrix,
                    "R5", name + " matrix coordinate changed or repeated")
            matrix[key] = _decode_entry(item.get("value"),
                                        "%s matrix%s" % (name, key))
        require(set(matrix) == {(row, column) for row in rows
                                for column in columns}, "R6",
                name + " matrix is incomplete")
        decoded[name] = matrix
    return decoded


def _padded_at(depth, regimes):
    if depth <= 7:
        matrix = regimes["R1"]
    elif depth <= 9:
        matrix = regimes["R2"]
    elif depth <= 11:
        matrix = regimes["R3"]
    elif depth <= 13:
        matrix = regimes["R4"]
    else:
        matrix = ZERO
    return {(row, column): matrix.get((row, column), ZERO)
            for row in ROWS for column in COLUMNS}


def _matrix_difference(after, before):
    return {key: value for key in after
            if (value := _add(after[key], before[key], Fraction(-1)))}


def _decode_jump(record, where):
    result = {}
    for item in record.get("entries", []):
        key = (item.get("row"), item.get("column"))
        require(key[0] in ROWS and key[1] in COLUMNS and key not in result,
                "J1", where + " coordinate changed or repeated")
        result[key] = _decode_entry(item.get("value"), where + str(key))
    return result


def _validate_recurrence(certificate):
    require(certificate.get("id") == "f2_h3_adjoint_recurrence" and
            certificate.get("schema_version") == 1, "N1",
            "native receipt identity or schema changed")
    require(certificate.get("layer") == (
        "actual-source derivative recurrence, conditional on P1..P5, S2, "
        "the pin and H8 (depths >= 8)"), "N2",
        "native conditionality layer changed")
    conventions = certificate.get("conventions", {})
    require(conventions.get("pin") == "15*t^3 + 1 = 0" and
            conventions.get("stratum") == "S2: c4_5 = c2_3^2/4" and
            "absent entries zero" in conventions.get("padding", ""), "N3",
            "pin, stratum, or padding convention changed")
    schedule = certificate.get("schedule", {})
    require(schedule.get("first_slotless_depth") == 14 and
            schedule.get("last_fresh_root7_slot_depth") == 11 and
            schedule.get("last_fresh_root8_slot_depth") == 13, "N4",
            "support cutoff schedule changed")
    require(certificate.get("annihilator") == EXPECTED_ANNIHILATOR, "N7",
            "corrected annihilator statement changed or regressed")
    regimes = _decode_regimes(certificate)

    jumps = certificate.get("operator_jumps", {})
    require(jumps.get("nonzero_at") == list(JUMP_DEPTHS) and
            "RB_8 == RB_9 exactly" in jumps.get("depth9_is_not_a_jump", ""),
            "J2", "declared jump set or depth-9 correction changed")
    records = jumps.get("values", [])
    require([(item.get("from_depth"), item.get("to_depth"))
             for item in records] == [(d, d + 1) for d in JUMP_DEPTHS], "J3",
            "jump record depths changed")
    recorded = {item["from_depth"]: _decode_jump(
        item, "jump %d" % item["from_depth"]) for item in records}
    computed = {}
    for depth in range(6, 24):
        difference = _matrix_difference(
            _padded_at(depth + 1, regimes), _padded_at(depth, regimes))
        if difference:
            computed[depth] = difference
    require(tuple(computed) == JUMP_DEPTHS and computed == recorded, "J4",
            "padded operator jumps do not reproduce the frozen records")

    tail_zero = all(not any(_padded_at(depth, regimes).values())
                    for depth in range(14, 26))
    endpoint_nonzero = any(_padded_at(13, regimes).values())
    require(tail_zero, "A1", "padded operator sequence is not zero from 14")
    require(endpoint_nonzero, "A2", "the depth-13 endpoint block is zero")
    require(all(not any(_padded_at(depth + 8, regimes).values())
                for depth in range(6, 18)), "A3", "S^8 does not annihilate")
    require(any(_padded_at(6 + 7, regimes).values()), "A4",
            "S^7 unexpectedly annihilates at the domain start")

    polynomial_shift_ok = all(
        depth in JUMP_DEPTHS or not _matrix_difference(
            _padded_at(depth + 1, regimes), _padded_at(depth, regimes))
        for depth in range(6, 24))
    require(polynomial_shift_ok and all(computed[d] for d in JUMP_DEPTHS),
            "A5", "polynomial-coefficient shift law or factor necessity failed")
    return {
        "domain_start": 6,
        "zero_from": 14,
        "cutoff_gap": 8,
        "endpoint_depth": 13,
        "endpoint_nonzero": True,
        "pure_forward_annihilator": "S^8",
        "S7_annihilates": False,
        "jump_depths": list(JUMP_DEPTHS),
        "global_polynomial_coefficient_annihilator":
            "(d-7)*(d-9)*(d-11)*(d-13)*(S-1)",
        "each_linear_factor_necessary": True,
    }


def _projection():
    return {
        "instance_id": "jc_h3_adjoint_fresh_operator",
        "operator_coefficient_domain": "QQ",
        "sequence_value_module": (
            "padded 5x2 sparse polynomial matrices with faithful QQ scaling"),
        "operator_representation": (
            "finite coefficient sequences canonically padded to width >= 8"),
        "shift_convention": "(S B)_d = B_(d+1)",
        "domain": {"kind": "UNILATERAL", "start": 6},
        "premises": {
            "checked_by_adapter": [
                "padded B_d is zero for every d >= 14",
                "padded B_13 is nonzero",
                "operator jumps occur exactly at d=7,9,11,13",
                "entries are exact sparse QQ-polynomials, so nonzero QQ "
                "scalars act faithfully",
            ],
            "native_assumptions_not_discharged": [
                "P1..P5", "S2", "15*t^3+1=0", "H8 for depths >=8",
            ],
        },
        "claims": {
            "constant_coefficient_annihilator_ideal": {
                "value": "(S^8)",
                "status": "VERIFIED_LEAN_BACKED_FROM_CHECKED_PREMISES",
                "lean_theorem":
                    "annihilatesFrom_iff_coefficients_below_gap_zero",
            },
            "pure_forward_truncation": {"operator": "S^8", "status": "VERIFIED"},
            "S7": {"status": "REFUTED_BY_B13_AT_D6"},
            "nonzero_constant_term_annihilator": {"status": "REFUTED"},
            "reversible_backward_recurrence": {"status": "REFUTED"},
            "polynomial_coefficient_annihilator": {
                "operator": "(d-7)*(d-9)*(d-11)*(d-13)*(S-1)",
                "status": "VERIFIED_ON_PADDED_SEQUENCE",
                "minimality_scope": "S_DEGREE_ONE_ONLY",
            },
        },
        "outside_adapter": [
            "cokernel-basis correctness",
            "depth-8 straggler and determinant identities",
            "additive compatibility values Omega_8 or Omega_9",
            "minimality among higher-S-degree polynomial-coefficient operators",
            "blanket minimality of S-1 within every regime (the zero-tail "
            "regimes admit the unit annihilator)",
        ],
        "refusals": [
            "H8 discharge", "source-image sufficiency", "actual-source membership",
            "geometric component exclusion", "H3 promotion",
            "(75,125) verdict change", "graph claim or transport authority",
        ],
        "graph_effect": "NONE",
    }


def build_fixture(native_root=NATIVE_ROOT):
    root = Path(native_root)
    bindings = {name: normalized_sha256(root / name)
                for name in sorted(NATIVE_BINDINGS)}
    require(bindings == dict(sorted(NATIVE_BINDINGS.items())), "B1",
            "native recurrence inputs drifted before freeze")
    certificate = json.loads((root /
        "f2_h3_adjoint_recurrence_certificate.json").read_text(encoding="utf-8"))
    _validate_recurrence(certificate)
    return {
        "schema": SCHEMA,
        "binding_digest_algo": "sha256-lf-normalized",
        "source_bindings": bindings,
        "native_certificate": certificate,
        "projection": _projection(),
        "authority_boundary": (
            "The checked finite-tail premises plus the Lean theorem establish "
            "the unilateral constant-coefficient annihilator ideal (S^8). "
            "They do not discharge H8 or license source, geometric, H3, graph, "
            "or verdict promotion."),
    }


def _validate_projection(projection):
    require(projection == _projection(), "M1",
            "recurrence scope, premises, conclusions, or refusals changed")


def validate_fixture_value(fixture):
    require(set(fixture) == {"schema", "binding_digest_algo", "source_bindings",
            "native_certificate", "projection", "authority_boundary"}, "F1",
            "fixture shape changed")
    require(fixture["schema"] == SCHEMA and
            fixture["binding_digest_algo"] == "sha256-lf-normalized", "F2",
            "fixture schema or binding algorithm changed")
    require(fixture["source_bindings"] == dict(sorted(NATIVE_BINDINGS.items())),
            "F3", "frozen native binding changed")
    _validate_projection(fixture["projection"])
    premises = _validate_recurrence(fixture["native_certificate"])
    return fixture, premises


def check_native_bindings(fixture, native_root=NATIVE_ROOT):
    root = Path(native_root)
    require(root.exists(), "B2", "sibling JC checkout is absent")
    for name, expected in fixture["source_bindings"].items():
        require((root / name).exists(), "B3", "native binding absent: " + name)
        require(normalized_sha256(root / name) == expected, "B4",
                "native binding changed: " + name)


def verify_fixture(path=DEFAULT_FIXTURE, check_bindings=False,
                   native_root=NATIVE_ROOT):
    raw = Path(path).read_bytes()
    if EXPECTED_FIXTURE_SHA256 is not None:
        require(hashlib.sha256(raw).hexdigest() == EXPECTED_FIXTURE_SHA256,
                "F4", "frozen recurrence fixture digest changed")
    fixture, premises = validate_fixture_value(json.loads(raw.decode("utf-8")))
    if check_bindings:
        check_native_bindings(fixture, native_root)
    report = copy.deepcopy(fixture["projection"])
    report.update({
        "schema": SCHEMA,
        "verdict": "VERIFIED_CONDITIONAL_UNILATERAL_ANNIHILATOR_IDEAL_S8",
        "checked_instance_premises": premises,
        "source_bindings": fixture["source_bindings"],
        "evidence_envelope": {
            "schema": SCHEMA,
            "checked_proposition": (
                "on d>=6, the padded operator sequence has constant-coefficient "
                "annihilator ideal exactly (S^8), conditional on the native "
                "sequence assumptions"),
            "licenses": [
                "S8_annihilates_padded_sequence",
                "S7_does_not_annihilate_padded_sequence",
                "all_constant_coefficients_below_shift_8_vanish",
                "no_nonzero_constant_term_annihilator",
                "no_reversible_backward_recurrence",
            ],
            "outstanding_premises": fixture["projection"]["premises"][
                "native_assumptions_not_discharged"],
            "graph_effect": "NONE",
            "authority_boundary": fixture["authority_boundary"],
        },
    })
    return report


def native_replay(native_root=NATIVE_ROOT):
    script = Path(native_root) / "f2_h3_adjoint_recurrence.py"
    completed = subprocess.run(
        [sys.executable, str(script), "--quiet"], cwd=str(native_root),
        capture_output=True, text=True, timeout=120, check=False)
    require(completed.returncode == 0, "N5",
            "native recurrence replay failed: " + completed.stderr.strip())
    require("44/44 checks passed" in completed.stdout and
            NATIVE_BINDINGS["f2_h3_adjoint_recurrence_certificate.json"] in
            completed.stdout, "N6", "native replay summary changed")
    return {"verdict": "VERIFIED_NATIVE_44_OF_44", "graph_effect": "NONE"}


def _atomic_write(path, value, force=False):
    path = Path(path)
    if path.exists() and not force:
        raise RecurrenceEvidenceError(
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
        print(json.dumps(report, indent=2, sort_keys=True))
        return 0
    except (OSError, ValueError, subprocess.SubprocessError) as exc:
        print(json.dumps({"schema": SCHEMA, "verdict": "REFUSED",
                          "error": str(exc)}, indent=2, sort_keys=True),
              file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
