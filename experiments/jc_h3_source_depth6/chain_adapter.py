#!/usr/bin/env python3
"""Independent GP replay adapter for the landed JC depth-6 chain.

The checked-in gzip is a byte-for-byte frozen copy of the native certificate
landed in math-stuff at cb3136c.  This adapter adds two consumer-side checks:

* the ten chain inputs are exactly the solutions already verified by GP's top
  and second-face triangular-chain fixtures; and
* the two outputs are exactly the boundary polynomials already frozen by GP.

``verify_chain(..., full_replay=False)`` is a quick integrity and weld gate.
``full_replay=True`` additionally recomputes every face substitution using
exact sparse rational arithmetic.  Neither mode licenses the missing raw
E-system -> face-table extraction, actual-source membership, or H3.
"""

from __future__ import annotations

import argparse
import gzip
import hashlib
import importlib.util
import json
import time
from fractions import Fraction
from pathlib import Path

try:  # The native lane uses the same optional acceleration.
    from gmpy2 import mpq as Q
except ImportError:  # pragma: no cover - exercised on minimal installs
    Q = Fraction

from grandportage import evidence as EV
from grandportage import groebner as G


ROOT = Path(__file__).resolve().parents[2]
DEFAULT_FROZEN = ROOT / "fixtures" / "jc_source_depth6" / "chain_v1.json.gz"
DEFAULT_NATIVE = (ROOT.parent / "math-stuff" / "d2_plane_72_108" /
                  "f2_h3_source_depth6_chain_certificate.json.gz")
BOUNDARY_FIXTURE = ROOT / "fixtures" / "jc_source_depth6" / "boundary_v1.json"
TOP_FIXTURE = (ROOT / "fixtures" / "jc_source_ladder" /
               "localized_triangular_solve_chain_v1.json")
SECOND_FIXTURE = (ROOT / "fixtures" / "jc_source_ladder" /
                  "localized_triangular_solve_chain_v2_second_face.json")
BOUNDARY_ADAPTER = Path(__file__).with_name("adapter.py")

EXPECTED_COMPRESSED_SHA256 = (
    "7d0ab133e5e0bd3f9f82d6cdac66302c8e3078321113820b56ca2ef04d4a5871"
)
EXPECTED_CANONICAL_SHA256 = (
    "d5ed44977e1f39312fbd2d30a286f686a0cd26d55dba237420a7a3d2bf513f15"
)
EXPECTED_RECEIPT_BINDING = (
    "3dde87dd53b07c851ce78c27227b63660a9177860791cc2dca5bff5152db9c0d"
)
PIN = {(('t', 3),): Q(15), (): Q(1)}


class Depth6ChainError(ValueError):
    """The frozen chain fails an integrity, replay, or scope check."""


def _require(condition, message):
    if not condition:
        raise Depth6ChainError(message)


def _sha256(data):
    return hashlib.sha256(data).hexdigest()


def _load_gzip(path):
    compressed = Path(path).read_bytes()
    canonical = gzip.decompress(compressed)
    return compressed, canonical, json.loads(canonical.decode("utf-8"))


def _sparse_string(value):
    return json.dumps({
        "symbols": list(value["symbols"]),
        "terms": [[list(map(list, monomial)), coefficient]
                  for monomial, coefficient in value["terms"]],
    }, separators=(",", ":"))


def _sparse_digest(value):
    return _sha256(_sparse_string(value).encode("utf-8"))


def _decode_sparse(value, where):
    _require(isinstance(value, dict) and set(value) == {"symbols", "terms"},
             where + ": sparse body has the wrong shape")
    symbols = value["symbols"]
    terms = value["terms"]
    _require(isinstance(symbols, list) and symbols == sorted(set(symbols)),
             where + ": symbols are not sorted and unique")
    _require(all(isinstance(name, str) and G._IDENTIFIER.fullmatch(name)
                 for name in symbols), where + ": invalid symbol")
    _require(isinstance(terms, list) and len(terms) <= G._MAX_TERMS,
             where + ": invalid term count")
    output = {}
    previous = None
    for position, term in enumerate(terms):
        _require(isinstance(term, list) and len(term) == 2,
                 "%s: malformed term %d" % (where, position))
        support, coefficient_text = term
        _require(isinstance(support, list) and isinstance(coefficient_text, str),
                 "%s: malformed term %d" % (where, position))
        try:
            coefficient = Q(coefficient_text)
        except (ValueError, ZeroDivisionError):
            raise Depth6ChainError("%s: invalid coefficient" % where)
        _require(coefficient and str(coefficient) == coefficient_text,
                 where + ": coefficient is zero or noncanonical")
        last_index = -1
        monomial = []
        for factor in support:
            _require(isinstance(factor, list) and len(factor) == 2,
                     where + ": malformed support factor")
            index, exponent = factor
            _require(type(index) is int and last_index < index < len(symbols),
                     where + ": support indices are not strictly increasing")
            _require(type(exponent) is int and 0 < exponent <= G._MAX_EXPONENT,
                     where + ": exponent is outside the checker bound")
            monomial.append((symbols[index], exponent))
            last_index = index
        monomial = tuple(monomial)
        _require(previous is None or previous < monomial,
                 where + ": terms are not strictly canonical")
        output[monomial] = coefficient
        previous = monomial
    return output


def _mono_mul(left, right):
    powers = dict(left)
    for name, exponent in right:
        powers[name] = powers.get(name, 0) + exponent
    return tuple(sorted(powers.items()))


def _multiply(left, right):
    if len(left) > len(right):
        left, right = right, left
    output = {}
    for lm, lc in left.items():
        for rm, rc in right.items():
            monomial = _mono_mul(lm, rm)
            value = output.get(monomial, Q(0)) + lc * rc
            if value:
                output[monomial] = value
            else:
                output.pop(monomial, None)
    return output


def _add(left, right, scale=Q(1)):
    output = dict(left)
    for monomial, coefficient in right.items():
        value = output.get(monomial, Q(0)) + scale * coefficient
        if value:
            output[monomial] = value
        else:
            output.pop(monomial, None)
    return output


def _pin_mul(value):
    return _multiply(PIN, value)


def _fingerprint(prefix):
    return _sha256(json.dumps(prefix, separators=(",", ":")).encode("utf-8"))


def _affine_split(polynomial, variable):
    coefficient, constant = {}, {}
    for monomial, value in polynomial.items():
        powers = dict(monomial)
        exponent = powers.pop(variable, 0)
        if exponent == 0:
            constant[monomial] = value
        elif exponent == 1:
            coefficient[tuple(sorted(powers.items()))] = value
        else:
            return None
    return coefficient, constant


def _evaluate_face(face, values):
    power_cache = {}

    def power(name, exponent):
        key = (name, exponent)
        if key not in power_cache:
            result = values[name]
            for _ in range(1, exponent):
                result = _multiply(result, values[name])
            power_cache[key] = result
        return power_cache[key]

    output = {}
    for monomial, coefficient in face.items():
        symbolic = []
        substituted = None
        for name, exponent in monomial:
            if name in values:
                factor = power(name, exponent)
                substituted = (factor if substituted is None else
                               _multiply(substituted, factor))
            else:
                symbolic.append((name, exponent))
        term = {tuple(symbolic): coefficient}
        if substituted is not None:
            term = _multiply(term, substituted)
        output = _add(output, term)
    return output


def _load_boundary_adapter():
    spec = importlib.util.spec_from_file_location(
        "jc_source_depth6_boundary_adapter", BOUNDARY_ADAPTER)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def _gp_input_digests(certificate):
    """Translate the already-checked GP ladder solutions to native digests."""
    adapter = _load_boundary_adapter()
    entries = certificate["input_state"]["values"]
    expected = {entry["var"]: entry for entry in entries}
    observed = {}
    for fixture_path in (TOP_FIXTURE, SECOND_FIXTURE):
        fixture = json.loads(fixture_path.read_text(encoding="utf-8"))
        for step in fixture["steps"]:
            variable = step["pivot"]
            if variable not in expected:
                continue
            symbols = expected[variable]["sparse"]["symbols"]
            variables = tuple(sorted(set(fixture["ring_vars"]) | set(symbols)))
            polynomial = G.parse_polynomial(
                step["solution"], variables, fixture["characteristic"],
                G._ArithmeticBudget())
            observed[variable] = adapter._polynomial_native_digest(
                polynomial, symbols)
    _require(set(observed) == set(expected),
             "GP top/second fixtures do not cover all ten chain inputs")
    for variable, digest in observed.items():
        _require(digest == expected[variable]["sha256"],
                 "GP ladder input weld failed for " + variable)
    return observed


def _boundary_native_polynomial(portable, variables):
    parsed = G.parse_polynomial(portable, variables, 0, G._ArithmeticBudget())
    output = {}
    for monomial, coefficient in parsed.terms.items():
        support = tuple((variables[index], exponent)
                        for index, exponent in enumerate(monomial) if exponent)
        output[support] = Q(str(coefficient))
    return output


def _validate_envelope(certificate, canonical, compressed):
    _require(_sha256(compressed) == EXPECTED_COMPRESSED_SHA256,
             "frozen compressed certificate digest changed")
    _require(_sha256(canonical) == EXPECTED_CANONICAL_SHA256,
             "frozen canonical certificate digest changed")
    _require(certificate.get("id") == "f2_h3_source_depth6_chain"
             and certificate.get("kind") == "chain_certificate"
             and certificate.get("schema_version") == 1,
             "unexpected chain certificate identity")
    _require(certificate.get("pin_semantics", {}).get("modulus") ==
             "15*t**3 + 1", "pin semantics changed")
    _require("cofactor" in certificate["pin_semantics"].get("convention", ""),
             "pin convention no longer demands explicit cofactors")
    _require(certificate.get("bindings", {}).get(
        "f2_h3_source_depth6_receipt.json") == EXPECTED_RECEIPT_BINDING,
        "native receipt binding changed")
    required_refusals = {
        "H3 promotion", "actual-source membership",
        "source-image sufficiency", "GP campaign promotion",
        "ambient identity beyond the recorded pin semantics",
    }
    _require(required_refusals <= set(certificate.get("refusals", [])),
             "certificate dropped a required refusal")
    _require(len(certificate.get("faces", {})) == 25,
             "expected exactly 25 depth-2..6 faces")
    _require(len(certificate.get("steps", [])) == 23
             and sum(step.get("depth", 0) <= 5
                     for step in certificate["steps"]) == 20,
             "expected 20 depth-2..5 steps and three depth-6 steps")
    _require(len(certificate.get("residuals", [])) == 2,
             "expected exactly two depth-6 residuals")


def preflight_chain(path=DEFAULT_FROZEN):
    """Check frozen bindings, record digests, order, and rung welds only.

    This tier intentionally never calls ``_decode_sparse`` and performs no
    polynomial arithmetic.  Its verdict names inputs; it is not a chain
    identity verdict and carries no mathematical license.
    """
    started = time.time()
    compressed, canonical, certificate = _load_gzip(path)
    _validate_envelope(certificate, canonical, compressed)
    boundary = json.loads(BOUNDARY_FIXTURE.read_text(encoding="utf-8"))
    rung_by_var = {rung["var"]: rung for rung in
                   boundary["schedule"]["rungs"]}

    for name, record in certificate["faces"].items():
        _require(set(record) == {"sha256", "sparse", "terms"},
                 name + ": face record shape changed")
        _require(_sparse_digest(record["sparse"]) == record["sha256"] and
                 record["terms"] == len(record["sparse"]["terms"]),
                 name + ": face digest or term count changed")

    prefix = []
    for entry in certificate["input_state"]["values"]:
        variable = entry["var"]
        _require(_sparse_digest(entry["sparse"]) == entry["sha256"],
                 "input digest mismatch: " + variable)
        _require(rung_by_var[variable]["value_sha256"] == entry["sha256"],
                 "input is not welded to boundary schedule: " + variable)
        prefix.append([variable, entry["sha256"]])
    _require(_fingerprint(prefix) == certificate["input_state"]["fingerprint"],
             "input state fingerprint mismatch")

    for index, step in enumerate(certificate["steps"]):
        label = "step %d (%s)" % (index, step.get("var", "?"))
        _require(step.get("prior") == [item[0] for item in prefix],
                 label + ": ordered prior mismatch")
        _require(step.get("input_fingerprint") == _fingerprint(prefix),
                 label + ": input fingerprint mismatch")
        for record_name in ("equation", "value"):
            record = step[record_name]
            _require(_sparse_digest(record["sparse"]) == record["sha256"] and
                     record["terms"] == len(record["sparse"]["terms"]),
                     "%s: %s digest or term count mismatch" %
                     (label, record_name))
        value = step["value"]
        _require(rung_by_var[step["var"]]["value_sha256"] == value["sha256"],
                 label + ": rung weld fails")
        prefix.append([step["var"], value["sha256"]])
        _require(step.get("output_fingerprint") == _fingerprint(prefix),
                 label + ": output fingerprint mismatch")

    residuals = {}
    for residual in certificate["residuals"]:
        label = "residual " + residual.get("seam", "?")
        _require(residual.get("prior") == [item[0] for item in prefix] and
                 residual.get("input_fingerprint") == _fingerprint(prefix),
                 label + ": prior or fingerprint mismatch")
        equation = residual["equation"]
        _require(_sparse_digest(equation["sparse"]) == equation["sha256"] and
                 equation["terms"] == len(equation["sparse"]["terms"]),
                 label + ": digest or term count mismatch")
        residuals[residual["identified_with"]] = equation["sha256"]
    _require(residuals.get("R2B") ==
             boundary["residuals"]["R2B"]["native_sha256"],
             "R2B output digest is not welded to the boundary projection")

    return {
        "verdict": "PREFLIGHT_BINDINGS_ONLY",
        "certificate_digest": "sha256:" + EXPECTED_CANONICAL_SHA256,
        "faces_digest_checked": 25,
        "input_rungs_welded": 10,
        "ordered_steps_bound": 23,
        "residual_digests_checked": 2,
        "graph_effect": EV.GRAPH_EFFECT_NONE,
        "licenses": ["frozen_inputs_are_the_named_inputs"],
        "refuses": [
            "chain identity authority",
            "solve or unit authority",
            "source membership, coverage, H3, or verdict promotion",
        ],
        "seconds": round(time.time() - started, 3),
    }


def verify_chain(path=DEFAULT_FROZEN, full_replay=False):
    """Verify the frozen chain, its GP input/output welds, and optionally V3."""
    started = time.time()
    compressed, canonical, certificate = _load_gzip(path)
    _validate_envelope(certificate, canonical, compressed)
    boundary = json.loads(BOUNDARY_FIXTURE.read_text(encoding="utf-8"))
    rung_by_var = {rung["var"]: rung for rung in boundary["schedule"]["rungs"]}

    faces = {}
    for name, record in certificate["faces"].items():
        _require(set(record) == {"sha256", "sparse", "terms"},
                 name + ": face record shape changed")
        _require(_sparse_digest(record["sparse"]) == record["sha256"]
                 and record["terms"] == len(record["sparse"]["terms"]),
                 name + ": face digest or term count changed")
        if full_replay:
            faces[name] = _decode_sparse(record["sparse"], "face " + name)

    _gp_input_digests(certificate)
    values = {}
    prefix = []
    for entry in certificate["input_state"]["values"]:
        variable = entry["var"]
        _require(_sparse_digest(entry["sparse"]) == entry["sha256"],
                 "input digest mismatch: " + variable)
        _require(rung_by_var[variable]["value_sha256"] == entry["sha256"],
                 "input is not welded to boundary schedule: " + variable)
        values[variable] = _decode_sparse(entry["sparse"], "input " + variable)
        prefix.append([variable, entry["sha256"]])
    _require(_fingerprint(prefix) == certificate["input_state"]["fingerprint"],
             "input state fingerprint mismatch")

    for index, step in enumerate(certificate["steps"]):
        label = "step %d (%s)" % (index, step.get("var", "?"))
        _require(step.get("prior") == [item[0] for item in prefix],
                 label + ": ordered prior mismatch")
        _require(step.get("input_fingerprint") == _fingerprint(prefix),
                 label + ": input fingerprint mismatch")
        equation = step["equation"]
        _require(_sparse_digest(equation["sparse"]) == equation["sha256"]
                 and equation["terms"] == len(equation["sparse"]["terms"]),
                 label + ": equation digest or term count mismatch")
        reduced = _decode_sparse(equation["sparse"], label + " equation")
        split = _affine_split(reduced, step["pivot"])
        _require(split is not None, label + ": equation is not affine")
        coefficient, constant = split
        declared = _decode_sparse(step["pivot_coefficient"],
                                  label + " pivot coefficient")
        _require(coefficient == declared, label + ": pivot coefficient mismatch")
        _require(len(coefficient) == 1 and
                 all(name == "t" for monomial in coefficient
                     for name, _exponent in monomial),
                 label + ": pivot is not a declared bare t-unit")
        inverse = _decode_sparse(step["pivot_inverse"], label + " inverse")
        inverse_cofactor = _decode_sparse(
            step["pin_cofactor_inverse"], label + " inverse cofactor")
        _require(_multiply(coefficient, inverse) ==
                 _add({(): Q(1)}, _pin_mul(inverse_cofactor)),
                 label + ": unit witness fails")
        value_record = step["value"]
        _require(_sparse_digest(value_record["sparse"]) == value_record["sha256"]
                 and value_record["terms"] == len(value_record["sparse"]["terms"]),
                 label + ": value digest or term count mismatch")
        _require(rung_by_var[step["var"]]["value_sha256"] ==
                 value_record["sha256"], label + ": rung weld fails")
        value = _decode_sparse(value_record["sparse"], label + " value")
        solve_cofactor = _decode_sparse(step["pin_cofactor_solve"],
                                        label + " solve cofactor")
        _require(_add(_multiply(coefficient, value), constant) ==
                 _pin_mul(solve_cofactor), label + ": solve identity fails")
        if full_replay:
            raw = _evaluate_face(
                faces["row%d_depth%d" % (step["row"], step["depth"])],
                values)
            substitution_cofactor = _decode_sparse(
                step["pin_cofactor_substitution"],
                label + " substitution cofactor")
            _require(raw == _add(reduced, _pin_mul(substitution_cofactor)),
                     label + ": full face substitution identity fails")
        values[step["var"]] = value
        prefix.append([step["var"], value_record["sha256"]])
        _require(step.get("output_fingerprint") == _fingerprint(prefix),
                 label + ": output fingerprint mismatch")

    residual_by_name = {}
    for residual in certificate["residuals"]:
        label = "residual " + residual.get("seam", "?")
        _require(residual.get("prior") == [item[0] for item in prefix]
                 and residual.get("input_fingerprint") == _fingerprint(prefix),
                 label + ": prior or fingerprint mismatch")
        equation = residual["equation"]
        _require(_sparse_digest(equation["sparse"]) == equation["sha256"]
                 and equation["terms"] == len(equation["sparse"]["terms"]),
                 label + ": digest or term count mismatch")
        reduced = _decode_sparse(equation["sparse"], label)
        if full_replay:
            raw = _evaluate_face(
                faces["row%d_depth%d" % (residual["row"], residual["depth"])],
                values)
            cofactor = _decode_sparse(residual["pin_cofactor_substitution"],
                                      label + " substitution cofactor")
            _require(raw == _add(reduced, _pin_mul(cofactor)),
                     label + ": full face substitution identity fails")
        residual_by_name[residual["identified_with"]] = (equation, reduced)

    r2_record = boundary["residuals"]["R2B"]
    _require(residual_by_name["R2B"][0]["sha256"] == r2_record["native_sha256"],
             "R2B output weld failed")
    variables = tuple(boundary["ring_vars"])
    beta_record = boundary["residuals"]["beta"]
    beta = _boundary_native_polynomial(beta_record["polynomial"], variables)
    alpha_c75 = {
        (("c2_3", 2), ("c7_5", 1), ("t", 1)): Q(5, 2),
        (("c4_5", 1), ("c7_5", 1), ("t", 1)): Q(-10),
    }
    _require(residual_by_name["R3B"][1] ==
             _add(beta, alpha_c75), "R3B affine output weld failed")

    authority = (
        "The exact ordered chain from GP's verified top/second-face values "
        "to R2B and alpha*c7_5+beta is replayed inside the 25 digest-bound "
        "face tables. The adapter does not prove those face tables are "
        "extracted from the raw E-system and creates no campaign edge."
    )
    context = EV.AffineContext(
        characteristic=0,
        coefficient_domain="Q[t]/(15*t^3+1) (canonical representatives)",
        point_universe="UNSPECIFIED_ALGEBRAIC_IDENTITY",
        ring_vars=tuple(sorted({symbol for face in certificate["faces"].values()
                                for symbol in face["sparse"]["symbols"]})),
        unit_generators=("t",),
        generators=("25 sparse face bodies bound by certificate digest",),
    )
    envelope = EV.EvidenceEnvelope(
        schema="jc_source_depth6_chain_v1",
        context=context,
        source_bindings=(
            EV.SourceBinding("JC chain certificate (canonical)",
                             "sha256:" + EXPECTED_CANONICAL_SHA256),
            EV.SourceBinding("GP depth-6 boundary projection",
                             "sha256:" + _sha256(BOUNDARY_FIXTURE.read_bytes())),
        ),
        checked_proposition=(
            "full exact depth-2..6 face replay" if full_replay else
            "certificate integrity, ordered solve identities, and GP endpoint welds"
        ),
        licenses=(("exact_ordered_depth2_6_face_replay",
                   "chain_inputs_welded_to_gp_ladder_solutions",
                   "boundary_residuals_welded_to_gp_projection") if full_replay else
                  ("certificate_integrity_and_order_verified",
                   "solve_and_unit_identities_verified",
                   "chain_inputs_welded_to_gp_ladder_solutions",
                   "boundary_residuals_welded_to_gp_projection")),
        outstanding_premises=(
            "raw E-system rows -> the 25 bound face tables",
            "actual-source membership and source-image sufficiency",
            "chart coverage, H3, and (75,125) verdict promotion",
        ),
        graph_effect=EV.GRAPH_EFFECT_NONE,
        authority_boundary=authority,
        certificate_payload={
            "canonical_sha256": EXPECTED_CANONICAL_SHA256,
            "faces": 25,
            "input_values": 10,
            "solved_steps": 23,
            "residuals": 2,
            "full_replay": bool(full_replay),
        },
    )
    return {
        "verdict": ("VERIFIED_DEPTH6_CHAIN_FULL_REPLAY" if full_replay else
                    "VERIFIED_DEPTH6_CHAIN_ENVELOPE"),
        "certificate_digest": "sha256:" + EXPECTED_CANONICAL_SHA256,
        "faces": 25,
        "input_values_welded": 10,
        "solved_steps": 23,
        "residuals_welded": 2,
        "seconds": round(time.time() - started, 3),
        "evidence_envelope": envelope.as_dict(),
    }


def native_copy_matches(path=DEFAULT_NATIVE):
    if not Path(path).exists():
        return None
    return Path(path).read_bytes() == DEFAULT_FROZEN.read_bytes()


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    modes = parser.add_mutually_exclusive_group()
    modes.add_argument("--preflight", action="store_true",
                       help="check bindings and digests without sparse decoding")
    modes.add_argument("--full-replay", action="store_true",
                       help="also recompute all 25 ambient face substitutions")
    parser.add_argument("--certificate", type=Path, default=DEFAULT_FROZEN)
    args = parser.parse_args(argv)
    report = (preflight_chain(args.certificate) if args.preflight else
              verify_chain(args.certificate, args.full_replay))
    print(json.dumps(report,
                     indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
