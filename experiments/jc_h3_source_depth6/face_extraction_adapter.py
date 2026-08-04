#!/usr/bin/env python3
"""Verify the bounded graded extraction from reduced E-system rows to faces.

This is the operation boundary left open by the depth-6 chain certificate.
The checked-in fixture carries five exact reduced E-system row polynomials,
the finite root supports and coordinate series, and commitments to the 25
depth-2..6 faces in the landed chain certificate.

The default verifier performs the row-polynomial -> face-table transformation
with a small exact sparse-series engine.  ``--full-source-replay`` additionally
reconstructs the five reduced rows from the defining power-series formulas and
the fourteen unit-triangular P-side eliminations.  It does not import or invoke
the native chain producer.

Authority remains narrow: extracted face equations are necessary consequences
of the declared finite E-system template.  This does not prove source-image
sufficiency, membership of an original polynomial pair, chart coverage, H3,
or the (75,125) verdict.
"""

from __future__ import annotations

import argparse
import gzip
import hashlib
import importlib.util
import json
import time
from pathlib import Path

from grandportage import evidence as EV


ROOT = Path(__file__).resolve().parents[2]
NATIVE_ROOT = ROOT.parent / "math-stuff" / "d2_plane_72_108"
DEFAULT_FIXTURE = (ROOT / "fixtures" / "jc_source_depth6" /
                   "graded_face_extraction_v1.json")
CHAIN_FIXTURE = ROOT / "fixtures" / "jc_source_depth6" / "chain_v1.json.gz"
CHAIN_ADAPTER_PATH = Path(__file__).with_name("chain_adapter.py")

SCHEMA = "graded_face_extraction_v1"
EXPECTED_FIXTURE_SHA256 = (
    "6c8887034321884b6bb0aa7cd8cf04d90e472a36f4a6ba4035a53e7eda1aa8a1"
)
EXPECTED_CHAIN_CANONICAL_SHA256 = (
    "d5ed44977e1f39312fbd2d30a286f686a0cd26d55dba237420a7a3d2bf513f15"
)
EXPECTED_NATIVE_BINDINGS = {
    "f2_h3_source_depth6_chain_producer.py":
        "aa6b286b753aadcec4d8df512d553b3d0ab024266dbeb4ac02e7dbb5ed611408",
    "f2_h3_esystem_seam.py":
        "e21ecff0f9f389b620fa599820e95c93eb44343c44ff20e9d25879f330b39aca",
    "f2_h3_graded_eliminator_contract.py":
        "63da51c56475d39266f3fc74e6f5b0a2f70d05e0d7781d98791aa6bf12535965",
    "f2_target_root_support_data.py":
        "16eb77a98c9c02939cc48a9b7f0e9f1141234784013daf4a34ca375666a2f2d2",
}

ROOT_SUPPORTS = {
    2: (-10, -7, -4, -1),
    3: (-15, -12, -9, -6, -3, 0),
    4: (-17, -14, -11, -8, -5, -2),
    5: (-22, -19, -16, -13, -10, -7, -4, -1),
    6: (-27, -24, -21, -18, -15, -12, -9, -6, -3, 0),
    7: (-32, -29, -26, -23, -20, -17, -14, -11, -8, -5, -2, 1),
    8: (-37, -34, -31, -28, -25, -22, -19, -16, -13, -10, -7, -4, -1),
    9: (-42, -39, -36, -33, -30, -27, -24, -21, -18, -15, -12, -9, -6, -3, 0),
}
ROOTS = tuple(sorted(ROOT_SUPPORTS))
DEPTH = 6
DELTA = 3
M = 3
N = 5
SOURCE_WINDOW_ROWS = 8
P_ROWS = SOURCE_WINDOW_ROWS + DELTA * (N - M)
SOURCE_ROW_COUNT = 5
SCALARS = ("a2", "a4", "a1", "am1", "lam")


class FaceExtractionError(ValueError):
    """The face-extraction fixture fails a bounded exact check."""


def _require(condition, message):
    if not condition:
        raise FaceExtractionError(message)


def _sha256(data):
    return hashlib.sha256(data).hexdigest()


def _normalized_file_digest(path):
    return _sha256(Path(path).read_bytes().replace(b"\r\n", b"\n"))


def _load_chain_adapter():
    spec = importlib.util.spec_from_file_location(
        "jc_source_depth6_chain_adapter_for_faces", CHAIN_ADAPTER_PATH)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


CHAIN = _load_chain_adapter()
Q = CHAIN.Q


class _Budget:
    def __init__(self, max_products=50_000_000, max_terms=20_000):
        self.max_products = max_products
        self.max_terms = max_terms
        self.products = 0

    def consume(self, left, right, where):
        self.products += len(left) * len(right)
        _require(self.products <= self.max_products,
                 where + ": multiplication work budget exceeded")

    def check_terms(self, value, where):
        _require(len(value) <= self.max_terms,
                 where + ": sparse term budget exceeded")


def _add(left, right, budget, where, scale=None):
    output = dict(left)
    for monomial, coefficient in right.items():
        if scale is not None:
            coefficient *= scale
        value = output.get(monomial, Q(0)) + coefficient
        if value:
            output[monomial] = value
        else:
            output.pop(monomial, None)
    budget.check_terms(output, where)
    return output


def _mono_mul(left, right):
    powers = dict(left)
    for name, exponent in right:
        powers[name] = powers.get(name, 0) + exponent
    return tuple(sorted(powers.items()))


def _multiply(left, right, budget, where):
    if not left or not right:
        return {}
    budget.consume(left, right, where)
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
    budget.check_terms(output, where)
    return output


def _power(value, exponent, budget, where):
    result = {(): Q(1)}
    base = value
    power = exponent
    while power:
        if power & 1:
            result = _multiply(result, base, budget, where)
        power //= 2
        if power:
            base = _multiply(base, base, budget, where)
    return result


def _series_multiply(left, right, budget, where, depth=DEPTH):
    output = [{} for _ in range(depth + 1)]
    for i, left_coefficient in enumerate(left):
        if not left_coefficient:
            continue
        for j, right_coefficient in enumerate(right[:depth + 1 - i]):
            if not right_coefficient:
                continue
            product = _multiply(left_coefficient, right_coefficient,
                                budget, where)
            output[i + j] = _add(output[i + j], product, budget, where)
    return output


def _series_power(value, exponent, budget, where, depth=DEPTH):
    result = [{(): Q(1)}] + [{} for _ in range(depth)]
    for _ in range(exponent):
        result = _series_multiply(result, value, budget, where, depth=depth)
    return result


def _coordinate_name(root, lift):
    if (root, lift) == (2, 0):
        return "p"
    if (root, lift) == (3, 0):
        return "q"
    if (root, lift) == (7, 11):
        return "t"
    return "c%d_%d" % (root, lift)


def _coordinate_series(root, depth=DEPTH):
    top_lift = len(ROOT_SUPPORTS[root]) - 1
    output = []
    for offset in range(depth + 1):
        lift = top_lift - offset
        output.append({((_coordinate_name(root, lift), 1),): Q(1)}
                      if lift >= 0 else {})
    return output


def _scalar_images():
    return {
        "a2": {(('a2', 1),): Q(1)},
        "a4": {(('I4', 1),): Q(1)},
        "a1": {
            (("I1", 1),): Q(1),
            (("I4", 1), ("a2", 1)): Q(4, 5),
        },
        "am1": {
            (("Im1", 1),): Q(1),
            (("a2", 2),): Q(1, 5),
        },
        "lam": {(('lam', 1),): Q(1)},
    }


def _row_max(row):
    maximum = None
    for monomial in row:
        powers = dict(monomial)
        weight = sum(powers.get("z%d" % root, 0) * ROOT_SUPPORTS[root][-1]
                     for root in ROOTS)
        maximum = weight if maximum is None else max(maximum, weight)
    _require(maximum is not None, "source row is zero")
    return maximum


def _build_faces(source_rows, depth=DEPTH):
    """Independent native sparse implementation of the weighted face pass."""
    budget = _Budget()
    root_series = {root: _coordinate_series(root, depth=depth) for root in ROOTS}
    scalars = _scalar_images()
    faces = {}
    row_maxima = {}
    for row_number, row in sorted(source_rows.items()):
        maximum = _row_max(row)
        row_maxima[row_number] = maximum
        output = [{} for _ in range(depth + 1)]
        for term_index, (monomial, coefficient) in enumerate(row.items()):
            powers = dict(monomial)
            weight = sum(powers.get("z%d" % root, 0) *
                         ROOT_SUPPORTS[root][-1] for root in ROOTS)
            distance = maximum - weight
            _require(distance >= 0 and distance % DELTA == 0,
                     "row %d term %d violates the frozen grading" %
                     (row_number, term_index))
            gap = distance // DELTA
            if gap > depth:
                continue
            scalar = {(): coefficient}
            for name in SCALARS:
                exponent = powers.pop(name, 0)
                if exponent:
                    scalar = _multiply(
                        scalar, _power(scalars[name], exponent, budget,
                                       "scalar substitution"),
                        budget, "scalar substitution")
            product_series = [{(): Q(1)}] + [{} for _ in range(depth)]
            for root in ROOTS:
                name = "z%d" % root
                exponent = powers.pop(name, 0)
                if exponent:
                    product_series = _series_multiply(
                        product_series,
                        _series_power(root_series[root], exponent, budget,
                                      "root-series power", depth=depth),
                        budget, "root-series product", depth=depth)
            _require(not powers,
                     "source row contains an unsupported symbol: %s" %
                     sorted(powers))
            for series_depth, value in enumerate(
                    product_series[:depth + 1 - gap]):
                if value:
                    contribution = _multiply(
                        scalar, value, budget, "face contribution")
                    output[gap + series_depth] = _add(
                        output[gap + series_depth], contribution, budget,
                        "face accumulation")
        for face_depth, value in enumerate(output):
            faces[(row_number, face_depth)] = value
    return faces, row_maxima, budget.products


def _to_sparse(polynomial):
    names = sorted({name for monomial in polynomial for name, _ in monomial})
    index = {name: position for position, name in enumerate(names)}
    terms = []
    for monomial, coefficient in polynomial.items():
        support = [[index[name], exponent] for name, exponent in monomial]
        terms.append([support, str(coefficient)])
    terms.sort(key=lambda term: tuple(tuple(pair) for pair in term[0]))
    return {"symbols": names, "terms": terms}


def _derive_source_rows():
    """Rebuild the five reduced rows from the defining E-system formulas."""
    try:
        import sympy as sp
    except ImportError as exc:  # pragma: no cover - optional slow audit
        raise FaceExtractionError("full source replay requires SymPy") from exc

    maximum = max(P_ROWS + DELTA * M, SOURCE_WINDOW_ROWS + DELTA * N)
    z = {exponent: sp.Symbol("z%d" % exponent)
         for exponent in range(2, maximum + 1)}
    zu = [sp.Integer(0)] * (maximum + 1)
    zu[0] = sp.Integer(1)
    for exponent, symbol in z.items():
        zu[exponent] = symbol

    def series_multiply(left, right):
        output = [sp.Integer(0)] * (maximum + 1)
        for i, left_value in enumerate(left):
            if left_value == 0:
                continue
            for j, right_value in enumerate(right[:maximum + 1 - i]):
                if right_value != 0:
                    output[i + j] += left_value * right_value
        return [sp.expand(value) for value in output]

    def series_power(value, exponent):
        output = [sp.Integer(0)] * (maximum + 1)
        output[0] = sp.Integer(1)
        for _ in range(exponent):
            output = series_multiply(output, value)
        return output

    inverse = [sp.Integer(0)] * (maximum + 1)
    inverse[0] = sp.Integer(1)
    for degree in range(1, maximum + 1):
        inverse[degree] = sp.expand(-sum(
            zu[k] * inverse[degree - k] for k in range(1, degree + 1)))
    positive1 = zu
    positive2 = series_power(zu, 2)
    positive3 = series_power(zu, 3)
    positive4 = series_power(zu, 4)
    positive5 = series_power(zu, 5)
    negative1 = inverse
    negative2 = series_multiply(inverse, inverse)

    solved = {}
    for k in range(1, P_ROWS + 1):
        expression = sp.expand(positive3[DELTA * M + k].subs(solved))
        target = z[DELTA * M + k]
        polynomial = sp.Poly(expression, target)
        _require(polynomial.degree() == 1 and polynomial.nth(1) == M,
                 "P-side triangular solve changed at row %d" % k)
        solved[target] = sp.expand(-polynomial.nth(0) / M)

    a2, a4, a1, am1, lam = sp.symbols("a2 a4 a1 am1 lam")
    scalar_symbols = (a2, a4, a1, am1, lam)
    seed_symbols = tuple(z[root] for root in ROOTS)
    rows = {}
    for row in range(1, SOURCE_ROW_COUNT + 1):
        expression = (positive5[DELTA * N + row]
                      + a4 * positive4[4 * DELTA + row]
                      + a2 * positive2[2 * DELTA + row]
                      + a1 * positive1[DELTA + row])
        if row >= DELTA:
            expression += am1 * negative1[row - DELTA]
        if row >= 2 * DELTA:
            expression += lam * negative2[row - 2 * DELTA]
        expression = sp.expand(expression.subs(solved))
        polynomial = sp.Poly(expression, *(seed_symbols + scalar_symbols))
        native = {}
        generators = seed_symbols + scalar_symbols
        for exponents, coefficient in polynomial.terms():
            monomial = tuple((str(symbol), exponent)
                             for symbol, exponent in zip(generators, exponents)
                             if exponent)
            native[tuple(sorted(monomial))] = Q(int(coefficient.p),
                                                int(coefficient.q))
        rows[row] = native
    return rows


def _load_chain():
    canonical = gzip.decompress(CHAIN_FIXTURE.read_bytes())
    _require(_sha256(canonical) == EXPECTED_CHAIN_CANONICAL_SHA256,
             "landed chain certificate digest changed")
    return json.loads(canonical.decode("utf-8"))


def _fixture_value(source_rows):
    chain = _load_chain()
    row_records = []
    for row, polynomial in sorted(source_rows.items()):
        sparse = _to_sparse(polynomial)
        row_records.append({
            "row": row,
            "sparse": sparse,
            "sha256": CHAIN._sparse_digest(sparse),
            "terms": len(sparse["terms"]),
        })
    faces = []
    for row in range(1, SOURCE_ROW_COUNT + 1):
        for depth in range(2, DEPTH + 1):
            record = chain["faces"]["row%d_depth%d" % (row, depth)]
            faces.append({
                "row": row,
                "depth": depth,
                "sha256": record["sha256"],
                "terms": record["terms"],
            })
    return {
        "schema": SCHEMA,
        "source_bindings": dict(EXPECTED_NATIVE_BINDINGS),
        "chain_canonical_sha256": EXPECTED_CHAIN_CANONICAL_SHA256,
        "formula": {
            "delta": DELTA,
            "m": M,
            "n": N,
            "source_window_rows": SOURCE_WINDOW_ROWS,
            "p_side_rows": P_ROWS,
            "output_rows": SOURCE_ROW_COUNT,
            "depth": DEPTH,
            "normalized_root_series": "Zu=1+sum(z_e*u^e)",
            "p_side_equations": "coeff_u^(delta*m+k)(Zu^m)=0, k=1..14",
            "row_equations": "coefficients of Zu^5+a4*Zu^4+a2*Zu^2+a1*Zu+am1*Zu^-1+lam*Zu^-2",
            "invariant_substitution": {
                "a4": "I4",
                "a1": "I1+4/5*a2*I4",
                "am1": "Im1+1/5*a2^2",
            },
        },
        "root_supports": {str(root): list(ROOT_SUPPORTS[root])
                          for root in ROOTS},
        "coordinate_series": {
            str(root): [_coordinate_name(root, lift)
                        for lift in range(len(ROOT_SUPPORTS[root]) - 1,
                                          max(-1, len(ROOT_SUPPORTS[root]) -
                                              DEPTH - 2), -1)]
            for root in ROOTS
        },
        "source_rows": row_records,
        "output_faces": faces,
        "licenses": [
            "exact_depth2_6_faces_from_declared_reduced_esystem_rows",
            "selected_face_equations_are_necessary_under_declared_root_supports",
        ],
        "refusals": [
            "source-image sufficiency",
            "actual polynomial-pair membership",
            "q-chart membership",
            "p-chart membership",
            "chart coverage",
            "H3 promotion",
            "(75,125) verdict change",
        ],
        "authority_boundary": (
            "Exact selected coefficient extraction only. The five carried "
            "source rows are after the declared P-side triangular reduction; "
            "full-source-replay rederives them. No reverse point lift, cover, "
            "membership, or H3 authority is supplied."
        ),
    }


def _encoded(value):
    return (json.dumps(value, indent=2, sort_keys=True,
                       ensure_ascii=True) + "\n").encode("utf-8")


def write_fixture(path=DEFAULT_FIXTURE):
    source_rows = _derive_source_rows()
    value = _fixture_value(source_rows)
    encoded = _encoded(value)
    path = Path(path)
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_suffix(path.suffix + ".tmp")
    temporary.write_bytes(encoded)
    temporary.replace(path)
    return "sha256:" + _sha256(encoded)


def _check_native_bindings(fixture):
    _require(NATIVE_ROOT.exists(), "sibling math-stuff checkout is absent")
    for name, expected in fixture["source_bindings"].items():
        path = NATIVE_ROOT / name
        _require(path.exists(), "native binding is absent: " + name)
        _require(_normalized_file_digest(path) == expected,
                 "native binding changed: " + name)


def verify_fixture(path=DEFAULT_FIXTURE, full_source_replay=False,
                   check_native_bindings=False):
    started = time.time()
    raw = Path(path).read_bytes()
    if EXPECTED_FIXTURE_SHA256 is not None:
        _require(_sha256(raw) == EXPECTED_FIXTURE_SHA256,
                 "graded face-extraction fixture digest changed")
    fixture = json.loads(raw.decode("utf-8"))
    expected_fields = {
        "authority_boundary", "chain_canonical_sha256", "coordinate_series",
        "formula", "licenses", "output_faces", "refusals", "root_supports",
        "schema", "source_bindings", "source_rows",
    }
    _require(set(fixture) == expected_fields and fixture["schema"] == SCHEMA,
             "graded face-extraction fixture schema changed")
    _require(fixture["source_bindings"] == EXPECTED_NATIVE_BINDINGS,
             "source file bindings changed")
    _require(fixture["chain_canonical_sha256"] ==
             EXPECTED_CHAIN_CANONICAL_SHA256,
             "chain binding changed")
    _require(fixture["root_supports"] == {
        str(root): list(ROOT_SUPPORTS[root]) for root in ROOTS},
        "root-support table changed")
    expected_coordinates = {
        str(root): [_coordinate_name(root, lift)
                    for lift in range(len(ROOT_SUPPORTS[root]) - 1,
                                      max(-1, len(ROOT_SUPPORTS[root]) -
                                          DEPTH - 2), -1)]
        for root in ROOTS
    }
    _require(fixture["coordinate_series"] == expected_coordinates,
             "coordinate-series manifest changed")
    expected_formula = {
        "delta": DELTA,
        "m": M,
        "n": N,
        "source_window_rows": SOURCE_WINDOW_ROWS,
        "p_side_rows": P_ROWS,
        "output_rows": SOURCE_ROW_COUNT,
        "depth": DEPTH,
        "normalized_root_series": "Zu=1+sum(z_e*u^e)",
        "p_side_equations": "coeff_u^(delta*m+k)(Zu^m)=0, k=1..14",
        "row_equations": "coefficients of Zu^5+a4*Zu^4+a2*Zu^2+a1*Zu+am1*Zu^-1+lam*Zu^-2",
        "invariant_substitution": {
            "a4": "I4",
            "a1": "I1+4/5*a2*I4",
            "am1": "Im1+1/5*a2^2",
        },
    }
    _require(fixture["formula"] == expected_formula,
             "graded extraction formula manifest changed")
    required_refusals = {
        "source-image sufficiency", "actual polynomial-pair membership",
        "chart coverage", "H3 promotion", "(75,125) verdict change",
    }
    _require(required_refusals <= set(fixture["refusals"]),
             "a required authority refusal was dropped")
    if check_native_bindings:
        _check_native_bindings(fixture)

    source_rows = {}
    _require([record.get("row") for record in fixture["source_rows"]] ==
             list(range(1, SOURCE_ROW_COUNT + 1)),
             "source row order changed")
    for record in fixture["source_rows"]:
        _require(set(record) == {"row", "sha256", "sparse", "terms"},
                 "source row record schema changed")
        _require(CHAIN._sparse_digest(record["sparse"]) == record["sha256"]
                 and len(record["sparse"]["terms"]) == record["terms"],
                 "source row digest or term count changed")
        source_rows[record["row"]] = CHAIN._decode_sparse(
            record["sparse"], "source row %d" % record["row"])

    replayed_source = False
    if full_source_replay:
        derived = _derive_source_rows()
        for row in range(1, SOURCE_ROW_COUNT + 1):
            _require(derived[row] == source_rows[row],
                     "full source replay changed row %d" % row)
        replayed_source = True

    calculated, row_maxima, products = _build_faces(source_rows)
    _require(row_maxima == {1: 1, 2: 2, 3: 0, 4: 1, 5: 2},
             "weighted row maxima changed")
    chain = _load_chain()
    expected_order = [(row, depth) for row in range(1, 6)
                      for depth in range(2, 7)]
    _require([(record.get("row"), record.get("depth"))
              for record in fixture["output_faces"]] == expected_order,
             "output face order changed")
    for record in fixture["output_faces"]:
        _require(set(record) == {"depth", "row", "sha256", "terms"},
                 "output face record schema changed")
        row, depth = record["row"], record["depth"]
        sparse = _to_sparse(calculated[row, depth])
        digest = CHAIN._sparse_digest(sparse)
        landed = chain["faces"]["row%d_depth%d" % (row, depth)]
        _require(digest == record["sha256"] == landed["sha256"],
                 "extracted face digest mismatch at row %d depth %d" %
                 (row, depth))
        _require(len(sparse["terms"]) == record["terms"] == landed["terms"],
                 "extracted face term count mismatch at row %d depth %d" %
                 (row, depth))

    licenses = [
        "exact_depth2_6_faces_from_declared_reduced_esystem_rows",
        "selected_face_equations_are_necessary_under_declared_root_supports",
        "all_25_outputs_welded_to_landed_chain_faces",
    ]
    if replayed_source:
        licenses.append("reduced_esystem_rows_rederived_from_defining_formula")
    context = EV.AffineContext(
        characteristic=0,
        coefficient_domain="Q",
        point_universe="FORMAL_FINITE_ROOT_TEMPLATE",
        ring_vars=tuple(sorted({name for polynomial in calculated.values()
                                for monomial in polynomial
                                for name, _ in monomial})),
        generators=tuple("row%d_depth%d@%s" %
                         (record["row"], record["depth"], record["sha256"])
                         for record in fixture["output_faces"]),
    )
    envelope = EV.EvidenceEnvelope(
        schema=SCHEMA,
        context=context,
        source_bindings=tuple(
            EV.SourceBinding(name, "sha256:" + digest)
            for name, digest in sorted(fixture["source_bindings"].items())) +
            (EV.SourceBinding("landed depth-6 chain certificate",
                              "sha256:" + EXPECTED_CHAIN_CANONICAL_SHA256),),
        checked_proposition=(
            "25 selected faces are the exact weighted coefficient extraction "
            "of five reduced E-system rows under the declared finite supports"
        ),
        licenses=tuple(licenses),
        outstanding_premises=(
            "original polynomial-pair -> this reduced E-system presentation",
            "source-image sufficiency or a reverse lift",
            "chart coverage, H3, and (75,125) verdict promotion",
        ),
        graph_effect=EV.GRAPH_EFFECT_NONE,
        authority_boundary=fixture["authority_boundary"],
        certificate_payload={
            "fixture_sha256": "sha256:" + _sha256(raw),
            "source_rows": 5,
            "faces": 25,
            "depths": [2, 3, 4, 5, 6],
            "sparse_products": products,
            "full_source_replay": replayed_source,
        },
    )
    return {
        "verdict": ("VERIFIED_GRADED_FACE_EXTRACTION_WITH_SOURCE_REPLAY"
                    if replayed_source else
                    "VERIFIED_GRADED_FACE_EXTRACTION"),
        "source_rows": 5,
        "faces": 25,
        "sparse_products": products,
        "seconds": round(time.time() - started, 3),
        "evidence_envelope": envelope.as_dict(),
    }


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--fixture", type=Path, default=DEFAULT_FIXTURE)
    parser.add_argument("--write-fixture", action="store_true",
                        help="derive and atomically freeze the reviewed fixture")
    parser.add_argument("--full-source-replay", action="store_true",
                        help="rederive reduced rows from the E-system formulas")
    parser.add_argument("--check-native-bindings", action="store_true")
    args = parser.parse_args(argv)
    if args.write_fixture:
        print(write_fixture(args.fixture))
        return 0
    print(json.dumps(verify_fixture(
        args.fixture, args.full_source_replay, args.check_native_bindings),
        indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
