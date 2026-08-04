"""Freeze and bind the JC actual-source depth-6 boundary receipt.

The native receipt carries full sparse maps for the two boundary residuals but
only digest commitments for the 33 preceding solve values.  This adapter keeps
that distinction executable: it validates and imports the exact boundary
polynomials, certifies the generic and discriminant-stratum affine rewrites,
and deliberately creates no edge from the native actual-source system.
"""

import argparse
import hashlib
import json
from fractions import Fraction
from pathlib import Path

from grandportage import check as C
from grandportage import evidence as EV
from grandportage import format as F
from grandportage import groebner as G
from grandportage import kernel as K
from grandportage import store as S
from grandportage import verify as V


ROOT = Path(__file__).resolve().parents[2]
DEFAULT_SOURCE = (ROOT.parent / "math-stuff" / "d2_plane_72_108" /
                  "f2_h3_source_depth6_receipt.json")
DEFAULT_FROZEN = (ROOT / "fixtures" / "jc_source_depth6" /
                  "boundary_v1.json")

EXPECTED_NATIVE_SHA256 = (
    "sha256:3c9954943d94faf8122ef556aa724845"
    "4d3d3d03e460747c6d55c0d3bc4a1464"
)
FROZEN_SCHEMA = "jc-f2-h3-source-depth6-boundary/v1"
BOUNDARY_MODEL = "JC-SOURCE-D6-BOUNDARY-IDEAL"
GENERIC_MODEL = "JC-SOURCE-D6-GENERIC"
GENERIC_SOLVED_MODEL = "JC-SOURCE-D6-GENERIC-SOLVED"
GENERIC_EDGE = "JC-SOURCE-D6-GENERIC-AFFINE-SOLVE"
DISCRIMINANT_MODEL = "JC-SOURCE-D6-DISCRIMINANT"
DISCRIMINANT_BETA_MODEL = "JC-SOURCE-D6-DISCRIMINANT-BETA"
DISCRIMINANT_EDGE = "JC-SOURCE-D6-DISCRIMINANT-COLLAPSE"
SOURCE_DEBT_NOTE = "JC-SOURCE-D6-SOURCE-BINDING-DEBT"
BETA_ALIAS = "GP_BETA"
ALPHA_INVERSE = "GP_INV_alpha"
ALPHA = "5/2*t*(c2_3^2-4*c4_5)"
DISCRIMINANT = "c2_3^2-4*c4_5"
PIN = "15*t^3+1"


class Depth6ReceiptError(ValueError):
    """The frozen native receipt cannot support the promised exact import."""


def _require(condition, message):
    if not condition:
        raise Depth6ReceiptError(message)


def _sha256(data):
    return "sha256:" + hashlib.sha256(data).hexdigest()


def _encoded(value):
    return (json.dumps(value, indent=2, sort_keys=True,
                       ensure_ascii=True) + "\n").encode("utf-8")


def _native_sparse_digest(value):
    canonical = {
        "symbols": list(value["symbols"]),
        "terms": [
            [[list(pair) for pair in monomial], coefficient]
            for monomial, coefficient in value["terms"]
        ],
    }
    return hashlib.sha256(json.dumps(
        canonical, separators=(",", ":")).encode("utf-8")).hexdigest()


def _polynomial_native_digest(polynomial, symbols):
    indices = [polynomial.variables.index(name) for name in symbols]
    terms = []
    for monomial, coefficient in polynomial.terms.items():
        support = tuple(
            (index, monomial[variable_index])
            for index, variable_index in enumerate(indices)
            if monomial[variable_index]
        )
        terms.append((support, str(coefficient)))
    terms.sort(key=lambda item: item[0])
    return _native_sparse_digest({
        "symbols": list(symbols),
        "terms": [
            [[[index, exponent] for index, exponent in support], coefficient]
            for support, coefficient in terms
        ],
    })

def _decode_native_sparse(value, variables, characteristic=0, budget=None):
    _require(isinstance(value, dict) and set(value) == {"symbols", "terms"},
             "native sparse polynomial has the wrong shape")
    symbols = value["symbols"]
    terms = value["terms"]
    _require(isinstance(symbols, list) and len(symbols) == len(set(symbols)),
             "native sparse symbols must be a unique list")
    _require(all(isinstance(name, str) and G._IDENTIFIER.fullmatch(name)
                 for name in symbols),
             "native sparse symbols must be GP identifiers")
    _require(set(symbols) <= set(variables),
             "native sparse polynomial names a variable outside the ring")
    _require(isinstance(terms, list) and 0 < len(terms) <= G._MAX_TERMS,
             "native sparse polynomial has an invalid term count")
    variable_index = {name: index for index, name in enumerate(variables)}
    decoded = {}
    for position, term in enumerate(terms):
        _require(isinstance(term, list) and len(term) == 2,
                 "native sparse term %d has the wrong shape" % position)
        support, coefficient_text = term
        _require(isinstance(support, list) and isinstance(coefficient_text, str),
                 "native sparse term %d is malformed" % position)
        try:
            coefficient = Fraction(coefficient_text)
        except (ValueError, ZeroDivisionError):
            raise Depth6ReceiptError(
                "native sparse term %d has an invalid coefficient" % position)
        _require(coefficient and str(coefficient) == coefficient_text,
                 "native sparse term %d coefficient is not canonical" % position)
        monomial = [0] * len(variables)
        previous = -1
        for factor in support:
            _require(isinstance(factor, list) and len(factor) == 2,
                     "native sparse term %d has a malformed factor" % position)
            symbol_index, exponent = factor
            _require(type(symbol_index) is int and previous < symbol_index < len(symbols),
                     "native sparse factor indices must be strictly increasing")
            _require(type(exponent) is int and 0 < exponent <= G._MAX_EXPONENT,
                     "native sparse exponent is outside the checker bound")
            monomial[variable_index[symbols[symbol_index]]] = exponent
            previous = symbol_index
        monomial = tuple(monomial)
        _require(monomial not in decoded,
                 "native sparse polynomial repeats a monomial")
        decoded[monomial] = coefficient
    return G.Polynomial(
        tuple(variables), characteristic, decoded,
        budget or G._ArithmeticBudget())


def _portable(polynomial, sparse=False):
    return G.portable_polynomial(
        polynomial, prefer_sparse=sparse or len(polynomial.terms) > 1000)


def _unit_vector(length, index):
    return ["1" if position == index else "0" for position in range(length)]


def _identity_map(variables):
    return {name: name for name in variables}


def _alpha_stratum_nonzero(beta, variables):
    c23 = variables.index("c2_3")
    c45 = variables.index("c4_5")
    reduced = {}
    for monomial, coefficient in beta.terms.items():
        monomial = list(monomial)
        power = monomial[c45]
        monomial[c45] = 0
        monomial[c23] += 2 * power
        key = tuple(monomial)
        value = reduced.get(key, Fraction(0)) + coefficient * Fraction(1, 4) ** power
        if value:
            reduced[key] = value
        else:
            reduced.pop(key, None)
    return bool(reduced)


def _validate_schedule(rungs):
    _require(isinstance(rungs, list) and len(rungs) == 33,
             "depth-6 schedule must contain exactly 33 rungs")
    _require([rung.get("stage") for rung in rungs[:5]] == ["top"] * 5,
             "the first five rungs must be the top face")
    expected_depths = [depth for depth in range(1, 6) for _ in range(5)]
    _require([rung.get("depth") for rung in rungs[5:30]] == expected_depths,
             "the receipt does not contain five ordered rungs at depths 1..5")
    _require([rung.get("depth") for rung in rungs[30:]] == [6, 6, 6],
             "the schedule must finish with three depth-6 solves")
    _require([rung.get("row") for rung in rungs[5:30]] ==
             [row for _depth in range(1, 6) for row in [2, 5, 1, 4, 3]],
             "depth 1..5 row order changed")
    for rung in rungs:
        digest = rung.get("value_sha256")
        _require(isinstance(digest, str) and len(digest) == 64
                 and all(ch in "0123456789abcdef" for ch in digest),
                 "every rung needs one full lowercase SHA-256 commitment")
        _require(type(rung.get("terms")) is int and rung["terms"] > 0,
                 "every rung needs a positive term count")
    _require(all(rung.get("pivot") in {"-5*t**2", "10*t"}
                 for rung in rungs[5:]),
             "a descent rung uses something other than a frozen unit pivot")


def freeze_native(native, source_bytes):
    """Project the exact portable boundary evidence from one pinned receipt."""
    source_sha = _sha256(source_bytes)
    _require(source_sha == EXPECTED_NATIVE_SHA256,
             "native depth-6 receipt changed: expected %s, got %s" %
             (EXPECTED_NATIVE_SHA256, source_sha))
    _require(native.get("id") == "f2_h3_source_depth6"
             and native.get("schema_version") == 1
             and native.get("kind") == "frozen_receipt",
             "unexpected native depth-6 receipt identity")
    _require(native.get("seam", {}).get("row2_depth6") == "E[2,21]"
             and native.get("seam", {}).get("row3_depth6") == "E[3,22]",
             "native depth-6 seam changed")
    refusals = list(native.get("refusals") or [])
    required_refusals = {
        "q-chart membership", "actual-source membership", "H3 promotion",
        "(75,125) verdict change",
        "substitution of the linearized q ladder into this nonlinear march",
    }
    _require(required_refusals <= set(refusals),
             "native depth-6 receipt dropped a required refusal")
    rungs = list(native.get("schedule", {}).get("rungs") or [])
    _validate_schedule(rungs)

    r2 = native.get("residuals", {}).get("R2B") or {}
    r3 = native.get("residuals", {}).get("R3B") or {}
    beta = r3.get("beta") or {}
    _require(r2.get("seam") == "E[2,21]" and r2.get("terms") == 3262,
             "R2B seam or term count changed")
    _require(r3.get("seam") == "E[3,22]"
             and r3.get("alpha") == "5*t*(c2_3**2 - 4*c4_5)/2"
             and r3.get("alpha_is_contract_unit") is False,
             "the affine depth-6 residual changed")
    _require(beta.get("terms") == 6124,
             "beta term count changed")
    _require(_native_sparse_digest(r2["sparse"]) == r2.get("sha256")
             and _native_sparse_digest(beta["sparse"]) == beta.get("sha256"),
             "native residual sparse digest changed")
    _require(r2["sparse"].get("symbols") == beta["sparse"].get("symbols"),
             "R2B and beta no longer share the same free-coordinate ring")

    variables = sorted(set(r2["sparse"]["symbols"]) |
                       {"c7_5", BETA_ALIAS})
    budget = G._ArithmeticBudget()
    r2_polynomial = _decode_native_sparse(r2["sparse"], variables, budget=budget)
    beta_polynomial = _decode_native_sparse(beta["sparse"], variables,
                                             budget=budget)
    _require(_alpha_stratum_nonzero(beta_polynomial, variables),
             "beta became zero on the discriminant stratum")
    witness = [0] * len(variables)
    for name in ("c2_3", "c8_7", "t"):
        witness[variables.index(name)] = 1
    _require(r2_polynomial.terms.get(tuple(witness)) == Fraction(-5),
             "R2B lost its exact -5*c2_3*c8_7*t witness")

    return {
        "schema": FROZEN_SCHEMA,
        "native_parent": {
            "id": native["id"],
            "sha256": source_sha,
            "base": native.get("base"),
            "producer": {
                "file": native.get("producer", {}).get("file"),
                "sha256": "sha256:" + native.get("producer", {}).get("sha256", ""),
            },
            "inputs": dict(native.get("inputs") or {}),
        },
        "characteristic": 0,
        "coefficient_domain": "Q",
        "point_universe": S.ALGEBRAIC_CLOSURE_POINT_UNIVERSE,
        "ring_vars": variables,
        "native_symbols": list(r2["sparse"]["symbols"]),
        "pin": PIN,
        "alpha": ALPHA,
        "discriminant": DISCRIMINANT,
        "beta_alias": BETA_ALIAS,
        "seam": dict(native["seam"]),
        "premises": dict(native.get("premises") or {}),
        "refusals": refusals,
        "schedule": {
            "rungs": rungs,
            "intermediate_values": "DIGEST_COMMITMENTS_ONLY",
        },
        "residuals": {
            "R2B": {
                "terms": len(r2_polynomial.terms),
                "native_sha256": r2["sha256"],
                "polynomial": G.encode_sparse_polynomial(r2_polynomial),
            },
            "beta": {
                "terms": len(beta_polynomial.terms),
                "native_sha256": beta["sha256"],
                "polynomial": G.encode_sparse_polynomial(beta_polynomial),
                "nonzero_on_discriminant": True,
            },
        },
        "source_binding": "UNBOUND_DIGEST_COMMITMENTS_ONLY",
        "authority_boundary": (
            "exact frozen depth-6 boundary polynomials and their generic/"
            "discriminant affine rewrites only; no replay of the 33-rung "
            "source march, source-extraction edge, stratum coverage, "
            "actual-source membership, depth 7, or H3 authority"
        ),
    }


def verify_frozen(frozen):
    """Independently validate the checked-in portable boundary projection."""
    required = {
        "schema", "native_parent", "characteristic", "coefficient_domain",
        "point_universe", "ring_vars", "native_symbols", "pin", "alpha", "discriminant",
        "beta_alias", "seam", "premises", "refusals", "schedule",
        "residuals", "source_binding", "authority_boundary",
    }
    _require(isinstance(frozen, dict) and set(frozen) == required,
             "frozen depth-6 projection has unknown or missing fields")
    _require(frozen["schema"] == FROZEN_SCHEMA,
             "unexpected frozen depth-6 schema")
    _require(frozen["native_parent"].get("sha256") == EXPECTED_NATIVE_SHA256,
             "frozen projection is bound to the wrong native receipt")
    _require(frozen["characteristic"] == 0
             and frozen["coefficient_domain"] == "Q"
             and frozen["point_universe"] == S.ALGEBRAIC_CLOSURE_POINT_UNIVERSE,
             "frozen depth-6 coefficient or point scope changed")
    _require(frozen["pin"] == PIN and frozen["alpha"] == ALPHA
             and frozen["discriminant"] == DISCRIMINANT
             and frozen["beta_alias"] == BETA_ALIAS,
             "frozen boundary formulas changed")
    _require(frozen["source_binding"] == "UNBOUND_DIGEST_COMMITMENTS_ONLY",
             "digest commitments were silently promoted to source authority")
    _validate_schedule(frozen["schedule"].get("rungs"))
    _require(frozen["schedule"].get("intermediate_values") ==
             "DIGEST_COMMITMENTS_ONLY",
             "intermediate rung commitments changed grade")

    variables = frozen["ring_vars"]
    _require(variables == sorted(variables) and len(variables) == len(set(variables))
             and BETA_ALIAS in variables and "c7_5" in variables,
             "frozen boundary ring is not canonical")
    r2_record = frozen["residuals"].get("R2B") or {}
    beta_record = frozen["residuals"].get("beta") or {}
    try:
        r2 = G.parse_polynomial(r2_record.get("polynomial"), variables)
        beta = G.parse_polynomial(beta_record.get("polynomial"), variables)
    except G.CertificateError as exc:
        raise Depth6ReceiptError("frozen residual polynomial rejected: %s" % exc)
    _require(len(r2.terms) == r2_record.get("terms") == 3262,
             "frozen R2B term count changed")
    _require(len(beta.terms) == beta_record.get("terms") == 6124,
             "frozen beta term count changed")
    _require(G.encode_sparse_polynomial(r2) == r2_record["polynomial"]
             and G.encode_sparse_polynomial(beta) == beta_record["polynomial"],
             "frozen residual encoding is not canonical")
    native_symbols = frozen["native_symbols"]
    _require(isinstance(native_symbols, list)
             and set(native_symbols) == set(variables) - {BETA_ALIAS, "c7_5"},
             "frozen native residual symbol order changed")
    _require(r2_record.get("native_sha256") ==
             "f53ce7ca1a0905c80bcdd29ac3174917fcffe71dd4ecda7f4c0eca040096d2e2"
             and beta_record.get("native_sha256") ==
             "aa2463edfd44c9234969e12300d7b8d73fa0f8ed7ad0fb73e1716ab8b6fcf60d"
             and _polynomial_native_digest(r2, native_symbols) ==
             r2_record["native_sha256"]
             and _polynomial_native_digest(beta, native_symbols) ==
             beta_record["native_sha256"],
             "frozen residual lost its exact native sparse-map binding")
    witness = [0] * len(variables)
    for name in ("c2_3", "c8_7", "t"):
        witness[variables.index(name)] = 1
    _require(r2.terms.get(tuple(witness)) == Fraction(-5),
             "frozen R2B witness changed")
    _require(beta_record.get("nonzero_on_discriminant") is True
             and _alpha_stratum_nonzero(beta, variables),
             "frozen beta is not checked nonzero on the discriminant")

    context = EV.AffineContext(
        characteristic=0,
        coefficient_domain="Q",
        point_universe=S.ALGEBRAIC_CLOSURE_POINT_UNIVERSE,
        ring_vars=tuple(variables),
        generators=(
            frozen["pin"],
            "R2B@sha256:" + r2_record["native_sha256"],
            "beta@sha256:" + beta_record["native_sha256"],
            frozen["alpha"] + "*c7_5+beta",
        ),
    )
    envelope = EV.EvidenceEnvelope(
        schema=FROZEN_SCHEMA,
        context=context,
        source_bindings=(EV.SourceBinding(
            "native-jc-source-depth6", EXPECTED_NATIVE_SHA256),),
        checked_proposition=(
            "the frozen sparse maps decode canonically to R2B and beta; "
            "beta remains nonzero after the discriminant substitution"
        ),
        certificate_payload={
            "R2B_terms": len(r2.terms),
            "beta_terms": len(beta.terms),
            "rung_commitments": len(frozen["schedule"]["rungs"]),
        },
        licenses=(
            "exact_boundary_polynomials_decoded",
            "boundary_stratum_rewrites_may_be_checked",
        ),
        outstanding_premises=(
            "the receipt does not expose the 33 intermediate rung polynomials",
            "actual-source coefficient extraction remains unbound",
            "generic and discriminant graph components have no checked cover",
        ),
        graph_effect=EV.GRAPH_EFFECT_NONE,
        authority_boundary=frozen["authority_boundary"],
    ).as_dict()
    return {
        "verdict": "VERIFIED_FROZEN_DEPTH6_BOUNDARY",
        "rung_commitments": 33,
        "R2B_terms": len(r2.terms),
        "beta_terms": len(beta.terms),
        "evidence_envelope": envelope,
    }


def _model_polynomials(frozen, variables):
    budget = G._ArithmeticBudget()
    parse = lambda value: G.parse_polynomial(value, variables, 0, budget)
    r2 = parse(frozen["residuals"]["R2B"]["polynomial"])
    beta = parse(frozen["residuals"]["beta"]["polynomial"])
    alias = parse(BETA_ALIAS)
    alpha = parse(ALPHA)
    c75 = parse("c7_5")
    values = {
        "pin": parse(PIN),
        "R2B": r2,
        "beta": beta,
        "link": alias - beta,
        "alpha": alpha,
        "delta": parse(DISCRIMINANT),
        "equation": alpha * c75 + alias,
    }
    if ALPHA_INVERSE in variables:
        values["inverse_equation"] = alpha * parse(ALPHA_INVERSE) - parse("1")
    return values


def _generic_events(frozen):
    variables = list(frozen["ring_vars"]) + [ALPHA_INVERSE]
    p = _model_polynomials(frozen, variables)
    source_generators = [
        _portable(p["pin"]), _portable(p["R2B"], True),
        _portable(p["link"], True), _portable(p["equation"]),
        _portable(p["inverse_equation"]),
    ]
    target_generators = [
        _portable(p["pin"]), _portable(p["R2B"], True),
        _portable(p["link"], True), "c7_5",
        _portable(p["inverse_equation"]),
    ]
    forward = _identity_map(variables)
    inverse = _identity_map(variables)
    forward["c7_5"] = "c7_5+GP_INV_alpha*GP_BETA"
    inverse["c7_5"] = "c7_5-GP_INV_alpha*GP_BETA"
    certificate = {
        "schema": "mapped_ring_iso_v1",
        "forward_cofactors": [
            _unit_vector(5, 0), _unit_vector(5, 1), _unit_vector(5, 2),
            ["0", "0", "0", "GP_INV_alpha", "-c7_5"],
            _unit_vector(5, 4),
        ],
        "inverse_cofactors": [
            _unit_vector(5, 0), _unit_vector(5, 1), _unit_vector(5, 2),
            ["0", "0", "0", ALPHA, "-GP_BETA"],
            _unit_vector(5, 4),
        ],
    }
    common = {
        "characteristic": 0,
        "coefficient_domain": "Q",
        "point_universe": S.ALGEBRAIC_CLOSURE_POINT_UNIVERSE,
        "ring_vars": variables,
        "cite": EXPECTED_NATIVE_SHA256,
    }
    return [
        dict(common, ev="model", id=GENERIC_MODEL,
             what=("exact imported depth-6 boundary on alpha != 0, with "
                   "alpha inverse algebraized; no actual-source edge"),
             generators=source_generators),
        dict(common, ev="model", id=GENERIC_SOLVED_MODEL,
             what=("same exact generic boundary after translating the affine "
                   "coordinate c7_5 to zero"),
             generators=target_generators),
        {
            "ev": "edge", "id": GENERIC_EDGE,
            "src": GENERIC_MODEL, "dst": GENERIC_SOLVED_MODEL,
            "type": K.EQUIVALENCE, "map_kind": K.POLYNOMIAL,
            "why": (
                "alpha*GP_INV_alpha=1 makes alpha*c7_5+beta=0 "
                "equivalent to c7_5+GP_INV_alpha*beta=0"
            ),
            "forward": forward, "inverse": inverse,
            "ring_iso": True, "ring_iso_certificate": certificate,
            "cite": EXPECTED_NATIVE_SHA256,
        },
    ]


def _discriminant_events(frozen):
    variables = list(frozen["ring_vars"])
    p = _model_polynomials(frozen, variables)
    source_generators = [
        _portable(p["pin"]), _portable(p["R2B"], True),
        _portable(p["link"], True), _portable(p["delta"]),
        _portable(p["equation"]),
    ]
    target_generators = [
        _portable(p["pin"]), _portable(p["R2B"], True),
        _portable(p["link"], True), _portable(p["delta"]), BETA_ALIAS,
    ]
    factor = "5/2*t*c7_5"
    certificate = {
        "schema": "mapped_ring_iso_v1",
        "forward_cofactors": [
            _unit_vector(5, 0), _unit_vector(5, 1), _unit_vector(5, 2),
            _unit_vector(5, 3), ["0", "0", "0", "-" + factor, "1"],
        ],
        "inverse_cofactors": [
            _unit_vector(5, 0), _unit_vector(5, 1), _unit_vector(5, 2),
            _unit_vector(5, 3), ["0", "0", "0", factor, "1"],
        ],
    }
    common = {
        "characteristic": 0,
        "coefficient_domain": "Q",
        "point_universe": S.ALGEBRAIC_CLOSURE_POINT_UNIVERSE,
        "ring_vars": variables,
        "cite": EXPECTED_NATIVE_SHA256,
    }
    identity = _identity_map(variables)
    return [
        dict(common, ev="model", id=DISCRIMINANT_MODEL,
             what=("exact imported boundary with c2_3^2-4*c4_5=0; "
                   "no actual-source edge"),
             generators=source_generators),
        dict(common, ev="model", id=DISCRIMINANT_BETA_MODEL,
             what=("same exact discriminant boundary with the affine row "
                   "replaced by beta=0; c7_5 remains free"),
             generators=target_generators),
        {
            "ev": "edge", "id": DISCRIMINANT_EDGE,
            "src": DISCRIMINANT_MODEL, "dst": DISCRIMINANT_BETA_MODEL,
            "type": K.EQUIVALENCE, "map_kind": K.POLYNOMIAL,
            "why": (
                "on c2_3^2-4*c4_5=0 the coefficient alpha vanishes "
                "exactly, so alpha*c7_5+beta=0 is beta=0"
            ),
            "forward": identity, "inverse": dict(identity),
            "ring_iso": True, "ring_iso_certificate": certificate,
            "cite": EXPECTED_NATIVE_SHA256,
        },
    ]


def graph_events(frozen):
    verify_frozen(frozen)
    variables = list(frozen["ring_vars"])
    p = _model_polynomials(frozen, variables)
    boundary = {
        "ev": "model", "id": BOUNDARY_MODEL,
        "what": (
            "exact affine ideal decoded from the frozen residual maps; the "
            "native receipt reports it as a necessary actual-source boundary, "
            "but GP has not checked that source-extraction transition"
        ),
        "characteristic": 0,
        "coefficient_domain": "Q",
        "point_universe": S.ALGEBRAIC_CLOSURE_POINT_UNIVERSE,
        "ring_vars": variables,
        "generators": [
            _portable(p["pin"]), _portable(p["R2B"], True),
            _portable(p["link"], True), _portable(p["equation"]),
        ],
        "cite": EXPECTED_NATIVE_SHA256,
    }
    note = {
        "ev": "note", "id": SOURCE_DEBT_NOTE,
        "kind": "OPEN_OBLIGATION", "domain": "actual-source",
        "source": EXPECTED_NATIVE_SHA256,
        "text": (
            "The frozen receipt exposes full R2B and beta maps but only "
            "SHA-256 commitments for the 33 intermediate solve values. No "
            "graph edge from the actual-source E-system is licensed until "
            "those polynomials or an independently checkable derivation are "
            "available. The generic/discriminant components also carry no "
            "checked parent-cover inference."
        ),
    }
    return [boundary] + _generic_events(frozen) + _discriminant_events(frozen) + [note]


def graph_from_frozen(frozen):
    graph = S.Graph()
    graph.apply(F.meta_event())
    for event in graph_events(frozen):
        graph.apply(event)
    graph.validate()
    return graph


def write_campaign(root, frozen, record=False):
    graph_path = Path(S.graph_path(str(root)))
    if graph_path.exists():
        raise ValueError("campaign graph already exists: %s" % graph_path)
    S.append(graph_events(frozen), root=str(root))
    results = V.verify_all(root=str(root)) if record else []
    graph = S.load(S.graph_path(str(root)))
    findings = C.run(graph)
    if record:
        for edge_id in (GENERIC_EDGE, DISCRIMINANT_EDGE):
            if graph.edges[edge_id].get("ring_iso_verdict") != V.ISO_VERIFIED:
                raise AssertionError("%s did not earn exact equivalence" % edge_id)
    return {
        "graph": str(graph_path),
        "generic_verdict": graph.edges[GENERIC_EDGE].get("ring_iso_verdict"),
        "discriminant_verdict": graph.edges[DISCRIMINANT_EDGE].get(
            "ring_iso_verdict"),
        "findings": [finding.as_dict() for finding in findings],
        "verify_results": [list(item[:3]) for item in results],
    }


def main(argv=None):
    parser = argparse.ArgumentParser()
    parser.add_argument("--source", type=Path, default=DEFAULT_SOURCE)
    parser.add_argument("--frozen", type=Path, default=DEFAULT_FROZEN)
    parser.add_argument("--write-fixture", action="store_true")
    parser.add_argument("--campaign-root", type=Path)
    parser.add_argument("--record", action="store_true")
    args = parser.parse_args(argv)
    if args.record and args.campaign_root is None:
        parser.error("--record requires --campaign-root")

    source_bytes = args.source.read_bytes()
    native = json.loads(source_bytes.decode("utf-8"))
    frozen = freeze_native(native, source_bytes)
    frozen_bytes = _encoded(frozen)
    if args.write_fixture:
        args.frozen.parent.mkdir(parents=True, exist_ok=True)
        args.frozen.write_bytes(frozen_bytes)
    elif args.frozen.read_bytes() != frozen_bytes:
        raise SystemExit("checked-in depth-6 fixture differs from native adapter output")
    checked = verify_frozen(frozen)
    output = {
        "verdict": checked["verdict"],
        "native_parent_sha256": EXPECTED_NATIVE_SHA256,
        "frozen_sha256": _sha256(frozen_bytes),
        "rung_commitments": checked["rung_commitments"],
        "R2B_terms": checked["R2B_terms"],
        "beta_terms": checked["beta_terms"],
        "authority_boundary": frozen["authority_boundary"],
        "evidence_envelope": checked["evidence_envelope"],
    }
    if args.campaign_root is not None:
        output["campaign"] = write_campaign(
            args.campaign_root, frozen, args.record)
    print(json.dumps(output, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
