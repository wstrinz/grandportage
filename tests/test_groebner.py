import copy
import subprocess

import pytest

from grandportage import cas
from grandportage import check as C
from grandportage import groebner as G
from grandportage import kernel as K
from grandportage import store as S
from grandportage import verify as V


def _certificate():
    """A complete lex certificate for (yx-1, y²-x) ∩ Q[x]."""
    return {
        "method": "groebner_elimination_v1",
        "characteristic": 0,
        "ring_vars": ["y", "x"],
        "eliminated": ["y"],
        "source_generators": ["y*x-1", "y^2-x"],
        "basis": ["x^3-1", "y-x^2"],
        "target_generators": ["x^3-1"],
        "source_in_basis": [
            ["1", "x"],
            ["x", "y+x^2"],
        ],
        "critical_pairs": [
            {"i": 0, "j": 1, "reducers": ["x^2", "-1"]},
        ],
        "retained_in_target": [["1"]],
    }


def test_exact_checker_accepts_a_complete_elimination_certificate():
    checked = G.check_elimination_certificate(_certificate())

    assert checked["critical_pair_count"] == 1
    assert checked["retained_basis"] == ["x^3-1"]
    assert checked["retained_ring_vars"] == ["x"]


def test_cusp_normalization_certificate_needs_no_polynomial_section():
    """Q[u,y,x] -> Q[y,x] is exact although u has no polynomial section."""
    certificate = {
        "method": "groebner_elimination_v1",
        "characteristic": 0,
        "ring_vars": ["u", "y", "x"],
        "eliminated": ["u"],
        "source_generators": ["u^2-x", "u^3-y"],
        "basis": ["y^2-x^3", "u*x-y", "u*y-x^2", "u^2-x"],
        "target_generators": ["2*y^2-2*x^3"],
        "source_in_basis": [
            ["0", "0", "0", "1"],
            ["0", "1", "0", "u"],
        ],
        "critical_pairs": [
            {"i": 0, "j": 1, "reducers": ["y", "-x^3", "0", "0"]},
            {"i": 0, "j": 2, "reducers": ["0", "-x^2", "0", "0"]},
            {"i": 0, "j": 3,
             "reducers": ["0", "-u*x^2-y*x", "0", "0"]},
            {"i": 1, "j": 2, "reducers": ["-1", "0", "0", "0"]},
            {"i": 1, "j": 3, "reducers": ["0", "0", "-1", "0"]},
            {"i": 2, "j": 3, "reducers": ["0", "-x", "0", "0"]},
        ],
        "retained_in_target": [["1/2"]],
    }

    checked = G.check_elimination_certificate(certificate)

    assert checked["critical_pair_count"] == 6
    assert checked["retained_basis"] == ["y^2-x^3"]
@pytest.mark.parametrize("mutate, match", [
    (lambda c: c["source_in_basis"][0].__setitem__(0, "0"),
     "source_in_basis"),
    (lambda c: c["critical_pairs"][0]["reducers"].__setitem__(0, "0"),
     "S-polynomial"),
    (lambda c: c["critical_pairs"][0].__setitem__(
        "reducers", ["y", "-x^3"]),
     "not below"),
    (lambda c: c["retained_in_target"][0].__setitem__(0, "x"),
     "retained_in_target"),
])
def test_exact_checker_rejects_false_finite_evidence(mutate, match):
    certificate = _certificate()
    mutate(certificate)

    with pytest.raises(G.CertificateError, match=match):
        G.check_elimination_certificate(certificate)


def test_pair_coverage_is_recomputed_not_trusted():
    certificate = _certificate()
    certificate["basis"].append("x+1")
    certificate["source_in_basis"] = [
        row + ["0"] for row in certificate["source_in_basis"]
    ]
    certificate["retained_in_target"].append(["1"])

    with pytest.raises(G.CertificateError, match="cover all 3"):
        G.check_elimination_certificate(certificate)


def test_elimination_order_is_derived_and_eliminated_block_must_lead():
    certificate = _certificate()
    certificate["ring_vars"] = ["x", "y"]

    with pytest.raises(G.CertificateError, match="eliminated variables first"):
        G.check_elimination_certificate(certificate)


def test_retained_cofactors_cannot_smuggle_an_eliminated_variable():
    certificate = _certificate()
    certificate["target_generators"] = ["y*(x^3-1)"]
    certificate["retained_in_target"] = [["1/y"]]

    with pytest.raises(G.CertificateError):
        G.check_elimination_certificate(certificate)


def test_target_generators_must_live_in_the_retained_ring():
    certificate = _certificate()
    certificate["target_generators"] = ["y*(x^3-1)"]
    certificate["retained_in_target"] = [["0"]]

    with pytest.raises(G.CertificateError, match="retained-coordinate ring"):
        G.check_elimination_certificate(certificate)
@pytest.mark.parametrize("characteristic", [False, 1, 4, 9])
def test_coefficient_domain_must_be_q_or_a_prime_field(characteristic):
    certificate = _certificate()
    certificate["characteristic"] = characteristic

    with pytest.raises(G.CertificateError, match="characteristic"):
        G.check_elimination_certificate(certificate)


def test_characteristic_size_is_bounded_before_primality_search():
    certificate = _certificate()
    certificate["characteristic"] = 2**127 - 1

    with pytest.raises(G.CertificateError, match="characteristic"):
        G.check_elimination_certificate(certificate)
@pytest.mark.parametrize("characteristic", [{}, [], set()])
def test_unhashable_characteristic_is_a_conservative_rejection(characteristic):
    with pytest.raises(G.CertificateError, match="characteristic"):
        G.parse_polynomial("x", ["x"], characteristic)


def test_exact_polynomial_substitution_is_simultaneous_and_oriented():
    assert G.substitute_polynomial(
        "x-y", ["x", "y"], {"x": "y", "y": "x"}) == "-x+y"
    assert G.substitute_polynomial(
        "x+3", ["x"], {"x": "x-2"}) == "x+1"
    assert G.substitute_polynomial(
        "x+3", ["x"], {"x": "x-1"}) == "x+2"


def test_polynomial_operations_share_one_global_work_budget():
    budget = G._ArithmeticBudget(10)

    with pytest.raises(G.CertificateError, match="global arithmetic-work"):
        G.parse_polynomial("(x+x)*(x+x)+(x+x)*(x+x)", ["x"], _budget=budget)
def test_prime_field_arithmetic_and_division_are_exact():
    left = G.parse_polynomial("1/2*x + 4*x", ["x"], characteristic=3)
    right = G.parse_polynomial("0", ["x"], characteristic=3)
    assert left == right

    with pytest.raises(G.CertificateError, match="nonzero scalar"):
        G.parse_polynomial("x/3", ["x"], characteristic=3)


def test_unicode_identifier_normalization_cannot_alias_ring_variables():
    certificate = {
        "method": "groebner_elimination_v1",
        "characteristic": 0,
        "ring_vars": ["y", "K", "K"],
        "eliminated": ["y"],
        "source_generators": ["K"],
        "basis": ["K"],
        "target_generators": ["K"],
        "source_in_basis": [["1"]],
        "critical_pairs": [],
        "retained_in_target": [["1"]],
    }

    with pytest.raises(G.CertificateError, match="ASCII CAS identifiers"):
        G.check_elimination_certificate(certificate)
@pytest.mark.parametrize("bad", [[{}], [[]]])
def test_malformed_eliminated_entries_are_conservative_rejections(bad):
    certificate = _certificate()
    certificate["eliminated"] = bad

    with pytest.raises(G.CertificateError, match="eliminated"):
        G.check_elimination_certificate(certificate)


def test_deep_expression_is_a_conservative_resource_rejection():
    expression = "+".join(["x"] * 1000)

    with pytest.raises(G.CertificateError, match="resource budget"):
        G.parse_polynomial(expression, ["x"])
def test_preflight_counts_object_keys_before_snapshot(monkeypatch):
    monkeypatch.setattr(G, "_MAX_CERTIFICATE_CHARACTERS", 10)

    with pytest.raises(G.CertificateError, match="text-size budget"):
        G.preflight_certificate({"an-oversized-unknown-key": 0})


def test_preflight_rejects_non_json_container_shapes():
    with pytest.raises(G.CertificateError, match="JSON-shaped"):
        G.preflight_certificate({"basis": ("x",)})
def test_certificate_schema_is_closed():
    certificate = copy.deepcopy(_certificate())
    certificate["monomial_order"] = "dp"

    with pytest.raises(G.CertificateError, match="unknown"):
        G.check_elimination_certificate(certificate)


def _cusp_graph():
    return S.Graph().apply_all([
        ({"ev": "model", "id": "SOURCE", "what": "cusp normalization",
          "characteristic": 0, "ring_vars": ["u", "y", "x"],
          "generators": ["u^2-x", "u^3-y"]}, "test", 0),
        ({"ev": "model", "id": "TARGET", "what": "cusp equation",
          "characteristic": 0, "ring_vars": ["y", "x"],
          "generators": ["2*y^2-2*x^3"], "eliminated": ["u"]},
         "test", 1),
        ({"ev": "edge", "id": "E", "src": "SOURCE", "dst": "TARGET",
          "type": K.IMAGE_CLOSURE, "map_kind": K.POLYNOMIAL,
          "why": "eliminate the normalization parameter",
          "built_by_operation": "Eliminate"}, "test", 2),
    ]).validate()


def _cusp_certificate():
    return {
        "method": "groebner_elimination_v1",
        "characteristic": 0,
        "ring_vars": ["u", "y", "x"],
        "eliminated": ["u"],
        "source_generators": ["u^2-x", "u^3-y"],
        "basis": ["y^2-x^3", "u*x-y", "u*y-x^2", "u^2-x"],
        "target_generators": ["2*y^2-2*x^3"],
        "source_in_basis": [
            ["0", "0", "0", "1"],
            ["0", "1", "0", "u"],
        ],
        "critical_pairs": [
            {"i": 0, "j": 1, "reducers": ["y", "-x^3", "0", "0"]},
            {"i": 0, "j": 2, "reducers": ["0", "-x^2", "0", "0"]},
            {"i": 0, "j": 3,
             "reducers": ["0", "-u*x^2-y*x", "0", "0"]},
            {"i": 1, "j": 2, "reducers": ["-1", "0", "0", "0"]},
            {"i": 1, "j": 3, "reducers": ["0", "0", "-1", "0"]},
            {"i": 2, "j": 3, "reducers": ["0", "-x", "0", "0"]},
        ],
        "retained_in_target": [["1/2"]],
    }


def test_graph_checker_binds_a_valid_proof_to_the_exact_elimination_edge():
    verdict, why, representation = V.elimination_groebner(
        _cusp_graph(), "E", _cusp_certificate()
    )

    assert verdict == V.GROEBNER_VERIFIED, why
    assert representation["edge"] == "E"
    assert representation["checked"]["critical_pair_count"] == 6
    assert "still requires" in why
    assert "geometric point-image closure" in why


def test_graph_checker_rejects_replay_after_ordered_inputs_change():
    certificate = _cusp_certificate()
    certificate["source_generators"].reverse()

    verdict, why, representation = V.elimination_groebner(
        _cusp_graph(), "E", certificate
    )

    assert verdict == V.GROEBNER_REJECTED
    assert "exact ordered graph inputs" in why
    assert representation is None


def test_completeness_check_alone_mints_no_exact_or_geometric_authority():
    graph = _cusp_graph()
    verdict, why, _representation = V.elimination_groebner(
        graph, "E", _cusp_certificate()
    )
    assert verdict == V.GROEBNER_VERIFIED, why

    assert not C.effective_exact_contraction(graph.edges["E"])
    assert not C.effective_geometric_closure(graph.edges["E"])

def test_graph_checker_rejects_an_unsupported_or_changed_coefficient_field():
    graph = _cusp_graph()
    graph.models["SOURCE"]["field"] = "Q"
    graph.models["TARGET"]["field"] = "R"

    verdict, why, representation = V.elimination_groebner(
        graph, "E", _cusp_certificate()
    )

    assert verdict == V.UNVERIFIED
    assert "proves polynomial identities only over Q" in why
    assert representation is None


def test_verified_representation_is_a_snapshot_not_a_caller_owned_alias():
    certificate = _cusp_certificate()
    verdict, why, representation = V.elimination_groebner(
        _cusp_graph(), "E", certificate
    )
    assert verdict == V.GROEBNER_VERIFIED, why

    certificate["basis"][0] = "0"
    assert representation["proof"]["basis"][0] == "y^2-x^3"

@pytest.mark.live
def test_real_singular_produces_the_no_section_cusp_basis():
    """Live producer crosscheck; authority still comes from the pure checker."""
    script = """\
ring r=0,(u,y,x),lp;
short=0;
ideal F=u^2-x,u^3-y;
matrix A;
ideal G=liftstd(F,A);
matrix B=lift(G,F);
G;
B;
quit;
"""
    completed = subprocess.run(
        cas._argv(), input=script, text=True, capture_output=True, timeout=120
    )
    transcript = (completed.stdout + completed.stderr).replace(" ", "")

    assert completed.returncode == 0, transcript
    assert "?error" not in transcript
    for polynomial in (
            "y^2-x^3", "u*x-y", "u*y-x^2", "u^2-x"):
        assert polynomial in transcript
    assert "B[4,1]=1" in transcript
    assert "B[2,2]=1" in transcript
    assert "B[4,2]=u" in transcript

    checked = G.check_elimination_certificate(_cusp_certificate())
    assert checked["critical_pair_count"] == 6


def _sparse_polynomial():
    return {
        "schema": G.SPARSE_POLYNOMIAL_SCHEMA,
        "terms": [
            {"coefficient": "2", "powers": [["x", 2]]},
            {"coefficient": "-3/5", "powers": [["y", 1]]},
            {"coefficient": "7", "powers": []},
        ],
    }


def test_sparse_polynomial_round_trip_is_exact_and_canonical():
    sparse = _sparse_polynomial()
    parsed = G.parse_polynomial(sparse, ["x", "y"])

    assert G.encode_sparse_polynomial(parsed) == sparse
    assert parsed == G.parse_polynomial("2*x^2-3/5*y+7", ["x", "y"])
    assert G.substitute_polynomial(
        sparse, ["x", "y"], {"x": "x", "y": "y"}
    ) == "(2)*x^2+(-3/5)*y+7"
    assert G.canonical_polynomial_value(sparse, ["x", "y"]) == sparse

def test_sparse_substitution_skips_coordinates_absent_from_support():
    sparse = _sparse_polynomial()

    assert G.substitute_polynomial(
        sparse,
        ["x", "y", "z"],
        {"x": "x", "y": "y", "z": "z+1"},
        _budget=G._ArithmeticBudget(10),
        _preserve_sparse=True,
    ) == sparse


@pytest.mark.parametrize("mutate, message", [
    (lambda value: value.update({"extra": True}), "exactly schema and terms"),
    (lambda value: value["terms"].__setitem__(
        0, {"coefficient": "2/1", "powers": [["x", 2]]}),
     "nonzero canonical"),
    (lambda value: value["terms"].__setitem__(
        0, {"coefficient": "0", "powers": [["x", 2]]}),
     "nonzero canonical"),
    (lambda value: value["terms"][0].update({
        "powers": [["y", 1], ["x", 2]]}), "ring-variable order"),
    (lambda value: value["terms"].reverse(), "descending lexicographic"),
    (lambda value: value["terms"][0].update({
        "powers": [["z", 1]]}), "unknown variable"),
])
def test_sparse_polynomial_surface_is_closed_bounded_and_unique(
        mutate, message):
    sparse = _sparse_polynomial()
    mutate(sparse)

    with pytest.raises(G.CertificateError, match=message):
        G.parse_polynomial(sparse, ["x", "y"])


def test_sparse_encoding_bypasses_no_algebraic_resource_budget(monkeypatch):
    sparse = {
        "schema": G.SPARSE_POLYNOMIAL_SCHEMA,
        "terms": [
            {"coefficient": "1", "powers": [["x", exponent]]}
            for exponent in range(40, 0, -1)
        ],
    }
    monkeypatch.setattr(G, "_MAX_TERMS", 39)

    with pytest.raises(G.CertificateError, match="at most 39"):
        G.parse_polynomial(sparse, ["x"])


def test_sparse_prime_field_coefficients_are_canonical_residues():
    sparse = {"schema": G.SPARSE_POLYNOMIAL_SCHEMA, "terms": [
        {"coefficient": "2", "powers": [["x", 1]]},
    ]}
    assert G.parse_polynomial(sparse, ["x"], 3) == G.parse_polynomial(
        "-x", ["x"], 3
    )
    sparse["terms"][0]["coefficient"] = "-1"
    with pytest.raises(G.CertificateError, match="invalid"):
        G.parse_polynomial(sparse, ["x"], 3)
