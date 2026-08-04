"""Checked affine coordinate normalization for product-split branches."""

import json
from pathlib import Path

import pytest

from grandportage import cli
from grandportage import contracts as OC
from grandportage import groebner as G
from grandportage import kernel as K
from grandportage import operations as O
from grandportage import store as S
from grandportage import verify as V


RING = ["p", "c6", "c8", "z"]
GENERATORS = ["p*c6+c8", "z+c8"]


def _operation(**overrides):
    args = {
        "src": "LEFT",
        "solved": "c8",
        "solution": "-p*c6",
        "produces": "LEFT-NORMAL",
        "ring_vars": RING,
        "generators": GENERATORS,
        "open_conditions": ["p"],
        "coefficient_domain": "Q",
        "point_universe": S.ALGEBRAIC_CLOSURE_POINT_UNIVERSE,
    }
    args.update(overrides)
    return O.affine_coordinate_solve(**args)


def _graph():
    parent = {
        "ev": "model", "id": "LEFT", "what": "left product branch",
        "characteristic": 0, "ring_vars": RING,
        "generators": GENERATORS, "open_conditions": ["p"],
        "coefficient_domain": "Q",
        "point_universe": S.ALGEBRAIC_CLOSURE_POINT_UNIVERSE,
    }
    return S.Graph().apply_all([
        (event, "affine-coordinate", index)
        for index, event in enumerate([parent] + _operation().events)
    ]).validate()


def _init_campaign(root):
    assert cli.main(["--root", str(root), "init"]) == 0
    S.append([{
        "ev": "model", "id": "LEFT", "what": "left product branch",
        "characteristic": 0, "ring_vars": RING,
        "generators": GENERATORS, "open_conditions": ["p"],
        "coefficient_domain": "Q",
        "point_universe": S.ALGEBRAIC_CLOSURE_POINT_UNIVERSE,
    }], str(root))


def test_affine_solve_contract_is_a_verified_mapped_equivalence():
    contract = OC.AFFINE_COORDINATE_SOLVE

    assert contract.edge_type == K.EQUIVALENCE
    assert contract.built_endpoint == "dst"
    assert contract.source_endpoint == "src"
    assert contract.point_transport.total
    assert contract.point_transport.point_surjective
    assert {item.name for item in contract.checked_obligations} == {
        "literal_affine_definition",
        "simultaneous_generator_rewrite",
        "coordinate_ring_isomorphism",
    }
    assert O.DERIVES["AffineCoordinateSolve"] == contract.derivation
    assert OC.CONTRACTS["AffineCoordinateSolve"] is contract


def test_jc_left_branch_normalizes_the_pivot_by_exact_translation():
    op = _operation()
    model, edge = op.events

    assert op.contract is OC.AFFINE_COORDINATE_SOLVE
    assert model["generators"] == ["c8", "-p*c6+c8+z"]
    assert model["open_conditions"] == ["p"]
    assert edge["src"] == "LEFT" and edge["dst"] == "LEFT-NORMAL"
    assert edge["type"] == K.EQUIVALENCE
    assert edge["ring_iso"] is True
    assert edge["forward"]["c8"] == "p*c6+c8"
    assert edge["inverse"]["c8"] == "-p*c6+c8"
    assert all(edge["forward"][name] == name
               for name in ("p", "c6", "z"))


def test_open_conditions_are_rewritten_into_target_coordinates():
    op = _operation(open_conditions=["c8+1"])
    model = op.events[0]

    assert model["open_conditions"] == ["-p*c6+c8+1"]


def test_affine_solve_events_form_a_valid_graph_but_need_verification():
    graph = _graph()
    edge = graph.edges["E-LEFT-NORMAL"]

    assert edge["ring_iso"] is True
    assert edge.get("ring_iso_verdict") is None


def test_ring_iso_verifier_consumes_the_constructed_maps():
    graph = _graph()

    class Backend:
        def __init__(self):
            self.ideal_checks = 0

        def pullback_reduce(self, ring, expression, substitution, generators,
                            characteristic, timeout):
            result = G.substitute_polynomial(
                expression, ring, substitution, characteristic)
            if generators:
                self.ideal_checks += 1
                return "0", True
            return result, result == "0"

    backend = Backend()
    verdict, why = V.ring_iso(
        graph, "E-LEFT-NORMAL", _backend=backend)

    assert verdict == V.ISO_VERIFIED, why
    assert backend.ideal_checks == len(GENERATORS) * 2


@pytest.mark.live
def test_jc_affine_coordinate_change_verifies_against_real_backend():
    verdict, why = V.ring_iso(_graph(), "E-LEFT-NORMAL", timeout=120)
    assert verdict == V.ISO_VERIFIED, why


@pytest.mark.parametrize("overrides,message", [
    ({"solved": "missing"}, "declared ring variable"),
    ({"solution": "c8+p"}, "independent of the pivot"),
    ({"solution": "p*c6"}, "literal source generator"),
])
def test_affine_solve_refuses_untyped_or_unbound_pivots(overrides, message):
    with pytest.raises(ValueError, match=message):
        _operation(**overrides)


def test_affine_rewrite_is_simultaneous_not_textual():
    op = _operation(
        solution="z", generators=["c8-z", "c8+z"],
        open_conditions=[])

    assert op.events[0]["generators"] == ["c8", "c8+(2)*z"]


def test_cli_construct_affine_solve_dry_run_and_declare(tmp_path, capsys):
    _init_campaign(tmp_path)
    capsys.readouterr()
    command = [
        "--root", str(tmp_path), "construct", "affine-solve",
        "--src", "LEFT", "--solve", "c8", "--value=-p*c6",
        "--produces", "LEFT-NORMAL",
    ]

    assert cli.main(command) == 0
    events = json.loads(capsys.readouterr().out)
    assert [event["ev"] for event in events] == ["model", "edge"]
    assert "LEFT-NORMAL" not in S.load(S.graph_path(str(tmp_path))).models

    assert cli.main(command + ["--declare"]) == 0
    assert "declared 2 event(s)" in capsys.readouterr().out
    graph = S.load(S.graph_path(str(tmp_path))).validate()
    assert "LEFT-NORMAL" in graph.models
    assert graph.edges["E-LEFT-NORMAL"]["ring_iso"] is True


def test_cli_affine_solve_requires_its_specific_inputs(tmp_path, capsys):
    _init_campaign(tmp_path)
    capsys.readouterr()

    rc = cli.main([
        "--root", str(tmp_path), "construct", "affine-solve",
        "--src", "LEFT", "--produces", "N",
    ])

    assert rc == 2
    assert "requires --solve and --value" in capsys.readouterr().err


def test_checked_product_branch_feeds_affine_normalization_directly():
    fixture = (Path(__file__).parents[1] / "fixtures" / "jc_p_axis" /
               "product_split_v1.json")
    spec = json.loads(fixture.read_text(encoding="utf-8"))
    receipt = spec["receipts"][0]
    split = O.product_split(
        "P_BOTTOM", spec["ring_vars"], [receipt["equation"]], spec,
        "E_2_0_bottom_split")
    left = next(event for event in split.events if event["ev"] == "model")

    normalized = O.affine_coordinate_solve(
        left["id"], "c8_0", "-p*c6_0", "P_BOTTOM-LEFT-NORMAL",
        left["ring_vars"], left["generators"])

    target = normalized.events[0]
    assert target["generators"][-1] == "c8_0"
    assert normalized.events[1]["forward"]["c8_0"] == "p*c6_0+c8_0"
