"""Hash-bound regressions from the ARR15 post-focus-group packet."""

import json
from pathlib import Path

from grandportage import format as F
from grandportage import groebner as G
from grandportage import kernel as K
from grandportage import store as S
from grandportage import verify as V


FIXTURES = Path(__file__).parent / "fixtures" / "arr15"


def _load(name):
    return json.loads((FIXTURES / name).read_text(encoding="utf-8"))


def _graph(model, claim):
    graph = S.Graph()
    graph.apply(F.meta_event())
    graph.apply(model)
    graph.apply(claim)
    return graph


class _ExactSubstitutionBackend(object):
    def evaluate_point(self, ring, expressions, point, characteristic=0,
                       **_kw):
        rows = []
        for expression in expressions:
            value = G.substitute_polynomial(
                expression, ring, point, characteristic)
            vanishes = G.parse_polynomial(
                value, ring, characteristic).is_zero
            rows.append({"generator": expression, "value": value,
                         "vanishes": vanishes})
        return all(row["vanishes"] for row in rows), {
            "point": dict(point), "generators": rows,
            "failed": [row["generator"] for row in rows
                       if not row["vanishes"]],
        }


def test_arr15_12909_equation_free_open_witness_is_checked_exactly():
    fixture = _load("class_12909_open_witness.json")
    assert fixture["source"]["arr15_commit"] == (
        "2fe83ac60c789da0bd2677d0d927e5decbd42b8e")
    assert fixture["generators"] == []
    assert len(fixture["open_conditions"]) == 108
    graph = _graph({
        "ev": "model", "id": "M", "desc": "ARR15 class 12909 open chart",
        "characteristic": 0,
        "ring_vars": fixture["ring_vars"],
        "generators": fixture["generators"],
        "open_conditions": fixture["open_conditions"],
    }, {
        "ev": "claim", "id": "C", "model": "M", "kind": K.NONEMPTY,
        "statement": "the copied ARR15 open chart has its exhibited point",
        "witness_kind": K.EXHIBITED, "witness": "ARR15 exact point",
        "witness_point": fixture["witness"],
        "established_by": "RAN", "ladder": "exact-checked",
    })
    verdict, why = V.point_witness(
        graph, "C", _backend=_ExactSubstitutionBackend())
    assert verdict == V.WITNESS_VERIFIED
    assert "0 equations" in why and "108 open guards" in why


class _MissMembershipBackend(object):
    def membership(self, *_args, **_kwargs):
        return {"is_member": False, "cofactors": []}


def test_arr15_full_4102_localization_is_bounded_and_never_raises():
    fixture = _load("class_4102.json")
    assert len(fixture["generators"]) == 42
    assert len(fixture["open_conditions"]) == 291
    graph = _graph({
        "ev": "model", "id": "M", "desc": "ARR15 class 4102 exact chart",
        "characteristic": 0,
        "ring_vars": fixture["ring_vars"],
        "generators": fixture["generators"],
        "open_conditions": fixture["open_conditions"],
    }, {
        "ev": "claim", "id": "C", "model": "M", "kind": K.EMPTY,
        "statement": "the copied ARR15 open chart is empty",
        "certificate": "LOCALIZED_UNIT_IDEAL_CERT",
        "established_by": "RAN", "ladder": "exact-checked",
    })
    verdict, why, representation = V.localized_unit_ideal(
        graph, "C", _backend=_MissMembershipBackend())
    assert verdict == V.UNVERIFIED
    assert representation is None
    assert "search exhaustion" in why
