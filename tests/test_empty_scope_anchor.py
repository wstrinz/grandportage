"""A field-relative EMPTY claim must quantify over typed field-valued points.

CFG23 registered a combinatorial/orientability certificate, attached it to a
bare role-coloured incidence model, and then put ``scope: R`` on an EMPTY
claim whose statement said "no straight-line realization over the reals".
The point-universe guard correctly refused REAL_CLOSURE on that bare model;
omitting the model fields entirely bypassed the guard.  ``gp check`` then had
no finding and ``gp verify`` had nothing it could run.

The repair is deliberately smaller than a certificate ontology.  Native logs
must anchor a field-relative emptiness to both a coefficient domain and a point
universe.  Combinatorial emptiness remains legal at a combinatorial model.
Historical epoch-0 logs remain readable, but the checker reports the missing
anchor so migration and baselining cannot silently turn it into authority.
"""

import pytest

from grandportage import format as F
from grandportage import check as C
from grandportage import kernel as K

import helpers as H


def _certificate(base_changes=False):
    return {
        "ev": "certificate",
        "id": "CERT_COMBINATORIAL",
        "base_changes": base_changes,
        "why": "a finite combinatorial contradiction, not a field model",
    }


def _claim(scope=None):
    out = {
        "ev": "claim",
        "id": "CL",
        "model": "M",
        "kind": K.EMPTY,
        "statement": "no straight-line realization over the reals",
        "certificate": "CERT_COMBINATORIAL",
    }
    if scope is not None:
        out["scope"] = scope
    return out


def _scope_findings(graph):
    return [f for f in C.run(graph) if f.rule == C.R_EMPTY_SCOPE]


@pytest.mark.parametrize("scope", ["Q", "R", "C", "F_19", "Q(i)"])
def test_native_field_empty_cannot_sit_at_a_bare_combinatorial_model(scope):
    events = [
        {"ev": "model", "id": "M", "desc": "bare incidence graph"},
        _certificate(base_changes=False),
        _claim(scope),
    ]
    graph = H.fold([F.meta_event()] + events)
    findings = _scope_findings(graph)
    assert [(f.subject, f.severity) for f in findings] == [
        ("CL", C.UNSOUND_PREMISE)]
    assert "bare combinatorial model" in findings[0].detail


def test_coefficient_domain_without_point_universe_is_not_an_anchor():
    events = [
        {"ev": "model", "id": "M", "desc": "Q equations, point functor unknown",
         "characteristic": 0, "coefficient_domain": "Q"},
        _certificate(base_changes=False),
        _claim("Q"),
    ]
    graph = H.fold([F.meta_event()] + events)
    assert len(_scope_findings(graph)) == 1


def test_typed_base_field_model_accepts_field_relative_empty():
    events = [
        {"ev": "model", "id": "M", "desc": "Q-valued point model",
         "characteristic": 0, "coefficient_domain": "Q",
         "point_universe": "BASE"},
        _certificate(base_changes=False),
        _claim("Q"),
    ]
    graph = H.fold([F.meta_event()] + events)
    assert graph.claims["CL"]["scope"] == "Q"
    assert _scope_findings(graph) == []


def test_combinatorial_empty_at_bare_model_remains_legal():
    events = [
        {"ev": "model", "id": "M", "desc": "orientation feasibility"},
        _certificate(base_changes=True),
        _claim(),
    ]
    graph = H.fold([F.meta_event()] + events)
    assert graph.claims["CL"]["scope"] == K.SCHEME
    assert _scope_findings(graph) == []


def test_epoch0_fieldless_model_remains_readable_for_compatibility():
    events = [
        {"ev": "model", "id": "M", "desc": "legacy prose says over Q"},
        _certificate(base_changes=False),
        _claim("Q"),
    ]
    graph = H.fold(events)
    assert graph.graph_format == 0
    assert graph.claims["CL"]["scope"] == "Q"
    assert len(_scope_findings(graph)) == 1
