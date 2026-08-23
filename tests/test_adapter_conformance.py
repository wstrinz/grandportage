from types import SimpleNamespace

import pytest

from grandportage import adapter_conformance as conformance


def _adapter(**changes):
    envelope = {
        "schema": "neutral_assay_v1",
        "context": {"characteristic": 0, "coefficient_domain": "Q",
                    "point_universe": "ALGEBRAIC_CLOSURE",
                    "ring_vars": ["x"], "unit_generators": [],
                    "generators": ["x"]},
        "source_bindings": [
            {"id": "fixture", "sha256": "sha256:" + "1" * 64}],
        "checked_proposition": "x belongs to (x)",
        "certificate_payload": {"cofactors": ["1"]},
        "licenses": ["identity_at_declared_model"],
        "outstanding_premises": [],
        "graph_effect": "NONE",
        "authority_boundary": "standalone only",
    }
    adapter = SimpleNamespace(
        GRAPH_EFFECT="NONE",
        MUTATION_CONTROLS=("source_digest", "cofactor_sign"),
        build_envelope=lambda: envelope,
        replay=lambda value: {"verified": value == envelope},
    )
    for name, value in changes.items():
        setattr(adapter, name, value)
    return adapter


def test_conforming_adapter_remains_descriptive_only():
    report = conformance.check_adapter(_adapter())
    assert report["status"] == "CONFORMING"
    assert report["authority"] == "DESCRIPTIVE_ONLY"
    assert report["graph_effect"] == "NONE"


@pytest.mark.parametrize("changes,match", [
    ({"MUTATION_CONTROLS": ()}, "MUTATION_CONTROLS"),
    ({"GRAPH_EFFECT": "LOCAL_EMPTY"}, "graph effects disagree"),
    ({"replay": lambda _value: {"verified": False}}, "did not verify"),
])
def test_adapter_contract_fails_closed(changes, match):
    with pytest.raises(conformance.AdapterConformanceError, match=match):
        conformance.check_adapter(_adapter(**changes))
