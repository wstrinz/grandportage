"""Full finite reduced E-system model and selected-face graph assay."""

import copy
import importlib.util
from pathlib import Path

import pytest


pytestmark = pytest.mark.exhaustive

from grandportage import provenance as P
from grandportage import verify as V
from grandportage import cli


ROOT = Path(__file__).parents[1]
ADAPTER_PATH = (
    ROOT / "experiments" / "jc_h3_source_depth6" /
    "full_template_campaign.py"
)
_spec = importlib.util.spec_from_file_location(
    "jc_source_depth6_full_template_campaign", ADAPTER_PATH)
ADAPTER = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(ADAPTER)


@pytest.fixture(scope="module")
def campaign():
    return ADAPTER.compile_campaign()


class _NoBackend:
    def classify_identity(self, *args, **kwargs):
        raise AssertionError("the exact selected subset must remain structural")


def test_complete_template_has_the_measured_finite_boundary(campaign):
    assert campaign["ring_variables"] == 78
    assert campaign["source_generators"] == 147
    assert campaign["selected_generators"] == 25
    assert campaign["dropped_generators"] == 122
    assert campaign["row_complete_depths"] == {
        1: 25, 2: 27, 3: 28, 4: 30, 5: 32,
    }
    assert campaign["sparse_terms"] == 424934
    assert campaign["selected_face_weld_verified"] is True
    assert campaign["generator_bundle_sha256"] == (
        "739ea3abeb73a60db99dfa7712e596ecc13b2a2dea9460cb635638c3b8dca371"
    )


def test_complete_template_earns_selected_face_containment(campaign):
    graph = ADAPTER.graph_from_campaign(campaign)

    verdict, why = V.containment(
        graph, ADAPTER.EDGE, _backend=_NoBackend())

    assert verdict == V.VERIFIED
    assert "unit-cofactor inclusion" in why
    assert P._eligible_structural_containment(graph, ADAPTER.EDGE)


def test_mutated_selected_face_loses_structural_authority(campaign):
    source, selected, edge = campaign["events"]
    selected = dict(selected)
    selected["generators"] = list(selected["generators"])
    changed = copy.deepcopy(selected["generators"][0])
    changed["terms"][0]["coefficient"] = "999"
    selected["generators"][0] = changed
    mutated = dict(campaign)
    mutated["events"] = [source, selected, edge]
    graph = ADAPTER.graph_from_campaign(mutated)

    assert not P._eligible_structural_containment(graph, ADAPTER.EDGE)
    with pytest.raises(AssertionError, match="must remain structural"):
        V.containment(graph, ADAPTER.EDGE, _backend=_NoBackend())


def test_authority_still_refuses_reverse_lift_and_h3(campaign):
    authority = campaign["authority"]

    assert "selected_faces_empty_implies_reduced_esystem_empty" in (
        authority["licenses"])
    assert "selected_faces_nonempty_implies_reduced_esystem_nonempty" in (
        authority["refuses"])
    assert "original polynomial-pair membership" in authority["refuses"]
    assert "H3 promotion" in authority["refuses"]

def test_show_summarizes_the_large_generator_bundle(
        campaign, monkeypatch, capsys):
    graph = ADAPTER.graph_from_campaign(campaign)
    monkeypatch.setattr(cli, "_load", lambda _args: graph)

    assert cli.cmd_show(object()) == 0
    output = capsys.readouterr().out

    assert "147 sparse generators; 424934 total terms" in output
    assert len(output) < 5000
