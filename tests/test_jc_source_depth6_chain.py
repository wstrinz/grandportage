"""Independent GP consumption of the landed JC depth-6 chain certificate."""

import gzip
import hashlib
import importlib.util
import json
import os
from pathlib import Path

import pytest


pytestmark = pytest.mark.replay

from grandportage import evidence as EV


ROOT = Path(__file__).parents[1]
ADAPTER_PATH = (ROOT / "experiments" / "jc_h3_source_depth6" /
                "chain_adapter.py")
FROZEN_PATH = ROOT / "fixtures" / "jc_source_depth6" / "chain_v1.json.gz"

_spec = importlib.util.spec_from_file_location(
    "jc_source_depth6_chain_adapter", ADAPTER_PATH)
ADAPTER = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(ADAPTER)


def _certificate():
    return json.loads(gzip.decompress(FROZEN_PATH.read_bytes()).decode("utf-8"))


def _repin_mutation(monkeypatch, tmp_path, certificate):
    """Re-sign a mutation so the semantic gate, not the outer hash, sees it."""
    canonical = json.dumps(certificate, separators=(",", ":")).encode("utf-8")
    compressed = gzip.compress(canonical, mtime=0)
    path = tmp_path / "mutated.json.gz"
    path.write_bytes(compressed)
    monkeypatch.setattr(ADAPTER, "EXPECTED_CANONICAL_SHA256",
                        hashlib.sha256(canonical).hexdigest())
    monkeypatch.setattr(ADAPTER, "EXPECTED_COMPRESSED_SHA256",
                        hashlib.sha256(compressed).hexdigest())
    return path


def test_checked_in_chain_fast_gate_welds_both_gp_endpoints():
    report = ADAPTER.verify_chain()

    assert report["verdict"] == "VERIFIED_DEPTH6_CHAIN_ENVELOPE"
    assert report["faces"] == 25
    assert report["input_values_welded"] == 10
    assert report["solved_steps"] == 23
    assert report["residuals_welded"] == 2
    envelope = report["evidence_envelope"]
    assert envelope["graph_effect"] == EV.GRAPH_EFFECT_NONE
    assert "chain_inputs_welded_to_gp_ladder_solutions" in envelope["licenses"]
    assert "boundary_residuals_welded_to_gp_projection" in envelope["licenses"]
    assert any("raw E-system rows" in premise
               for premise in envelope["outstanding_premises"])
    assert all("H3" not in license for license in envelope["licenses"])


def test_preflight_checks_bindings_without_any_sparse_decode(monkeypatch):
    def forbidden(*_args, **_kwargs):
        raise AssertionError("preflight attempted sparse decoding")

    monkeypatch.setattr(ADAPTER, "_decode_sparse", forbidden)
    report = ADAPTER.preflight_chain()

    assert report["verdict"] == "PREFLIGHT_BINDINGS_ONLY"
    assert report["graph_effect"] == EV.GRAPH_EFFECT_NONE
    assert report["ordered_steps_bound"] == 23
    assert report["residual_digests_checked"] == 2
    assert report["licenses"] == ["frozen_inputs_are_the_named_inputs"]
    assert "chain identity authority" in report["refuses"]


def test_checked_in_copy_is_byte_identical_to_landed_native_certificate():
    if not ADAPTER.DEFAULT_NATIVE.exists():
        pytest.skip("the sibling JC research checkout is not present")
    assert ADAPTER.native_copy_matches() is True


def test_reordered_steps_are_rejected_after_resigning(monkeypatch, tmp_path):
    certificate = _certificate()
    certificate["steps"][0], certificate["steps"][1] = (
        certificate["steps"][1], certificate["steps"][0])
    path = _repin_mutation(monkeypatch, tmp_path, certificate)

    with pytest.raises(ADAPTER.Depth6ChainError,
                       match="ordered prior mismatch"):
        ADAPTER.verify_chain(path)


def test_mutated_unit_witness_is_rejected_after_resigning(monkeypatch, tmp_path):
    certificate = _certificate()
    term = certificate["steps"][0]["pivot_inverse"]["terms"][0]
    term[1] = str(ADAPTER.Q(term[1]) * 2)
    path = _repin_mutation(monkeypatch, tmp_path, certificate)

    with pytest.raises(ADAPTER.Depth6ChainError, match="unit witness fails"):
        ADAPTER.verify_chain(path)


def test_mutated_solved_value_is_rejected_after_resigning(monkeypatch, tmp_path):
    certificate = _certificate()
    term = certificate["steps"][0]["value"]["sparse"]["terms"][0]
    term[1] = str(ADAPTER.Q(term[1]) + 1)
    path = _repin_mutation(monkeypatch, tmp_path, certificate)

    with pytest.raises(ADAPTER.Depth6ChainError, match="value digest"):
        ADAPTER.verify_chain(path)


def test_dropped_scope_refusal_is_rejected_after_resigning(monkeypatch, tmp_path):
    certificate = _certificate()
    certificate["refusals"].remove("H3 promotion")
    path = _repin_mutation(monkeypatch, tmp_path, certificate)

    with pytest.raises(ADAPTER.Depth6ChainError,
                       match="dropped a required refusal"):
        ADAPTER.verify_chain(path)


@pytest.mark.skipif(os.environ.get("GP_RUN_SLOW_CHAIN_REPLAY") != "1",
                    reason="set GP_RUN_SLOW_CHAIN_REPLAY=1 for the ~80s replay")
def test_full_exact_face_replay():
    report = ADAPTER.verify_chain(full_replay=True)

    assert report["verdict"] == "VERIFIED_DEPTH6_CHAIN_FULL_REPLAY"
    assert "exact_ordered_depth2_6_face_replay" in (
        report["evidence_envelope"]["licenses"])
    assert report["evidence_envelope"]["graph_effect"] == EV.GRAPH_EFFECT_NONE
