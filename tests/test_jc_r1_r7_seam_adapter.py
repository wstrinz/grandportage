import copy
import hashlib
import importlib.util
import json
from pathlib import Path

import pytest


ROOT = Path(__file__).resolve().parents[1]
SCRIPT = (ROOT / "experiments" / "jc_h3_source_depth6" /
          "r1_r7_seam_adapter.py")


def load_adapter():
    spec = importlib.util.spec_from_file_location("jc_r1_r7_adapter_test", SCRIPT)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def fixture_value(module):
    return json.loads(module.DEFAULT_FIXTURE.read_text(encoding="utf-8"))


def frontier(value, stage_id):
    return next(item for item in value["projection"]["open_frontier"]
                if item["id"] == stage_id)


def test_frozen_adapter_reports_the_exact_corrected_open_frontier():
    module = load_adapter()
    report = module.verify_fixture()

    assert report["verdict"] == "VERIFIED_R1_R7_OPEN_FRONTIER"
    assert report["parent_obligation"] == (
        "target_pair_to_normalized_laurent_root")
    assert report["parent_status"] == "UNMATERIALIZED_OPEN"
    assert report["closed_substages"] == ["R1", "R2", "R3", "R4"]
    assert {item["id"]: item["status"] for item in report["open_frontier"]} == {
        "R5": "CHECKED_PREMISE_BOUND",
        "R6": "OPEN_NONMONOMIAL_FRAME_CONVERSION",
        "R7": "INFERRED_UNBOUND_75_125_IDENTIFICATION",
    }
    assert report["R6"] == module.R6_TYPED
    assert report["graph_effect"] == "NONE"
    assert report["evidence_envelope"]["graph_effect"] == "NONE"
    assert report["binding_digest_algo"] == "sha256-lf-normalized"


def mutate_r6_closed(value):
    frontier(value, "R6")["status"] = "CLOSED"


def mutate_q_forced(value):
    value["projection"]["R6"]["Q_positive_j"] = "FORCED"


def mutate_point_every_gauge(value):
    value["projection"]["R6"]["covered_point_1_2"] = (
        "ACTUAL_NONZERO_EVERY_GAUGE")


def mutate_drop_branch_premise(value):
    value["projection"]["R6"]["premises"] = [
        "actual_pair", "source_polynomiality"]


def mutate_r7_proved(value):
    frontier(value, "R7")["status"] = "PROVED"


def mutate_r5_unconditional(value):
    frontier(value, "R5")["status"] = "CHECKED"


def mutate_graph_effect(value):
    value["projection"]["graph_effect"] = "POINT_INCLUSION"


def mutate_binding(value):
    first = sorted(value["source_bindings"])[0]
    value["source_bindings"][first] = "0" * 64


def mutate_parent_closed(value):
    value["projection"]["parent_status"] = "COMPLETE"


def mutate_drop_gap5(value):
    value["projection"]["outstanding_premises"].remove(
        "GAP-5 source equivalence")


@pytest.mark.parametrize("mutator,check_id", [
    (mutate_r6_closed, "M1"),
    (mutate_q_forced, "M2"),
    (mutate_point_every_gauge, "M3"),
    (mutate_drop_branch_premise, "M4"),
    (mutate_r7_proved, "M5"),
    (mutate_r5_unconditional, "M6"),
    (mutate_graph_effect, "M7"),
    (mutate_binding, "M8"),
    (mutate_parent_closed, "M9"),
    (mutate_drop_gap5, "M10"),
])
def test_mandatory_authority_mutations_are_independently_refused(
        mutator, check_id):
    module = load_adapter()
    value = fixture_value(module)
    mutator(value)

    with pytest.raises(module.R1R7SeamError, match=check_id + ":"):
        module.validate_fixture_value(value)


def test_fixture_is_a_deterministic_copy_and_projection_of_native_inputs():
    module = load_adapter()
    if not module.NATIVE_ROOT.exists():
        pytest.skip("live sibling math-stuff checkout is not available")
    frozen = fixture_value(module)
    rebuilt = module.build_fixture()

    assert rebuilt == frozen
    assert hashlib.sha256(module.encoded(rebuilt)).hexdigest() == (
        module.EXPECTED_FIXTURE_SHA256)


def test_live_native_bindings_when_sibling_checkout_is_available():
    module = load_adapter()
    if not module.NATIVE_ROOT.exists():
        pytest.skip("live sibling math-stuff checkout is not available")

    report = module.verify_fixture(check_bindings=True)
    assert report["binding_digest_algo"] == "sha256-lf-normalized"


def test_lf_normalized_binding_check_fails_closed_on_a_tampered_copy(tmp_path):
    module = load_adapter()
    native = tmp_path / "native"
    native.mkdir()
    path = native / "bound.txt"
    path.write_bytes(b"first\r\nsecond\r\n")
    expected = hashlib.sha256(b"first\nsecond\n").hexdigest()
    value = {"source_bindings": {"bound.txt": expected}}

    module.check_native_bindings(value, native)
    path.write_bytes(b"first\r\nchanged\r\n")
    with pytest.raises(module.R1R7SeamError, match="M8:"):
        module.check_native_bindings(value, native)


def test_normal_verification_never_executes_a_native_checker(monkeypatch):
    module = load_adapter()

    def forbidden(*_args, **_kwargs):
        raise AssertionError("native checker executed during fixture verification")

    monkeypatch.setattr(module.subprocess, "run", forbidden)
    assert module.verify_fixture()["verdict"] == (
        "VERIFIED_R1_R7_OPEN_FRONTIER")


def test_fixture_digest_is_a_separate_fail_closed_boundary(tmp_path):
    module = load_adapter()
    value = fixture_value(module)
    value["authority_boundary"] += " changed"
    path = tmp_path / "changed.json"
    path.write_bytes(module.encoded(value))

    with pytest.raises(module.R1R7SeamError, match="F5:"):
        module.verify_fixture(path)
