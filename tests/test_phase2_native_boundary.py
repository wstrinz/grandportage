"""Adversarial raw configuration inputs through the compiled native runner."""
import copy
import importlib.util
import json
from pathlib import Path
import subprocess

import pytest

ROOT = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location("native_slice", ROOT / "tools/run-phase2-slice.py")
bridge = importlib.util.module_from_spec(spec)
spec.loader.exec_module(bridge)


@pytest.fixture
def native(tmp_path):
    registry, events = bridge.prepared([copy.deepcopy(bridge.POLYNOMIALS["x"])], copy.deepcopy(bridge.POLYNOMIALS["x"]))

    def run(config, log=None):
        config_path = tmp_path / "registry.json"
        event_path = tmp_path / "events.json"
        config_path.write_text(config if isinstance(config, str) else json.dumps(config), encoding="utf-8")
        event_path.write_text(json.dumps(events if log is None else log), encoding="utf-8")
        result = subprocess.run([str(bridge.EXE), str(config_path), str(event_path)],
                                cwd=ROOT, capture_output=True, text=True, check=True, encoding="utf-8")
        return json.loads(result.stdout)

    return registry, events, run


def test_actual_fraction_and_signed_replay(native):
    registry, _, run = native
    registry["clauses"][0]["generators"] = [[{"exp": 0, "num": -1, "den": 2}]]
    registry["clauses"][0]["target"] = [{"exp": 0, "num": 1, "den": 1}]
    registry["receipts"][0]["cofactors"] = [[{"exp": 0, "num": -2, "den": 1}]]
    assert run(registry)["held"] == [1]
    registry["receipts"][0]["cofactors"][0][0]["num"] = 2
    assert run(registry)["held"] == []


@pytest.mark.parametrize("defect", [
    "zero_den", "negative_exp", "fractional_num", "extra_term_field",
    "missing_term_field", "unknown_schema", "unknown_registry_field",
    "duplicate_clause_id", "duplicate_receipt_name", "extra_receipt_field",
    "missing_binding_field", "duplicate_raw_key", "escaped_duplicate_raw_key",
])
def test_malformed_registry_never_reaches_held(native, defect):
    registry, _, run = native
    term = registry["clauses"][0]["target"][0]
    if defect == "zero_den":
        term["den"] = 0
    elif defect == "negative_exp":
        term["exp"] = -1
    elif defect == "fractional_num":
        term["num"] = 0.5
    elif defect == "extra_term_field":
        term["ok"] = True
    elif defect == "missing_term_field":
        del term["den"]
    elif defect == "unknown_schema":
        registry["schema_version"] = 2
    elif defect == "unknown_registry_field":
        registry["success"] = True
    elif defect == "duplicate_clause_id":
        registry["clauses"].append(copy.deepcopy(registry["clauses"][0]))
    elif defect == "duplicate_receipt_name":
        registry["receipts"].append(copy.deepcopy(registry["receipts"][0]))
    elif defect == "extra_receipt_field":
        registry["receipts"][0]["success"] = True
    elif defect == "missing_binding_field":
        del registry["clauses"][0]["binding"]["inputHashes"]
    else:
        text = json.dumps(registry)
        duplicate = '"schema_version": 1,' if defect == "duplicate_raw_key" else '"schema_\\u0076ersion": 1,'
        registry = "{" + duplicate + text[1:]
    result = run(registry)
    assert result["status"] == "MALFORMED"
    assert "held" not in result


def test_event_error_and_inert_theorem_pointer(native):
    registry, events, run = native
    events["events"][1]["value"]["evidence"] = {"kind": "theorem_warrant", "declaration": "receipt-1"}
    result = run(registry, events)
    assert result["status"] == "OK"
    assert result["held"] == []
    events["events"][1]["value"]["evidence"] = {"kind": "receipt", "data": "receipt-1", "success": True}
    assert run(registry, events)["status"] == "MALFORMED"

def test_x164_current_positive_preserves_exact_identity_and_refuses_mismatches(native):
    registry, events, run = native
    case = json.loads((ROOT / "corpus/must/GP-X164.json").read_bytes())
    registry, events, contrast, fidelity, key = bridge.translate(case)
    assert contrast is None and run(registry, events)["held"] == [key]
    for field, changed in (("authorityVersion", 2), ("kernelVersion", 2),
                           ("inputHashes", ["different"]), ("modelHash", "different")):
        altered = copy.deepcopy(events)
        altered["events"][1]["value"]["binding"][field] = changed
        assert run(registry, altered)["held"] == []
    registry["receipts"][0]["cofactors"] = []
    assert run(registry, events)["held"] == []
