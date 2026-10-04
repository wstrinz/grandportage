"""Unchanged current-provenance fixtures; native Rat replay replaces fabricated backend metadata."""
import argparse
import ast
import copy
import hashlib
import importlib.util
import json
from pathlib import Path
import subprocess

EXE_SUFFIX = ".exe" if __import__("os").name == "nt" else ""
ROOT = Path(__file__).resolve().parents[1]
SCRATCH = ROOT / "tmp/phase2-provenance"
INSPECTOR = ROOT / ("phase2/lean/.lake/build/bin/gp_lifecycle_runner" + EXE_SUFFIX)
CASES = tuple("GP-X" + str(i) for i in range(165, 173))
PIN = "ac4155787207e2847d248cffed7be871d5dcd577"
ORACLE_COMMITS = {PIN, __import__("json").loads((ROOT / "oracle/PIN.json").read_text(encoding="utf-8-sig")).get("public_commit", PIN)}
SOURCE = "tests/test_verdict_provenance.py"
ANCHORS = {
    "GP-X165": (508, "test_mismatched_verifier_kernel_or_backend_is_stale"),
    "GP-X166": (508, "test_mismatched_verifier_kernel_or_backend_is_stale"),
    "GP-X167": (508, "test_mismatched_verifier_kernel_or_backend_is_stale"),
    "GP-X168": (508, "test_mismatched_verifier_kernel_or_backend_is_stale"),
    "GP-X169": (488, "test_verdict_for_different_semantic_input_is_stale"),
    "GP-X170": (463, "test_legacy_verified_remains_readable_but_inactive"),
    "GP-X171": (69, "test_fresh_epoch1_verdict_is_active"),
    "GP-X172": (69, "test_fresh_epoch1_verdict_is_active"),
}
INPUTS = {
    "GP-X165": {"mutation": {"verifier": "verify.old_identity"}},
    "GP-X166": {"mutation": {"verifier_version": 999}},
    "GP-X167": {"mutation": {"kernel_epoch": 13}},
    "GP-X168": {"mutation": {"backend": "not-singular"}},
    "GP-X169": {"new_generator": "x^2"},
    "GP-X170": {"legacy": True},
    "GP-X171": {"order": "valid_stale"},
    "GP-X172": {"order": "stale_valid"},
}
spec = importlib.util.spec_from_file_location("bound_slice", ROOT / "tools/run-phase2-slice.py")
shared = importlib.util.module_from_spec(spec)
spec.loader.exec_module(shared)
shared.SCRATCH = SCRATCH

def require(condition, message):
    if not condition:
        raise ValueError(message)

def sha(raw):
    return hashlib.sha256(raw).hexdigest()

def source_records(generator="x"):
    return {
        "model": {"id": "M", "what": "a line", "characteristic": 0,
                  "ring_vars": ["x"], "generators": [generator]},
        "claim": {"id": "C", "model": "M", "kind": "K.IDENTITY",
                  "statement": "x vanishes", "lhs": "x", "rhs": "0",
                  "ring_vars": ["x"], "identity_origin": "K.DERIVED",
                  "established_by": "RAN", "ladder": "exact-checked"},
    }

def source_contract():
    pin = json.loads((ROOT / "oracle/PIN.json").read_bytes())
    require(pin["commit"] == PIN, "source pin changed")
    checkout = ROOT / "oracle/checkout"
    git = ["git", "-c", "safe.directory=" + str(checkout), "-C", str(checkout)]
    require(subprocess.check_output(git + ["rev-parse", "HEAD"], text=True).strip() in ORACLE_COMMITS,
            "source checkout is not pinned")
    pinned = subprocess.check_output(git + ["show", "HEAD:" + SOURCE])
    require((checkout / SOURCE).read_bytes() == pinned, "named source file differs from pin")
    text = pinned.decode("utf-8")
    wanted = {"_identity_graph", "_execution", "_verdict"} | {a[1] for a in ANCHORS.values()}
    blocks = {}
    for node in ast.parse(text).body:
        if isinstance(node, ast.FunctionDef) and node.name in wanted:
            start = min([node.lineno] + [d.lineno for d in node.decorator_list])
            segment = "\n".join(text.splitlines()[start - 1:node.end_lineno])
            blocks[node.name] = {"line": node.lineno, "start_line": start,
                                 "end_line": node.end_lineno, "sha256": sha(segment.encode("utf-8"))}
    require(set(blocks) == wanted, "named source helper/anchor missing")
    for line, anchor in ANCHORS.values():
        require(blocks[anchor]["line"] == line, "named source anchor moved")
    return {"commit": PIN, "path": SOURCE, "file_sha256": sha(pinned), "named_blocks": blocks}

def retained_order_contract():
    baseline = json.loads((ROOT / "reports/PHASE-2-BASELINE.json").read_bytes())["base_commit"]
    path = "tools/lifecycle_probes.py"
    pinned = subprocess.check_output(["git", "show", baseline + ":" + path], cwd=ROOT)
    require((ROOT / path).read_bytes() == pinned, "retained order adapter differs from baseline")
    text = pinned.decode("utf-8")
    require("valid['id']='receipt.valid'" in text
            and "stale['id']='receipt.stale';stale['kernel_epoch']=F.KERNEL_EPOCH-1" in text
            and "[valid,stale] if d['order']=='valid_stale' else [stale,valid]" in text,
            "retained order constructor changed")
    source_path = "grandportage/format.py"
    epoch_source = subprocess.check_output(["git", "-c", "safe.directory=" + str(ROOT / "oracle/checkout"),
        "-C", str(ROOT / "oracle/checkout"), "show", "HEAD:" + source_path])
    require((ROOT / "oracle/checkout" / source_path).read_bytes() == epoch_source, "epoch source changed")
    epoch = next(node.value.value for node in ast.parse(epoch_source.decode("utf-8")).body
        if isinstance(node, ast.Assign) and any(isinstance(t, ast.Name) and t.id == "KERNEL_EPOCH"
                                               for t in node.targets))
    require(epoch == 12, "recorded source current epoch changed")
    return {"base_commit": baseline, "path": path, "sha256": sha(pinned),
            "source_epoch_path": source_path, "source_epoch_sha256": sha(epoch_source),
            "source_current_epoch": epoch, "source_stale_epoch": epoch - 1,
            "native_current_epoch": 1, "native_stale_epoch": 0}

def checked_cases():
    tags = json.loads((ROOT / "corpus/LAYER-TAGS.json").read_bytes())
    routes = json.loads((ROOT / "oracle/ROUTES.json").read_bytes())
    require(routes["commit"] == PIN, "route source pin changed")
    result = []
    for case_id in CASES:
        path = ROOT / "corpus/must" / (case_id + ".json")
        raw = path.read_bytes()
        case = json.loads(raw)
        tag = next(row for row in tags["cases"] if row["id"] == case_id)
        line, anchor = ANCHORS[case_id]
        require(tag["primary_layer"] == "kernel" and sha(raw) == tag["sha256"],
                case_id + ": fixture bytes/layer differ from pin")
        require(case["id"] == case_id and case["inputs"] == INPUTS[case_id],
                case_id + ": literal input contract changed")
        require(case["sources"] == [{"repository": "gp-v037", "commit": PIN,
            "path": SOURCE, "line": line, "anchor": "def " + anchor + "("}], "source pointer changed")
        require(case["expected"]["verdict"] == ("ACCEPT" if case_id in CASES[-2:] else "REFUSE"),
                "expectation changed")
        result.append((case, raw, copy.deepcopy(routes["routes"][case_id])))
    return result

def fresh(generator="x"):
    registry, events = shared.prepared([copy.deepcopy(shared.POLYNOMIALS[generator])],
                                      copy.deepcopy(shared.POLYNOMIALS["x"]))
    literal = source_records(generator)
    b = registry["clauses"][0]["binding"]
    b["statementHash"] = shared.digest(literal["claim"])
    b["modelHash"] = shared.digest(literal["model"])
    b["inputHashes"].append(shared.digest(literal))
    b["authority"] = shared.encoded({"verifier": "gp50-rat-span-test-stub",
                                    "backend": "native-rat-cofactor-replay"})
    registry["receipts"][0]["name"] = "current:C"
    registry["receipts"][0]["binding"] = copy.deepcopy(b)
    for event in events["events"]:
        event["value"]["binding"] = copy.deepcopy(b)
    events["events"][1]["value"]["evidence"]["data"] = "current:C"
    return registry, events

def translate(case):
    case_id = case["id"]
    require(case_id in CASES and case["inputs"] == INPUTS[case_id], "unsupported literal contract")
    baseline = fresh()
    registry, events = copy.deepcopy(baseline)
    literal = source_records()
    provenance = {"source_constructor": "_verdict(_identity_graph())",
                  "native_warrant_id": 10, "native_claim_key": 1, "source_model": "M", "source_claim": "C"}
    if case_id in CASES[:4]:
        field, value = next(iter(case["inputs"]["mutation"].items()))
        receipt, warrant = registry["receipts"][0], events["events"][1]["value"]
        source_id = "v.C.mismatch." + field
        receipt["name"] = source_id
        warrant["evidence"]["data"] = source_id
        for b in (receipt["binding"], warrant["binding"]):
            if field in ("verifier", "backend"):
                authority = json.loads(b["authority"])
                authority[field] = value
                b["authority"] = shared.encoded(authority)
            else:
                b[{"verifier_version": "authorityVersion", "kernel_epoch": "kernelVersion"}[field]] = value
        provenance.update(source_verdict_id=source_id, mutation=case["inputs"]["mutation"])
        fidelity = "Exact recorded producer/backend/version/epoch mismatch is retained in native receipt and warrant bindings; current clause/current custody remain unchanged."
    elif case_id == "GP-X169":
        registry, events = fresh("x^2")
        old_registry, old_events = baseline
        registry["receipts"] = copy.deepcopy(old_registry["receipts"])
        events["events"][1] = copy.deepcopy(old_events["events"][1])
        literal = source_records("x^2")
        provenance.update(source_semantic_generator_before="x", source_semantic_generator_after="x^2",
                          old_receipt_retained=True)
        fidelity = "M changes literally from (x) to (x^2), C remains x=0; old exact-replay receipt/warrant binding is retained while current model/input digests change."
    elif case_id in CASES[-2:]:
        retained_order_contract()
        valid_receipt = registry["receipts"][0]
        valid_warrant = events["events"][1]["value"]
        valid_receipt["name"] = "receipt.valid"
        valid_warrant["evidence"]["data"] = "receipt.valid"
        stale_receipt = copy.deepcopy(valid_receipt)
        stale_receipt["name"] = "receipt.stale"
        stale_receipt["binding"]["kernelVersion"] = 0
        stale_warrant = copy.deepcopy(valid_warrant)
        stale_warrant.update(id=11, binding=copy.deepcopy(stale_receipt["binding"]))
        stale_warrant["evidence"]["data"] = "receipt.stale"
        registry["receipts"].append(stale_receipt)
        current, valid = events["events"]
        stale = {"kind": "warrant", "value": stale_warrant}
        events["events"] = [current] + ([valid, stale] if case_id == "GP-X171" else [stale, valid])
        provenance.update(source_constructor="retained lifecycle_probes.probe receipt/order",
                          source_verdict_ids=["receipt.valid", "receipt.stale"],
                          native_warrant_ids=[10, 11], source_epochs=[12, 11], native_epochs=[1, 0],
                          order=case["inputs"]["order"])
        baseline = None
        fidelity = "Retained baseline adapter supplies both exact histories: valid/stale IDs and source epoch 12/11. Native epochs 1/0 preserve their equality/mismatch contract. Both complete records survive; only the valid receipt contributes held authority in either order."
    else:
        legacy = {"ev": "verdict", "id": "v.C.legacy", "subject": "claim", "of": "C",
                  "verdict": "VERIFIED_DERIVED", "why": "an epoch-0 verifier said so"}
        registry["receipts"] = []
        warrant = events["events"][1]["value"]
        warrant["binding"].update(authority="legacy-unbound-provenance", authorityVersion=0, kernelVersion=0)
        warrant["evidence"] = {"kind": "citation", "text": shared.encoded(legacy)}
        provenance.update(source_verdict_id="v.C.legacy", retained_legacy_event=legacy,
                          absent_source_producer_fields=["verifier", "verifier_version", "kernel_epoch", "backend"])
        fidelity = "The complete literal epoch-0 event is retained as an opaque readable citation; unbound/zero native provenance placeholders confer no receipt authority and cannot match current custody."
    return registry, events, baseline, literal, provenance, fidelity

def execute(label, registry, events):
    observed, inputs = shared.execute(label, registry, events)
    event_path = SCRATCH / (label + ".events.json")
    inspection = subprocess.run([str(INSPECTOR), str(event_path)], cwd=ROOT,
                                capture_output=True, text=True, encoding="utf-8", check=True)
    identity = json.loads(inspection.stdout)
    require(identity["status"] == "OK" and identity["resolve_fold_snapshot_equal"] is True,
            "native identity inspection failed")
    result = {"authority": observed, "identity": identity["snapshot"],
              "identity_admission": identity["admission"]}
    return result, inputs

def verify(result, events, expected_held):
    authority, snapshot = result["authority"], result["identity"]
    currents = sorted((e["value"] for e in events["events"] if e["kind"] == "current"),
                      key=lambda c: c["claim"])
    warrants = sorted((e["value"] for e in events["events"] if e["kind"] == "warrant"),
                      key=lambda w: w["id"])
    expected = {"domain": [1], "currents": currents, "warrants": warrants,
                "retracted": [], "successors": []}
    require(snapshot == expected, "complete native identity/binding records differ")
    require(authority["held"] == expected_held, "native held authority differs")
    expected_supports = [10] if expected_held else []
    require(authority["supports"] == expected_supports, "native support IDs differ")
    require(authority["domain"] == [1] and authority["warrant_count"] == len(warrants)
            and authority["current_count"] == len(currents)
            and authority["retracted"] == [] and authority["successors"] == [],
            "authority and identity native projections differ")
    expected_live = [w["id"] for w in warrants if any(c["claim"] == w["claim"]
                    and c["version"] == w["version"] and c["binding"] == w["binding"] for c in currents)]
    require(authority["live_warrants"] == expected_live, "native current binding eligibility differs")

def run(output):
    source = source_contract()
    order_source = retained_order_contract()
    results = []
    for case, raw, route in checked_cases():
        translated = translate(case)
        registry, events, baseline, literal, provenance, fidelity = translated
        positive, positive_inputs = (None, None) if baseline is None else execute(case["id"] + "-positive", *baseline)
        if positive is not None:
            verify(positive, baseline[1], [1])
        observed, native_inputs = execute(case["id"], registry, events)
        expected_held = [1] if case["id"] in CASES[-2:] else []
        verify(observed, events, expected_held)
        verdict = "ACCEPT" if expected_held else "REFUSE"
        require(verdict == case["expected"]["verdict"], "native verdict differs from fixture")
        require((ROOT / "corpus/must" / (case["id"] + ".json")).read_bytes() == raw, "fixture modified")
        results.append({"id": case["id"], "source_sha256": sha(raw), "expected": case["expected"],
                        "status": "EXECUTED", "observed": verdict, "full_fixture_contract": True,
                        "route": route, "literal_source_records": literal, "provenance_mapping": provenance,
                        "native_result": observed, "native_inputs": native_inputs,
                        "positive_contrast": positive, "positive_inputs": positive_inputs,
                        "translation_fidelity": fidelity})
    for case, raw, _ in checked_cases():
        require(sha(raw) == next(row["source_sha256"] for row in results if row["id"] == case["id"]),
                "fixture bytes changed during run")
    record = {"schema": "gp-phase2-provenance-slice/v1", "commissioned_case_count": 8,
              "executed_case_count": 8, "unexecuted_case_count": 0, "positive_contrasts": 6,
              "complete_ten_case_slice": False, "g2_pass": False, "cases": results,
              "pinned_source": source, "retained_order_constructor": order_source,
              "branch_order_records_equal": results[-2]["native_result"] == results[-1]["native_result"], "runner_sha256": sha(shared.EXE.read_bytes()),
              "identity_inspector_sha256": sha(INSPECTOR.read_bytes()),
              "adapter_sha256": sha(Path(__file__).read_bytes()),
              "shared_adapter_sha256": sha((ROOT / "tools/run-phase2-slice.py").read_bytes()),
              "vocabulary_mapping": {
                  "verifier_and_backend": "Native binding.authority stores a canonical pair. Current source verifier/backend contract maps to the actual Rat checker/replay; literal mismatches replace the corresponding component.",
                  "verifier_version": "Native authorityVersion=1 is the admitted test checker version; literal mismatch 999 stays 999.",
                  "kernel_epoch": "Source current epoch contract maps to native kernelVersion=1; literal differing epoch 13 stays 13. No source kernel numeric equality is asserted.",
                  "semantic_input": "Current M/C literal packets and actual polynomial data are hashed separately; old receipt/warrant inputs remain unchanged.",
                  "native_identity_view": "The same event bytes run through the native lifecycle inspector to expose complete resolution records. Its refuseAll admission does not supply authority; authority comes only from the bound Rat runner."},
              "trust_boundary": "Host deterministic JSON/SHA-256 binding and native compiler/runtime remain explicit. The source fabricates Singular execution descriptors; no Singular process or source Python success flag supplies native authority.",
              "scope_limit": "Eight full provenance fixtures are aggregated separately from component contrasts; required slice behavior coverage remains incomplete."}
    require(record["branch_order_records_equal"], "complete order results differ")
    output.write_bytes((json.dumps(record, indent=2) + "\n").encode("utf-8"))
    print("Provenance slice: 8 literal fixtures and 6 native Rat contrasts passed; complete order records equal.")
    return record

if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, default=ROOT / "reports/PHASE-2-PROVENANCE-SLICE.json")
    run(parser.parse_args().output)
