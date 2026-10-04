"""Execute selected unchanged kernel fixtures through the native bound-span runner."""
import argparse
import copy
import hashlib
import importlib.util
import json
from pathlib import Path
import subprocess

EXE_SUFFIX = ".exe" if __import__("os").name == "nt" else ""
ROOT = Path(__file__).resolve().parents[1]
EXE = ROOT / ("phase2/lean/.lake/build/bin/gp_span_runner" + EXE_SUFFIX)
SCRATCH = ROOT / "tmp/phase2-slice"
POLYNOMIALS = {
    "x": [{"exp": 1, "num": 1, "den": 1}],
    "x^2": [{"exp": 2, "num": 1, "den": 1}],
}
ONE = [{"exp": 0, "num": 1, "den": 1}]

def encoded(value):
    return json.dumps(value, sort_keys=True, separators=(",", ":"), ensure_ascii=True)

def digest(value):
    return hashlib.sha256(encoded(value).encode("utf-8")).hexdigest()

def binding(generators, target):
    return {
        "statementHash": digest({"kind": "formal-span", "generators": generators, "target": target}),
        "scopeHash": digest({"coefficient_field": "Q", "reach": "formal-univariate-span"}),
        "modelHash": digest({"ring": "Q[x]", "encoding": "sparse-rational-terms/v1"}),
        "inputHashes": [digest(generators), digest(target)],
        "authority": "gp50-rat-span-test-stub",
        "authorityVersion": 1,
        "kernelVersion": 1,
    }

def prepared(generators, target, version=1):
    b = binding(generators, target)
    clause = {"key": 1, "version": version, "binding": b,
              "generators": generators, "target": target}
    receipt = {"name": "receipt-1", "claim": 1, "version": version,
               "binding": copy.deepcopy(b), "cofactors": [copy.deepcopy(ONE)]}
    registry = {"schema_version": 1, "clauses": [clause], "receipts": [receipt]}
    current = {"kind": "current", "value": {"claim": 1, "version": version, "binding": b}}
    warrant = {"kind": "warrant", "value": {
        "id": 10, "claim": 1, "version": version, "binding": copy.deepcopy(b),
        "evidence": {"kind": "receipt", "data": receipt["name"]}}}
    return registry, {"schema_version": 1, "events": [current, warrant]}

def translate(case):
    inputs = case["inputs"]
    if case["id"] == "GP-A18":
        if set(inputs) != {"old_ideal", "new_ideal", "identity"} or inputs["identity"] != "x=0":
            raise ValueError("A18 requires the literal declared x=0 identity contract")
        old = [copy.deepcopy(POLYNOMIALS[name]) for name in inputs["old_ideal"]]
        new = [copy.deepcopy(POLYNOMIALS[name]) for name in inputs["new_ideal"]]
        if old != [POLYNOMIALS["x"]] or new != [POLYNOMIALS["x^2"]]:
            raise ValueError("A18 bridge supports only this unchanged recorded ideal mutation")
        registry, events = prepared(old, copy.deepcopy(POLYNOMIALS["x"]))
        baseline = (copy.deepcopy(registry), copy.deepcopy(events))
        changed_registry, changed_events = prepared(new, copy.deepcopy(POLYNOMIALS["x"]), 2)
        changed_registry["receipts"] = registry["receipts"]
        changed_events["events"][1] = events["events"][1]
        return changed_registry, changed_events, baseline, (
            "Actual x=1*x replay accepts before the input mutation. "
            "The unchanged receipt keeps its old version/input binding after (x) becomes (x^2). "
            "The query is whether that receipt remains current, not geometric emptiness."), 1
    if case["id"] == "GP-A17":
        if set(inputs) != {"attempt_status", "earlier_current_warrant"} or inputs["earlier_current_warrant"] is not False:
            raise ValueError("A17 bridge requires no earlier current warrant")
        statuses = {"UNVERIFIED": "absent", "TIMEOUT": "timeout", "FAILED": "failed"}
        status = statuses[inputs["attempt_status"]]
        registry, events = prepared([copy.deepcopy(POLYNOMIALS["x"])], copy.deepcopy(POLYNOMIALS["x"]))
        baseline = (copy.deepcopy(registry), copy.deepcopy(events))
        registry["receipts"] = []
        events["events"][1]["value"]["evidence"] = {"kind": "attempt", "status": status}
        return registry, events, baseline, (
            "Explicit UNVERIFIED-to-absent vocabulary translation; no earlier warrant is supplied. "
            "A successful exact-replay contrast uses the same statement and current binding."), 1
    if case["id"] == "GP-A25b":
        if set(inputs) != {"identifiers", "alias_evidence"} or inputs["alias_evidence"] is not None:
            raise ValueError("A25b requires the unchanged absent-alias contract")
        names = inputs["identifiers"]
        if len(names) != 2 or names[0] == names[1]:
            raise ValueError("A25b requires two distinct selected object identities")
        first, first_events = prepared([copy.deepcopy(POLYNOMIALS["x"])], copy.deepcopy(POLYNOMIALS["x"]))
        second, second_events = prepared([copy.deepcopy(POLYNOMIALS["x"])], copy.deepcopy(POLYNOMIALS["x"]))
        for registry, events, key, name in ((first, first_events, 1, names[0]),
                                          (second, second_events, 2, names[1])):
            b = copy.deepcopy(registry["clauses"][0]["binding"])
            b["modelHash"] = digest({"ring": "Q[x]", "selected_object": name})
            b["inputHashes"].append(digest({"selected_object": name}))
            registry["clauses"][0].update(key=key, binding=copy.deepcopy(b))
            registry["receipts"][0].update(claim=key, binding=copy.deepcopy(b))
            events["events"][0]["value"].update(claim=key, binding=copy.deepcopy(b))
            events["events"][1]["value"].update(claim=key, binding=copy.deepcopy(b))
        baseline = (copy.deepcopy(second), copy.deepcopy(second_events))
        second["clauses"].insert(0, first["clauses"][0])
        second["receipts"] = first["receipts"]
        return second, second_events, baseline, (
            "Both selected identities are preserved in registry keys and model/input bindings. "
            "The B warrant asks for the A-owned receipt; no alias rule is registered. "
            "A fresh independently bound B receipt is a separate positive control."), 2
    if case["id"] == "GP-X164":
        if inputs:
            raise ValueError("X164 requires the unchanged fresh provenance control")
        # Pinned test_verdict_provenance.py: _identity_graph/_verdict and
        # test_fresh_epoch1_verdict_is_active use M:(x), C:x=0.
        registry, events = prepared([copy.deepcopy(POLYNOMIALS["x"])], copy.deepcopy(POLYNOMIALS["x"]))
        b = registry["clauses"][0]["binding"]
        b["statementHash"] = digest({"id": "C", "model": "M", "lhs": "x", "rhs": "0",
                                    "kind": "identity", "identity_origin": "derived"})
        b["modelHash"] = digest({"id": "M", "ring_vars": ["x"], "characteristic": 0,
                                "generators": registry["clauses"][0]["generators"]})
        b["inputHashes"].append(digest({"claim": "C", "model": "M"}))
        registry["receipts"][0]["binding"] = copy.deepcopy(b)
        for event in events["events"]:
            event["value"]["binding"] = copy.deepcopy(b)
        return registry, events, None, (
            "Pinned source has M:(x), C:x=0, current epoch-1 provenance. "
            "Those exact polynomial and selected-object identities are preserved. "
            "Native Rat cofactor replay supplies checked identity authority instead of the source's "
            "fabricated Singular execution metadata; no Singular execution is claimed."), 1
    raise ValueError("Uncommissioned fixture: " + case["id"])

def execute(label, registry, events):
    SCRATCH.mkdir(parents=True, exist_ok=True)
    config_path = SCRATCH / (label + ".registry.json")
    event_path = SCRATCH / (label + ".events.json")
    config_path.write_bytes((encoded(registry) + "\n").encode("utf-8"))
    event_path.write_bytes((encoded(events) + "\n").encode("utf-8"))
    result = subprocess.run([str(EXE), str(config_path), str(event_path)], cwd=ROOT,
                            capture_output=True, text=True, encoding="utf-8", check=True)
    observed = json.loads(result.stdout)
    if observed["status"] != "OK":
        raise ValueError(label + ": malformed native input: " + observed.get("error", ""))
    return observed, {
        "registry_sha256": hashlib.sha256(config_path.read_bytes()).hexdigest(),
        "events_sha256": hashlib.sha256(event_path.read_bytes()).hexdigest(),
    }

def run(output):
    results = []
    tags = json.loads((ROOT / "corpus/LAYER-TAGS.json").read_text(encoding="utf-8"))
    for case_id in ("GP-A17", "GP-A18", "GP-A25b", "GP-X164"):
        path = ROOT / "corpus/must" / (case_id + ".json")
        raw = path.read_bytes()
        case = json.loads(raw)
        row = next(row for row in tags["cases"] if row["id"] == case_id)
        assert row["primary_layer"] == "kernel"
        assert hashlib.sha256(raw).hexdigest() == row["sha256"]
        registry, events, baseline, fidelity, query = translate(case)
        positive, positive_inputs = (None, None) if baseline is None else execute(
            case_id + "-positive-control", *baseline)
        if positive is not None:
            assert query in positive["held"], case_id + ": positive replay control failed"
        observed, receipts = execute(case_id, registry, events)
        verdict = "ACCEPT" if query in observed["held"] else "REFUSE"
        assert verdict == case["expected"]["verdict"], case_id + ": unexpected native verdict"
        assert path.read_bytes() == raw, case_id + ": fixture modified"
        results.append({"id": case_id, "source_sha256": hashlib.sha256(raw).hexdigest(),
                        "expected": case["expected"], "observed": verdict, "native_query": query,
                        "native_result": observed, "positive_control": positive,
                        "native_inputs": receipts, "positive_inputs": positive_inputs, "full_fixture_contract": True,
                        "translation_fidelity": fidelity})
    source_path = ROOT / "oracle/checkout/tests/test_verdict_provenance.py"
    results[-1]["pinned_source_sha256"] = hashlib.sha256(source_path.read_bytes()).hexdigest()
    results[-1]["positive_corpus_control"] = True
    record = {"schema": "gp-phase2-native-slice/v1", "case_count": len(results),
              "complete_ten_case_slice": False, "g2_pass": False,
              "runner_sha256": hashlib.sha256(EXE.read_bytes()).hexdigest(),
              "adapter_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
              "cases": results,
              "remaining_slice_behaviors": [
                  "non-exhaustive cover", "independent checked support and targeted retraction",
                  "failed retry", "real supersession branch-order fixture", "K2 narrowing",
                  "earned consequence", "proved-overlap conflict"]}
    spec = importlib.util.spec_from_file_location("lifecycle_slice", ROOT / "tools/run-phase2-lifecycle-slice.py")
    lifecycle = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(lifecycle)
    lifecycle_path = ROOT / "reports/PHASE-2-LIFECYCLE-SLICE.json"
    operational = lifecycle.run(lifecycle_path)
    record["cases"].extend(operational["cases"])
    record["case_count"] = len(record["cases"])
    record["execution_counts"] = {"receipt_path_cases": 4, "receipt_positive_contrasts": 3,
                                  "lifecycle_cases": 3, "lifecycle_branch_folds": 6}
    record["lifecycle_report_sha256"] = hashlib.sha256(lifecycle_path.read_bytes()).hexdigest()
    record["remaining_slice_behaviors"].remove("real supersession branch-order fixture")
    spec = importlib.util.spec_from_file_location("provenance_slice", ROOT / "tools/run-phase2-provenance-slice.py")
    provenance = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(provenance)
    provenance_path = ROOT / "reports/PHASE-2-PROVENANCE-SLICE.json"
    provenance_record = provenance.run(provenance_path)
    record["cases"].extend(row for row in provenance_record["cases"] if row["status"] == "EXECUTED")
    record["case_count"] = len(record["cases"])
    record["execution_counts"].update(provenance_cases=provenance_record["executed_case_count"],
                                    provenance_positive_contrasts=provenance_record["positive_contrasts"])
    record["provenance_report_sha256"] = hashlib.sha256(provenance_path.read_bytes()).hexdigest()
    assert len({row["id"] for row in record["cases"]}) == record["case_count"], "duplicate case count"
    spec = importlib.util.spec_from_file_location("conditional_cover", ROOT / "tools/run-phase2-conditional-cover-slice.py")
    conditional = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(conditional)
    conditional_path = ROOT / "reports/PHASE-2-CONDITIONAL-COVER-SLICE.json"
    conditional_record = conditional.run(conditional_path)
    record["cases"].extend(conditional_record["cases"])
    record["case_count"] = len(record["cases"])
    record["execution_counts"]["conditional_cover_cases"] = conditional_record["case_count"]
    record["conditional_cover_report_sha256"] = hashlib.sha256(conditional_path.read_bytes()).hexdigest()
    record["remaining_slice_behaviors"].remove("non-exhaustive cover")
    assert len({row["id"] for row in record["cases"]}) == record["case_count"]
    spec = importlib.util.spec_from_file_location("declaration_slice", ROOT / "tools/run-phase2-declaration-slice.py")
    declaration = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(declaration)
    declaration_path = ROOT / "reports/PHASE-2-DECLARATION-SLICE.json"
    declaration_record = declaration.run(declaration_path)
    record["cases"].extend(declaration_record["cases"])
    record["case_count"] = len(record["cases"])
    record["execution_counts"].update(declaration_cases=declaration_record["case_count"],
                                    declaration_original_folds=declaration_record["corpus_native_executions"],
                                    declaration_repaired_controls=declaration_record["repaired_control_executions"])
    record["declaration_report_sha256"] = hashlib.sha256(declaration_path.read_bytes()).hexdigest()
    assert len({row["id"] for row in record["cases"]}) == record["case_count"]
    spec = importlib.util.spec_from_file_location("conditional_partition", ROOT / "tools/run-phase2-conditional-partition-slice.py")
    partition = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(partition)
    partition_path = ROOT / "reports/PHASE-2-CONDITIONAL-PARTITION-SLICE.json"
    partition_record = partition.run(partition_path)
    record["cases"].extend(partition_record["cases"])
    record["case_count"] = len(record["cases"])
    record["execution_counts"].update(conditional_partition_cases=partition_record["case_count"],
                                    conditional_partition_native_folds=partition_record["native_executions"])
    record["conditional_partition_report_sha256"] = hashlib.sha256(partition_path.read_bytes()).hexdigest()
    assert len({row["id"] for row in record["cases"]}) == record["case_count"]
    spec = importlib.util.spec_from_file_location("conditional_routes", ROOT / "tools/run-phase2-conditional-routes-slice.py")
    routes_slice = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(routes_slice)
    routes_path = ROOT / "reports/PHASE-2-CONDITIONAL-ROUTES-SLICE.json"
    routes_record = routes_slice.run(routes_path)
    record["cases"].extend(routes_record["cases"])
    record["case_count"] = len(record["cases"])
    record["execution_counts"].update(conditional_routes_cases=routes_record["case_count"],
                                    conditional_routes_native_folds=routes_record["native_executions"])
    record["conditional_routes_report_sha256"] = hashlib.sha256(routes_path.read_bytes()).hexdigest()
    record["remaining_slice_behaviors"].remove("K2 narrowing")
    assert len({row["id"] for row in record["cases"]}) == record["case_count"]
    spec = importlib.util.spec_from_file_location("retraction_slice", ROOT / "tools/run-phase2-retraction-slice.py")
    retraction = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(retraction)
    retraction_path = ROOT / "reports/PHASE-2-RETRACTION-SLICE.json"
    retraction_record = retraction.run(retraction_path)
    record["cases"].extend(retraction_record["cases"])
    record["case_count"] = len(record["cases"])
    record["execution_counts"].update(retraction_cases=retraction_record["case_count"],
                                    retraction_original_folds=retraction_record["corpus_native_folds"],
                                    retraction_separate_controls=retraction_record["separate_control_folds"])
    record["retraction_report_sha256"] = hashlib.sha256(retraction_path.read_bytes()).hexdigest()
    assert len({row["id"] for row in record["cases"]}) == record["case_count"]
    spec = importlib.util.spec_from_file_location("checked_lifecycle_supplement", ROOT / "tools/run-phase2-checked-lifecycle-supplement.py")
    supplement = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(supplement)
    supplement_path = ROOT / "reports/PHASE-2-CHECKED-LIFECYCLE-SUPPLEMENT.json"
    supplemental = supplement.run(supplement_path)
    assert supplemental["distinct_corpus_passes_added"] == supplemental["new_corpus_cases"] == 0
    record["execution_counts"].update(checked_lifecycle_supplemental_scenarios=supplemental["supplemental_scenario_count"],
                                    checked_lifecycle_supplemental_checked_folds=supplemental["supplemental_checked_folds"],
                                    checked_lifecycle_supplemental_custody_folds=supplemental["supplemental_custody_folds"])
    record["checked_lifecycle_supplement_sha256"] = hashlib.sha256(supplement_path.read_bytes()).hexdigest()
    record["supplemental_slice_contracts"] = {
        "independent checked support and targeted retraction": "Two independently replay-validated X164 receipts; one survives targeted retraction, neither survives both retractions.",
        "failed retry": "Explicit failed/timeout attempts preserve prior native checked support; attempt-only controls are unheld.",
        "earned consequence": "Actual earned query reports held but caller-unclaimed X164, ranked by open obligations. This is direct checked-receipt closure, not a new K3-derived mathematical theorem."}
    for behavior in record["supplemental_slice_contracts"]:
        record["remaining_slice_behaviors"].remove(behavior)
    spec = importlib.util.spec_from_file_location("supersession_guards", ROOT / "tools/run-phase2-supersession-guards.py")
    guards = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(guards)
    guards_path = ROOT / "reports/PHASE-2-SUPERSESSION-GUARDS.json"
    guards_record = guards.run(guards_path)
    record["cases"].extend(guards_record["cases"])
    record["case_count"] = len(record["cases"])
    record["execution_counts"].update(supersession_guard_cases=guards_record["case_count"],
                                    supersession_guard_original_folds=guards_record["corpus_native_executions"],
                                    supersession_guard_separate_controls=guards_record["control_native_executions"])
    record["supersession_guards_report_sha256"] = hashlib.sha256(guards_path.read_bytes()).hexdigest()
    assert len({row["id"] for row in record["cases"]}) == record["case_count"]
    spec = importlib.util.spec_from_file_location("residual_successors", ROOT / "tools/run-phase2-residual-successors.py")
    residual = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(residual)
    residual_path = ROOT / "reports/PHASE-2-RESIDUAL-SUCCESSORS.json"
    residual_record = residual.run(residual_path)
    record["cases"].extend(residual_record["cases"])
    record["case_count"] = len(record["cases"])
    record["execution_counts"].update(residual_successor_cases=residual_record["case_count"],
                                    residual_successor_original_folds=residual_record["corpus_native_executions"],
                                    residual_successor_separate_controls=residual_record["control_native_executions"])
    record["residual_successors_report_sha256"] = hashlib.sha256(residual_path.read_bytes()).hexdigest()
    assert len({row["id"] for row in record["cases"]}) == record["case_count"]
    spec = importlib.util.spec_from_file_location("missing_authority", ROOT / "tools/run-phase2-missing-authority.py")
    missing = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(missing)
    missing_path = ROOT / "reports/PHASE-2-MISSING-AUTHORITY.json"
    missing_record = missing.run(missing_path)
    record["cases"].extend(missing_record["cases"])
    record["case_count"] = len(record["cases"])
    record["execution_counts"].update(missing_authority_cases=missing_record["case_count"],
                                    missing_authority_checked_folds=missing_record["corpus_native_checked_folds"],
                                    missing_authority_custody_folds=missing_record["corpus_native_custody_folds"],
                                    missing_authority_separate_contrasts=missing_record["separate_contrast_scenarios"])
    record["missing_authority_report_sha256"] = hashlib.sha256(missing_path.read_bytes()).hexdigest()
    assert len({row["id"] for row in record["cases"]}) == record["case_count"]
    spec = importlib.util.spec_from_file_location("conditional_point_routes", ROOT / "tools/run-phase2-conditional-point-routes.py")
    point_routes = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(point_routes)
    point_path = ROOT / "reports/PHASE-2-CONDITIONAL-POINT-ROUTES.json"
    point_record = point_routes.run(point_path)
    record["cases"].extend(point_record["cases"])
    record["case_count"] = len(record["cases"])
    record["execution_counts"].update(conditional_point_route_cases=point_record["case_count"],
                                    conditional_point_route_folds=point_record["corpus_executions"],
                                    conditional_point_route_separate_controls=point_record["separate_control_executions"])
    record["conditional_point_routes_report_sha256"] = hashlib.sha256(point_path.read_bytes()).hexdigest()
    assert len({row["id"] for row in record["cases"]}) == record["case_count"]
    spec = importlib.util.spec_from_file_location("recorded_use_coverage", ROOT / "tools/run-phase2-recorded-use-coverage.py")
    coverage = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(coverage)
    coverage_path = ROOT / "reports/PHASE-2-RECORDED-USE-COVERAGE.json"
    coverage_record = coverage.run(coverage_path)
    record["cases"].extend(coverage_record["cases"])
    record["case_count"] = len(record["cases"])
    record["execution_counts"].update(recorded_use_coverage_cases=coverage_record["case_count"],
                                    recorded_use_coverage_folds=coverage_record["corpus_executions"],
                                    recorded_use_coverage_separate_controls=coverage_record["separate_control_executions"])
    record["recorded_use_coverage_report_sha256"] = hashlib.sha256(coverage_path.read_bytes()).hexdigest()
    assert len({row["id"] for row in record["cases"]}) == record["case_count"]
    spec = importlib.util.spec_from_file_location("conditional_admission_scope", ROOT / "tools/run-phase2-conditional-admission-scope.py")
    admission_scope = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(admission_scope)
    admission_path = ROOT / "reports/PHASE-2-CONDITIONAL-ADMISSION-SCOPE.json"
    admission_record = admission_scope.run(admission_path)
    record["cases"].extend(admission_record["cases"])
    record["case_count"] = len(record["cases"])
    record["execution_counts"].update(conditional_admission_scope_cases=admission_record["case_count"],
                                    conditional_admission_scope_folds=admission_record["corpus_executions"],
                                    conditional_admission_scope_separate_controls=admission_record["separate_control_executions"])
    record["conditional_admission_scope_report_sha256"] = hashlib.sha256(admission_path.read_bytes()).hexdigest()
    assert len({row["id"] for row in record["cases"]}) == record["case_count"]
    spec = importlib.util.spec_from_file_location("conditional_theorem_transport", ROOT / "tools/run-phase2-conditional-theorem-transport.py")
    theorem_transport = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(theorem_transport)
    transport_path = ROOT / "reports/PHASE-2-CONDITIONAL-THEOREM-TRANSPORT.json"
    transport_record = theorem_transport.run(transport_path)
    record["cases"].extend(transport_record["cases"])
    record["case_count"] = len(record["cases"])
    record["execution_counts"].update(conditional_theorem_transport_cases=transport_record["case_count"],
                                    conditional_theorem_transport_folds=transport_record["corpus_executions"],
                                    conditional_theorem_transport_separate_controls=transport_record["separate_control_executions"])
    record["conditional_theorem_transport_report_sha256"] = hashlib.sha256(transport_path.read_bytes()).hexdigest()
    assert len({row["id"] for row in record["cases"]}) == record["case_count"]
    spec = importlib.util.spec_from_file_location("section_provenance", ROOT / "tools/run-phase2-section-provenance.py")
    section_provenance = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(section_provenance)
    section_path = ROOT / "reports/PHASE-2-SECTION-PROVENANCE.json"
    section_record = section_provenance.run(section_path)
    record["cases"].extend(section_record["cases"])
    record["case_count"] = len(record["cases"])
    record["execution_counts"].update(section_provenance_cases=section_record["case_count"],
                                    section_provenance_folds=section_record["corpus_executions"],
                                    section_provenance_separate_controls=section_record["separate_control_executions"])
    record["section_provenance_report_sha256"] = hashlib.sha256(section_path.read_bytes()).hexdigest()
    assert len({row["id"] for row in record["cases"]}) == record["case_count"]
    spec = importlib.util.spec_from_file_location("context_reach", ROOT / "tools/run-phase2-context-reach.py")
    context_reach = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(context_reach)
    reach_path = ROOT / "reports/PHASE-2-CONTEXT-REACH.json"
    reach_record = context_reach.run(reach_path)
    record["cases"].extend(reach_record["cases"])
    record["case_count"] = len(record["cases"])
    record["execution_counts"].update(context_reach_cases=reach_record["case_count"],
                                    context_reach_folds=reach_record["corpus_executions"],
                                    context_reach_separate_controls=reach_record["separate_control_executions"])
    record["context_reach_report_sha256"] = hashlib.sha256(reach_path.read_bytes()).hexdigest()
    assert len({row["id"] for row in record["cases"]}) == record["case_count"]
    spec = importlib.util.spec_from_file_location("open_premise_guard", ROOT / "tools/run-phase2-open-premise-guard.py")
    open_premise_guard = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(open_premise_guard)
    guard_path = ROOT / "reports/PHASE-2-OPEN-PREMISE-GUARD.json"
    guard_record = open_premise_guard.run(guard_path)
    record["cases"].extend(guard_record["cases"])
    record["case_count"] = len(record["cases"])
    record["execution_counts"].update(open_premise_guard_cases=guard_record["case_count"],
                                    open_premise_guard_folds=guard_record["corpus_executions"],
                                    open_premise_guard_separate_controls=guard_record["separate_control_executions"])
    record["open_premise_guard_report_sha256"] = hashlib.sha256(guard_path.read_bytes()).hexdigest()
    assert len({row["id"] for row in record["cases"]}) == record["case_count"]
    spec = importlib.util.spec_from_file_location("unreplayed_evidence", ROOT / "tools/run-phase2-unreplayed-evidence.py")
    unreplayed_evidence = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(unreplayed_evidence)
    unreplayed_path = ROOT / "reports/PHASE-2-UNREPLAYED-EVIDENCE.json"
    unreplayed_record = unreplayed_evidence.run(unreplayed_path)
    record["cases"].extend(unreplayed_record["cases"])
    record["case_count"] = len(record["cases"])
    record["execution_counts"].update(unreplayed_evidence_cases=unreplayed_record["case_count"],
                                    unreplayed_evidence_folds=unreplayed_record["corpus_executions"],
                                    unreplayed_evidence_separate_controls=unreplayed_record["separate_control_executions"])
    record["unreplayed_evidence_report_sha256"] = hashlib.sha256(unreplayed_path.read_bytes()).hexdigest()
    assert len({row["id"] for row in record["cases"]}) == record["case_count"]
    spec = importlib.util.spec_from_file_location("rule_shape", ROOT / "tools/run-phase2-rule-shape.py")
    rule_shape = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(rule_shape)
    shape_path = ROOT / "reports/PHASE-2-RULE-SHAPE.json"
    shape_record = rule_shape.run(shape_path)
    record["cases"].extend(shape_record["cases"])
    record["case_count"] = len(record["cases"])
    record["execution_counts"].update(rule_shape_cases=shape_record["case_count"],
                                    rule_shape_folds=shape_record["corpus_executions"],
                                    rule_shape_separate_controls=shape_record["separate_control_executions"])
    record["rule_shape_report_sha256"] = hashlib.sha256(shape_path.read_bytes()).hexdigest()
    assert len({row["id"] for row in record["cases"]}) == record["case_count"]
    spec = importlib.util.spec_from_file_location("lifecycle_concerns", ROOT / "tools/run-phase2-lifecycle-concerns.py")
    lifecycle_concerns = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(lifecycle_concerns)
    concerns_path = ROOT / "reports/PHASE-2-LIFECYCLE-CONCERNS.json"
    concerns_record = lifecycle_concerns.run(concerns_path)
    record["cases"].extend(concerns_record["cases"])
    record["case_count"] = len(record["cases"])
    record["execution_counts"].update(lifecycle_concern_cases=concerns_record["case_count"],
                                    lifecycle_concern_folds=concerns_record["corpus_executions"],
                                    lifecycle_concern_separate_controls=concerns_record["separate_control_executions"])
    record["lifecycle_concerns_report_sha256"] = hashlib.sha256(concerns_path.read_bytes()).hexdigest()
    assert len({row["id"] for row in record["cases"]}) == record["case_count"]
    spec = importlib.util.spec_from_file_location("conflict_demonstration", ROOT / "tools/run-phase2-conflict-demonstration.py")
    conflict = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(conflict)
    conflict_path = ROOT / "reports/PHASE-2-CONFLICT-DEMONSTRATION.json"
    conflict_record = conflict.run(conflict_path)
    assert conflict_record["required_slice_behavior_satisfied"] and not conflict_record["g2_pass"]
    record["conflict_demonstration_report_sha256"] = hashlib.sha256(conflict_path.read_bytes()).hexdigest()
    record["remaining_slice_behaviors"].remove("proved-overlap conflict")
    record["complete_ten_case_slice"] = len(record["cases"]) >= 10 and not record["remaining_slice_behaviors"]
    output.write_bytes((json.dumps(record, indent=2) + "\n").encode("utf-8"))
    print("Native slice: 79 unchanged fixtures passed; replay contrasts, branch orders and declaration duplicates checked separately.")
    return record

if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, default=ROOT / "reports/PHASE-2-SLICE.json")
    args = parser.parse_args()
    run(args.output)
