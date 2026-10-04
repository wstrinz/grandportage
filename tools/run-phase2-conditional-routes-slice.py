"""Execute two unchanged conditional universal-premise route fixtures."""
import argparse
import ast
import hashlib
import json
from pathlib import Path
import subprocess
EXE_SUFFIX = ".exe" if __import__("os").name == "nt" else ""
ROOT = Path(__file__).resolve().parents[1]
SCRATCH = ROOT / "tmp/phase2-conditional-routes"
EXE = ROOT / ("phase2/lean/.lake/build/bin/gp_conditional_routes_fixture" + EXE_SUFFIX)
CASES = ("GP-X177", "GP-X178")
PIN = "ac4155787207e2847d248cffed7be871d5dcd577"
ORACLE_COMMITS = {PIN, __import__("json").loads((ROOT / "oracle/PIN.json").read_text(encoding="utf-8-sig")).get("public_commit", PIN)}
SOURCE = "tests/test_adversarial.py"
ANCHORS = {"GP-X177": (1429,"test_an_argument_can_now_combine_two_premises"),
           "GP-X178": (1465,"test_premises_that_never_meet_are_a_fold_error")}
HASHES = {"GP-X177": "11bed549fcac8804b86b0926812855b2c93232699e567c67a99c9e3c1a0a3b27",
          "GP-X178": "898649e2bf114370e452ea0537b0afc3a952aa654216f57e661bb6a97050bc85"}
MODEL = "contexts=[tight,loose,side];first:tight->loose:equations_forgotten;second:tight->side:equations_forgotten"
CONCLUSION = "both premises have licensed routes to the tight context"
HYPOTHESES = ["loose: a universal property (first selected predicate)",
    "side: a universal property (second selected predicate)",
    "first: tight subset loose (equations_forgotten)", "second: tight subset side (equations_forgotten)"]

def require(condition, message):
    if not condition:
        raise ValueError(message)

def sha(raw):
    return hashlib.sha256(raw).hexdigest()

def source_contract():
    checkout = ROOT / "oracle/checkout"
    pin_raw = (ROOT / "oracle/PIN.json").read_bytes()
    require(json.loads(pin_raw)["commit"] == PIN, "source pin changed")
    git = ["git","-c","safe.directory=" + str(checkout),"-C",str(checkout)]
    require(subprocess.check_output(git + ["rev-parse","HEAD"],text=True).strip() in ORACLE_COMMITS, "checkout pin changed")
    raw = subprocess.check_output(git + ["show","HEAD:" + SOURCE])
    require((checkout / SOURCE).read_bytes() == raw, "pinned source changed")
    text = raw.decode("utf-8")
    tree = ast.parse(text)
    functions = {}
    for case_id,(line,name) in ANCHORS.items():
        node = next(n for n in tree.body if isinstance(n,ast.FunctionDef) and n.name == name)
        require(node.lineno == line, "source anchor moved")
        segment = "\n".join(text.splitlines()[line-1:node.end_lineno])
        needles = ('assert len(i["premises"]) == 2','"both premises must land together"') if case_id == "GP-X177" else (
            "pytest.raises(S.GraphError)",'"do not meet"','"LOOSE" in msg and "SIDE" in msg')
        require(all(needle in segment for needle in needles), "source endpoint contract changed")
        functions[case_id] = {"line":line,"anchor":"def " + name + "(",
                             "function_sha256":sha(segment.encode("utf-8"))}
    return {"commit":PIN,"path":SOURCE,"file_sha256":sha(raw),"pin_file_sha256":sha(pin_raw),
        "functions":functions,"boundary":"Literal unchanged fixture abstraction, not reconstruction of historical graph statements/routes or renderer behavior."}

def checked_case(case_id, tags, routes, baseline):
    raw = (ROOT / ("corpus/must/" + case_id + ".json")).read_bytes()
    case = json.loads(raw)
    tag = next(r for r in tags["cases"] if r["id"] == case_id)
    prior = next(r for r in baseline["cases"] if r["id"] == case_id)
    require(sha(raw) == HASHES[case_id] == tag["sha256"] == prior["sha256"], "fixture bytes changed")
    require(case["expected"] == prior["expected"], "expectation changed")
    require(tag["primary_layer"] == "kernel" and tag["full_contract_required"] is True and tag["g2_kernel_eligible"] is True, "layer changed")
    line,name = ANCHORS[case_id]
    require(case["sources"] == [{"repository":"gp-v037","commit":PIN,"path":SOURCE,
            "line":line,"anchor":"def " + name + "("}], "fixture source pointer changed")
    expected_route = {"kind":"joint_premises","layer":"conditional_premise_routes",
        "limitation":"Legacy transport/coverage rule under declared premises; not logical entailment or GP 0.50 held authority. Partition verification is explicitly assumed for rule isolation. Whole checker and renderer also execute without an external CAS."}
    require(routes["commit"] == PIN and routes["routes"][case_id] == expected_route, "legacy route changed")
    return case,raw,tag

def execute(raw,label,mode="normal",runner=EXE):
    SCRATCH.mkdir(parents=True,exist_ok=True)
    path = SCRATCH / (label + ".json")
    path.write_bytes(raw)
    result = subprocess.run([str(runner),str(path),sha(raw),mode],cwd=ROOT,
        capture_output=True,text=True,encoding="utf-8",check=True)
    require(path.read_bytes() == raw, "input bytes changed")
    return json.loads(result.stdout),sha(raw)

def binding(digest,slot,scope):
    statement = CONCLUSION if slot == "joint" else "premise:" + slot + ";a universal property;selected-predicate:" + slot
    return {"statementHash":statement,"scopeHash":digest + ":" + scope,"modelHash":MODEL,
            "inputHashes":[digest],"authority":"test-only-named-route-assumptions",
            "authorityVersion":1,"kernelVersion":1}

def expected_records(case,digest):
    routes = [p["route"] for p in case["inputs"]["premises"]]
    licensed = [route == [{"relation":name,"direction":"reverse"}] for route,name in zip(routes,("first","second"))]
    records = []
    for wid,claim,slot,scope in ((10,1,"first","loose"),(20,2,"second","side")):
        records.append({"id":wid,"claim":claim,"version":1,"binding":binding(digest,slot,scope),
            "evidence":{"kind":"receipt","data":"given:" + scope + ":a universal property:" + slot}})
    for valid,wid,claim,slot,dependency in ((licensed[0],110,11,"first",10),(licensed[1],120,12,"second",20)):
        if valid:
            records.append({"id":wid,"claim":claim,"version":1,"binding":binding(digest,slot,"tight"),
                "evidence":{"kind":"narrow","premise":dependency}})
    deps = [110 if licensed[0] else 10,120 if licensed[1] else 20]
    records.append({"id":30,"claim":3,"version":1,"binding":binding(digest,"joint","conditional-route-licensing"),
        "evidence":{"kind":"derived","premises":deps,"sideReceipt":"exact-named-route-join"}})
    return sorted(records,key=lambda r:r["id"]),licensed,deps

def verify(case,raw,observed):
    digest = sha(raw)
    records,licensed,deps = expected_records(case,digest)
    require(observed["conditional"] is True and observed["case"] == case["id"] and
        observed["source_digest"] == digest and observed["literal_inputs"] == case["inputs"] and
        observed["conclusion"] == CONCLUSION, "literal fixture/conditional boundary changed")
    require(observed["route_licensed"] == licensed and observed["argument_dependency_ids"] == deps and
        observed["route_endpoints"] == ["tight" if licensed[0] else "loose","tight" if licensed[1] else "side"],
        "routes/endpoints/dependencies differ")
    require(observed["named_hypotheses"] == HYPOTHESES and observed["narrow_checker"] == "GP50.Semantic.acceptsNarrow",
            "named assumptions or actual K2 checker differs")
    claims = sorted(r["claim"] for r in records)
    currents = [{"claim":r["claim"],"version":1,"binding":r["binding"]} for r in sorted(records,key=lambda r:r["claim"])]
    expected_snapshot = {"domain":claims,"currents":currents,"warrants":records,"retracted":[],"successors":[]}
    require(observed["snapshot"] == expected_snapshot, "complete resolved record contract differs")
    supports = [10,20] + ([110] if licensed[0] else []) + ([120] if licensed[1] else []) + ([30] if all(licensed) else [])
    held = sorted(r["claim"] for r in records if r["id"] in supports)
    require(observed["state"] == {"status":"OK","domain":claims,"held":held,"supports":supports,
        "live_warrants":[r["id"] for r in records],"warrant_count":len(records),"current_count":len(records),
        "retracted":[],"successors":[]}, "actual fold/held closure differs")
    return "ACCEPT" if 3 in held else "REFUSE"

def run(output,runner=EXE):
    source = source_contract()
    paths = {"layer_tags":"corpus/LAYER-TAGS.json","routes":"oracle/ROUTES.json",
             "baseline":"reports/PHASE-2-BASELINE.json","pin":"oracle/PIN.json"}
    metadata = {key:(ROOT / path).read_bytes() for key,path in paths.items()}
    tags,routes,baseline = (json.loads(metadata[key]) for key in ("layer_tags","routes","baseline"))
    runner_hash = sha(runner.read_bytes())
    rows = []
    for case_id in CASES:
        case,raw,tag = checked_case(case_id,tags,routes,baseline)
        outputs,hashes = {},{}
        for mode in ("normal","reverse","duplicates"):
            observed,input_hash = execute(raw,case_id + "-" + mode,mode,runner)
            require(verify(case,raw,observed) == case["expected"]["verdict"], "conditional verdict differs")
            outputs[mode],hashes[mode] = observed,input_hash
        require(all({k:v for k,v in o.items() if k != "mode"} ==
            {k:v for k,v in outputs["normal"].items() if k != "mode"} for o in outputs.values()),"orders/duplicates differ")
        require((ROOT / ("corpus/must/" + case_id + ".json")).read_bytes() == raw, "fixture changed")
        rows.append({"id":case_id,"source_sha256":sha(raw),"expected":case["expected"],"sources":case["sources"],
            "layer_entry":tag,"legacy_route":routes["routes"][case_id],"observed":verify(case,raw,outputs["normal"]),
            "executed":True,"full_fixture_contract":True,"conditional_conclusion_only":True,
            "literal_inputs":case["inputs"],"native_results":outputs,"native_input_sha256":hashes,
            "named_hypotheses":HYPOTHESES,
            "translation_fidelity":"Distinct arbitrary selected predicates for both identically worded premises survive scope restriction. Empty routes stay empty and retain their source endpoint. The conclusion asserts licensed routes, not only semantic property truth."})
    require(source_contract() == source and sha(runner.read_bytes()) == runner_hash, "source/runner changed")
    for key,path in paths.items():
        require((ROOT / path).read_bytes() == metadata[key], "registry/pin/baseline changed")
    report = {"schema":"gp-phase2-conditional-routes-slice/v1","case_count":2,"native_executions":6,"cases":rows,
        "source_contract":source,"registry_sha256":{k:sha(v) for k,v in metadata.items()},
        "runner_path":str(runner),"runner_sha256":runner_hash,"adapter_sha256":sha(Path(__file__).read_bytes()),
        "harness_sha256":sha((ROOT / "phase2/lean/Tests/ConditionalRoutes.lean").read_bytes()),
        "test_source_sha256":sha((ROOT / "tests/test_phase2_conditional_routes.py").read_bytes()),
        "proofs":["ConditionalRoutes.subset_sound","ConditionalRoutes.routes_composition_sound",
            "ConditionalRoutes.actual_validator_sound","ConditionalRoutes.actual_fold_held_sound",
            "ConditionalRoutes.native_fold_held_sound"],
        "axioms":["propext","Quot.sound"],"production_profile_adoption":False,
        "underlying_algebraic_truth_certified":False,"g2_pass":False,
        "mechanism":"Existing GP50.Semantic.acceptsNarrow executes individual K2 restrictions; an exact K3 rule joins the two supplied licensed routes. Parent review qualifies the required K2 example through actual acceptsNarrow execution, fixed selected predicates/model and proved inclusion, under the approved conditional hypotheses.",
        "guarantee":"For every Point type and every named tight/loose/side interpretation with two fixed predicate identities satisfying the four explicit theory hypotheses, actual held claims have their registered meanings. Licensing is global, including when regions are empty.",
        "binding_boundary":"Exact selected-predicate/statement/model data plus host SHA-256 of unchanged fixture bytes bind registered warrants and clauses. The same executable admission is point-type independent; assumptions certify conditional conclusions only."}
    output.write_bytes((json.dumps(report,indent=2) + "\n").encode("utf-8"))
    print("Conditional routes: 2 unchanged fixtures, 6 native folds; ACCEPT/REFUSE under named hypotheses.")
    return report

if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--output",type=Path,default=ROOT / "reports/PHASE-2-CONDITIONAL-ROUTES-SLICE.json")
    parser.add_argument("--runner",type=Path,default=EXE)
    args = parser.parse_args()
    run(args.output,args.runner)
