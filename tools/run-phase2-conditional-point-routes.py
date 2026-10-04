"""Native conditional routes for universal and global exhibited-point premises."""
import argparse
import ast
import copy
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess

EXE_SUFFIX = ".exe" if __import__("os").name == "nt" else ""
ELAN_HOME = Path(__import__("os").environ.get("ELAN_HOME") or Path.home() / ".elan")
ROOT=Path(__file__).resolve().parents[1]
PACKAGE=ROOT/"phase2/lean"
HARNESS=PACKAGE/"Tests/ConditionalPointRoutes.lean"
SCRATCH=ROOT/"tmp/phase2-conditional-point-routes"
TOOLCHAIN=ELAN_HOME/"toolchains"/(ROOT/"phase2/lean/lean-toolchain").read_text(encoding="utf-8").strip().replace("/","--").replace(":","---")
LAKE=TOOLCHAIN/("bin/lake" + EXE_SUFFIX)
LEAN=TOOLCHAIN/("bin/lean" + EXE_SUFFIX)
CHECKER=TOOLCHAIN/("bin/leanchecker" + EXE_SUFFIX)
OLEAN=SCRATCH/"Tests/ConditionalPointRoutes.olean"
WRAPPER=SCRATCH/"Run.lean"
PIN="ac4155787207e2847d248cffed7be871d5dcd577"
ORACLE_COMMITS = {PIN, __import__("json").loads((ROOT / "oracle/PIN.json").read_text(encoding="utf-8-sig")).get("public_commit", PIN)}
CASES=("GP-X179","GP-X180")
HASHES={"GP-X179":"6753b6d331b21b26afc1064c925618447610d96bb4db1f3fd1860225add82b67",
        "GP-X180":"69ee5dc417caa4a683b14c37f3c13ba1a472bab0e586edad2f1af50e2d20c54b"}
MODEL="contexts=[tight,loose,side];first:tight->loose:equations_forgotten;second:tight->side:equations_forgotten;selected-witness=side-premise"
STATEMENTS={
 "universal":"universal_property;a universal property;selected-predicate:universal-premise",
 "side":"exhibited_point;a point in the relaxed side model;selected-model:side;selected-witness:side-premise",
 "tight":"exhibited_point;same supplied exhibited point;selected-model:tight;selected-witness:side-premise",
 "join":"both premises have licensed routes to the tight context"}
CONTROL_MODES=("withheld_universal","withheld_point","wrong_binding","wrong_point_identity","wrong_model",
               "wrong_dependency","pointwise_laundering","justified_tight_membership")

def require(ok,message):
    if not ok:
        raise ValueError(message)

def encoded(v):
    return json.dumps(v,sort_keys=True,separators=(",",":"),ensure_ascii=True)

def sha(raw):
    return hashlib.sha256(raw).hexdigest()

def command(args,env=None):
    p=subprocess.run(list(map(str,args)),cwd=PACKAGE,env=env,capture_output=True,text=True,encoding="utf-8")
    require(p.returncode==0,"command failed: "+str(args)+"\n"+p.stdout+p.stderr)
    return p.stdout

def build_inputs():
    paths = sorted((PACKAGE/"GP50").glob("*.lean")) + sorted((PACKAGE/".lake/build/lib/lean/GP50").glob("*.olean"))
    paths += [PACKAGE/"lean-toolchain", PACKAGE/"lakefile.toml", LEAN, CHECKER]
    return {str(p):sha(p.read_bytes()) for p in paths}

def build():
    SCRATCH.mkdir(parents=True,exist_ok=True);OLEAN.parent.mkdir(parents=True,exist_ok=True)
    env=os.environ.copy();env["TEMP"]=str(PACKAGE/".lake/tmp");env["TMP"]=env["TEMP"]
    stamp=SCRATCH/"build.json";source_hash=sha(HARNESS.read_bytes());inputs=build_inputs()
    if stamp.exists() and OLEAN.exists() and WRAPPER.exists():
        old=json.loads(stamp.read_bytes())
        if old.get("build_input_hashes")==inputs and old["harness_sha256"]==source_hash and old["olean_sha256"]==sha(OLEAN.read_bytes()) and old["wrapper_sha256"]==sha(WRAPPER.read_bytes()):
            return old
    args=[LAKE,"env","lean","-o",OLEAN,"Tests/ConditionalPointRoutes.lean"]
    log=command(args,env)
    (SCRATCH/"compile.log").write_text(log,encoding="utf-8")
    require("sorryAx" not in log and "error:" not in log,"unproved harness")
    axioms=sorted(set(a.strip() for group in re.findall(r"depends on axioms: \[([^\]]*)\]",log)
                      for a in group.split(",") if a.strip()))
    require(set(axioms)<= {"propext","Quot.sound","Classical.choice"} and len(re.findall(r"depends on axioms:",log))==8,
            "axiom audit incomplete")
    base_path=command([LAKE,"env","python","-c","import os;print(os.environ.get('LEAN_PATH',''))"],env).strip()
    env["LEAN_PATH"]=str(SCRATCH)+os.pathsep+base_path
    check_args=[CHECKER,"-v","Tests.ConditionalPointRoutes"]
    checked=command(check_args,env)
    (SCRATCH/"checker.log").write_text(checked,encoding="utf-8")
    WRAPPER.write_text("import Tests.ConditionalPointRoutes\n",encoding="utf-8")
    require(build_inputs()==inputs,"build dependencies changed during compilation")
    result={"build_input_hashes":inputs,"harness_sha256":source_hash,"olean_sha256":sha(OLEAN.read_bytes()),
            "wrapper_sha256":sha(WRAPPER.read_bytes()),"lean_path":env["LEAN_PATH"],"axioms":axioms,
            "compile_command":list(map(str,args)),"compile_exit_code":0,"compile_log_sha256":sha(log.encode()),
            "checker_command":list(map(str,check_args)),"checker_exit_code":0,
            "checker_log_sha256":sha(checked.encode()),"kernel_checked":True}
    stamp.write_text(json.dumps(result,indent=2),encoding="utf-8")
    return result

def source_contract():
    checkout=ROOT/"oracle/checkout"
    git=["git","-c","safe.directory="+str(checkout),"-C",str(checkout)]
    require(json.loads((ROOT/"oracle/PIN.json").read_bytes())["commit"]==PIN,"pin changed")
    require(subprocess.check_output(git+["rev-parse","HEAD"],text=True).strip() in ORACLE_COMMITS,"checkout changed")
    path="tests/test_adversarial.py";raw=subprocess.check_output(git+["show","HEAD:" +path])
    require((checkout/path).read_bytes()==raw,"pinned source modified")
    text=raw.decode("utf-8");name="test_a_refused_leg_refuses_the_whole_argument"
    node=next(n for n in ast.parse(text).body if isinstance(n,ast.FunctionDef) and n.name==name)
    require(node.lineno==1494,"anchor moved")
    segment="\n".join(text.splitlines()[node.lineno-1:node.end_lineno])
    require('assert not ok' in segment and '[True, False]' in segment and 'EXHIBITED' in segment,"source contract changed")
    return {"commit":PIN,"path":path,"line":1494,"anchor":"def "+name+"(",
            "file_sha256":sha(raw),"function_sha256":sha(segment.encode())}

def checked_case(case_id,tags,routes):
    raw=(ROOT/"corpus/must"/(case_id+".json")).read_bytes();case=json.loads(raw)
    row=next(r for r in tags["cases"] if r["id"]==case_id)
    require(sha(raw)==HASHES[case_id]==row["sha256"],"fixture bytes changed")
    require(row["primary_layer"]=="kernel" and row["full_contract_required"] is True and row["g2_kernel_eligible"] is True,
            "layer contract changed")
    require(case["expected"]["verdict"]=="REFUSE" and case["sources"]==[{"repository":"gp-v037","commit":PIN,
            "path":"tests/test_adversarial.py","line":1494,"anchor":"def test_a_refused_leg_refuses_the_whole_argument("}],
            "source/expectation changed")
    require(routes["commit"]==PIN and routes["routes"][case_id]=={
        "kind":"joint_premises","layer":"conditional_premise_routes",
        "limitation":"Legacy transport/coverage rule under declared premises; not logical entailment or GP 0.50 held authority. Partition verification is explicitly assumed for rule isolation. Whole checker and renderer also execute without an external CAS."},"route changed")
    return case,raw,row

def execute(raw,label,mode,compiled=None):
    compiled=build() if compiled is None else compiled
    path=SCRATCH/(label+".fixture.json");path.write_bytes(raw)
    env=os.environ.copy();env["LEAN_PATH"]=compiled["lean_path"]
    env["TEMP"]=str(PACKAGE/".lake/tmp");env["TMP"]=env["TEMP"]
    args=[LEAN,"--run",WRAPPER,path,sha(raw),mode]
    result=command(args,env)
    return json.loads(result.strip().splitlines()[-1]),sha(path.read_bytes())

def binding(source,formula,scope):
    return {"statementHash":STATEMENTS[formula],"scopeHash":source+":"+scope,"modelHash":MODEL,
            "inputHashes":[source],"authority":"test-only-supplied-universal-and-exhibited-point",
            "authorityVersion":1,"kernelVersion":1}

def records(case,source,mode):
    point_first=case["id"]=="GP-X180"
    deps=[120,110] if point_first else [110,120]
    def record(id,claim,formula,scope,evidence):
        return {"id":id,"claim":claim,"version":1,"binding":binding(source,formula,scope),"evidence":evidence}
    rows=[record(10,1,"universal","loose",{"kind":"receipt","data":"given:loose:universal-property"}),
          record(20,2,"side","global-conditional-theory",{"kind":"receipt","data":"given:side:exhibited-point"}),
          record(110,11,"universal","tight",{"kind":"narrow","premise":10}),
          record(120,12,"tight","global-conditional-theory",{"kind":"narrow","premise":20}),
          record(30,3,"join","global-conditional-theory",
                 {"kind":"derived","premises":deps,"sideReceipt":"join:universal-and-same-exhibited-point"})]
    byid={r["id"]:r for r in rows}
    if mode=="withheld_universal": rows.remove(byid[10])
    if mode=="withheld_point": rows.remove(byid[20])
    if mode=="wrong_binding": byid[110]["binding"]["inputHashes"]=["changed"]
    if mode=="wrong_point_identity": byid[120]["binding"]=binding(source,"side","global-conditional-theory")
    if mode=="wrong_model": byid[120]["binding"]["modelHash"]="other selected model"
    if mode=="wrong_dependency": byid[110]["evidence"]={"kind":"narrow","premise":20}
    if mode=="pointwise_laundering": byid[120]["binding"]=binding(source,"side","tight")
    if mode=="justified_tight_membership":
        byid[120]["evidence"]={"kind":"receipt","data":"additional:justified-tight-membership-of-same-witness"}
    return sorted(rows,key=lambda r:r["id"]),deps

def verify(case,raw,observed,mode):
    source=sha(raw);rows,deps=records(case,source,mode)
    require(observed["conditional"] is True and observed["literal_fixture"]==case and observed["literal_inputs"]==case["inputs"]
            and observed["source_digest"]==source and observed["case"]==case["id"] and observed["mode"]==mode,
            "complete literal fixture differs")
    require(observed["narrow_checks"]=={"universal":True,"exhibited_point":False},"actual K2 results differ")
    licensed=[False,True] if case["id"]=="GP-X180" else [True,False]
    if mode=="justified_tight_membership": licensed=[True,True]
    if mode in ("withheld_universal","wrong_binding","wrong_dependency"): licensed=[False,False]
    require(observed["route_licensed"]==licensed and observed["argument_dependency_ids"]==deps
            and observed["additional_tight_membership"]==(mode=="justified_tight_membership"),
            "literal premise order/licensing/dependencies differ")
    require(observed["point_statement_scope"]=="global-conditional-theory" and
            observed["countermodel"]=={"tight_empty":True,"side_inhabited":True,"same_witness_not_tight":True},
            "existential/global/countermodel boundary differs")
    ids=sorted(r["claim"] for r in rows)
    currents=[{k:r[k] for k in ("claim","version","binding")} for r in sorted(rows,key=lambda r:r["claim"])]
    require(observed["snapshot"]=={"domain":ids,"currents":currents,"warrants":rows,"retracted":[],"successors":[]},
            "complete native snapshot differs")
    supports=[10,20,110]
    if mode=="withheld_universal": supports=[20]
    if mode=="withheld_point": supports=[10,110]
    if mode in ("wrong_binding","wrong_dependency"): supports=[10,20]
    if mode=="justified_tight_membership": supports=[10,20,120,110,30]
    held=sorted(r["claim"] for r in rows if r["id"] in supports)
    require(observed["state"]=={"status":"OK","held":held,"supports":supports,"domain":ids,
        "live_warrants":[r["id"] for r in rows],"warrant_count":len(rows),"current_count":len(rows),
        "retracted":[],"successors":[]},"actual fold held/support state differs")
    return "ACCEPT" if 3 in observed["state"]["held"] else "REFUSE"

def run(output):
    compiled=build();source=source_contract()
    protected=[ROOT/p for p in ("corpus/LAYER-TAGS.json","oracle/ROUTES.json","oracle/PIN.json")]
    before={str(p):p.read_bytes() for p in protected}
    tags,routes=json.loads(protected[0].read_bytes()),json.loads(protected[1].read_bytes())
    results,controls=[],[]
    for case_id in CASES:
        case,raw,layer=checked_case(case_id,tags,routes);runs,hashes={},{}
        for mode in ("normal","reverse","duplicates","reverse_duplicates"):
            observed,h=execute(raw,case_id+"-"+mode,mode,compiled)
            require(verify(case,raw,observed,mode)=="REFUSE","original joint must refuse")
            runs[mode]=observed;hashes[mode]=h
        require(all({k:v for k,v in r.items() if k!="mode"}=={k:v for k,v in runs["normal"].items() if k!="mode"}
                    for r in runs.values()),"orders/duplicates differ")
        results.append({"id":case_id,"source_sha256":sha(raw),"expected":case["expected"],"observed":"REFUSE",
                        "full_fixture_contract":True,"conditional_conclusion_only":True,"status":"EXECUTED",
                        "literal_inputs":case["inputs"],"layer_entry":layer,"native_results":runs,"input_sha256":hashes})
        for mode in CONTROL_MODES:
            observed,h=execute(raw,case_id+"-"+mode,mode,compiled)
            verdict=verify(case,raw,observed,mode)
            require(verdict==("ACCEPT" if mode=="justified_tight_membership" else "REFUSE"),"control differs")
            controls.append({"case":case_id,"mode":mode,"corpus_pass":False,"observed":verdict,
                             "input_sha256":h,"native_result":observed})
        require((ROOT/"corpus/must"/(case_id+".json")).read_bytes()==raw,"fixture changed")
    require(source_contract()==source and all(p.read_bytes()==before[str(p)] for p in protected),"source/metadata changed")
    require(sha(HARNESS.read_bytes())==compiled["harness_sha256"],"harness changed")
    report={"schema":"gp-phase2-conditional-point-routes/v1","case_count":2,"corpus_executions":8,
            "separate_control_executions":16,"cases":results,"controls":controls,"source_contract":source,
            "metadata_hashes":{k:sha(v) for k,v in before.items()},"build":compiled,
            "runtime":{"path":str(LEAN),"sha256":sha(LEAN.read_bytes())},
            "checker":{"path":str(CHECKER),"sha256":sha(CHECKER.read_bytes())},
            "adapter_sha256":sha(Path(__file__).read_bytes()),
            "tests_sha256":sha((ROOT/"tests/test_phase2_conditional_point_routes.py").read_bytes()),
            "g2_pass":False,"production_profile_adoption":False,"underlying_algebraic_truth_certified":False,
            "hypotheses":["supplied universal truth on loose","SIDE membership of a named supplied exhibited witness",
                          "tight subset loose","tight subset side"],
            "additional_accepting_control_hypothesis":"TIGHT membership of the same exhibited SIDE witness, supplied explicitly only in the separate accepting control.",
            "semantic_boundary":"For arbitrary Point/worlds satisfying these hypotheses, actual fold held claims have their registered meanings. Exhibited-point statements assert global existence of the named witness in their selected model; K2 cannot change SIDE identity into TIGHT identity. The join meaning is global, so empty TIGHT cannot vacuously license it.",
            "countermodel":"Point=Unit; TIGHT empty, SIDE/LOOSE inhabited, universal property true, named SIDE witness outside TIGHT. Checked theorem refutes TIGHT point existence and global joint licensing despite valid inclusion.",
            "binding_boundary":"Literal fixture and ordered inputs are returned intact; exact statement/model/witness identities, version and unchanged fixture SHA bind all registered records. Actual acceptsNarrow validates the universal route and refuses the point route. No metadata-only authority or pointwise existential recasting."}
    output.write_bytes((json.dumps(report,indent=2)+"\n").encode("utf-8"))
    print("Conditional point routes: 2 unchanged fixtures, 8 folds, 16 separate controls; conditional REFUSE.")
    return report

if __name__=="__main__":
    p=argparse.ArgumentParser();p.add_argument("--output",type=Path,default=ROOT/"reports/PHASE-2-CONDITIONAL-POINT-ROUTES.json")
    a=p.parse_args();run(a.output)
