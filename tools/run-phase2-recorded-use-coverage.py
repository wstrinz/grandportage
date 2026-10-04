"""Checked finite structural coverage of every recorded construction and conclusion use."""
import argparse
import ast
import copy
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import time

EXE_SUFFIX = ".exe" if __import__("os").name == "nt" else ""
ELAN_HOME = Path(__import__("os").environ.get("ELAN_HOME") or Path.home() / ".elan")
ROOT=Path(__file__).resolve().parents[1]
PACKAGE=ROOT/"phase2/lean"
HARNESS=PACKAGE/"Tests/RecordedUseCoverage.lean"
SCRATCH=ROOT/"tmp/phase2-recorded-use-coverage"
TOOLCHAIN=ELAN_HOME/"toolchains"/(ROOT/"phase2/lean/lean-toolchain").read_text(encoding="utf-8").strip().replace("/","--").replace(":","---")
LAKE=TOOLCHAIN/("bin/lake" + EXE_SUFFIX)
LEAN=TOOLCHAIN/("bin/lean" + EXE_SUFFIX)
CHECKER=TOOLCHAIN/("bin/leanchecker" + EXE_SUFFIX)
OLEAN=SCRATCH/"Tests/RecordedUseCoverage.olean"
WRAPPER=SCRATCH/"Run.lean"
PIN="ac4155787207e2847d248cffed7be871d5dcd577"
ORACLE_COMMITS = {PIN, __import__("json").loads((ROOT / "oracle/PIN.json").read_text(encoding="utf-8-sig")).get("public_commit", PIN)}
CASES=tuple("GP-X"+str(n) for n in range(193,199))
HASHES=dict(zip(CASES,[
"7c5e562d49d59f7c5caca6c9dab17fd71cbe19b4a935a799cfea904e2495bacb",
"029b40f131356433159528c129d545dd1f14e1fa02b113972650fcdb4173b4ab",
"5155e185ed4fab938c9303c04a33d573e158fc82bd3659ad9161ffaa9260041b",
"8b286ab7af0fc2796d9061aa6aa4a7b479d1607413689e089c83e1c164657ae7",
"8ff6043ccb8e32f614be8d41986416ed8da60bb56dead908015ccfc16932ffab",
"5f94db80e494848ce57cb06685f427c72a605a8db4d9cca2075f3752a24f558b"]))
SOURCES={
"tests/test_retrodiction.py":("test_each_axis_is_necessary_the_other_cannot_cover_for_it",154),
"tests/test_mutations.py":("test_mut_declaring_the_missing_component_silences_the_coverage_gap",103),
"grandportage/check.py":("coverage_gaps",658)}
STATEMENTS=["recorded coverage:dimension=place","recorded coverage:dimension=order",
"all asserted dimensions cover every recorded construction and conclusion use","complete literal fixture custody"]

def require(ok,message):
    if not ok: raise ValueError(message)

def sha(raw): return hashlib.sha256(raw).hexdigest()
def encoded(value): return json.dumps(value,sort_keys=True,separators=(",",":"),ensure_ascii=False).encode()
def command(args,env=None):
    p=subprocess.run(list(map(str,args)),cwd=PACKAGE,env=env,capture_output=True,text=True,encoding="utf-8")
    require(p.returncode==0,"command failed: "+str(args)+"\n"+p.stdout+p.stderr)
    return p.stdout

def build_inputs():
    # Includes all local modules and compiled imports, a conservative superset of
    # the transitive import closure; changing either source or compiled code invalidates reuse.
    paths=sorted((PACKAGE/"GP50").rglob("*.lean"))+sorted((PACKAGE/".lake/build/lib/lean/GP50").rglob("*.olean"))
    paths += [PACKAGE/"lean-toolchain",PACKAGE/"lakefile.toml",LEAN,LAKE,CHECKER]
    paths += sorted((TOOLCHAIN/"bin").glob("*.dll"))
    paths += [TOOLCHAIN/"lib/lean"/(name+".olean") for name in ("Init","Std","Lean")]
    return {str(p):sha(p.read_bytes()) for p in paths}

def cache_matches(old,inputs,source_hash):
    return (old.get("build_input_hashes")==inputs and old.get("harness_sha256")==source_hash
        and OLEAN.exists() and WRAPPER.exists() and old.get("olean_sha256")==sha(OLEAN.read_bytes())
        and old.get("wrapper_sha256")==sha(WRAPPER.read_bytes()))

def build():
    SCRATCH.mkdir(parents=True,exist_ok=True);OLEAN.parent.mkdir(parents=True,exist_ok=True)
    env=os.environ.copy();env["TEMP"]=str(SCRATCH);env["TMP"]=str(SCRATCH)
    stamp=SCRATCH/"build.json";inputs=build_inputs();source_hash=sha(HARNESS.read_bytes())
    if stamp.exists():
        old=json.loads(stamp.read_bytes())
        if cache_matches(old,inputs,source_hash): return old
    args=[LAKE,"env","lean","-o",OLEAN,"Tests/RecordedUseCoverage.lean"]
    log=command(args,env);(SCRATCH/"compile.log").write_text(log,encoding="utf-8")
    require("sorryAx" not in log and "error:" not in log,"unproved harness")
    declarations=re.findall(r"'RecordedUseCoverage\.([^']+)' depends on axioms: \[([^\]]*)\]",log)
    require({n for n,_ in declarations}=={"checker_iff","missing_iff","empty_recorded_uses_covered",
        "actual_validator_sound","actual_fold_held_sound","actual_join_means_all_recorded_uses"},"axiom audit incomplete")
    axioms=sorted({a.strip() for _,group in declarations for a in group.split(",") if a.strip()})
    require(set(axioms)<={"propext","Quot.sound","Classical.choice"},"unexpected axiom")
    base=command([LAKE,"env","python","-c","import os;print(os.environ.get('LEAN_PATH',''))"],env).strip()
    env["LEAN_PATH"]=str(SCRATCH)+os.pathsep+base
    check_args=[CHECKER,"-v","Tests.RecordedUseCoverage"];checked=command(check_args,env)
    (SCRATCH/"checker.log").write_text(checked,encoding="utf-8")
    WRAPPER.write_text("import Tests.RecordedUseCoverage\n",encoding="utf-8")
    require(inputs==build_inputs() and source_hash==sha(HARNESS.read_bytes()),"build inputs changed during compilation")
    result={"build_input_hashes":inputs,"harness_sha256":source_hash,"olean_sha256":sha(OLEAN.read_bytes()),
      "wrapper_sha256":sha(WRAPPER.read_bytes()),"lean_path":env["LEAN_PATH"],"axioms":axioms,
      "compile_command":list(map(str,args)),"compile_exit_code":0,"compile_log_sha256":sha(log.encode()),
      "checker_command":list(map(str,check_args)),"checker_exit_code":0,"checker_log_sha256":sha(checked.encode()),
      "kernel_checked":True,"axiom_declarations":[n for n,_ in declarations]}
    stamp.write_text(json.dumps(result,indent=2),encoding="utf-8")
    return result

def source_contract():
    checkout=ROOT/"oracle/checkout";git=["git","-c","safe.directory="+str(checkout),"-C",str(checkout)]
    require(json.loads((ROOT/"oracle/PIN.json").read_bytes())["commit"]==PIN,"pin changed")
    require(subprocess.check_output(git+["rev-parse","HEAD"],text=True).strip() in ORACLE_COMMITS,"checkout changed")
    out=[]
    selections=[(p,n,l) for p,(n,l) in SOURCES.items()]
    selections.append(("tests/test_mutations.py","test_mut_emptying_the_gauge_and_read_lists_silences_it_the_other_way",114))
    for path,name,line in selections:
        raw=subprocess.check_output(git+["show","HEAD:" +path]);require((checkout/path).read_bytes()==raw,"pinned source modified")
        text=raw.decode();node=next(n for n in ast.parse(text).body if isinstance(n,ast.FunctionDef) and n.name==name)
        require(node.lineno==line,"source anchor changed")
        segment="\n".join(text.splitlines()[node.lineno-1:node.end_lineno])
        if name=="coverage_gaps":
            require('model["touches"] + model["reads"]' in segment and 'touched - set(model["declares"].get(axis, []))' in segment,
                    "union/subtraction source contract changed")
        out.append({"commit":PIN,"path":path,"line":line,"anchor":"def "+name+"(",
                    "file_sha256":sha(raw),"function_sha256":sha(segment.encode())})
    return out

def checked_case(case_id,tags,routes):
    raw=(ROOT/"corpus/must"/(case_id+".json")).read_bytes();case=json.loads(raw)
    row=next(r for r in tags["cases"] if r["id"]==case_id)
    require(sha(raw)==HASHES[case_id]==row["sha256"],"fixture bytes changed")
    require(row["primary_layer"]=="kernel" and row["full_contract_required"] is True and row["g2_kernel_eligible"] is True
            and row["review_group"]=="finite-recorded-use-coverage","layer contract changed")
    require(case["expected"]["verdict"]==("ACCEPT" if case_id in ("GP-X196","GP-X197") else "REFUSE"),"expectation changed")
    require(routes["commit"]==PIN and routes["routes"][case_id]=={
      "kind":"inventory_diagnostic","layer":"declared_inventory_or_type_consistency",
      "limitation":"No proof of model adequacy, equation independence, or held mathematical claims. Coverage acceptance is relative to declared axes and recorded uses."},"route changed")
    contracts=source_contract()
    require(all(s["repository"]=="gp-v037" and any(all(s[k]==c[k] for k in ("commit","path","line","anchor"))
      for c in contracts) for s in case["sources"]),"source pointers changed")
    return case,raw,row

def execute(raw,label,mode,compiled=None):
    compiled=build() if compiled is None else compiled
    path=SCRATCH/(label+".fixture.json");path.write_bytes(raw)
    env=os.environ.copy();env["LEAN_PATH"]=compiled["lean_path"];env["TEMP"]=str(SCRATCH);env["TMP"]=str(SCRATCH)
    args=[LEAN,"--run",WRAPPER,path,sha(raw),mode]
    result=command(args,env)
    return json.loads(result.strip().splitlines()[-1]),sha(path.read_bytes())

def expected_sets(case):
    inputs=case["inputs"]
    required={d:sorted({label for row in inputs["construction_uses"]+inputs["conclusion_uses"]
                       if row["dimension"]==d for label in row["indices"]}) for d in ("place","order")}
    missing={d:sorted(set(required[d])-set(inputs["represented_indices"][d])) for d in required}
    return required,missing

def binding(source,literal,statement):
    return {"statementHash":statement,"scopeHash":"finite-recorded-use-coverage","modelHash":literal,
      "inputHashes":[source,literal,statement],"authority":"test-only-exact-recorded-inventory-containment",
      "authorityVersion":1,"kernelVersion":1}

def records(source,literal,mode):
    rows=[]
    for id,claim,statement,evidence in [
      (10,1,STATEMENTS[0],{"kind":"receipt","data":"recorded-coverage:place"}),
      (20,2,STATEMENTS[1],{"kind":"receipt","data":"recorded-coverage:order"}),
      (30,3,STATEMENTS[2],{"kind":"derived","premises":[10,20],"sideReceipt":"both-recorded-dimensions"}),
      (100,100,STATEMENTS[3],{"kind":"citation","text":literal})]:
        rows.append({"id":id,"claim":claim,"version":1,"binding":binding(source,literal,statement),"evidence":evidence})
    if mode=="withheld_order": rows=[r for r in rows if r["id"]!=20]
    if mode=="wrong_binding": rows[1]["binding"]["inputHashes"]=["corrupt binding"]
    return rows

def verify(case,raw,observed,mode):
    if mode=="dimension_collision":
        require(observed=={"status":"MALFORMED","error":"conflicting warrant contents: 10"},"identity collision not refused")
        return "MALFORMED"
    source=sha(raw);required,missing=expected_sets(case)
    require(observed["literal_fixture"]==case and observed["literal_inputs"]==case["inputs"] and
      observed["source_digest"]==source and observed["case"]==case["id"] and observed["mode"]==mode,"literal custody differs")
    literal=observed["bound_literal"];require(json.loads(literal)==case,"bound literal does not bind complete fixture")
    require(observed["required_by_dimension"]==required and observed["missing_by_dimension"]==missing
       and observed["checker_coverage"]=={d:not missing[d] for d in missing}
       and observed["joint_dependencies"]==[10,20],"native dimension checker differs")
    rows=records(source,literal,mode);ids=sorted(r["claim"] for r in rows)
    currents=[{k:r[k] for k in ("claim","version","binding")} for r in sorted(rows,key=lambda r:r["claim"])]
    require(observed["snapshot"]=={"domain":ids,"currents":currents,"warrants":rows,"retracted":[],"successors":[]},
      "complete native snapshot differs")
    supports=([10] if not missing["place"] else [])+([20] if not missing["order"] and mode not in ("withheld_order","wrong_binding") else [])
    if supports==[10,20]: supports.append(30)
    held=sorted(r["claim"] for r in rows if r["id"] in supports)
    require(observed["state"]=={"status":"OK","held":held,"supports":supports,"domain":ids,
      "live_warrants":[r["id"] for r in rows],"warrant_count":len(rows),"current_count":len(rows),
      "retracted":[],"successors":[]},"actual fold state differs")
    return "ACCEPT" if 3 in held else "REFUSE"

def control_inputs(cases):
    controls=[]
    def add(label,base,edit,expected):
        c=copy.deepcopy(cases[base]);edit(c["inputs"]);controls.append((label,encoded(c),"normal",expected))
    add("repair_place_only","GP-X193",lambda i:i["represented_indices"]["place"].append("t"),"REFUSE")
    add("repair_order_only","GP-X193",lambda i:i["represented_indices"]["order"].extend(["-4","0","1","2"]),"REFUSE")
    def repair(i):
        i["represented_indices"]["place"].append("t");i["represented_indices"]["order"].extend(["-4","0","1","2"])
    add("repair_both","GP-X193",repair,"ACCEPT")
    add("omitted_conclusion_read","GP-X198",lambda i:i.update(conclusion_uses=[r for r in i["conclusion_uses"] if r["dimension"]!="order"]),"ACCEPT")
    add("withhold_interior_order","GP-X196",lambda i:i["represented_indices"]["order"].remove("-4"),"REFUSE")
    add("withhold_place_t","GP-X196",lambda i:i["represented_indices"]["place"].remove("t"),"REFUSE")
    add("empty_inventory_recorded_vacuity","GP-X197",lambda i:i.update(represented_indices={"place":[],"order":[]}),"ACCEPT")
    add("reintroduce_recorded_read","GP-X197",lambda i:i["conclusion_uses"].append({"dimension":"order","indices":["0"],"description":"reintroduced recorded obligation"}),"REFUSE")
    def infinity(i):
        i["conclusion_uses"].append({"dimension":"place","indices":["infinity"],"description":"literal infinity recorded use"})
    add("literal_infinity_covered","GP-X196",infinity,"ACCEPT")
    def alias(i):
        infinity(i);i["represented_indices"]["place"].remove("infinity");i["represented_indices"]["place"].append("inf")
    add("no_infinity_alias","GP-X196",alias,"REFUSE")
    for mode,verdict in (("dimension_collision","MALFORMED"),("withheld_order","REFUSE"),("wrong_binding","REFUSE")):
        controls.append((mode,encoded(cases["GP-X196"]),mode,verdict))
    return controls

def run(output):
    started=time.time();compiled=build();source=source_contract()
    protected=[ROOT/p for p in ("corpus/LAYER-TAGS.json","oracle/ROUTES.json","oracle/PIN.json")]
    before={str(p):p.read_bytes() for p in protected};tags,routes=json.loads(protected[0].read_bytes()),json.loads(protected[1].read_bytes())
    results=[];cases={}
    for case_id in CASES:
        case,raw,layer=checked_case(case_id,tags,routes);cases[case_id]=case;runs={}
        for mode in ("normal","reverse","duplicates","reverse_duplicates"):
            observed,h=execute(raw,case_id+"-"+mode,mode,compiled)
            verdict=verify(case,raw,observed,mode)
            require(verdict==case["expected"]["verdict"],"original fixture verdict differs")
            runs[mode]=observed
        require(all({k:v for k,v in r.items() if k!="mode"}=={k:v for k,v in runs["normal"].items() if k!="mode"} for r in runs.values()),
                "event orders/duplicates differ")
        results.append({"id":case_id,"source_sha256":sha(raw),"expected":case["expected"],"observed":verdict,
          "full_fixture_contract":True,"status":"EXECUTED","literal_inputs":case["inputs"],"layer_entry":layer,"native_results":runs})
        require((ROOT/"corpus/must"/(case_id+".json")).read_bytes()==raw,"fixture changed")
        print(case_id+": "+verdict,flush=True)
    controls=[]
    for label,raw,mode,expected in control_inputs(cases):
        observed,h=execute(raw,label,mode,compiled);verdict=verify(json.loads(raw),raw,observed,mode)
        require(verdict==expected,"control differs: "+label)
        controls.append({"label":label,"mode":mode,"corpus_pass":False,"expected":expected,"observed":verdict,
                         "input_sha256":h,"native_result":observed})
        print("control "+label+": "+verdict,flush=True)
    require(source_contract()==source and all(p.read_bytes()==before[str(p)] for p in protected),"source/metadata changed")
    require(compiled["build_input_hashes"]==build_inputs() and compiled["harness_sha256"]==sha(HARNESS.read_bytes()),"build inputs changed")
    report={"schema":"gp-phase2-recorded-use-coverage/v1","case_count":6,"corpus_executions":24,
      "separate_control_executions":len(controls),"cases":results,"controls":controls,"source_contract":source,
      "metadata_hashes":{k:sha(v) for k,v in before.items()},"build":compiled,"adapter_sha256":sha(Path(__file__).read_bytes()),
      "tests_sha256":sha((ROOT/"tests/test_phase2_recorded_use_coverage.py").read_bytes()),
      "g2_pass":False,"production_profile_adoption":False,"mathematical_sufficiency_certified":False,
      "elapsed_seconds":round(time.time()-started,3),
      "semantic_boundary":"Finite structural containment of every literal recorded construction and conclusion use, per asserted dimension. Empty use lists discharge only recorded gaps; no adequacy, equation independence, real obligation discovery, or mathematical sufficiency is certified.",
      "label_boundary":"Labels are exact strings. Fixture infinity remains infinity; predecessor inf spelling is not an alias. Order -4 and nonnegative 0,1,2 are preserved.",
      "authority_boundary":"Native Lean list containment supplies receipt admission; actual GP50 fold supplies held verdict. Python set computation only verifies returned results. Complete raw-fixture digest and native full literal serialization bind every record.",
      "runtime_command_template":[str(LEAN),"--run",str(WRAPPER),"<scratch fixture>","<sha256 of exact bytes>","<mode>"]}
    output.parent.mkdir(parents=True,exist_ok=True);output.write_bytes((json.dumps(report,indent=2)+"\n").encode())
    return report

if __name__=="__main__":
    p=argparse.ArgumentParser();p.add_argument("--output",type=Path,default=ROOT/"reports/PHASE-2-RECORDED-USE-COVERAGE.json")
    run(p.parse_args().output)
