"""Native lifecycle concerns for eight lifecycle-scenario fixtures; nothing is held."""
import argparse
import ast
import copy
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import time

EXE_SUFFIX = ".exe" if __import__("os").name == "nt" else ""
ELAN_HOME = Path(__import__("os").environ.get("ELAN_HOME") or Path.home() / ".elan")
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/"tools"))
import lifecycle_inputs as LI
PACKAGE=ROOT/"phase2/lean"
HARNESS=PACKAGE/"Tests/LifecycleConcerns.lean"
SCRATCH=ROOT/"tmp/phase2-lifecycle-concerns"
TOOLCHAIN=ELAN_HOME/"toolchains"/(ROOT/"phase2/lean/lean-toolchain").read_text(encoding="utf-8").strip().replace("/","--").replace(":","---")
LAKE=TOOLCHAIN/("bin/lake" + EXE_SUFFIX)
LEAN=TOOLCHAIN/("bin/lean" + EXE_SUFFIX)
CHECKER=TOOLCHAIN/("bin/leanchecker" + EXE_SUFFIX)
OLEAN=SCRATCH/"Tests/LifecycleConcerns.olean"
WRAPPER=SCRATCH/"Run.lean"
PIN="ac4155787207e2847d248cffed7be871d5dcd577"
ORACLE_COMMITS = {PIN, __import__("json").loads((ROOT / "oracle/PIN.json").read_text(encoding="utf-8-sig")).get("public_commit", PIN)}
CASES=('GP-X149', 'GP-X150', 'GP-X151', 'GP-X156', 'GP-X157', 'GP-X160', 'GP-X162', 'GP-X163')
HASHES={
"GP-X149": "b32fbcd22f808170e6c97ba3d0a2405060a645f0e22d609dc13720edf71e0036",
"GP-X150": "0f4ea6874f9b69d61b1f60aea2bf4232e2091fd8ff0ec785a5b1470667c5d749",
"GP-X151": "d9f6326a9ed24dd4dc582165dd4adcb3613f1fc27bce6c514c55e2bfc7c27dde",
"GP-X156": "0912b420817c1865da733305feaaf78474f5bde7f1abeaa99c522735812e07d2",
"GP-X157": "cdbe878ab858f42de03f214b6ce72225296edf8ebe1103ed8b584eaf975a1510",
"GP-X160": "b79be0fabef9acba5f6f8c39fd32aa32bb035349006d315e59e871cd52e41178",
"GP-X162": "c729a088716cfd6d7f8ab1ec30e0062db067422330a21e88dde8d81a95da7f1e",
"GP-X163": "784186b5c127a8dbf56cf12eff14f8a008b5c81382835e0e965552f306cd24c4"
}
EXPECTED={"GP-X149": "REFUSE", "GP-X150": "REFUSE", "GP-X151": "ACCEPT", "GP-X156": "ACCEPT", "GP-X157": "REFUSE", "GP-X160": "REFUSE", "GP-X162": "REFUSE", "GP-X163": "ACCEPT"}
DECLARATIONS=("unmoved","amend_sound","routeCleared_sound","untypedCleared_sound","contextCleared_sound","liveRelation_sound")
ORDERS=("normal","reverse","duplicates","reverse_duplicates")

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
    args=[LAKE,"env","lean","-o",OLEAN,"Tests/LifecycleConcerns.lean"]
    log=command(args,env);(SCRATCH/"compile.log").write_text(log,encoding="utf-8")
    require("sorryAx" not in log and "error:" not in log,"unproved harness")
    declarations=re.findall(r"'LifecycleConcerns\.([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)",log)
    require({n for n,_ in declarations}==set(DECLARATIONS),
      "axiom audit incomplete")
    axioms=sorted({a.strip() for _,group in declarations for a in group.split(",") if a.strip()})
    require(set(axioms)<={"propext","Quot.sound","Classical.choice"},"unexpected axiom")
    base=command([LAKE,"env","python","-c","import os;print(os.environ.get('LEAN_PATH',''))"],env).strip()
    env["LEAN_PATH"]=str(SCRATCH)+os.pathsep+base
    check_args=[CHECKER,"-v","Tests.LifecycleConcerns"];checked=command(check_args,env)
    (SCRATCH/"checker.log").write_text(checked,encoding="utf-8")
    WRAPPER.write_text("import Tests.LifecycleConcerns\n",encoding="utf-8")
    require(inputs==build_inputs() and source_hash==sha(HARNESS.read_bytes()),"build inputs changed during compilation")
    result={"build_input_hashes":inputs,"harness_sha256":source_hash,"olean_sha256":sha(OLEAN.read_bytes()),
      "wrapper_sha256":sha(WRAPPER.read_bytes()),"lean_path":env["LEAN_PATH"],"axioms":axioms,
      "compile_command":list(map(str,args)),"compile_exit_code":0,"compile_log_sha256":sha(log.encode()),
      "checker_command":list(map(str,check_args)),"checker_exit_code":0,"checker_log_sha256":sha(checked.encode()),
      "kernel_checked":True,"axiom_declarations":[n for n,_ in declarations]}
    stamp.write_text(json.dumps(result,indent=2),encoding="utf-8")
    return result

ANCHORS=(("tests/test_supersession_noise.py",123,"def test_edge_withdraw_retires_a_declaration_without_minting_an_edge("),
         ("tests/test_supersession_noise.py",135,"def test_withdrawing_an_edge_does_not_hide_live_traffic("),
         ("tests/test_supersession_noise.py",497,"def test_a_withdrawn_edge_whose_only_rider_was_withdrawn_too_is_gone("),
         ("tests/test_supersession_noise.py",330,"def test_an_untyped_edge_that_was_retyped_stops_reporting_as_live_debt("),
         ("tests/test_supersession_noise.py",348,"def test_a_replacement_that_is_also_untyped_is_still_caught("),
         ("tests/test_supersession_noise.py",210,"def test_verify_declines_a_live_edge_with_a_superseded_endpoint("),
         ("tests/test_adversarial.py",1697,"def test_amend_is_computed_not_declared("),
         ("tests/test_adversarial.py",1732,"def test_over_declaring_a_supersession_is_allowed("))

def kernel_fields(raw):
    found={}
    for n in ast.parse(raw.decode("utf-8")).body:
        if isinstance(n,ast.Assign) and getattr(n.targets[0],"id","") in ("IDENTIFYING_FIELDS","LICENSING_FIELDS"):
            found[n.targets[0].id]=(n.lineno,list(ast.literal_eval(n.value)))
    require(found["IDENTIFYING_FIELDS"][0]==1723 and found["LICENSING_FIELDS"][0]==1732,"pinned field tables moved")
    return found["IDENTIFYING_FIELDS"][1],found["LICENSING_FIELDS"][1]

def source_contract():
    checkout=ROOT/"oracle/checkout";git=["git","-c","safe.directory="+str(checkout),"-C",str(checkout)]
    require(json.loads((ROOT/"oracle/PIN.json").read_bytes())["commit"]==PIN,"pin changed")
    require(subprocess.check_output(git+["rev-parse","HEAD"],text=True).strip() in ORACLE_COMMITS,"checkout changed")
    out=[];cache={}
    def pinned(path):
        if path not in cache:
            raw=subprocess.check_output(git+["show","HEAD:" +path]);require((checkout/path).read_bytes()==raw,"pinned source changed")
            cache[path]=raw
        return cache[path]
    for path,n,anchor in ANCHORS:
        raw=pinned(path);line=raw.decode().splitlines()[n-1];require(line.startswith(anchor),"predecessor anchor changed: %s:%d"%(path,n))
        out.append({"repository":"gp-v037","commit":PIN,"path":path,"line":n,"anchor":anchor,"file_sha256":sha(raw),"anchor_sha256":sha(line.encode())})
    ident,lic=kernel_fields(pinned("grandportage/kernel.py"))
    vocab=(ROOT/"tools/lifecycle_inputs.py").read_bytes()
    out.append({"repository":"gp-v037","commit":PIN,"path":"grandportage/kernel.py","field_tables":{"identifying":ident,"licensing":lic},
                "file_sha256":sha(pinned("grandportage/kernel.py"))})
    out.append({"repository":"grandportage-0.50","path":"tools/lifecycle_inputs.py","file_sha256":sha(vocab)})
    return out

def tables(contract): return next(c["field_tables"] for c in contract if "field_tables" in c)

def checked_case(case_id,tags,routes,contract):
    raw=(ROOT/"corpus/must"/(case_id+".json")).read_bytes();case=json.loads(raw)
    row=next(r for r in tags["cases"] if r["id"]==case_id)
    require(sha(raw)==HASHES[case_id]==row["sha256"],"fixture changed")
    require(row["primary_layer"]=="kernel" and row["full_contract_required"] is True and row["g2_kernel_eligible"] is True
      and row["review_group"]=="native-event-lifecycle","layer changed")
    require(case["expected"]["verdict"]==EXPECTED[case_id],"expectation changed")
    require(all(any(all(c.get(k)==s[k] for k in s) for c in contract) for s in case["sources"]),"source pointers changed")
    route=routes["routes"][case_id];require(route["kind"]=="lifecycle" and route["layer"]=="lifecycle_contract","frozen route changed")
    return case,raw,row

def execute(raw,label,mode,compiled=None):
    compiled=build() if compiled is None else compiled
    path=SCRATCH/(label+".fixture.json");path.write_bytes(raw)
    env=os.environ.copy();env["LEAN_PATH"]=compiled["lean_path"];env["TEMP"]=str(SCRATCH);env["TMP"]=str(SCRATCH)
    result=command([LEAN,"--run",WRAPPER,path,sha(raw),mode],env)
    return json.loads(result.strip().splitlines()[-1]),sha(path.read_bytes())

# Independent host model of the lifecycle fold and concerns.
def mapped(key):
    if key in LI.ATTRIBUTES: return LI.ATTRIBUTES[key]
    if key in LI.ENUMS: return LI.ENUMS[key][0]
    return None
def tomb(o): return o["category"] in ("relation","argument") and list(o["properties"])==["justification"]
def classify(old,new,ident,lic):
    val=lambda o,f:next((canon(v) for k,v in o["properties"].items() if mapped(k)==f),None)
    mv=lambda fs:[f for f in fs if val(old,f)!=val(new,f)]
    return ("RESTATE",mv(ident)) if mv(ident) else (("RELICENSE",mv(lic)) if mv(lic) else ("AMEND",[]))
def canon(v): return json.dumps(v,sort_keys=True,separators=(",",":"),ensure_ascii=False)

def model(case,ident,lic):
    i=case["inputs"];objs={k:dict(o,id=int(k.split("-")[1])) for k,o in i["objects"].items()}
    byname={o["name"]:o for o in objs.values()};retracted=set();links=[]
    for step in i["history"]:
        o=objs[step["object"]]
        if "replacement" not in step: continue
        r=step["replacement"];p=byname[r["prior"]]
        if r["change"] in ("relation_withdrawal","argument_retraction"): retracted.add(p["id"])
        elif r["change"] in ("relation_reclassification","restatement"): links.append([p["id"],o["id"]])
        elif r["change"]=="annotation_only":
            kind,moved=classify(p,o,ident,lic)
            if kind!="AMEND": return {"error":"annotation_only hides %s: [%s]"%(kind,", ".join(moved))}
            links.append([p["id"],o["id"]])
    dead=retracted|{a for a,_ in links}
    live={o["name"] for o in objs.values() if not tomb(o) and o["id"] not in dead}
    q=i["question"]
    if "object" in q:
        o=byname.get(q["object"]);concern,cleared="live_relation_query",bool(o and o["category"]=="relation" and not tomb(o) and o["name"] in live)
    elif q.get("concerns")==["retired_route_dependency"]:
        concern="retired_route_dependency";cleared=all(byname[s["relation"]]["id"] not in retracted
            for o in objs.values() if o["category"]=="argument" and not tomb(o) and o["name"] in live for s in o["properties"]["transport_route"])
    elif q.get("concerns")==["unresolved_relation"]:
        concern="unresolved_relation";cleared=all(o["properties"].get("relation_class")!="unspecified"
            for o in objs.values() if o["category"]=="relation" and not tomb(o) and o["name"] in live)
    elif q.get("concerns")==["retired_context_dependency"]:
        concern="retired_context_dependency";cleared=all(o["properties"]["context"] in live
            for o in objs.values() if o["category"]=="assertion" and o["name"] in live)
    else:
        require(q=={},"question");concern,cleared="computed_amendment",True
    order=[o["name"] for _,o in sorted(objs.items(),key=lambda kv:kv[0])]
    return {"concern":concern,"cleared":cleared,"live":[n for n in order if n in live],"retracted":sorted(retracted),
            "successors":sorted(links),"field_keys":sorted({k for o in objs.values() for k in o["properties"]})}

def verify(case,raw,observed,mode,contract):
    t=tables(contract);expect=model(case,t["identifying"],t["licensing"])
    if "error" in expect:
        require(observed=={"status":"MALFORMED","error":expect["error"]},"native construction refusal differs");return "REFUSE"
    require(observed["literal_fixture"]==case and observed["source_digest"]==sha(raw) and observed["case"]==case["id"]
      and observed["mode"]==mode and json.loads(observed["bound_literal"])==case,"whole fixture differs")
    require(observed["identifying_fields"]==t["identifying"] and observed["licensing_fields"]==t["licensing"],"native field tables differ from pinned kernel")
    for k,f in observed["field_map"].items():
        hm=mapped(k);both=set(t["identifying"]+t["licensing"])
        require((f in both)==(hm in both) and (f not in both or f==hm),"native field mapping differs: "+k)
    require(sorted(observed["field_map"])==expect["field_keys"],"field keys differ")
    require(observed["concern"]==expect["concern"] and observed["cleared"]==expect["cleared"] and observed["live_names"]==expect["live"]
      and observed["state"]["retracted"]==expect["retracted"] and sorted(observed["state"]["successors"])==expect["successors"]
      and observed["state"]["held"]==[] and observed["state"]["supports"]==[],"native lifecycle concern differs")
    return "ACCEPT" if expect["cleared"] else "REFUSE"

def control_inputs(cases):
    out=[]
    def add(label,base,edit,expected):
        c=copy.deepcopy(cases[base]);edit(c["inputs"]);out.append((label,encoded(c),"normal",expected))
    def obj(i,name): return next(o for o in i["objects"].values() if o["name"]==name)
    add("X157_query_live_untyped_successor","GP-X157",lambda i:i.update(question={"object":"E2","collection":"relations"}),"ACCEPT")
    add("X157_typed_successor","GP-X157",lambda i:obj(i,"E2")["properties"].update(relation_class="subset_restriction") or obj(i,"E2")["properties"].pop("unresolved_reason"),"ACCEPT")
    add("X156_without_reclassification","GP-X156",lambda i:[s.pop("replacement",None) for s in i["history"]],"REFUSE")
    add("X160_consumer_repointed","GP-X160",lambda i:obj(i,"C")["properties"].update(context="M2"),"ACCEPT")
    add("X162_without_licensing_field","GP-X162",lambda i:obj(i,"C2")["properties"].pop("coefficients_from_base"),"ACCEPT")
    add("X162_declared_restatement","GP-X162",lambda i:[s["replacement"].update(change="restatement") for s in i["history"] if "replacement" in s],"ACCEPT")
    add("X163_statement_change_as_annotation","GP-X163",lambda i:obj(i,"C2")["properties"].update(statement="Q"),"REFUSE")
    add("X150_unknown_change","GP-X150",lambda i:[s["replacement"].update(change="erasure") for s in i["history"] if "replacement" in s],"MALFORMED")
    add("X150_unknown_concern","GP-X150",lambda i:i.update(question={"concerns":["anything"]}),"MALFORMED")
    return out

def run(output):
    started=time.time();compiled=build();contract=source_contract()
    protected=[ROOT/p for p in ("corpus/LAYER-TAGS.json","oracle/ROUTES.json","oracle/PIN.json")]
    before={str(p):p.read_bytes() for p in protected};tags,routes=json.loads(protected[0].read_bytes()),json.loads(protected[1].read_bytes())
    results=[];cases={}
    for case_id in CASES:
        case,raw,layer=checked_case(case_id,tags,routes,contract);cases[case_id]=case;runs={}
        for mode in ORDERS:
            observed,h=execute(raw,case_id+"-"+mode,mode,compiled);v=verify(case,raw,observed,mode,contract)
            require(v==case["expected"]["verdict"],"original verdict differs: "+case_id)
            runs[mode]=observed
        strip=lambda r:{k:x for k,x in r.items() if k!="mode"}
        require(all(strip(r)==strip(runs["normal"]) for r in runs.values()),"event order/duplicates differ")
        results.append({"id":case_id,"source_sha256":sha(raw),"expected":case["expected"],"observed":v,
          "full_fixture_contract":True,"status":"EXECUTED","literal_inputs":case["inputs"],"layer_entry":layer,"native_results":runs})
        require((ROOT/"corpus/must"/(case_id+".json")).read_bytes()==raw,"fixture changed")
        print(case_id+": "+v,flush=True)
    controls=[]
    for label,raw,mode,expected in control_inputs(cases):
        observed,h=execute(raw,label,mode,compiled)
        if expected=="MALFORMED":
            require(observed.get("status")=="MALFORMED","malformed control accepted: "+label);v="MALFORMED"
        else: v=verify(json.loads(raw),raw,observed,mode,contract)
        require(v==expected,"control differs: "+label)
        controls.append({"label":label,"mode":mode,"corpus_pass":False,"status":"EXECUTED","expected":expected,"observed":v,
                         "input_sha256":h,"native_result":observed})
        print("control "+label+": "+v,flush=True)
    require(source_contract()==contract and all(p.read_bytes()==before[str(p)] for p in protected),"source/metadata changed")
    require(compiled["build_input_hashes"]==build_inputs() and compiled["harness_sha256"]==sha(HARNESS.read_bytes()),"build inputs changed")
    report={"schema":"gp-phase2-lifecycle-concerns/v1","case_count":8,"corpus_executions":32,
      "separate_control_executions":len(controls),"cases":results,"controls":controls,"source_contract":contract,
      "metadata_hashes":{k:sha(v) for k,v in before.items()},"build":compiled,"adapter_sha256":sha(Path(__file__).read_bytes()),
      "tests_sha256":sha((ROOT/"tests/test_phase2_lifecycle_concerns.py").read_bytes()),
      "g2_pass":False,"production_profile_adoption":False,"held_authority_claimed":False,
      "elapsed_seconds":round(time.time()-started,3),
      "lifecycle_contract":"All records are inert custody under refuseAll; nothing is held. Concerns are evaluated natively over production custody liveness after explicit withdrawal (retract) and replacement (supersede) events. Supersession never repoints consumers.",
      "amendment_contract":"annotation_only is accepted only when the computed classification over the pinned identifying and licensing fields is AMEND (amend_sound); a moved licensing or identifying field is a construction refusal.",
      "runtime_command_template":[str(LEAN),"--run",str(WRAPPER),"<scratch fixture>","<exact byte sha256>","<mode>"]}
    output.parent.mkdir(parents=True,exist_ok=True);output.write_bytes((json.dumps(report,indent=2)+"\n").encode())
    return report

if __name__=="__main__":
    p=argparse.ArgumentParser();p.add_argument("--output",type=Path,default=ROOT/"reports/PHASE-2-LIFECYCLE-CONCERNS.json")
    run(p.parse_args().output)
