"""Conditional theorem transport for X60-X62; no premise is discharged and no theorem is replayed."""
import argparse
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
HARNESS=PACKAGE/"Tests/ConditionalTheoremTransport.lean"
SCRATCH=ROOT/"tmp/phase2-conditional-theorem-transport"
TOOLCHAIN=ELAN_HOME/"toolchains"/(ROOT/"phase2/lean/lean-toolchain").read_text(encoding="utf-8").strip().replace("/","--").replace(":","---")
LAKE=TOOLCHAIN/("bin/lake" + EXE_SUFFIX)
LEAN=TOOLCHAIN/("bin/lean" + EXE_SUFFIX)
CHECKER=TOOLCHAIN/("bin/leanchecker" + EXE_SUFFIX)
OLEAN=SCRATCH/"Tests/ConditionalTheoremTransport.olean"
WRAPPER=SCRATCH/"Run.lean"
HISTORY="7991c9052f13e8dcaa78b5eae36f31663e080c1e"
CASES=("GP-X60","GP-X61","GP-X62")
HASHES=dict(zip(CASES,[
"403f25ddb8e0501c84b5a87ba58ae7f5b109bd44a70d210290cb1efd64515ad2",
"4fd5df164768d81f71f3846c48135b68b253a2ae205f0bff35bf6a79ae3c624d",
"e01e2677a02ec11e9729aec4d74fed863141b75d11c52edf6294ceb0bea09846"]))
PROPOSALS=dict(zip(CASES,("retain","omit_premise","rebind_target")))
PREMISE_IDS=["JC.PREM.ORDER_EIGHT_BOUNDED","JC.PREM.SLICE_IS_SOLUTION","JC.PREM.ALL_ORDERS_GAUGE"]
ORDER_EIGHT="Every omitted transfer term is zero below stage eight times the first live block."
RELAXED="relaxed seven-coordinate summit point"
EXTRA={"statement":"An uncommissioned premise invented by the consuming derivation.","status":"ASSUMED"}
DECLARATIONS=("licensed_sound","transport_sound","named_theorem_given","edge_from_licensed_authority",
  "actual_base_sound","actual_validator_sound","actual_fold_held_sound","held_edge_is_conditional",
  "open_premises_not_discharged","omitted_premise_not_transported","rebound_target_not_transported")
ORDERS=("normal","reverse","duplicates","reverse_duplicates")
EDGE_CONTROLS=("reorder_edge_premises","duplicate_edge_premise","invent_edge_premise","discharge_open_premises",
  "omit_gauge_premise","rebind_edge_source","rebind_edge_target")
EVIDENCE_CONTROLS=("withheld_authority","wrong_binding","theorem_pointer","citation_only")

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
    args=[LAKE,"env","lean","-o",OLEAN,"Tests/ConditionalTheoremTransport.lean"]
    log=command(args,env);(SCRATCH/"compile.log").write_text(log,encoding="utf-8")
    require("sorryAx" not in log and "error:" not in log,"unproved harness")
    declarations=re.findall(r"'ConditionalTheoremTransport\.([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)",log)
    require({n for n,_ in declarations}==set(DECLARATIONS),
      "axiom audit incomplete")
    axioms=sorted({a.strip() for _,group in declarations for a in group.split(",") if a.strip()})
    require(set(axioms)<={"propext","Quot.sound","Classical.choice"},"unexpected axiom")
    base=command([LAKE,"env","python","-c","import os;print(os.environ.get('LEAN_PATH',''))"],env).strip()
    env["LEAN_PATH"]=str(SCRATCH)+os.pathsep+base
    check_args=[CHECKER,"-v","Tests.ConditionalTheoremTransport"];checked=command(check_args,env)
    (SCRATCH/"checker.log").write_text(checked,encoding="utf-8")
    WRAPPER.write_text("import Tests.ConditionalTheoremTransport\n",encoding="utf-8")
    require(inputs==build_inputs() and source_hash==sha(HARNESS.read_bytes()),"build inputs changed during compilation")
    result={"build_input_hashes":inputs,"harness_sha256":source_hash,"olean_sha256":sha(OLEAN.read_bytes()),
      "wrapper_sha256":sha(WRAPPER.read_bytes()),"lean_path":env["LEAN_PATH"],"axioms":axioms,
      "compile_command":list(map(str,args)),"compile_exit_code":0,"compile_log_sha256":sha(log.encode()),
      "checker_command":list(map(str,check_args)),"checker_exit_code":0,"checker_log_sha256":sha(checked.encode()),
      "kernel_checked":True,"axiom_declarations":[n for n,_ in declarations]}
    stamp.write_text(json.dumps(result,indent=2),encoding="utf-8")
    return result

def lower_label(label): return label[:1].lower()+label[1:]

def source_contract():
    pin=json.loads((ROOT/"oracle/history/PIN.json").read_bytes());require(pin["commit"]==HISTORY,"history pin changed")
    pinned={f["path"]:f["sha256"] for f in pin["files"]};out=[]
    def bound(path):
        raw=(ROOT/"oracle/history/checkout"/path).read_bytes();require(sha(raw)==pinned[path],"pinned history source changed")
        return raw
    test="tests/test_jc_formalization_transport.py";raw=bound(test);lines=raw.decode().splitlines()
    for n,anchor in ((96,"def test_block_one_binding_retains_every_formal_premise("),(111,"def test_omitting_a_formal_premise_is_refused("),
                     (121,"def test_authority_cannot_be_rebound_to_different_semantic_endpoints(")):
        require(lines[n-1].startswith(anchor),"history anchor changed")
        out.append({"repository":"gp-history","commit":HISTORY,"path":test,"line":n,"anchor":anchor,
                    "file_sha256":sha(raw),"anchor_sha256":sha(lines[n-1].encode())})
    adapter="experiments/jc_formalization_transport/adapter.py";raw=bound(adapter);lines=raw.decode().splitlines()
    for n,needle in ((232,'authority["target_object_id"] == result["target"], "EDG6",'),
                     (234,'_require(authority["premise_ids"] == result["premise_ids"], "EDG7",')):
        require(needle in lines[n-1],"history rule anchor changed")
        out.append({"repository":"gp-history","commit":HISTORY,"path":adapter,"line":n,"anchor":needle,
                    "file_sha256":sha(raw),"anchor_sha256":sha(lines[n-1].encode())})
    fixture="fixtures/jc_formalization_transport/v0.json";raw=bound(fixture);ledger=json.loads(raw)
    by=lambda kind:{r["id"]:r for r in ledger[kind]}
    auth=by("authorities")["JC.AUTH.ACTUAL_BLOCK_ONE"];edge=by("edges")["JC.EDGE.SLICE_TO_BLOCK_ONE_ZERO"]
    objects=by("objects");premises=by("premises")
    require(auth["premise_ids"]==edge["premise_ids"]==PREMISE_IDS and auth["source_object_id"]==edge["source"]
      and auth["target_object_id"]==edge["target"] and edge["authority_id"]==auth["id"],"pinned binding changed")
    view={"premises":[{"statement":premises[p]["statement"],"status":premises[p]["status"]} for p in PREMISE_IDS],
      "source":lower_label(objects[auth["source_object_id"]]["label"]),"target":lower_label(objects[auth["target_object_id"]]["label"]),
      "rebound_target":lower_label(objects["JC.SEM.RELAXED_SUMMIT_POINT"]["label"])}
    require(view["rebound_target"]==RELAXED and view["premises"][0]["statement"]==ORDER_EIGHT,"pinned labels changed")
    out.append({"repository":"gp-history","commit":HISTORY,"path":fixture,"ledger_view":view,"file_sha256":sha(raw)})
    return out

def ledger_view(contract): return next(c["ledger_view"] for c in contract if "ledger_view" in c)

def checked_case(case_id,tags,routes,contract):
    raw=(ROOT/"corpus/must"/(case_id+".json")).read_bytes();case=json.loads(raw)
    row=next(r for r in tags["cases"] if r["id"]==case_id);view=ledger_view(contract)
    require(sha(raw)==HASHES[case_id]==row["sha256"],"fixture changed")
    require(row["primary_layer"]=="kernel" and row["full_contract_required"] is True and row["g2_kernel_eligible"] is True
      and row["review_group"]=="supplied-premise-authority","layer changed")
    i=case["inputs"]
    require(i["premises"]==view["premises"] and i["source"]==view["source"] and i["target"]==view["target"]
      and i["proposal"]==PROPOSALS[case_id],"fixture no longer matches the pinned ledger")
    require(case["expected"]["verdict"]==("ACCEPT" if case_id=="GP-X60" else "REFUSE"),"expectation changed")
    require(all(any(all(c.get(k)==s[k] for k in s) for c in contract) for s in case["sources"]),"source pointers changed")
    route=routes["routes"][case_id]
    require(route["kind"]=="formalization_ledger" and route["action"]==PROPOSALS[case_id] and route["historical_commit"]==HISTORY,"frozen route changed")
    return case,raw,row

def execute(raw,label,mode,compiled=None):
    compiled=build() if compiled is None else compiled
    path=SCRATCH/(label+".fixture.json");path.write_bytes(raw)
    env=os.environ.copy();env["LEAN_PATH"]=compiled["lean_path"];env["TEMP"]=str(SCRATCH);env["TMP"]=str(SCRATCH)
    result=command([LEAN,"--run",WRAPPER,path,sha(raw),mode],env)
    return json.loads(result.strip().splitlines()[-1]),sha(path.read_bytes())

# Independent host mirror of the Lean transport policy: exact endpoint and premise-record equality.
def licensed(authority,edge):
    return authority==edge

def authority_of(i):
    return {"source":i["source"],"target":RELAXED if i["proposal"]=="rebind_target" else i["target"],"premises":i["premises"]}
def edge_of(i,mode):
    ps=[p for p in i["premises"] if p["statement"]!=ORDER_EIGHT] if i["proposal"]=="omit_premise" else list(i["premises"])
    e={"source":i["source"],"target":i["target"],"premises":ps}
    if mode=="reorder_edge_premises": e["premises"]=ps[::-1]
    if mode=="duplicate_edge_premise": e["premises"]=ps+ps[:1]
    if mode=="invent_edge_premise": e["premises"]=ps+[EXTRA]
    if mode=="discharge_open_premises": e["premises"]=[dict(p,status="ASSUMED") for p in ps]
    if mode=="omit_gauge_premise": e["premises"]=ps[:-1]
    if mode=="rebind_edge_source": e["source"]=RELAXED
    if mode=="rebind_edge_target": e["target"]=RELAXED
    return e

def compact(value): return json.dumps(value,sort_keys=True,separators=(",",":"),ensure_ascii=False)
def binding(source,literal,authority,statement):
    return {"statementHash":statement,"scopeHash":"BOTH","modelHash":compact(authority),"inputHashes":[source,literal],
      "authority":"test-only-explicit-conditional-theorem-transport","authorityVersion":1,"kernelVersion":1}

def records(case,source,obs,mode):
    i=case["inputs"];literal=obs["bound_literal"];a=authority_of(i);e=edge_of(i,mode)
    auth=lambda x:"named conditional Lean theorem:"+compact(x);use=lambda x:"consuming conditional derivation:"+compact(x)
    rows=[{"id":5,"claim":5,"version":1,"binding":binding(source,literal,a,auth(a)),
           "evidence":{"kind":"receipt","data":"supplied:named-conditional-lean-theorem"}},
          {"id":1,"claim":1,"version":1,"binding":binding(source,literal,a,use(e)),
           "evidence":{"kind":"derived","premises":[5],"sideReceipt":"licensed-premise-endpoint-transport"}},
          {"id":100,"claim":100,"version":1,"binding":binding(source,literal,a,use(edge_of(i,"normal"))),
           "evidence":{"kind":"citation","text":literal}}]
    if mode=="withheld_authority": rows=rows[1:]
    if mode=="wrong_binding": rows[0]["binding"]["inputHashes"]=["corrupt binding"]
    if mode=="theorem_pointer": rows[0]["evidence"]={"kind":"theorem","declaration":"JC.SigmaMarkedBlockOneInstance.actual_blockOne"}
    if mode=="citation_only": rows[0]["evidence"]={"kind":"citation","text":"PACKET_REPORTED_PASS"}
    return sorted(rows,key=lambda r:r["id"])

def verify(case,raw,observed,mode):
    i=case["inputs"];source=sha(raw);a=authority_of(i);e=edge_of(i,mode);ok=licensed(a,e)
    require(observed["literal_fixture"]==case and observed["literal_inputs"]==i and observed["source_digest"]==source
      and observed["case"]==case["id"] and observed["mode"]==mode and observed["conditional"] is True
      and json.loads(observed["bound_literal"])==case,"whole conditional fixture differs")
    require(observed["authority"]==a and observed["consumer_edge"]==e and observed["actual_license_check"]==ok
      and observed["edge_dependencies"]==[5],"actual transport check differs")
    rows=records(case,source,observed,mode);ids=sorted(r["claim"] for r in rows)
    currents=[{k:r[k] for k in ("claim","version","binding")} for r in sorted(rows,key=lambda r:r["claim"])]
    require(observed["snapshot"]=={"domain":ids,"warrants":rows,"currents":currents,"retracted":[],"successors":[]},"complete snapshot differs")
    supports=[] if mode in EVIDENCE_CONTROLS else [5]
    if supports and ok: supports.append(1)
    require(observed["state"]=={"status":"OK","held":sorted(supports),"supports":supports,"domain":ids,
      "live_warrants":[r["id"] for r in rows],"warrant_count":len(rows),"current_count":len(rows),
      "retracted":[],"successors":[]},"actual fold support/held differs")
    return "ACCEPT" if 1 in supports else "REFUSE"

def control_inputs(cases):
    base=encoded(cases["GP-X60"]);i=cases["GP-X60"]["inputs"];out=[]
    for mode in EDGE_CONTROLS:
        out.append((mode,base,mode,"ACCEPT" if licensed(authority_of(i),edge_of(i,mode)) else "REFUSE"))
    for mode in EVIDENCE_CONTROLS: out.append((mode,base,mode,"REFUSE"))
    def add(label,edit):
        c=copy.deepcopy(cases["GP-X60"]);edit(c["inputs"]);out.append((label,encoded(c),"normal","MALFORMED"))
    add("unknown_premise_status",lambda i:i["premises"][0].update(status="PROVEN"))
    add("unknown_proposal",lambda i:i.update(proposal="weaken"))
    add("extra_input_field",lambda i:i.update(discharged=True))
    return out

def run(output):
    started=time.time();compiled=build();contract=source_contract()
    protected=[ROOT/p for p in ("corpus/LAYER-TAGS.json","oracle/ROUTES.json","oracle/history/PIN.json")]
    before={str(p):p.read_bytes() for p in protected};tags,routes=json.loads(protected[0].read_bytes()),json.loads(protected[1].read_bytes())
    results=[];cases={}
    for case_id in CASES:
        case,raw,layer=checked_case(case_id,tags,routes,contract);cases[case_id]=case;runs={}
        for mode in ORDERS:
            observed,h=execute(raw,case_id+"-"+mode,mode,compiled);verdict=verify(case,raw,observed,mode)
            require(verdict==case["expected"]["verdict"],"original conditional verdict differs")
            runs[mode]=observed
        require(all({k:v for k,v in r.items() if k!="mode"}=={k:v for k,v in runs["normal"].items() if k!="mode"} for r in runs.values()),"event order/duplicates differ")
        results.append({"id":case_id,"source_sha256":sha(raw),"expected":case["expected"],"observed":verdict,
          "conditional_conclusion_only":True,"full_fixture_contract":True,"status":"EXECUTED","literal_inputs":case["inputs"],
          "layer_entry":layer,"native_results":runs})
        require((ROOT/"corpus/must"/(case_id+".json")).read_bytes()==raw,"fixture changed")
        print(case_id+": "+verdict,flush=True)
    controls=[]
    for label,raw,mode,expected in control_inputs(cases):
        observed,h=execute(raw,label,mode,compiled)
        if expected=="MALFORMED":
            require(observed.get("status")=="MALFORMED","malformed control accepted: "+label);verdict="MALFORMED"
        else: verdict=verify(json.loads(raw),raw,observed,mode)
        require(verdict==expected,"control differs: "+label)
        controls.append({"label":label,"mode":mode,"corpus_pass":False,"status":"EXECUTED","expected":expected,"observed":verdict,
                         "input_sha256":h,"native_result":observed})
        print("control "+label+": "+verdict,flush=True)
    require(source_contract()==contract and all(p.read_bytes()==before[str(p)] for p in protected),"source/metadata changed")
    require(compiled["build_input_hashes"]==build_inputs() and compiled["harness_sha256"]==sha(HARNESS.read_bytes()),"build inputs changed")
    report={"schema":"gp-phase2-conditional-theorem-transport/v1","case_count":3,"corpus_executions":12,
      "separate_control_executions":len(controls),"cases":results,"controls":controls,"source_contract":contract,
      "metadata_hashes":{k:sha(v) for k,v in before.items()},"build":compiled,"adapter_sha256":sha(Path(__file__).read_bytes()),
      "tests_sha256":sha((ROOT/"tests/test_phase2_conditional_theorem_transport.py").read_bytes()),
      "g2_pass":False,"production_profile_adoption":False,"premises_discharged":False,"theorem_replayed":False,
      "elapsed_seconds":round(time.time()-started,3),
      "semantic_hypotheses":["named conditional Lean theorem JC.AUTH.ACTUAL_BLOCK_ONE: its three premise statements jointly imply its source-to-target reach"],
      "conditional_guarantee":"For every interpretation satisfying the named theorem hypothesis, a held consumer edge means only its own conditional statement: its premises imply its exact source-to-target reach. The target itself is never held; OPEN premises stay open.",
      "transport_boundary":"Licensing must imply equal authority/consumer endpoints and retention of every authority premise. Lean countermodels show omitted premises and rebound targets are not consequences of the authority.",
      "frozen_oracle_boundary":"Frozen observations come from the historical metadata normalizer only; no predecessor theorem replay is claimed.",
      "runtime_command_template":[str(LEAN),"--run",str(WRAPPER),"<scratch fixture>","<exact byte sha256>","<mode>"]}
    output.parent.mkdir(parents=True,exist_ok=True);output.write_bytes((json.dumps(report,indent=2)+"\n").encode())
    return report

if __name__=="__main__":
    p=argparse.ArgumentParser();p.add_argument("--output",type=Path,default=ROOT/"reports/PHASE-2-CONDITIONAL-THEOREM-TRANSPORT.json")
    run(p.parse_args().output)
