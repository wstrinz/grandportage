"""Context reach for A01, A08a, X283 and X14; no field arithmetic is certified."""
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
HARNESS=PACKAGE/"Tests/ContextReach.lean"
SCRATCH=ROOT/"tmp/phase2-context-reach"
TOOLCHAIN=ELAN_HOME/"toolchains"/(ROOT/"phase2/lean/lean-toolchain").read_text(encoding="utf-8").strip().replace("/","--").replace(":","---")
LAKE=TOOLCHAIN/("bin/lake" + EXE_SUFFIX)
LEAN=TOOLCHAIN/("bin/lean" + EXE_SUFFIX)
CHECKER=TOOLCHAIN/("bin/leanchecker" + EXE_SUFFIX)
OLEAN=SCRATCH/"Tests/ContextReach.olean"
WRAPPER=SCRATCH/"Run.lean"
PIN="ac4155787207e2847d248cffed7be871d5dcd577"
ORACLE_COMMITS = {PIN, __import__("json").loads((ROOT / "oracle/PIN.json").read_text(encoding="utf-8-sig")).get("public_commit", PIN)}
CASES=('GP-A01', 'GP-A08a', 'GP-X283', 'GP-X14')
HASHES={
"GP-A01": "7344ab02090d0a57ae055ae0dd21187c6ad9d06b80fb19b76cf1585f50bc1b7e",
"GP-A08a": "1b1c035dbd18a9551b6828a250e757f0af21bdc54c2e434c3d4b3efb9745e41e",
"GP-X283": "4b2743f1f238273aa6972ce5cf50a4bc535b88ab41baae46082e34ea141939df",
"GP-X14": "8fb9507f532fded8e382eb118d0788a574a8ca86f6b1e735133c66d647b98fff"
}
ROUTE_KINDS={"GP-A01": "transport", "GP-A08a": "transport", "GP-X283": "universe_boundary", "GP-X14": "empty_anchor"}
DECLARATIONS=("source_given","direct_given","identity_transport_sound","debt_is_only_a_record","actual_base_sound",
  "actual_validator_sound","actual_fold_held_sound","held_target_fact","context_change_not_transported","debt_record_not_transport")
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
    args=[LAKE,"env","lean","-o",OLEAN,"Tests/ContextReach.lean"]
    log=command(args,env);(SCRATCH/"compile.log").write_text(log,encoding="utf-8")
    require("sorryAx" not in log and "error:" not in log,"unproved harness")
    declarations=re.findall(r"'ContextReach\.([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)",log)
    require({n for n,_ in declarations}==set(DECLARATIONS),
      "axiom audit incomplete")
    axioms=sorted({a.strip() for _,group in declarations for a in group.split(",") if a.strip()})
    require(set(axioms)<={"propext","Quot.sound","Classical.choice"},"unexpected axiom")
    base=command([LAKE,"env","python","-c","import os;print(os.environ.get('LEAN_PATH',''))"],env).strip()
    env["LEAN_PATH"]=str(SCRATCH)+os.pathsep+base
    check_args=[CHECKER,"-v","Tests.ContextReach"];checked=command(check_args,env)
    (SCRATCH/"checker.log").write_text(checked,encoding="utf-8")
    WRAPPER.write_text("import Tests.ContextReach\n",encoding="utf-8")
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
    for path,n,anchor in (("tests/test_kernel.py",222,"def test_field_relative_emptiness_refused_under_every_lossy_typing("),
                          ("tests/test_kernel.py",153,"def test_specialization_is_maximally_lossy("),
                          ("tests/test_adversarial.py",5229,"def test_untyped_remains_the_escape_valve_for_a_real_point_universe_change("),
                          ("tests/test_empty_scope_anchor.py",67,"def test_coefficient_domain_without_point_universe_is_not_an_anchor(")):
        raw=subprocess.check_output(git+["show","HEAD:" +path]);require((checkout/path).read_bytes()==raw,"pinned source changed")
        line=raw.decode().splitlines()[n-1];require(line.startswith(anchor),"predecessor anchor changed")
        out.append({"repository":"gp-v037","commit":PIN,"path":path,"line":n,"anchor":anchor,
                    "file_sha256":sha(raw),"anchor_sha256":sha(line.encode())})
    path="docs/GP-0.50-REWORK-PACKET.md";raw=(ROOT/path).read_bytes();lines=raw.decode("utf-8-sig").splitlines()
    for n,anchor in ((541,"| A1 |"),(548,"| A8 |")):
        require(lines[n-1].startswith(anchor),"packet anchor changed")
        out.append({"repository":"rework-packet","path":path,"line":n,"anchor":anchor,
                    "file_sha256":sha(raw),"anchor_sha256":sha(lines[n-1].encode())})
    return out

def checked_case(case_id,tags,routes,contract):
    raw=(ROOT/"corpus/must"/(case_id+".json")).read_bytes();case=json.loads(raw)
    row=next(r for r in tags["cases"] if r["id"]==case_id)
    require(sha(raw)==HASHES[case_id]==row["sha256"],"fixture changed")
    require(row["primary_layer"]=="kernel" and row["full_contract_required"] is True and row["g2_kernel_eligible"] is True
      and row["review_group"]=="supplied-premise-authority","layer changed")
    require(case["expected"]["verdict"]=="REFUSE","expectation changed")
    require(all(any(all(c.get(k)==s[k] for k in s) for c in contract) for s in case["sources"]),"source pointers changed")
    require(routes["routes"][case_id]["kind"]==ROUTE_KINDS[case_id],"frozen route changed")
    return case,raw,row

def execute(raw,label,mode,compiled=None):
    compiled=build() if compiled is None else compiled
    path=SCRATCH/(label+".fixture.json");path.write_bytes(raw)
    env=os.environ.copy();env["LEAN_PATH"]=compiled["lean_path"];env["TEMP"]=str(SCRATCH);env["TMP"]=str(SCRATCH)
    result=command([LEAN,"--run",WRAPPER,path,sha(raw),mode],env)
    return json.loads(result.strip().splitlines()[-1]),sha(path.read_bytes())

# Independent host decoding of each fixture schema into one context-reach input.
def decode(case):
    c,i=case["id"],case["inputs"]
    if c=="GP-A01":
        require(set(i)=={"context","target_context","warrant"} and i["warrant"]=="field-specific obstruction","A01 schema")
        s,t=i["context"],i["target_context"];return {"kind":"EMPTY","source":s,"target":t,"relation":"IDENTITY" if s==t else "BASE_EXTENSION","direct":None,"question":"license","debt":None}
    if c=="GP-A08a":
        require(set(i)=={"source_context","target_context","extra_certificate"},"A08a schema")
        s,t=i["source_context"],i["target_context"];return {"kind":"EMPTY","source":s,"target":t,"relation":"IDENTITY" if s==t else "SPECIALIZATION","direct":i["extra_certificate"],"question":"license","debt":None}
    if c=="GP-X283":
        require(set(i)=={"variables","equations","source_universe","target_universe","relation","question","debt_reason"} and i["relation"]=="UNTYPED","X283 schema")
        q={"license_nonempty_along":"license","record_step":"record"}[i["question"]]
        return {"kind":"NONEMPTY","source":i["source_universe"],"target":i["target_universe"],"relation":"UNTYPED","direct":None,"question":q,"debt":i["debt_reason"]}
    if c=="GP-X14":
        require(set(i)=={"coefficient_domain","point_universe","claimed_field"},"X14 schema")
        s=i["point_universe"] if i["point_universe"] is not None else "unanchored combinatorial objects over "+i["coefficient_domain"]
        t=i["claimed_field"];return {"kind":"EMPTY","source":s,"target":t,"relation":"IDENTITY" if s==t else "UNANCHORED","direct":None,"question":"license","debt":None}
    raise ValueError("uncommissioned")

def binding(d,source,literal,statement):
    return {"statementHash":statement,"scopeHash":d["relation"],"modelHash":d["source"]+" -> "+d["target"],"inputHashes":[source,literal],
      "authority":"test-only-context-reach-contract","authorityVersion":1,"kernelVersion":1}

def records(d,source,literal,mode):
    fact=lambda c:d["kind"]+" in context:"+c;debt="unanswered context step recorded:"+(d["debt"] or "none")
    rows=[{"id":1,"claim":1,"version":1,"binding":binding(d,source,literal,fact(d["target"])),
           "evidence":{"kind":"derived","premises":[10],"sideReceipt":"identity-context-transport"}},
          {"id":10,"claim":10,"version":1,"binding":binding(d,source,literal,fact(d["source"])),
           "evidence":{"kind":"receipt","data":"supplied:named-source-warrant"}},
          {"id":100,"claim":100,"version":1,"binding":binding(d,source,literal,"unanswered context step recorded:custody"),
           "evidence":{"kind":"citation","text":literal}}]
    if d["direct"] is not None:
        rows.append({"id":11,"claim":1,"version":1,"binding":binding(d,source,literal,fact(d["target"])),
                     "evidence":{"kind":"receipt","data":"supplied:named-direct-target-warrant:"+d["direct"]}})
    if d["debt"] is not None:
        rows.append({"id":3,"claim":3,"version":1,"binding":binding(d,source,literal,debt),
                     "evidence":{"kind":"receipt","data":"recorded:unanswered-context-step"}})
    if mode=="withheld_source": rows=[r for r in rows if r["id"]!=10]
    return sorted(rows,key=lambda r:r["id"])

def verify(case,raw,observed,mode):
    d=decode(case);source=sha(raw);ok=d["source"]==d["target"]
    require(observed["literal_fixture"]==case and observed["literal_inputs"]==case["inputs"] and observed["source_digest"]==source
      and observed["case"]==case["id"] and observed["mode"]==mode and json.loads(observed["bound_literal"])==case,"whole fixture differs")
    require(observed["kind"]==d["kind"] and observed["source_context"]==d["source"] and observed["target_context"]==d["target"]
      and observed["relation"]==d["relation"] and observed["direct_target_warrant"]==d["direct"] and observed["debt"]==d["debt"]
      and observed["actual_license_check"]==ok,"actual reach check differs")
    asked=3 if d["question"]=="record" else 1
    require(observed["asked_claim"]==asked,"asked claim differs")
    rows=records(d,source,observed["bound_literal"],mode)
    ids=sorted({r["claim"] for r in rows})
    currents=[{k:r[k] for k in ("claim","version","binding")} for r in rows if r["id"]!=11]
    currents=sorted(currents,key=lambda r:r["claim"])
    require(observed["snapshot"]=={"domain":ids,"warrants":rows,"currents":currents,"retracted":[],"successors":[]},"complete snapshot differs")
    source_held=mode!="withheld_source"
    supports=[r["id"] for r in rows if (r["id"]==10 and source_held) or (r["id"]==1 and ok and source_held)
              or r["id"]==11 or r["id"]==3]
    held=sorted({r["claim"] for r in rows if r["id"] in supports})
    require(observed["state"]["held"]==held and sorted(observed["state"]["supports"])==sorted(supports),"actual fold support/held differs")
    return "ACCEPT" if asked in held else "REFUSE"

def control_inputs(cases):
    out=[]
    def add(label,base,edit,expected,mode="normal"):
        c=copy.deepcopy(cases[base]);edit(c["inputs"]);out.append((label,encoded(c),mode,expected))
    add("A01_same_context_use","GP-A01",lambda i:i.update(target_context=i["context"]),"ACCEPT")
    add("A01_same_context_withheld_source","GP-A01",lambda i:i.update(target_context=i["context"]),"REFUSE","withheld_source")
    add("A08a_direct_target_certificate","GP-A08a",lambda i:i.update(extra_certificate="named characteristic-2 emptiness certificate"),"ACCEPT")
    add("A08a_reverse_characteristic","GP-A08a",lambda i:i.update(source_context="F_2",target_context="Q"),"REFUSE")
    add("X283_record_step_only","GP-X283",lambda i:i.update(question="record_step"),"ACCEPT")
    add("X283_reverse_universe","GP-X283",lambda i:i.update(source_universe="ALGEBRAIC_CLOSURE",target_universe="BASE"),"REFUSE")
    add("X14_anchored_point_universe","GP-X14",lambda i:i.update(point_universe="Q"),"ACCEPT")
    add("X14_mismatched_point_universe","GP-X14",lambda i:i.update(point_universe="Q(sqrt(17))"),"REFUSE")
    add("X283_typed_relation_unsupported","GP-X283",lambda i:i.update(relation="BASE_EXTENSION"),"MALFORMED")
    add("A01_unknown_warrant","GP-A01",lambda i:i.update(warrant="universal obstruction"),"MALFORMED")
    add("X14_extra_input_field","GP-X14",lambda i:i.update(bridge="asserted"),"MALFORMED")
    return out

def run(output):
    started=time.time();compiled=build();contract=source_contract()
    protected=[ROOT/p for p in ("corpus/LAYER-TAGS.json","oracle/ROUTES.json","oracle/PIN.json")]
    before={str(p):p.read_bytes() for p in protected};tags,routes=json.loads(protected[0].read_bytes()),json.loads(protected[1].read_bytes())
    results=[];cases={}
    for case_id in CASES:
        case,raw,layer=checked_case(case_id,tags,routes,contract);cases[case_id]=case;runs={}
        for mode in ORDERS:
            observed,h=execute(raw,case_id+"-"+mode,mode,compiled);v=verify(case,raw,observed,mode)
            require(v==case["expected"]["verdict"],"original verdict differs")
            runs[mode]=observed
        require(all({k:x for k,x in r.items() if k!="mode"}=={k:x for k,x in runs["normal"].items() if k!="mode"} for r in runs.values()),"event order/duplicates differ")
        results.append({"id":case_id,"source_sha256":sha(raw),"expected":case["expected"],"observed":v,
          "full_fixture_contract":True,"status":"EXECUTED","literal_inputs":case["inputs"],"layer_entry":layer,"native_results":runs})
        require((ROOT/"corpus/must"/(case_id+".json")).read_bytes()==raw,"fixture changed")
        print(case_id+": "+v,flush=True)
    controls=[]
    for label,raw,mode,expected in control_inputs(cases):
        observed,h=execute(raw,label,mode,compiled)
        if expected=="MALFORMED":
            require(observed.get("status")=="MALFORMED","malformed control accepted: "+label);v="MALFORMED"
        else: v=verify(json.loads(raw),raw,observed,mode)
        require(v==expected,"control differs: "+label)
        controls.append({"label":label,"mode":mode,"corpus_pass":False,"status":"EXECUTED","expected":expected,"observed":v,
                         "input_sha256":h,"native_result":observed})
        print("control "+label+": "+v,flush=True)
    require(source_contract()==contract and all(p.read_bytes()==before[str(p)] for p in protected),"source/metadata changed")
    require(compiled["build_input_hashes"]==build_inputs() and compiled["harness_sha256"]==sha(HARNESS.read_bytes()),"build inputs changed")
    report={"schema":"gp-phase2-context-reach/v1","case_count":4,"corpus_executions":16,
      "separate_control_executions":len(controls),"cases":results,"controls":controls,"source_contract":contract,
      "metadata_hashes":{k:sha(v) for k,v in before.items()},"build":compiled,"adapter_sha256":sha(Path(__file__).read_bytes()),
      "tests_sha256":sha((ROOT/"tests/test_phase2_context_reach.py").read_bytes()),
      "g2_pass":False,"production_profile_adoption":False,"field_arithmetic_certified":False,
      "elapsed_seconds":round(time.time()-started,3),
      "semantic_hypotheses":["named warrant for the stated emptiness/nonemptiness fact at its own source context",
        "named direct warrant for the target context, only when one is explicitly supplied"],
      "conditional_guarantee":"A held target fact means the stated emptiness/nonemptiness at exactly the target context. It is supported only by identity transport from the same context or a separately supplied direct target warrant.",
      "reach_boundary":"Base extension to a field family, specialization across characteristic, untyped point-universe change and unanchored combinatorial certificates license nothing; countermodels show each source fact is compatible with failure at the target. A recorded unanswered step is a record, not transport.",
      "runtime_command_template":[str(LEAN),"--run",str(WRAPPER),"<scratch fixture>","<exact byte sha256>","<mode>"]}
    output.parent.mkdir(parents=True,exist_ok=True);output.write_bytes((json.dumps(report,indent=2)+"\n").encode())
    return report

if __name__=="__main__":
    p=argparse.ArgumentParser();p.add_argument("--output",type=Path,default=ROOT/"reports/PHASE-2-CONTEXT-REACH.json")
    run(p.parse_args().output)
