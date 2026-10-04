"""Open-premise guards for X399, X402 and X403; no census or family mathematics is certified."""
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
HARNESS=PACKAGE/"Tests/OpenPremiseGuard.lean"
SCRATCH=ROOT/"tmp/phase2-open-premise-guard"
TOOLCHAIN=ELAN_HOME/"toolchains"/(ROOT/"phase2/lean/lean-toolchain").read_text(encoding="utf-8").strip().replace("/","--").replace(":","---")
LAKE=TOOLCHAIN/("bin/lake" + EXE_SUFFIX)
LEAN=TOOLCHAIN/("bin/lean" + EXE_SUFFIX)
CHECKER=TOOLCHAIN/("bin/leanchecker" + EXE_SUFFIX)
OLEAN=SCRATCH/"Tests/OpenPremiseGuard.olean"
WRAPPER=SCRATCH/"Run.lean"
PIN="ac4155787207e2847d248cffed7be871d5dcd577"
ORACLE_COMMITS = {PIN, __import__("json").loads((ROOT / "oracle/PIN.json").read_text(encoding="utf-8-sig")).get("public_commit", PIN)}
SOURCE_COMMIT="b876fe4ed5c8963a0e8c19e18c829821c0686654"
CASES=('GP-X399', 'GP-X402', 'GP-X403')
HASHES={
"GP-X399": "cf8583a6198d4d29c479da443df2f26e7f4e4c1b3d021623a2a6e11bddc774a7",
"GP-X402": "490987e96755ceb32a5f6fb44bd0202488212ce348bc04cd1e70d37b7d1c144f",
"GP-X403": "f17172a2744b2346f254402b94c5aa755fed17ad81d1227a21a7ae0c23033f52"
}
DECLARATIONS=("licensed_slots","licensed_conclusion_sound","actual_base_sound","actual_validator_sound",
  "actual_fold_held_sound","open_slot_blocks","family_fact_is_not_model_fact")
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
    args=[LAKE,"env","lean","-o",OLEAN,"Tests/OpenPremiseGuard.lean"]
    log=command(args,env);(SCRATCH/"compile.log").write_text(log,encoding="utf-8")
    require("sorryAx" not in log and "error:" not in log,"unproved harness")
    declarations=re.findall(r"'OpenPremiseGuard\.([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)",log)
    require({n for n,_ in declarations}==set(DECLARATIONS),
      "axiom audit incomplete")
    axioms=sorted({a.strip() for _,group in declarations for a in group.split(",") if a.strip()})
    require(set(axioms)<={"propext","Quot.sound","Classical.choice"},"unexpected axiom")
    base=command([LAKE,"env","python","-c","import os;print(os.environ.get('LEAN_PATH',''))"],env).strip()
    env["LEAN_PATH"]=str(SCRATCH)+os.pathsep+base
    check_args=[CHECKER,"-v","Tests.OpenPremiseGuard"];checked=command(check_args,env)
    (SCRATCH/"checker.log").write_text(checked,encoding="utf-8")
    WRAPPER.write_text("import Tests.OpenPremiseGuard\n",encoding="utf-8")
    require(inputs==build_inputs() and source_hash==sha(HARNESS.read_bytes()),"build inputs changed during compilation")
    result={"build_input_hashes":inputs,"harness_sha256":source_hash,"olean_sha256":sha(OLEAN.read_bytes()),
      "wrapper_sha256":sha(WRAPPER.read_bytes()),"lean_path":env["LEAN_PATH"],"axioms":axioms,
      "compile_command":list(map(str,args)),"compile_exit_code":0,"compile_log_sha256":sha(log.encode()),
      "checker_command":list(map(str,check_args)),"checker_exit_code":0,"checker_log_sha256":sha(checked.encode()),
      "kernel_checked":True,"axiom_declarations":[n for n,_ in declarations]}
    stamp.write_text(json.dumps(result,indent=2),encoding="utf-8")
    return result

FRAMES={"GP-X399":"fixtures/D1-inference-on-family-claim/input.json","GP-X402":"transports/X8-X10.json","GP-X403":"transports/X8-X10.json"}
DK=Path("tests/fixtures/dk_retrodiction")

def lf_sha(raw): return sha(raw.replace(b"\r\n",b"\n"))

def source_contract():
    checkout=ROOT/"oracle/checkout";git=["git","-c","safe.directory="+str(checkout),"-C",str(checkout)]
    require(json.loads((ROOT/"oracle/PIN.json").read_bytes())["commit"]==PIN,"pin changed")
    require(subprocess.check_output(git+["rev-parse","HEAD"],text=True).strip() in ORACLE_COMMITS,"checkout changed")
    def pinned(path):
        raw=subprocess.check_output(git+["show","HEAD:" +path]);require((checkout/path).read_bytes()==raw,"pinned source changed")
        return raw
    out=[];test="tests/test_guard_release.py";raw=pinned(test);lines=raw.decode().splitlines()
    for n,anchor in ((26,"def test_family_premise_refuses_with_discharge_without_crashing("),
                     (75,"def test_ledger_and_open_slots_keep_their_original_obligations(")):
        require(lines[n-1].startswith(anchor),"predecessor anchor changed")
        out.append({"repository":"gp-v037","commit":PIN,"path":test,"line":n,"anchor":anchor,
                    "file_sha256":sha(raw),"anchor_sha256":sha(lines[n-1].encode())})
    manifest=json.loads(pinned((DK/"manifest.json").as_posix()))
    require(manifest["source_commit"]==SOURCE_COMMIT and manifest["hash_bytes"]=="LF","frozen manifest changed")
    for name in sorted(set(FRAMES.values())):
        raw=pinned((DK/name).as_posix());require(lf_sha(raw)==manifest["files"][name],"frozen frame changed")
        out.append({"repository":"gp-v037","commit":PIN,"path":(DK/name).as_posix(),"frame":name,
                    "lf_sha256":lf_sha(raw),"file_sha256":sha(raw)})
    return out

def frame_bytes(case_id): return (ROOT/"oracle/checkout"/DK/FRAMES[case_id]).read_bytes()

def checked_case(case_id,tags,routes,contract):
    raw=(ROOT/"corpus/must"/(case_id+".json")).read_bytes();case=json.loads(raw)
    row=next(r for r in tags["cases"] if r["id"]==case_id);i=case["inputs"]
    require(sha(raw)==HASHES[case_id]==row["sha256"],"fixture changed")
    require(row["primary_layer"]=="kernel" and row["full_contract_required"] is True and row["g2_kernel_eligible"] is True
      and row["review_group"]=="supplied-premise-authority","layer changed")
    require(case["expected"]["verdict"]=="REFUSE","expectation changed")
    require(i["fixture"]==FRAMES[case_id] and i["fixture_manifest_source_commit"]==SOURCE_COMMIT
      and i["fixture_lf_sha256"]==lf_sha(frame_bytes(case_id)),"fixture frame binding changed")
    require(all(any(all(c.get(k)==s[k] for k in s) for c in contract) for s in case["sources"]),"source pointers changed")
    route=routes["routes"][case_id]
    require(route["kind"]=="closure_fixture" and route["layer"]=="frozen_declaration_or_open_premise_guard","frozen route changed")
    return case,raw,row

def execute(raw,label,mode,frame,compiled=None):
    compiled=build() if compiled is None else compiled
    path=SCRATCH/(label+".fixture.json");path.write_bytes(raw)
    framed=SCRATCH/(label+".frame.json");framed.write_bytes(frame)
    env=os.environ.copy();env["LEAN_PATH"]=compiled["lean_path"];env["TEMP"]=str(SCRATCH);env["TMP"]=str(SCRATCH)
    result=command([LEAN,"--run",WRAPPER,path,sha(raw),mode,framed],env)
    return json.loads(result.strip().splitlines()[-1]),sha(path.read_bytes())

# Independent host decoding of the frozen frame and the slot gate.
def decode(frame):
    claims=[];infs={}
    for e in frame:
        if e["ev"]=="claim":
            require(("model" in e)!=("family" in e),"claim scope")
            claims.append({"id":e["id"],"model":"model" in e,"scope":e.get("model",e.get("family")),"statement":e["statement"]})
        elif e["ev"]=="inference":
            slots=[]
            for p in e["premises"]:
                if "claim" in p: require(p["path"]==[],"path");slots.append(("filled",p["claim"]))
                else: slots.append(("opened",p["required_kind"],p["at"],p["missing_why"]))
            infs[e["id"]]={"id":e["id"],"slots":slots,"asserted":e["asserted"]}
        else: require(e["ev"] in ("note","model","family"),"event")
    return claims,infs

def select(case,frame,mode):
    claims,infs=decode(frame);i=case["inputs"]
    inf=infs[i["inference"]["id"]] if case["id"]=="GP-X399" else infs[i["attempt"].split(":")[0]]
    if mode=="select_INF-X9": inf=infs["INF-X9"]
    if mode=="fill_open_slots":
        claims=claims+[{"id":"SUPPLIED:"+s[3],"model":True,"scope":s[2],"statement":s[3]} for s in inf["slots"] if s[0]=="opened"]
        inf=dict(inf,slots=[("filled","SUPPLIED:"+s[3]) if s[0]=="opened" else s for s in inf["slots"]])
    if mode=="family_bridge": claims=[dict(c,model=True) for c in claims]
    if mode=="dangling_reference": inf=dict(inf,slots=[("filled","UNKNOWN-CLAIM") if s[0]=="filled" else s for s in inf["slots"]])
    return claims,inf

def verify(case,raw,observed,mode,frame_raw):
    frame=json.loads(frame_raw);claims,inf=select(case,frame,mode);source=sha(raw)
    model=lambda c:any(r["id"]==c and r["model"] for r in claims)
    ok=all(s[0]=="filled" and model(s[1]) for s in inf["slots"])
    require(observed["literal_fixture"]==case and observed["source_digest"]==source and observed["case"]==case["id"]
      and observed["mode"]==mode and json.loads(observed["bound_literal"])==case and observed["frozen_frame"]==frame,"whole fixture/frame differs")
    slots=[{"claim":s[1],"model_level":model(s[1])} if s[0]=="filled" else {"required_kind":s[1],"at":s[2],"missing_why":s[3]} for s in inf["slots"]]
    require(observed["inference"]==inf["id"] and observed["asserted"]==inf["asserted"] and observed["slots"]==slots
      and observed["actual_license_check"]==ok,"actual slot gate differs")
    supports=[1] if ok else []
    require(observed["state"]=={"status":"OK","held":supports,"supports":supports,"domain":[1,100],"live_warrants":[1,100],
      "warrant_count":2,"current_count":2,"retracted":[],"successors":[]},"actual fold support/held differs")
    return "ACCEPT" if ok else "REFUSE"

def control_inputs(cases):
    out=[]
    for label,base,mode,expected in (("INF-X9_declared_E5_contrast","GP-X402","select_INF-X9","ACCEPT"),
                                     ("X8_supplied_E5_slot","GP-X402","fill_open_slots","ACCEPT"),
                                     ("X10_supplied_E5_gap_slot","GP-X403","fill_open_slots","ACCEPT"),
                                     ("D1_checked_family_bridge","GP-X399","family_bridge","ACCEPT"),
                                     ("X10_dangling_reference","GP-X403","dangling_reference","REFUSE"),
                                     ("INF-X9_dangling_reference","GP-X402","dangling_reference","REFUSE")):
        out.append((label,base,encoded(cases[base]),mode,expected))
    def add(label,base,edit):
        c=copy.deepcopy(cases[base]);edit(c["inputs"]);out.append((label,base,encoded(c),"normal","MALFORMED"))
    add("X402_wrong_available_premise","GP-X402",lambda i:i.update(available_premise="CL-E5-DECLARED"))
    add("X403_partial_available_premises","GP-X403",lambda i:i.update(available_premises=["CL-E5A","CL-E5B"]))
    add("X399_wrong_family","GP-X399",lambda i:i["claim"].update(family="G"))
    return out

def run(output):
    started=time.time();compiled=build();contract=source_contract()
    protected=[ROOT/p for p in ("corpus/LAYER-TAGS.json","oracle/ROUTES.json","oracle/PIN.json")]
    before={str(p):p.read_bytes() for p in protected};tags,routes=json.loads(protected[0].read_bytes()),json.loads(protected[1].read_bytes())
    results=[];cases={}
    for case_id in CASES:
        case,raw,layer=checked_case(case_id,tags,routes,contract);cases[case_id]=case;runs={};frame=frame_bytes(case_id)
        for mode in ORDERS:
            observed,h=execute(raw,case_id+"-"+mode,mode,frame,compiled);v=verify(case,raw,observed,mode,frame)
            require(v==case["expected"]["verdict"],"original verdict differs")
            runs[mode]=observed
        require(all({k:x for k,x in r.items() if k!="mode"}=={k:x for k,x in runs["normal"].items() if k!="mode"} for r in runs.values()),"event order/duplicates differ")
        results.append({"id":case_id,"source_sha256":sha(raw),"expected":case["expected"],"observed":v,
          "full_fixture_contract":True,"status":"EXECUTED","literal_inputs":case["inputs"],"layer_entry":layer,
          "frozen_frame_lf_sha256":lf_sha(frame),"native_results":runs})
        require((ROOT/"corpus/must"/(case_id+".json")).read_bytes()==raw,"fixture changed")
        print(case_id+": "+v,flush=True)
    controls=[]
    for label,base,raw,mode,expected in control_inputs(cases):
        frame=frame_bytes(base);observed,h=execute(raw,label,mode,frame,compiled)
        if expected=="MALFORMED":
            require(observed.get("status")=="MALFORMED","malformed control accepted: "+label);v="MALFORMED"
        else: v=verify(json.loads(raw),raw,observed,mode,frame)
        require(v==expected,"control differs: "+label)
        controls.append({"label":label,"mode":mode,"corpus_pass":False,"status":"EXECUTED","expected":expected,"observed":v,
                         "input_sha256":h,"native_result":observed})
        print("control "+label+": "+v,flush=True)
    require(source_contract()==contract and all(p.read_bytes()==before[str(p)] for p in protected),"source/metadata changed")
    require(compiled["build_input_hashes"]==build_inputs() and compiled["harness_sha256"]==sha(HARNESS.read_bytes()),"build inputs changed")
    report={"schema":"gp-phase2-open-premise-guard/v1","case_count":3,"corpus_executions":12,
      "separate_control_executions":len(controls),"cases":results,"controls":controls,"source_contract":contract,
      "metadata_hashes":{k:sha(v) for k,v in before.items()},"build":compiled,"adapter_sha256":sha(Path(__file__).read_bytes()),
      "tests_sha256":sha((ROOT/"tests/test_phase2_open_premise_guard.py").read_bytes()),
      "g2_pass":False,"production_profile_adoption":False,"census_or_family_mathematics_certified":False,
      "elapsed_seconds":round(time.time()-started,3),
      "semantic_hypotheses":["each supplied frozen claim's statement, at its own model or family level","the selected frozen inference step: its slot statements jointly imply its conclusion"],
      "conditional_guarantee":"A held conclusion means the selected inference's conclusion under its supplied premises; it is admitted only when every premise slot is filled by a model-level claim of the frozen frame.",
      "guard_boundary":"Open slots (E5 completeness, the E5 gap) and family-level premises without a checked bridge block the inference; countermodels show supplied facts compatible with the conclusion failing. INF-X9 and filled-slot controls accept only at the authority of their supplied, possibly declared-but-unproved premises.",
      "runtime_command_template":[str(LEAN),"--run",str(WRAPPER),"<scratch fixture>","<exact byte sha256>","<mode>","<frozen frame>"]}
    output.parent.mkdir(parents=True,exist_ok=True);output.write_bytes((json.dumps(report,indent=2)+"\n").encode())
    return report

if __name__=="__main__":
    p=argparse.ArgumentParser();p.add_argument("--output",type=Path,default=ROOT/"reports/PHASE-2-OPEN-PREMISE-GUARD.json")
    run(p.parse_args().output)
