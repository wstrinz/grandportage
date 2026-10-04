"""Unreplayed evidence for X229 and X65; historical metadata and certificate names grant no authority."""
import argparse
import copy
from fractions import Fraction
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
HARNESS=PACKAGE/"Tests/UnreplayedEvidence.lean"
SCRATCH=ROOT/"tmp/phase2-unreplayed-evidence"
TOOLCHAIN=ELAN_HOME/"toolchains"/(ROOT/"phase2/lean/lean-toolchain").read_text(encoding="utf-8").strip().replace("/","--").replace(":","---")
LAKE=TOOLCHAIN/("bin/lake" + EXE_SUFFIX)
LEAN=TOOLCHAIN/("bin/lean" + EXE_SUFFIX)
CHECKER=TOOLCHAIN/("bin/leanchecker" + EXE_SUFFIX)
OLEAN=SCRATCH/"Tests/UnreplayedEvidence.olean"
WRAPPER=SCRATCH/"Run.lean"
PIN="ac4155787207e2847d248cffed7be871d5dcd577"
ORACLE_COMMITS = {PIN, __import__("json").loads((ROOT / "oracle/PIN.json").read_text(encoding="utf-8-sig")).get("public_commit", PIN)}
HISTORY="7991c9052f13e8dcaa78b5eae36f31663e080c1e"
CASES=('GP-X229', 'GP-X65')
HASHES={
"GP-X229": "3f3685e1ed902923312b9089569f97f7ae1d16c5e41636c4de7f36a555b2ccb8",
"GP-X65": "64a3d188feba3c23337c590efc67f4f950af984f0674041f7a67b120daf20cbe"
}
ROUTE_KINDS={"GP-X229": "replay_boundary", "GP-X65": "historical_paxis"}
DECLARATIONS=("unregistered_name_refused","held_identity_is_formal_span","current_verdict_sound","actual_base_sound",
  "actual_fold_held_sound","name_alone_no_meaning","stale_verdict_not_current")
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
    args=[LAKE,"env","lean","-o",OLEAN,"Tests/UnreplayedEvidence.lean"]
    log=command(args,env);(SCRATCH/"compile.log").write_text(log,encoding="utf-8")
    require("sorryAx" not in log and "error:" not in log,"unproved harness")
    declarations=re.findall(r"'UnreplayedEvidence\.([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)",log)
    require({n for n,_ in declarations}==set(DECLARATIONS),
      "axiom audit incomplete")
    axioms=sorted({a.strip() for _,group in declarations for a in group.split(",") if a.strip()})
    require(set(axioms)<={"propext","Quot.sound","Classical.choice"},"unexpected axiom")
    base=command([LAKE,"env","python","-c","import os;print(os.environ.get('LEAN_PATH',''))"],env).strip()
    env["LEAN_PATH"]=str(SCRATCH)+os.pathsep+base
    check_args=[CHECKER,"-v","Tests.UnreplayedEvidence"];checked=command(check_args,env)
    (SCRATCH/"checker.log").write_text(checked,encoding="utf-8")
    WRAPPER.write_text("import Tests.UnreplayedEvidence\n",encoding="utf-8")
    require(inputs==build_inputs() and source_hash==sha(HARNESS.read_bytes()),"build inputs changed during compilation")
    result={"build_input_hashes":inputs,"harness_sha256":source_hash,"olean_sha256":sha(OLEAN.read_bytes()),
      "wrapper_sha256":sha(WRAPPER.read_bytes()),"lean_path":env["LEAN_PATH"],"axioms":axioms,
      "compile_command":list(map(str,args)),"compile_exit_code":0,"compile_log_sha256":sha(log.encode()),
      "checker_command":list(map(str,check_args)),"checker_exit_code":0,"checker_log_sha256":sha(checked.encode()),
      "kernel_checked":True,"axiom_declarations":[n for n,_ in declarations]}
    stamp.write_text(json.dumps(result,indent=2),encoding="utf-8")
    return result

def source_contract():
    out=[]
    checkout=ROOT/"oracle/checkout";git=["git","-c","safe.directory="+str(checkout),"-C",str(checkout)]
    require(json.loads((ROOT/"oracle/PIN.json").read_bytes())["commit"]==PIN,"pin changed")
    require(subprocess.check_output(git+["rev-parse","HEAD"],text=True).strip() in ORACLE_COMMITS,"checkout changed")
    path="tests/test_artifacts.py";raw=subprocess.check_output(git+["show","HEAD:" +path])
    require((checkout/path).read_bytes()==raw,"pinned source changed");line=raw.decode().splitlines()[253]
    anchor="def test_unavailable_historical_backend_is_readable_but_not_authority("
    require(line.startswith(anchor),"predecessor anchor changed")
    out.append({"repository":"gp-v037","commit":PIN,"path":path,"line":254,"anchor":anchor,"file_sha256":sha(raw),"anchor_sha256":sha(line.encode())})
    pin=json.loads((ROOT/"oracle/history/PIN.json").read_bytes());require(pin["commit"]==HISTORY,"history pin changed")
    pinned={f["path"]:f["sha256"] for f in pin["files"]}
    path="tests/test_jc_p_axis_authority.py";raw=(ROOT/"oracle/history/checkout"/path).read_bytes()
    require(sha(raw)==pinned[path],"pinned history source changed");lines=raw.decode().splitlines()
    for n,anchor in ((168,"def test_certificate_name_without_verdict_grants_no_authority("),
                     (190,"def test_equation_or_guard_mutation_refuses_old_authority(")):
        require(lines[n-1].startswith(anchor),"history anchor changed")
        out.append({"repository":"gp-history","commit":HISTORY,"path":path,"line":n,"anchor":anchor,"file_sha256":sha(raw),"anchor_sha256":sha(lines[n-1].encode())})
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

# Independent host univariate parser and replay, matching PolyStub's summed coefficients.
def parse_poly(s):
    text=s.replace(" ","");require(text!="","empty");terms=[];cur="";neg=False
    for ch in text:
        if ch in "+-" and cur: terms.append((neg,cur));cur="";neg=ch=="-"
        elif ch=="-" and not cur: neg=not neg
        elif ch=="+" and not cur: pass
        else: cur+=ch
    terms.append((neg,cur));out=[]
    for neg,t in terms:
        parts=t.split("*")
        coeff,power=(parts if len(parts)==2 else (("1",parts[0]) if parts[0].startswith("x") else (parts[0],"")))
        c=Fraction(coeff);e=0 if power=="" else 1 if power=="x" else int(power.split("^")[1])
        require(power in ("","x") or power.startswith("x^"),"monomial")
        out.append((e,-c if neg else c))
    return out
def poly_json(p): return [[e,str(c)] for e,c in p]
def coefficient(p,e): return sum((c for x,c in p if x==e),Fraction(0))
def replay(gens,cofs,target):
    if len(gens)!=len(cofs): return False
    prod=[(i+j,x*y) for g,c in zip(gens,cofs) for i,x in g for j,y in c]
    top=max([e for e,_ in prod+target]+[0])
    return all(coefficient(prod,e)==coefficient(target,e) for e in range(top+1))

def verify229(case,observed):
    i=case["inputs"];gens=[parse_poly(g) for g in i["model"]["equations"]]
    target=parse_poly(i["identity"]["left"])+[(e,-c) for e,c in parse_poly(i["identity"]["right"])]
    cofs=None if i["cofactors"] is None else [parse_poly(c) for c in i["cofactors"]]
    ok=cofs is not None and replay(gens,cofs,target)
    historical="historical-execution:"+i["historical_identity"]+":"+i["local_backend"]+":"+i["raw_artifact"]
    require(observed["generators"]==[poly_json(g) for g in gens] and observed["target"]==poly_json(target)
      and observed["cofactors"]==(None if cofs is None else [poly_json(c) for c in cofs])
      and observed["historical_receipt"]==historical and observed["actual_replay"]==ok,"actual replay check differs")
    live=[10,20,100] if cofs is not None else [20,100]
    require(observed["state"]=={"status":"OK","held":[1] if ok else [],"supports":[10] if ok else [],"domain":[1,100],
      "live_warrants":live,"warrant_count":len(live),"current_count":2,"retracted":[],"successors":[]},"actual fold differs")
    return "ACCEPT" if ok else "REFUSE"

GENERATOR_MUTATION=["15*t^3+1","10*t*c9_11+14*p*t^2","5*c9_11^2+10*c9_11*p*t+5*p^2*t^2"]
def verify65(case,observed,mode):
    i=case["inputs"];canon=lambda v:json.dumps(v,sort_keys=True,separators=(",",":"),ensure_ascii=False)
    current=dict(i)
    if mode=="stale_after_generator_mutation": current["generators"]=GENERATOR_MUTATION
    if mode=="stale_after_guard_mutation": current["guards"]=["p"]
    checked=canon(i) if mode in ("checked_verdict","stale_after_generator_mutation","stale_after_guard_mutation") else None
    ok=checked==canon(current)
    require(observed["current_stratum"]==canon(current) and observed["checked_stratum"]==checked
      and observed["actual_currency_check"]==ok,"actual currency check differs")
    live=[10,20] if checked else [20]
    require(observed["state"]=={"status":"OK","held":[1] if ok else [],"supports":[10] if ok else [],"domain":[1],
      "live_warrants":live,"warrant_count":len(live),"current_count":1,"retracted":[],"successors":[]},"actual fold differs")
    return "ACCEPT" if ok else "REFUSE"

def verify(case,raw,observed,mode):
    require(observed["literal_fixture"]==case and observed["source_digest"]==sha(raw) and observed["case"]==case["id"]
      and observed["mode"]==mode and json.loads(observed["bound_literal"])==case,"whole fixture differs")
    return verify229(case,observed) if case["id"]=="GP-X229" else verify65(case,observed,mode)

def control_inputs(cases):
    out=[]
    def add(label,base,edit,expected,mode="normal"):
        c=copy.deepcopy(cases[base]);edit(c["inputs"]);out.append((label,encoded(c),mode,expected))
    add("X229_replayed_cofactor","GP-X229",lambda i:i.update(cofactors=["x"]),"ACCEPT")
    add("X229_wrong_cofactor","GP-X229",lambda i:i.update(cofactors=["1"]),"REFUSE")
    add("X229_false_identity_with_cofactor","GP-X229",lambda i:(i.update(cofactors=["x"]),i["identity"].update(right="1")),"REFUSE")
    add("X229_identified_historical_backend","GP-X229",lambda i:i.update(historical_identity="available"),"REFUSE")
    add("X229_unknown_question","GP-X229",lambda i:i.update(question="current_authority"),"MALFORMED")
    add("X229_unsupported_variable","GP-X229",lambda i:i["model"].update(variables=["y"]),"MALFORMED")
    add("X65_checked_verdict","GP-X65",lambda i:None,"ACCEPT","checked_verdict")
    add("X65_stale_after_generator_mutation","GP-X65",lambda i:None,"REFUSE","stale_after_generator_mutation")
    add("X65_stale_after_guard_mutation","GP-X65",lambda i:None,"REFUSE","stale_after_guard_mutation")
    add("X65_extra_input_field","GP-X65",lambda i:i.update(certificate_verdict="VERIFIED"),"MALFORMED")
    return out

def run(output):
    started=time.time();compiled=build();contract=source_contract()
    protected=[ROOT/p for p in ("corpus/LAYER-TAGS.json","oracle/ROUTES.json","oracle/PIN.json","oracle/history/PIN.json")]
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
    report={"schema":"gp-phase2-unreplayed-evidence/v1","case_count":2,"corpus_executions":8,
      "separate_control_executions":len(controls),"cases":results,"controls":controls,"source_contract":contract,
      "metadata_hashes":{k:sha(v) for k,v in before.items()},"build":compiled,"adapter_sha256":sha(Path(__file__).read_bytes()),
      "tests_sha256":sha((ROOT/"tests/test_phase2_unreplayed_evidence.py").read_bytes()),
      "g2_pass":False,"production_profile_adoption":False,"localized_certificate_replayed":False,
      "elapsed_seconds":round(time.time()-started,3),
      "X229_guarantee":"Held identity means formal univariate span membership (fold_held_formalSpan), admitted only by exact native cofactor replay. Historical execution metadata is never a registered receipt (unregistered_name_refused).",
      "X65_guarantee":"Held local emptiness requires a named checked verdict on exactly the current stratum data; a certificate name alone, or a verdict on mutated generators or guards, supplies nothing.",
      "boundary":"No backend process runs. The X65 localized certificate is multivariate and is not replayed; only its verdict binding is checked.",
      "runtime_command_template":[str(LEAN),"--run",str(WRAPPER),"<scratch fixture>","<exact byte sha256>","<mode>"]}
    output.parent.mkdir(parents=True,exist_ok=True);output.write_bytes((json.dumps(report,indent=2)+"\n").encode())
    return report

if __name__=="__main__":
    p=argparse.ArgumentParser();p.add_argument("--output",type=Path,default=ROOT/"reports/PHASE-2-UNREPLAYED-EVIDENCE.json")
    run(p.parse_args().output)
