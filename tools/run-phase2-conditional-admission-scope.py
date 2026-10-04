"""Conditional admission and GRH scope; no arithmetic checker or result is certified."""
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
HARNESS=PACKAGE/"Tests/ConditionalAdmissionScope.lean"
SCRATCH=ROOT/"tmp/phase2-conditional-admission-scope"
TOOLCHAIN=ELAN_HOME/"toolchains"/(ROOT/"phase2/lean/lean-toolchain").read_text(encoding="utf-8").strip().replace("/","--").replace(":","---")
LAKE=TOOLCHAIN/("bin/lake" + EXE_SUFFIX)
LEAN=TOOLCHAIN/("bin/lean" + EXE_SUFFIX)
CHECKER=TOOLCHAIN/("bin/leanchecker" + EXE_SUFFIX)
OLEAN=SCRATCH/"Tests/ConditionalAdmissionScope.olean"
WRAPPER=SCRATCH/"Run.lean"
PIN="ac4155787207e2847d248cffed7be871d5dcd577"
ORACLE_COMMITS = {PIN, __import__("json").loads((ROOT / "oracle/PIN.json").read_text(encoding="utf-8-sig")).get("public_commit", PIN)}
CASES=tuple("GP-A27-"+v for v in ("full","keep-GRH","drop-GRH","partial","heuristic","label"))
HASHES=dict(zip(CASES,[
"3b6a4951e36ee3eef411a6683042c4835ae0d91c951ae7b06531744eb2c49c8d",
"60edb3cb590c1499f5373c297a6955a7a811c5327a82f32fc604adfe399ee563",
"07e71e75ba74c4e6f72c189d6ade30debd93588986aa255c64bee548cf38d581",
"f8b86f9bfbe12ac9d85c3a6b72a6857a48d64b7cb3608ab5293c67f6b0be8183",
"f5e51e3992dc7f8d532af2d6bd54e2354c61ae1baf1506667fd4bc6e4721fcbf",
"300b58ac9161721c8e577cf8331c1f742bdd6bcfae1a66c640698d1f18c71b2e"]))
CLAIM={"kind":"class_group_complete","number_field":{"coefficient_field":"Q","defining_polynomial":"a^2+5","generator":"a"},"candidate_group_invariant_factors":[2]}
CLAIM_DIGEST="sha256:8e0e9c4edbfa3978deaa7a2f99aad4abed22e848eed83f93111d50c60fcc6149"
VERSION="synthetic-contract-1"

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
    args=[LAKE,"env","lean","-o",OLEAN,"Tests/ConditionalAdmissionScope.lean"]
    log=command(args,env);(SCRATCH/"compile.log").write_text(log,encoding="utf-8")
    require("sorryAx" not in log and "error:" not in log,"unproved harness")
    declarations=re.findall(r"'ConditionalAdmissionScope\.([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)",log)
    require({n for n,_ in declarations}=={"subset_sound","named_admission_given","named_success_given",
      "result_from_sound_contract","actual_base_sound","actual_validator_sound","actual_fold_held_sound",
      "held_target_is_conditional_full","GRH_cannot_be_dropped","quotient_does_not_imply_full","scope_narrowing_direction"},
      "axiom audit incomplete")
    axioms=sorted({a.strip() for _,group in declarations for a in group.split(",") if a.strip()})
    require(set(axioms)<={"propext","Quot.sound","Classical.choice"},"unexpected axiom")
    base=command([LAKE,"env","python","-c","import os;print(os.environ.get('LEAN_PATH',''))"],env).strip()
    env["LEAN_PATH"]=str(SCRATCH)+os.pathsep+base
    check_args=[CHECKER,"-v","Tests.ConditionalAdmissionScope"];checked=command(check_args,env)
    (SCRATCH/"checker.log").write_text(checked,encoding="utf-8")
    WRAPPER.write_text("import Tests.ConditionalAdmissionScope\n",encoding="utf-8")
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
    path="grandportage/kernel.py";raw=subprocess.check_output(git+["show","HEAD:" +path])
    require((checkout/path).read_bytes()==raw,"pinned source changed")
    line=raw.decode().splitlines()[141];require(line=="CLAIM_KINDS = (EMPTY, NONEMPTY, PREDICATE, IDENTITY)","predecessor anchor changed")
    out=[{"repository":"gp-v037","commit":PIN,"path":path,"line":142,"anchor":line,"file_sha256":sha(raw),"anchor_sha256":sha(line.encode())}]
    for path,line,anchor in [("docs/A27-CORRECTED-CONTRACT.md",n,"A27-"+variant+":") for n,variant in
      ((13,"heuristic"),(14,"drop-GRH"),(15,"keep-GRH"),(16,"partial"),(17,"full"),(18,"label"))]+[
      ("reports/PACKET-REV3-REVIEW.md",39,"**Proposed replacement:**")]:
        raw=(ROOT/path).read_bytes();text=raw.decode("utf-8-sig").splitlines()[line-1]
        require(anchor in text,"corrected source anchor changed")
        out.append({"repository":"rework-packet","path":path,"line":line,"anchor":anchor,
                    "file_sha256":sha(raw),"anchor_sha256":sha(text.encode())})
    return out

def checked_case(case_id,tags,routes,contracts):
    raw=(ROOT/"corpus/must"/(case_id+".json")).read_bytes();case=json.loads(raw)
    row=next(r for r in tags["cases"] if r["id"]==case_id)
    require(sha(raw)==HASHES[case_id]==row["sha256"],"fixture changed")
    require(row["primary_layer"]=="kernel" and row["full_contract_required"] is True and row["g2_kernel_eligible"] is True
      and row["review_group"]=="supplied-premise-authority","layer changed")
    require(case["inputs"]["claim"]==CLAIM and case["inputs"]["claim_sha256"]==CLAIM_DIGEST and
      "sha256:"+sha(encoded(CLAIM))==CLAIM_DIGEST,"fixed full claim digest changed")
    require(case["expected"]["verdict"]==("ACCEPT" if case_id in CASES[:2] else "REFUSE"),"expectation changed")
    require(all(any(all(c[k]==s[k] for k in s) for c in contracts) for s in case["sources"]),"source pointers changed")
    require(routes["commit"]==PIN and routes["routes"][case_id]=={
      "kind":"a27_unsupported_contract","layer":"unsupported_class_group_conditional_admission",
      "limitation":"Rule-level expectations under supplied premises only; no actual receipt/checker/tool run. Frozen v0.37 has no selected projection for class-group certification with explicit GRH assumptions. No native verdict inferred."},"frozen route changed")
    return case,raw,row

def execute(raw,label,mode,compiled=None):
    compiled=build() if compiled is None else compiled
    path=SCRATCH/(label+".fixture.json");path.write_bytes(raw)
    env=os.environ.copy();env["LEAN_PATH"]=compiled["lean_path"];env["TEMP"]=str(SCRATCH);env["TMP"]=str(SCRATCH)
    result=command([LEAN,"--run",WRAPPER,path,sha(raw),mode],env)
    return json.loads(result.strip().splitlines()[-1]),sha(path.read_bytes())

def scope(assumptions): return "assumptions=[GRH]" if assumptions==["GRH"] else "assumptions=[]"
def registration(inputs):
    p=inputs["supplied_premises"]
    registered=(p["checker_contract_version"]==VERSION and inputs["synthetic_producer"]==
      {"id":"class-group-contract-fixture","version":"1"} and p["evidence_status"]=="assumed_for_rule_level_test")
    admitted=p["checker_admitted"] and registered
    succeeded=p["bound_check_succeeded"] and registered and inputs["claim"]==CLAIM and inputs["claim_sha256"]==CLAIM_DIGEST and p["checked_claim_sha256"]==CLAIM_DIGEST and inputs["effective_result"]["conclusion"] in ("full_class_group","class_group_is_quotient_of_candidate")
    return admitted,succeeded

def binding(source,literal,claim_literal,statement,where):
    return {"statementHash":statement,"scopeHash":where,"modelHash":claim_literal,"inputHashes":[source,literal],
      "authority":"test-only-explicit-synthetic-admission-contract","authorityVersion":1,"kernelVersion":1}

def records(case,source,obs,mode):
    i=case["inputs"];literal=obs["bound_literal"];model=obs["bound_claim_literal"];fixed=obs["fixed_claim_literal"]
    kind=i["effective_result"]["conclusion"];reach=scope(i["effective_result"]["assumptions"]);requested=scope(i["requested_scope_assumptions"])
    result=lambda k,c:"result:"+k+":"+CLAIM_DIGEST+":"+c
    data=[
      (5,5,"named admitted checker contract:"+VERSION,"assumptions=[]",{"kind":"receipt","data":"supplied:named-admitted-contract"}),
      (6,6,"named successful bound check:"+CLAIM_DIGEST+":"+kind+":"+reach,"assumptions=[]",{"kind":"receipt","data":"supplied:named-successful-bound-check"}),
      (10,1,result(kind,fixed),reach,{"kind":"derived","premises":[5,6],"sideReceipt":"sound-bound-result-at-effective-reach"}),
      (20,2,result("full_class_group",fixed),requested,{"kind":"narrow","premise":10}),
      (100,100,result("producer_full_certification_label",model),"assumptions=[]",{"kind":"citation","text":literal})]
    rows=[{"id":id,"claim":key,"version":1,"binding":binding(source,literal,model,stmt,where),"evidence":ev}
      for id,key,stmt,where,ev in data]
    if mode=="withheld_success": rows=[r for r in rows if r["id"]!=6]
    if mode=="wrong_binding": rows[1]["binding"]["inputHashes"]=["corrupt binding"]
    if mode=="theorem_pointer": rows[1]["evidence"]={"kind":"theorem","declaration":"unadmitted_theorem_pointer"}
    if mode=="producer_label_only": rows[1]["evidence"]={"kind":"citation","text":"producer:Proof=Full"}
    if mode=="quotient_laundering": rows[3]["binding"]["statementHash"]=result(kind,fixed)
    return rows

def verify(case,raw,observed,mode):
    i=case["inputs"];source=sha(raw);admitted,succeeded=registration(i)
    require(observed["literal_fixture"]==case and observed["literal_inputs"]==i and observed["source_digest"]==source
      and observed["case"]==case["id"] and observed["mode"]==mode and observed["conditional"] is True,"whole conditional fixture differs")
    require(json.loads(observed["bound_literal"])==case and observed["bound_claim"]==i["claim"] and
      json.loads(observed["bound_claim_literal"])==i["claim"] and json.loads(observed["fixed_claim_literal"])==CLAIM,"whole claim binding differs")
    kind=i["effective_result"]["conclusion"];reach=scope(i["effective_result"]["assumptions"]);requested=scope(i["requested_scope_assumptions"])
    narrow=kind=="full_class_group" and (requested==reach or requested=="assumptions=[GRH]")
    if mode=="quotient_laundering" and kind!="full_class_group": narrow=False
    require(observed["admission_premise_registered"]==admitted and observed["successful_bound_check_registered"]==succeeded
      and observed["effective_result_kind"]==kind and observed["effective_scope"]==reach and observed["requested_scope"]==requested
      and observed["actual_narrow_check"]==narrow and observed["result_dependencies"]==[5,6],"actual admission/scope checks differ")
    rows=records(case,source,observed,mode);ids=sorted(r["claim"] for r in rows)
    currents=[{k:r[k] for k in ("claim","version","binding")} for r in sorted(rows,key=lambda r:r["claim"])]
    require(observed["snapshot"]=={"domain":ids,"warrants":rows,"currents":currents,"retracted":[],"successors":[]},"complete snapshot differs")
    supports=([5] if admitted else [])+([6] if succeeded and mode not in ("withheld_success","wrong_binding","theorem_pointer","producer_label_only") else [])
    if supports==[5,6]:
        supports.append(10)
        if narrow: supports.append(20)
    held=sorted(r["claim"] for r in rows if r["id"] in supports)
    require(observed["state"]=={"status":"OK","held":held,"supports":supports,"domain":ids,
      "live_warrants":[r["id"] for r in rows],"warrant_count":len(rows),"current_count":len(rows),
      "retracted":[],"successors":[]},"actual fold support/held differs")
    return "ACCEPT" if 2 in held else "REFUSE"

def control_inputs(cases):
    controls=[]
    def add(label,base,edit,expected):
        c=copy.deepcopy(cases[base]);edit(c["inputs"]);controls.append((label,encoded(c),"normal",expected))
    add("unconditional_full_narrows_to_GRH","GP-A27-full",lambda i:i.update(requested_scope_assumptions=["GRH"]),"ACCEPT")
    add("retain_GRH_scope","GP-A27-drop-GRH",lambda i:i.update(requested_scope_assumptions=["GRH"]),"ACCEPT")
    add("drop_GRH_scope","GP-A27-keep-GRH",lambda i:i.update(requested_scope_assumptions=[]),"REFUSE")
    add("checked_claim_digest_mismatch","GP-A27-full",lambda i:i["supplied_premises"].update(checked_claim_sha256="sha256:changed"),"REFUSE")
    add("declared_claim_digest_mismatch","GP-A27-full",lambda i:i.update(claim_sha256="sha256:changed"),"REFUSE")
    add("contract_version_mismatch","GP-A27-full",lambda i:i["supplied_premises"].update(checker_contract_version="synthetic-contract-2"),"REFUSE")
    add("producer_version_mismatch","GP-A27-full",lambda i:i["synthetic_producer"].update(version="2"),"REFUSE")
    add("changed_defining_polynomial","GP-A27-full",lambda i:i["claim"]["number_field"].update(defining_polynomial="a^2+6"),"REFUSE")
    add("changed_candidate_group","GP-A27-full",lambda i:i["claim"].update(candidate_group_invariant_factors=[3]),"REFUSE")
    add("withheld_success_flag","GP-A27-full",lambda i:i["supplied_premises"].update(bound_check_succeeded=False),"REFUSE")
    def fake(i):
        i["supplied_premises"].update(checker_admitted=True,bound_check_succeeded=True,
          checker_contract_version=VERSION,checked_claim_sha256=CLAIM_DIGEST,evidence_status="assumed_for_rule_level_test")
    add("heuristic_raw_success_flags","GP-A27-heuristic",fake,"REFUSE")
    add("label_raw_success_flags","GP-A27-label",fake,"REFUSE")
    for mode in ("withheld_success","wrong_binding","theorem_pointer","producer_label_only"):
        controls.append((mode,encoded(cases["GP-A27-full"]),mode,"REFUSE"))
    controls.append(("quotient_equality_laundering",encoded(cases["GP-A27-partial"]),"quotient_laundering","REFUSE"))
    return controls

def run(output):
    started=time.time();compiled=build();source=source_contract()
    protected=[ROOT/p for p in ("corpus/LAYER-TAGS.json","oracle/ROUTES.json","oracle/PIN.json")]
    before={str(p):p.read_bytes() for p in protected};tags,routes=json.loads(protected[0].read_bytes()),json.loads(protected[1].read_bytes())
    results=[];cases={}
    for case_id in CASES:
        case,raw,layer=checked_case(case_id,tags,routes,source);cases[case_id]=case;runs={}
        for mode in ("normal","reverse","duplicates","reverse_duplicates"):
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
        observed,h=execute(raw,label,mode,compiled);verdict=verify(json.loads(raw),raw,observed,mode)
        require(verdict==expected,"control differs: "+label)
        controls.append({"label":label,"mode":mode,"corpus_pass":False,"status":"EXECUTED","expected":expected,"observed":verdict,
                         "input_sha256":h,"native_result":observed})
        print("control "+label+": "+verdict,flush=True)
    require(source_contract()==source and all(p.read_bytes()==before[str(p)] for p in protected),"source/metadata changed")
    require(compiled["build_input_hashes"]==build_inputs() and compiled["harness_sha256"]==sha(HARNESS.read_bytes()),"build inputs changed")
    report={"schema":"gp-phase2-conditional-admission-scope/v1","case_count":6,"corpus_executions":24,
      "separate_control_executions":len(controls),"cases":results,"controls":controls,"source_contract":source,
      "metadata_hashes":{k:sha(v) for k,v in before.items()},"build":compiled,"adapter_sha256":sha(Path(__file__).read_bytes()),
      "tests_sha256":sha((ROOT/"tests/test_phase2_conditional_admission_scope.py").read_bytes()),
      "g2_pass":False,"production_profile_adoption":False,"class_group_arithmetic_certified":False,
      "elapsed_seconds":round(time.time()-started,3),
      "semantic_hypotheses":["named admitted synthetic checker contract premise","named successful check of the exact fixed claim, contract, result kind and assumption reach","sound registered contract maps admitted successful bound checks to only their result kind at their effective reach"],
      "conditional_guarantee":"For every arbitrary interpretation satisfying these explicit hypotheses, the actual fold's held target means full_class_group of exactly Q[a]/(a^2+5), generator a, candidate factors [2], only at the requested justified scope. Boolean metadata selects supplied premises; it never supplies unconditional arithmetic truth.",
      "scope_boundary":"GRH is a hypothesis restricting contexts. Actual acceptsNarrow permits unconditional full to GRH, refuses GRH to unconditional, and refuses quotient to full equality. Heuristics and producer labels have no admitted result even with fabricated success flags.",
      "frozen_oracle_boundary":"v0.37 remains UNSUPPORTED for these six contracts; no predecessor native arithmetic verdict is fabricated.",
      "runtime_command_template":[str(LEAN),"--run",str(WRAPPER),"<scratch fixture>","<exact byte sha256>","<mode>"]}
    output.parent.mkdir(parents=True,exist_ok=True);output.write_bytes((json.dumps(report,indent=2)+"\n").encode())
    return report

if __name__=="__main__":
    p=argparse.ArgumentParser();p.add_argument("--output",type=Path,default=ROOT/"reports/PHASE-2-CONDITIONAL-ADMISSION-SCOPE.json")
    run(p.parse_args().output)

