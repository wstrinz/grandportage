"""Section verdict provenance for X173-X176; no section arithmetic is replayed."""
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
HARNESS=PACKAGE/"Tests/SectionProvenance.lean"
SCRATCH=ROOT/"tmp/phase2-section-provenance"
TOOLCHAIN=ELAN_HOME/"toolchains"/(ROOT/"phase2/lean/lean-toolchain").read_text(encoding="utf-8").strip().replace("/","--").replace(":","---")
LAKE=TOOLCHAIN/("bin/lake" + EXE_SUFFIX)
LEAN=TOOLCHAIN/("bin/lean" + EXE_SUFFIX)
CHECKER=TOOLCHAIN/("bin/leanchecker" + EXE_SUFFIX)
OLEAN=SCRATCH/"Tests/SectionProvenance.olean"
WRAPPER=SCRATCH/"Run.lean"
PIN="ac4155787207e2847d248cffed7be871d5dcd577"
ORACLE_COMMITS = {PIN, __import__("json").loads((ROOT / "oracle/PIN.json").read_text(encoding="utf-8-sig")).get("public_commit", PIN)}
CASES=("GP-X173","GP-X174","GP-X175","GP-X176")
HASHES=dict(zip(CASES,[
"07eeaece74605fe78225a8bfc0cc1ea1c6cfbe3fba9c5e2731d3ef7a106d25d1","c524ac066832167e42a2951b35825864065a67a1e844e26ca114e52588a5dbbd","e9ef06ff3361a803278b6438c8c67a4a351001c0ce816c333bd7ee3075fc03aa","29d6ad1e77fd57de76ce5e417de4318fe3fe56766ae537d8cb434df1536a9a31"]))
INPUTS={"GP-X173":{"sequence":["success","rejected"],"mutation":None},"GP-X174":{"sequence":["rejected"],"mutation":None},
  "GP-X175":{"sequence":["success"],"mutation":"proof"},"GP-X176":{"sequence":["success"],"mutation":"missing"}}
VERIFIER="verify.elimination_section"
EDGE="E:SOURCE->TARGET"
DECLARATIONS=("bound_stores_checked","bound_section_sound","rejection_given","actual_base_sound","actual_validator_sound",
  "actual_fold_held_sound","held_section_is_valid_stored","mutated_certificate_not_covered",
  "missing_object_has_no_meaning","rejection_is_not_section")
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
    args=[LAKE,"env","lean","-o",OLEAN,"Tests/SectionProvenance.lean"]
    log=command(args,env);(SCRATCH/"compile.log").write_text(log,encoding="utf-8")
    require("sorryAx" not in log and "error:" not in log,"unproved harness")
    declarations=re.findall(r"'SectionProvenance\.([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)",log)
    require({n for n,_ in declarations}==set(DECLARATIONS),
      "axiom audit incomplete")
    axioms=sorted({a.strip() for _,group in declarations for a in group.split(",") if a.strip()})
    require(set(axioms)<={"propext","Quot.sound","Classical.choice"},"unexpected axiom")
    base=command([LAKE,"env","python","-c","import os;print(os.environ.get('LEAN_PATH',''))"],env).strip()
    env["LEAN_PATH"]=str(SCRATCH)+os.pathsep+base
    check_args=[CHECKER,"-v","Tests.SectionProvenance"];checked=command(check_args,env)
    (SCRATCH/"checker.log").write_text(checked,encoding="utf-8")
    WRAPPER.write_text("import Tests.SectionProvenance\n",encoding="utf-8")
    require(inputs==build_inputs() and source_hash==sha(HARNESS.read_bytes()),"build inputs changed during compilation")
    result={"build_input_hashes":inputs,"harness_sha256":source_hash,"olean_sha256":sha(OLEAN.read_bytes()),
      "wrapper_sha256":sha(WRAPPER.read_bytes()),"lean_path":env["LEAN_PATH"],"axioms":axioms,
      "compile_command":list(map(str,args)),"compile_exit_code":0,"compile_log_sha256":sha(log.encode()),
      "checker_command":list(map(str,check_args)),"checker_exit_code":0,"checker_log_sha256":sha(checked.encode()),
      "kernel_checked":True,"axiom_declarations":[n for n,_ in declarations]}
    stamp.write_text(json.dumps(result,indent=2),encoding="utf-8")
    return result

def canonical(value): return json.dumps(value,sort_keys=True,separators=(",",":"),ensure_ascii=False)

def pinned_representations(raw):
    tree=ast.parse(raw.decode("utf-8"))
    fn=next(n for n in tree.body if isinstance(n,ast.FunctionDef) and n.name=="_section_representation")
    require((fn.lineno,fn.end_lineno)==(646,662) and len(fn.body)==1,"pinned certificate moved")
    checked=ast.literal_eval(fn.body[0].value);mutated=copy.deepcopy(checked)
    # Exactly the four edits of test_mutating_stored_section_certificate_makes_verdict_stale.
    mutated["section"]["y"]="x^99";mutated["images"]["y"]="x^99"
    mutated["rows"][0]["substituted"]="totally_forged";mutated["rows"][0]["cofactors"]=["also_forged"]
    return canonical(checked),canonical(mutated)

def source_contract():
    checkout=ROOT/"oracle/checkout";git=["git","-c","safe.directory="+str(checkout),"-C",str(checkout)]
    require(json.loads((ROOT/"oracle/PIN.json").read_bytes())["commit"]==PIN,"pin changed")
    require(subprocess.check_output(git+["rev-parse","HEAD"],text=True).strip() in ORACLE_COMMITS,"checkout changed")
    out=[]
    def pinned(path):
        raw=subprocess.check_output(git+["show","HEAD:" +path]);require((checkout/path).read_bytes()==raw,"pinned source changed")
        return raw
    test="tests/test_verdict_provenance.py";raw=pinned(test);lines=raw.decode().splitlines()
    for n,anchor in ((679,"def test_rejected_section_does_not_erase_prior_exact_certificate("),
                     (706,"def test_verified_section_without_proof_object_is_refused("),
                     (731,"def test_mutating_stored_section_certificate_makes_verdict_stale("),
                     (748,"def test_section_verdict_stamped_as_groebner_is_stale("),
                     (646,"def _section_representation(")):
        require(lines[n-1].startswith(anchor),"predecessor anchor changed")
        out.append({"repository":"gp-v037","commit":PIN,"path":test,"line":n,"anchor":anchor,
                    "file_sha256":sha(raw),"anchor_sha256":sha(lines[n-1].encode())})
    checked,mutated=pinned_representations(raw)
    verify="grandportage/verify.py";vraw=pinned(verify);vlines=vraw.decode().splitlines()
    for n,anchor in ((974,'SECTION_VERIFIED = "VERIFIED_SECTION"'),(975,'SECTION_REJECTED = "CERTIFICATE_REJECTED"')):
        require(vlines[n-1]==anchor,"verdict name anchor changed")
        out.append({"repository":"gp-v037","commit":PIN,"path":verify,"line":n,"anchor":anchor,
                    "file_sha256":sha(vraw),"anchor_sha256":sha(anchor.encode())})
    prov="grandportage/provenance.py";praw=pinned(prov);plines=praw.decode().splitlines()
    require(plines[82].strip()=='"VERIFIED_SECTION": "verify.elimination_section",',"verifier anchor changed")
    out.append({"repository":"gp-v037","commit":PIN,"path":prov,"line":83,"anchor":plines[82].strip(),
                "file_sha256":sha(praw),"anchor_sha256":sha(plines[82].encode())})
    out.append({"repository":"gp-v037","commit":PIN,"path":test,"certificates":{"checked":checked,"mutated":mutated},
                "file_sha256":sha(raw)})
    return out

def certificates(contract): return next(c["certificates"] for c in contract if "certificates" in c)

def checked_case(case_id,tags,routes,contract):
    raw=(ROOT/"corpus/must"/(case_id+".json")).read_bytes();case=json.loads(raw)
    row=next(r for r in tags["cases"] if r["id"]==case_id)
    require(sha(raw)==HASHES[case_id]==row["sha256"],"fixture changed")
    require(row["primary_layer"]=="kernel" and row["full_contract_required"] is True and row["g2_kernel_eligible"] is True
      and row["review_group"]==("stored-certificate-binding" if case_id=="GP-X175" else "supplied-premise-authority"),"layer changed")
    require(case["inputs"]==INPUTS[case_id],"fixture inputs changed")
    require(case["expected"]["verdict"]==("ACCEPT" if case_id=="GP-X173" else "REFUSE"),"expectation changed")
    require(all(any(all(c.get(k)==s[k] for k in s) for c in contract) for s in case["sources"]),"source pointers changed")
    route=routes["routes"][case_id]
    require(route["kind"]=="lifecycle" and route["action"]=="section" and route["layer"]=="exact_section_and_provenance","frozen route changed")
    return case,raw,row

def execute(raw,label,mode,compiled=None):
    compiled=build() if compiled is None else compiled
    path=SCRATCH/(label+".fixture.json");path.write_bytes(raw)
    env=os.environ.copy();env["LEAN_PATH"]=compiled["lean_path"];env["TEMP"]=str(SCRATCH);env["TMP"]=str(SCRATCH)
    result=command([LEAN,"--run",WRAPPER,path,sha(raw),mode],env)
    return json.loads(result.strip().splitlines()[-1]),sha(path.read_bytes())

# Independent host mirror of the Lean verdict, binding check and warrant records.
def verdict(inputs,mode,certs):
    stored={None:certs["checked"],"missing":None,"proof":certs["mutated"]}[inputs["mutation"]]
    v={"verifier":VERIFIER,"verdict":"VERIFIED_SECTION","checked":certs["checked"],"stored":stored}
    if mode=="groebner_stamp": v["verifier"]="verify.elimination_groebner"
    if mode=="rejected_verdict_stamp": v["verdict"]="CERTIFICATE_REJECTED"
    return v
def bound(v,certs):
    return v["verifier"]==VERIFIER and v["verdict"]=="VERIFIED_SECTION" and v["checked"]==certs["checked"] and v["stored"]==v["checked"]

def binding(source,literal,statement):
    return {"statementHash":statement,"scopeHash":"N/A","modelHash":EDGE,"inputHashes":[source,literal],
      "authority":"test-only-section-provenance-contract","authorityVersion":1,"kernelVersion":1}

def records(case,source,literal,v):
    section="current exact section certificate:"+EDGE+":"+(v["stored"] if v["stored"] is not None else "none")
    rejection="different proposed section rejected:"+EDGE
    data=v["verdict"]+":"+v["verifier"]+":checked="+v["checked"]+":stored="+(v["stored"] if v["stored"] is not None else "none")
    made={"success":{"id":10,"claim":1,"version":1,"binding":binding(source,literal,section),"evidence":{"kind":"receipt","data":data}},
          "rejected":{"id":20,"claim":2,"version":1,"binding":binding(source,literal,rejection),
            "evidence":{"kind":"receipt","data":"CERTIFICATE_REJECTED:"+VERIFIER+":this different proposed section fails"}}}
    rows=[made[s] for s in dict.fromkeys(case["inputs"]["sequence"])]
    rows.append({"id":100,"claim":100,"version":1,"binding":binding(source,literal,"current exact section certificate:"+EDGE+":none"),
                 "evidence":{"kind":"citation","text":literal}})
    return sorted(rows,key=lambda r:r["id"])

def verify(case,raw,observed,mode,certs):
    i=case["inputs"];source=sha(raw);v=verdict(i,mode,certs);ok=bound(v,certs)
    require(observed["literal_fixture"]==case and observed["literal_inputs"]==i and observed["source_digest"]==source
      and observed["case"]==case["id"] and observed["mode"]==mode and json.loads(observed["bound_literal"])==case,"whole fixture differs")
    require(observed["checked_representation"]==certs["checked"] and observed["stored_representation"]==v["stored"]
      and observed["verifier"]==v["verifier"] and observed["verdict"]==v["verdict"] and observed["actual_binding_check"]==ok,"actual binding check differs")
    rows=records(case,source,observed["bound_literal"],v);ids=sorted(r["claim"] for r in rows)
    retracted=[10] if mode=="rejection_as_retraction" else []
    currents=[{k:r[k] for k in ("claim","version","binding")} for r in rows]
    require(observed["snapshot"]=={"domain":ids,"warrants":rows,"currents":currents,"retracted":retracted,"successors":[]},"complete snapshot differs")
    supports=[r["id"] for r in rows if (r["id"]==10 and ok and not retracted) or r["id"]==20]
    held=sorted(r["claim"] for r in rows if r["id"] in supports)
    require(observed["state"]["held"]==held and sorted(observed["state"]["supports"])==sorted(supports),"actual fold support/held differs")
    return "ACCEPT" if 1 in held else "REFUSE"

def control_inputs(cases):
    out=[];base=encoded(cases["GP-X173"])
    for mode in ("groebner_stamp","rejected_verdict_stamp","rejection_as_retraction"): out.append((mode,base,mode,"REFUSE"))
    def add(label,inputs,expected):
        c=copy.deepcopy(cases["GP-X173"]);c["inputs"]=inputs;out.append((label,encoded(c),"normal",expected))
    add("success_only",{"sequence":["success"],"mutation":None},"ACCEPT")
    add("rejected_before_success",{"sequence":["rejected","success"],"mutation":None},"ACCEPT")
    add("missing_object_with_rejection",{"sequence":["success","rejected"],"mutation":"missing"},"REFUSE")
    add("mutated_object_with_rejection",{"sequence":["success","rejected"],"mutation":"proof"},"REFUSE")
    add("unknown_step",{"sequence":["promoted"],"mutation":None},"MALFORMED")
    add("unknown_mutation",{"sequence":["success"],"mutation":"cofactor"},"MALFORMED")
    add("extra_input_field",{"sequence":["success"],"mutation":None,"verified":True},"MALFORMED")
    return out

def run(output):
    started=time.time();compiled=build();contract=source_contract();certs=certificates(contract)
    protected=[ROOT/p for p in ("corpus/LAYER-TAGS.json","oracle/ROUTES.json","oracle/PIN.json")]
    before={str(p):p.read_bytes() for p in protected};tags,routes=json.loads(protected[0].read_bytes()),json.loads(protected[1].read_bytes())
    results=[];cases={}
    for case_id in CASES:
        case,raw,layer=checked_case(case_id,tags,routes,contract);cases[case_id]=case;runs={}
        for mode in ORDERS:
            observed,h=execute(raw,case_id+"-"+mode,mode,compiled);v=verify(case,raw,observed,mode,certs)
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
        else: v=verify(json.loads(raw),raw,observed,mode,certs)
        require(v==expected,"control differs: "+label)
        controls.append({"label":label,"mode":mode,"corpus_pass":False,"status":"EXECUTED","expected":expected,"observed":v,
                         "input_sha256":h,"native_result":observed})
        print("control "+label+": "+v,flush=True)
    require(source_contract()==contract and all(p.read_bytes()==before[str(p)] for p in protected),"source/metadata changed")
    require(compiled["build_input_hashes"]==build_inputs() and compiled["harness_sha256"]==sha(HARNESS.read_bytes()),"build inputs changed")
    report={"schema":"gp-phase2-section-provenance/v1","case_count":4,"corpus_executions":16,
      "separate_control_executions":len(controls),"cases":results,"controls":controls,"source_contract":contract,
      "metadata_hashes":{k:sha(v) for k,v in before.items()},"build":compiled,"adapter_sha256":sha(Path(__file__).read_bytes()),
      "tests_sha256":sha((ROOT/"tests/test_phase2_section_provenance.py").read_bytes()),
      "g2_pass":False,"production_profile_adoption":False,"section_arithmetic_replayed":False,
      "elapsed_seconds":round(time.time()-started,3),
      "semantic_hypotheses":["named successful check by verify.elimination_section of exactly the pinned section certificate",
        "named rejection of a different proposed section"],
      "conditional_guarantee":"A held section claim means its stored certificate is valid; the binding check admits it only when the stored object is byte-identical to the certificate the registered verifier checked.",
      "lifecycle_boundary":"A rejection is a separate current record about another proposal; it neither supplies nor retracts the section claim. Only an explicit targeted retraction removes support (contrast control).",
      "profile_boundary":"No polynomial substitution or cofactor arithmetic is replayed; any replacement certificate needs separate profile validation.",
      "runtime_command_template":[str(LEAN),"--run",str(WRAPPER),"<scratch fixture>","<exact byte sha256>","<mode>"]}
    output.parent.mkdir(parents=True,exist_ok=True);output.write_bytes((json.dumps(report,indent=2)+"\n").encode())
    return report

if __name__=="__main__":
    p=argparse.ArgumentParser();p.add_argument("--output",type=Path,default=ROOT/"reports/PHASE-2-SECTION-PROVENANCE.json")
    run(p.parse_args().output)
