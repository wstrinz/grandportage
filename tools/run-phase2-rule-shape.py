"""Rule-shape closure for A14, X04 and X09; no geometric content is certified."""
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
HARNESS=PACKAGE/"Tests/RuleShape.lean"
SCRATCH=ROOT/"tmp/phase2-rule-shape"
TOOLCHAIN=ELAN_HOME/"toolchains"/(ROOT/"phase2/lean/lean-toolchain").read_text(encoding="utf-8").strip().replace("/","--").replace(":","---")
LAKE=TOOLCHAIN/("bin/lake" + EXE_SUFFIX)
LEAN=TOOLCHAIN/("bin/lean" + EXE_SUFFIX)
CHECKER=TOOLCHAIN/("bin/leanchecker" + EXE_SUFFIX)
OLEAN=SCRATCH/"Tests/RuleShape.olean"
WRAPPER=SCRATCH/"Run.lean"
PIN="ac4155787207e2847d248cffed7be871d5dcd577"
ORACLE_COMMITS = {PIN, __import__("json").loads((ROOT / "oracle/PIN.json").read_text(encoding="utf-8-sig")).get("public_commit", PIN)}
CASES=('GP-A14', 'GP-X04', 'GP-X09')
HASHES={
"GP-A14": "e5861cacc4fd93f44bfecf22b11cbb91122a14d280353e1614cd772c1c81f2a6",
"GP-X04": "66765d2d909ccc85ea5aae3bfb92b10e4227bf617e955df86f68ff2d86c3c7cf",
"GP-X09": "a96cadd2b19933b83f7bfd83483e3d7323d78c43a32e5049bd74a3c9f1049230"
}
ROUTE_KINDS={"GP-A14": "disconnected", "GP-X04": "partition", "GP-X09": "kind_composition"}
DECLARATIONS=("step_sound","iterate_sound","closure_sound","closed_set_countermodel","derived_goal_sound",
  "actual_base_sound","actual_fold_held_sound")
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
    args=[LAKE,"env","lean","-o",OLEAN,"Tests/RuleShape.lean"]
    log=command(args,env);(SCRATCH/"compile.log").write_text(log,encoding="utf-8")
    require("sorryAx" not in log and "error:" not in log,"unproved harness")
    declarations=re.findall(r"'RuleShape\.([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)",log)
    require({n for n,_ in declarations}==set(DECLARATIONS),
      "axiom audit incomplete")
    axioms=sorted({a.strip() for _,group in declarations for a in group.split(",") if a.strip()})
    require(set(axioms)<={"propext","Quot.sound","Classical.choice"},"unexpected axiom")
    base=command([LAKE,"env","python","-c","import os;print(os.environ.get('LEAN_PATH',''))"],env).strip()
    env["LEAN_PATH"]=str(SCRATCH)+os.pathsep+base
    check_args=[CHECKER,"-v","Tests.RuleShape"];checked=command(check_args,env)
    (SCRATCH/"checker.log").write_text(checked,encoding="utf-8")
    WRAPPER.write_text("import Tests.RuleShape\n",encoding="utf-8")
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
    for path,n,anchor in (("tests/test_store.py",74,"def test_disconnected_inference_path_is_refused("),
                          ("tests/test_store.py",91,"def test_the_prototypes_fano_control_really_was_disconnected("),
                          ("grandportage/kernel.py",1252,"def transport_over_partition("),
                          ("grandportage/kernel.py",1595,"def check_conclusion_kind(")):
        raw=subprocess.check_output(git+["show","HEAD:" +path]);require((checkout/path).read_bytes()==raw,"pinned source changed")
        line=raw.decode().splitlines()[n-1];require(line.startswith(anchor),"predecessor anchor changed")
        out.append({"repository":"gp-v037","commit":PIN,"path":path,"line":n,"anchor":anchor,"file_sha256":sha(raw),"anchor_sha256":sha(line.encode())})
    path="docs/GP-0.50-REWORK-PACKET.md";raw=(ROOT/path).read_bytes();line=raw.decode("utf-8-sig").splitlines()[553]
    require(line.startswith("| A14 |"),"packet anchor changed")
    out.append({"repository":"rework-packet","path":path,"line":554,"anchor":"| A14 |","file_sha256":sha(raw),"anchor_sha256":sha(line.encode())})
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

# Independent host decoding and closure, matching the Lean step order exactly.
KINDS={"universal predicate":"PREDICATE","existence":"NONEMPTY","emptiness":"EMPTY"}
def decode(case):
    c,i=case["id"],case["inputs"]
    if c=="GP-A14":
        require(set(i)=={"claim_object","map_source","map_target"},"A14 schema")
        s,t=i["map_source"],i["map_target"]
        return ["NONEMPTY "+i["claim_object"]],[{"name":"inclusion "+s+"->"+t,"premises":["NONEMPTY "+s],"concl":"NONEMPTY "+t}],"NONEMPTY "+t
    if c=="GP-X04":
        require(set(i)=={"checked_exhaustive_cover","all_branches_empty"},"X04 schema")
        branches=["EMPTY branch-1","EMPTY branch-2"]
        rules=[{"name":"checked exhaustive partition","premises":branches,"concl":"EMPTY parent"}] if i["checked_exhaustive_cover"] else []
        return (branches if i["all_branches_empty"] else branches[:1]),rules,"EMPTY parent"
    if c=="GP-X09":
        require(set(i)=={"premise_kind","conclusion_kind","extra_rule"},"X09 schema")
        p,k=KINDS[i["premise_kind"]],KINDS[i["conclusion_kind"]]
        rules=[{"name":"pure transport","premises":[p+" source"],"concl":p+" target"}]
        if i["extra_rule"] is not None: rules.append({"name":i["extra_rule"],"premises":[p+" target"],"concl":k+" target"})
        return [p+" source"],rules,k+" target"
    raise ValueError("uncommissioned")
def closure(supplied,rules):
    T=list(supplied)
    for _ in range(len(rules)+1):
        T=T+[r["concl"] for r in rules if all(p in T for p in r["premises"])]
    return T

def verify(case,raw,observed,mode):
    supplied,rules,goal=decode(case);T=closure(supplied,rules);ok=goal in T
    closed=all(not all(p in T for p in r["premises"]) or r["concl"] in T for r in rules)
    require(observed["literal_fixture"]==case and observed["source_digest"]==sha(raw) and observed["case"]==case["id"]
      and observed["mode"]==mode and json.loads(observed["bound_literal"])==case,"whole fixture differs")
    require(observed["supplied"]==supplied and observed["rules"]==rules and observed["goal"]==goal and observed["closure"]==T
      and observed["closure_is_closed"] is True and closed and observed["actual_derivation"]==ok,"actual closure differs")
    require(observed["state"]=={"status":"OK","held":[1] if ok else [],"supports":[1] if ok else [],"domain":[1,100],
      "live_warrants":[1,100],"warrant_count":2,"current_count":2,"retracted":[],"successors":[]},"actual fold differs")
    return "ACCEPT" if ok else "REFUSE"

def control_inputs(cases):
    out=[]
    def add(label,base,edit,expected):
        c=copy.deepcopy(cases[base]);edit(c["inputs"]);out.append((label,encoded(c),"normal",expected))
    add("A14_path_starts_at_claim_object","GP-A14",lambda i:i.update(claim_object="A"),"ACCEPT")
    add("A14_other_disconnected_object","GP-A14",lambda i:i.update(claim_object="D"),"REFUSE")
    add("X04_every_branch_warranted","GP-X04",lambda i:i.update(all_branches_empty=True),"ACCEPT")
    add("X04_unchecked_cover","GP-X04",lambda i:i.update(all_branches_empty=True,checked_exhaustive_cover=False),"REFUSE")
    add("X09_same_kind_conclusion","GP-X09",lambda i:i.update(conclusion_kind="universal predicate"),"ACCEPT")
    add("X09_supplied_kind_changing_rule","GP-X09",lambda i:i.update(extra_rule="named witness-exhibition rule"),"ACCEPT")
    add("X09_emptiness_conclusion","GP-X09",lambda i:i.update(conclusion_kind="emptiness"),"REFUSE")
    add("X09_unknown_kind","GP-X09",lambda i:i.update(conclusion_kind="count"),"MALFORMED")
    add("A14_extra_input_field","GP-A14",lambda i:i.update(path=["E"]),"MALFORMED")
    add("X04_non_boolean_cover","GP-X04",lambda i:i.update(checked_exhaustive_cover="yes"),"MALFORMED")
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
    report={"schema":"gp-phase2-rule-shape/v1","case_count":3,"corpus_executions":12,
      "separate_control_executions":len(controls),"cases":results,"controls":controls,"source_contract":contract,
      "metadata_hashes":{k:sha(v) for k,v in before.items()},"build":compiled,"adapter_sha256":sha(Path(__file__).read_bytes()),
      "tests_sha256":sha((ROOT/"tests/test_phase2_rule_shape.py").read_bytes()),
      "g2_pass":False,"production_profile_adoption":False,"geometric_content_certified":False,
      "elapsed_seconds":round(time.time()-started,3),
      "semantic_hypotheses":["supplied atomic statements","registered one-step rules: inclusion edges, checked exhaustive partition, kind-preserving transport, and any explicitly supplied kind-changing rule"],
      "conditional_guarantee":"A held goal lies in the forward closure of the supplied atoms under the registered rules, so it holds in every interpretation satisfying them (closure_sound).",
      "rule_boundary":"A path not starting at the claim's object, a partition with an unwarranted branch or unchecked cover, and a kind change without a kind-changing rule leave the goal outside a closed set; closed_set_countermodel then gives an interpretation where every supplied atom and rule holds and the goal fails.",
      "runtime_command_template":[str(LEAN),"--run",str(WRAPPER),"<scratch fixture>","<exact byte sha256>","<mode>"]}
    output.parent.mkdir(parents=True,exist_ok=True);output.write_bytes((json.dumps(report,indent=2)+"\n").encode())
    return report

if __name__=="__main__":
    p=argparse.ArgumentParser();p.add_argument("--output",type=Path,default=ROOT/"reports/PHASE-2-RULE-SHAPE.json")
    run(p.parse_args().output)
