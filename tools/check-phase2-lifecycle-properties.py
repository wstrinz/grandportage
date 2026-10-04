"""Kernel-checked lifecycle, retraction and totality properties (proof-only; no corpus cases)."""
import argparse
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
HARNESS=PACKAGE/"Tests/LifecycleProperties.lean"
SCRATCH=ROOT/"tmp/phase2-lifecycle-properties"
TOOLCHAIN=ELAN_HOME/"toolchains"/(ROOT/"phase2/lean/lean-toolchain").read_text(encoding="utf-8").strip().replace("/","--").replace(":","---")
LAKE=TOOLCHAIN/("bin/lake" + EXE_SUFFIX)
LEAN=TOOLCHAIN/("bin/lean" + EXE_SUFFIX)
CHECKER=TOOLCHAIN/("bin/leanchecker" + EXE_SUFFIX)
OLEAN=SCRATCH/"Tests/LifecycleProperties.olean"
WRAPPER=SCRATCH/"Run.lean"
DECLARATIONS=("retract_reachable_iff","retract_closure_iff","retracted_not_supported","avoiding_reachable",
  "requirements_not_live","attempt_requirements","extra_nodes_keep_support","no_bootstrap","fold_total")
NONTOTAL=re.compile(r"\b(partial|unsafe)\s+def\b|\bopaque\b|implemented_by|@\[extern|\bsorry\b|\bnative_decide\b")

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
    args=[LAKE,"env","lean","-o",OLEAN,"Tests/LifecycleProperties.lean"]
    log=command(args,env);(SCRATCH/"compile.log").write_text(log,encoding="utf-8")
    require("sorryAx" not in log and "error:" not in log,"unproved harness")
    declarations=re.findall(r"'GP50\.LifecycleProperties\.([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)",log)
    require({n for n,_ in declarations}==set(DECLARATIONS),
      "axiom audit incomplete")
    axioms=sorted({a.strip() for _,group in declarations for a in group.split(",") if a.strip()})
    require(set(axioms)<={"propext","Quot.sound","Classical.choice"},"unexpected axiom")
    base=command([LAKE,"env","python","-c","import os;print(os.environ.get('LEAN_PATH',''))"],env).strip()
    env["LEAN_PATH"]=str(SCRATCH)+os.pathsep+base
    check_args=[CHECKER,"-v","Tests.LifecycleProperties"];checked=command(check_args,env)
    (SCRATCH/"checker.log").write_text(checked,encoding="utf-8")
    WRAPPER.write_text("import Tests.LifecycleProperties\n",encoding="utf-8")
    require(inputs==build_inputs() and source_hash==sha(HARNESS.read_bytes()),"build inputs changed during compilation")
    result={"build_input_hashes":inputs,"harness_sha256":source_hash,"olean_sha256":sha(OLEAN.read_bytes()),
      "wrapper_sha256":sha(WRAPPER.read_bytes()),"lean_path":env["LEAN_PATH"],"axioms":axioms,
      "compile_command":list(map(str,args)),"compile_exit_code":0,"compile_log_sha256":sha(log.encode()),
      "checker_command":list(map(str,check_args)),"checker_exit_code":0,"checker_log_sha256":sha(checked.encode()),
      "kernel_checked":True,"axiom_declarations":[n for n,_ in declarations]}
    stamp.write_text(json.dumps(result,indent=2),encoding="utf-8")
    return result

def totality_audit():
    sources=sorted((PACKAGE/"GP50").rglob("*.lean"))
    hits=[(str(p.relative_to(ROOT)),n+1,line.strip()) for p in sources
          for n,line in enumerate(p.read_text(encoding="utf-8").splitlines())
          if NONTOTAL.search(line.split("--")[0])]
    return {"kernel_sources":len(sources),"source_hashes":{str(p.relative_to(ROOT)):sha(p.read_bytes()) for p in sources},"violations":hits}

def run(output):
    started=time.time();compiled=build();audit=totality_audit()
    require(not audit["violations"],"kernel contains non-total or unchecked declarations")
    report={"schema":"gp-phase2-lifecycle-properties/v1","build":compiled,"totality_audit":audit,
      "adapter_sha256":sha(Path(__file__).read_bytes()),"corpus_cases":0,"g2_pass":False,
      "properties":{
        "retraction_invalidates_exactly_dependents":"retract_reachable_iff / retract_closure_iff: after retracting w, an id is supported iff it has a derivation avoiding w; retracted_not_supported and avoiding_reachable bound both directions; requirements_not_live ties retraction to the runtime.",
        "failed_retries_never_revoke":"attempt_requirements: attempts contribute no requirements; extra_nodes_keep_support: added nodes never remove support.",
        "circular_support_never_bootstraps":"no_bootstrap: with no requirement-free node, nothing is reachable.",
        "determinism_and_totality":"fold_total plus the source audit: every kernel definition is an ordinary total Lean function (no partial, unsafe, opaque, implemented_by, extern, sorry or native_decide); fold_eq_of_mem_iff makes the result depend only on the event set."},
      "elapsed_seconds":round(time.time()-started,3)}
    output.parent.mkdir(parents=True,exist_ok=True);output.write_bytes((json.dumps(report,indent=2)+"\n").encode())
    return report

if __name__=="__main__":
    p=argparse.ArgumentParser();p.add_argument("--output",type=Path,default=ROOT/"reports/PHASE-2-LIFECYCLE-PROPERTIES.json")
    run(p.parse_args().output)
