"""Native residual-relation and multi-successor custody contracts."""
import argparse
import ast
import copy
import hashlib
import json
from pathlib import Path
import subprocess

EXE_SUFFIX = ".exe" if __import__("os").name == "nt" else ""
ROOT=Path(__file__).resolve().parents[1]
EXE=ROOT/("phase2/lean/.lake/build/bin/gp_lifecycle_runner" + EXE_SUFFIX)
SCRATCH=ROOT/"tmp/phase2-residual-successors"
PIN="ac4155787207e2847d248cffed7be871d5dcd577"
ORACLE_COMMITS = {PIN, __import__("json").loads((ROOT / "oracle/PIN.json").read_text(encoding="utf-8-sig")).get("public_commit", PIN)}
CASES=("GP-X159","GP-X161")
IDS={"IV":1,"PD":2,"E-IV-PD":3,"E-IV-PD-RESTRICT":4,"EXTRA":5,"M":6,"N":7,"C":8,"C2":9,"C3":10}
HASHES={"GP-X159":"ecba1f4a9332c27c6316a86de7fdd91aad5bf6fe98bcc05486ff0da6686f4302",
        "GP-X161":"c7da5736c1c06a4681eb2ec8631807726fb7f0ca596b688b0a0fbbaa0d65641e"}
ANCHORS={"GP-X159":("tests/test_supersession_noise.py",447,"test_a_replacement_parallel_to_a_live_edge_is_still_reported"),
         "GP-X161":("tests/test_adversarial.py",2345,"test_a_claim_can_be_split_and_the_split_is_not_lost")}
LIMITATION="Frozen v0.37 lifecycle/binding contract, not a GP 0.50 held claim. No external backend. Receipt routes explicitly use fabricated historical backend descriptors; section arithmetic is replayed separately by the fold."

def require(ok,message):
    if not ok:
        raise ValueError(message)

def encoded(value):
    return json.dumps(value,sort_keys=True,separators=(",",":"),ensure_ascii=True)

def sha(raw):
    return hashlib.sha256(raw).hexdigest()

def digest(value):
    return sha(encoded(value).encode("utf-8"))

def fields(value,keys,message):
    require(isinstance(value,dict) and set(value)==set(keys),message)

def source_contract():
    checkout=ROOT/"oracle/checkout"
    git=["git","-c","safe.directory="+str(checkout),"-C",str(checkout)]
    pin_raw=(ROOT/"oracle/PIN.json").read_bytes()
    require(json.loads(pin_raw)["commit"]==PIN,"pin changed")
    require(subprocess.check_output(git+["rev-parse","HEAD"],text=True).strip() in ORACLE_COMMITS,"checkout changed")
    result={}
    for case_id,(path,line,name) in ANCHORS.items():
        raw=subprocess.check_output(git+["show","HEAD:" +path])
        require((checkout/path).read_bytes()==raw,"pinned source changed")
        text=raw.decode("utf-8")
        node=next(n for n in ast.parse(text).body if isinstance(n,ast.FunctionDef) and n.name==name)
        require(node.lineno==line,"source anchor moved")
        segment="\n".join(text.splitlines()[node.lineno-1:node.end_lineno])
        needles=('2 edges join','"E-IV-PD-RESTRICT" in par.detail','"E-IV-PD-EQ" in par.detail','"E-IV-PD [" not in par.detail') if case_id=="GP-X159" else (
            '["superseded_by"] == ["C1", "C2"]','S.successors(g.claims["C"]) == "C1 and C2"')
        require(all(s in segment for s in needles),"named source contract changed")
        result[case_id]={"path":path,"line":line,"anchor":"def "+name+"(",
                        "file_sha256":sha(raw),"function_sha256":sha(segment.encode("utf-8"))}
    return {"commit":PIN,"pin_file_sha256":sha(pin_raw),"functions":result,
            "boundary":"Named predecessor contracts only. Replay literal fixture abstractions, not predecessor object classes or message rendering."}

def checked_case(case_id,tags,routes):
    require(case_id in CASES,"uncommissioned fixture")
    raw=(ROOT/"corpus/must"/(case_id+".json")).read_bytes()
    case=json.loads(raw)
    row=next(r for r in tags["cases"] if r["id"]==case_id)
    require(sha(raw)==HASHES[case_id]==row["sha256"],"fixture bytes changed")
    require(row["primary_layer"]=="kernel" and row["g2_kernel_eligible"] is True
            and row["full_contract_required"] is True,"layer contract changed")
    path,line,name=ANCHORS[case_id]
    require(case["sources"]==[{"repository":"gp-v037","commit":PIN,"path":path,"line":line,
                             "anchor":"def "+name+"("}],"source pointer changed")
    require(case["id"]==case_id and case["expected"]["verdict"]==("REFUSE" if case_id=="GP-X159" else "ACCEPT"),
            "fixture expectation changed")
    require(routes["commit"]==PIN and routes["routes"][case_id]=={
        "kind":"lifecycle","action":"no_rule" if case_id=="GP-X159" else "successors",
        "layer":"lifecycle_contract","limitation":LIMITATION},"route changed")
    return case,raw,row

def translate(case,raw_hash):
    fields(case,("schema_version","id","seed","title","situation","inputs","attempted_conclusion",
                 "expected","scope_or_region","sources"),"unknown fixture fields")
    require(case["id"] in CASES and type(case["schema_version"]) is int and case["schema_version"]==1,
            "unsupported fixture")
    inputs=case["inputs"]
    fields(inputs,("vocabulary","objects","history","question"),"unknown input fields")
    require(inputs["vocabulary"]=="lifecycle-scenario/v1","unsupported vocabulary")
    question=inputs["question"]
    require(question==({"concerns":["competing_relations"]} if case["id"]=="GP-X159" else
                       {"object":"C","successors":["C2","C3"]}),"unsupported literal query")
    objects,history=inputs["objects"],inputs["history"]
    require(isinstance(objects,dict) and objects and isinstance(history,list) and history,"invalid objects/history")
    names={}
    for key,obj in objects.items():
        require(isinstance(key,str) and key,"invalid source key")
        fields(obj,("category","name","properties"),"unknown object fields")
        require(isinstance(obj["name"],str) and obj["name"] in IDS and obj["name"] not in names,
                "uncommissioned/ambiguous identifier")
        names[obj["name"]]=key
        p=obj["properties"]
        if obj["category"]=="context":
            fields(p,("description",),"unknown context properties")
        elif obj["category"]=="relation":
            require(isinstance(p,dict) and p.get("relation_class") in ("unspecified","subset_restriction"),
                    "unsupported relation class")
            keys=("source_context","target_context","relation_class","justification","coordinate_action")
            fields(p,keys+(("unresolved_reason",) if p["relation_class"]=="unspecified" else ()),
                   "unknown relation properties")
            require(p["coordinate_action"]=="unchanged","unsupported coordinate action")
        elif obj["category"]=="assertion":
            fields(p,("context","statement_class","statement"),"unknown assertion properties")
            require(p["statement_class"]=="universal_property","unsupported statement class")
        else:
            raise ValueError("unsupported category")
        require(all(isinstance(v,str) and v for v in p.values()),"nonliteral source properties")
    for obj in objects.values():
        p=obj["properties"]
        refs=("source_context","target_context") if obj["category"]=="relation" else (
            ("context",) if obj["category"]=="assertion" else ())
        require(all(p[k] in names and objects[names[p[k]]]["category"]=="context" for k in refs),
                "unresolved source context")
    steps={}
    for step in history:
        require(isinstance(step,dict) and set(step) in ({"object"},{"object","replacement"}),"unknown history fields")
        key=step["object"]
        require(isinstance(key,str) and key in objects and (key not in steps or steps[key]==step),"inconsistent history")
        steps[key]=step
        if "replacement" in step:
            r=step["replacement"]
            fields(r,("prior","change"),"unknown replacement fields")
            require(r["prior"] is None or (isinstance(r["prior"],str) and r["prior"] in IDS),"unsupported prior")
            change={"relation":"relation_reclassification","assertion":"restatement"}.get(objects[key]["category"])
            require(change is not None and r["change"]==change,"unsupported replacement change")
    require(set(steps)==set(objects),"history record loss")
    records,currents,identities,by_key=[],[],[],{}
    for key in sorted(objects,key=lambda k:IDS[objects[k]["name"]]):
        obj,step=objects[key],steps[key]
        identity={"fixture":case["id"],"source_key":key,"object":copy.deepcopy(obj),"history_step":copy.deepcopy(step)}
        b={"statementHash":digest(identity),"scopeHash":digest({"mode":"inert-residual-successor-custody"}),
           "modelHash":digest({"vocabulary":inputs["vocabulary"],"identifier":obj["name"]}),
           "inputHashes":[raw_hash,digest(obj),digest(step)],"authority":"gp50-inert-residual-successor-custody",
           "authorityVersion":1,"kernelVersion":1}
        current={"claim":IDS[obj["name"]],"version":1,"binding":b}
        record=dict(current,id=IDS[obj["name"]],evidence={"kind":"citation","text":encoded(identity)})
        records.append(record);currents.append(current);identities.append(identity);by_key[key]=record
    def events(order):
        result=[]
        for step in order:
            record=by_key[step["object"]]
            result.extend([{"kind":"declare_claim","claim":record["claim"]},
                {"kind":"current","value":{k:record[k] for k in ("claim","version","binding")}},
                {"kind":"warrant","value":copy.deepcopy(record)}])
            replacement=step.get("replacement")
            # A literal null prior is preserved in custody, but does not name a target.
            if replacement is not None and replacement["prior"] is not None:
                result.append({"kind":"supersede","target":IDS[replacement["prior"]],"successor":record["id"]})
        return result
    forward,reverse=events(history),events(list(reversed(history)))
    links=sorted({(IDS[s["replacement"]["prior"]],IDS[objects[k]["name"]]) for k,s in steps.items()
                  if "replacement" in s and s["replacement"]["prior"] is not None})
    return {"records":records,"currents":currents,"identities":identities,"history":copy.deepcopy(history),
            "question":copy.deepcopy(question),"links":[list(e) for e in links],"retracted":[],
            "identifier_ids":{n:IDS[n] for n in names},
            "orders":{k:{"schema_version":1,"events":v} for k,v in {
                "forward":forward,"reverse":reverse,"forward_duplicates":forward+copy.deepcopy(forward),
                "reverse_duplicates":reverse+copy.deepcopy(reverse)}.items()}}

def execute(label,wire):
    SCRATCH.mkdir(parents=True,exist_ok=True)
    path=SCRATCH/(label+".events.json")
    path.write_bytes((encoded(wire)+"\n").encode("utf-8"))
    result=subprocess.run([str(EXE),str(path)],cwd=ROOT,capture_output=True,text=True,encoding="utf-8",check=True)
    return json.loads(result.stdout),sha(path.read_bytes())

def expected_ok(plan):
    domain=sorted(plan["identifier_ids"].values())
    dead={a for a,b in plan["links"]}|set(plan["retracted"])
    live=[r["id"] for r in plan["records"] if r["id"] not in dead]
    return {"status":"OK","admission":"refuseAll","resolve_fold_snapshot_equal":True,
            "snapshot":{"domain":domain,"currents":plan["currents"],"warrants":plan["records"],
                        "retracted":plan["retracted"],"successors":plan["links"]},
            "supports":[],"held":[],"held_queries":[{"claim":i,"held":False} for i in domain],
            "live_warrants":live}

def verify(observed,plan):
    require(observed==expected_ok(plan),"complete native records/bindings/liveness differ")

def project(observed,case_id):
    # Native liveness is the source of membership. Literal identity only supplies labels/endpoints.
    records={r["id"]:json.loads(r["evidence"]["text"])["object"] for r in observed["snapshot"]["warrants"]}
    live=observed["live_warrants"]
    contexts=[i for i in live if records[i]["category"]=="context"]
    if case_id=="GP-X159":
        heads=[{"id":i,"name":records[i]["name"],
                "source_context":records[i]["properties"]["source_context"],
                "target_context":records[i]["properties"]["target_context"]}
               for i in live if records[i]["category"]=="relation"
               and records[i]["properties"]["source_context"]=="IV"
               and records[i]["properties"]["target_context"]=="PD"]
        old=IDS["E-IV-PD"]
        return {"live_context_ids":contexts,"pair":["IV","PD"],"live_relation_heads":heads,
                "old_record_retained":old in records,"old_record_live":old in live,
                "literal_conclusion_verdict":"ACCEPT" if len(heads)==1 else "REFUSE"}
    old=IDS["C"]
    successors=[{"id":b,"name":records[b]["name"],"live":b in live}
                for a,b in observed["snapshot"]["successors"] if a==old]
    complete=[s["name"] for s in successors]==["C2","C3"] and all(s["live"] for s in successors)
    return {"live_context_ids":contexts,"old_record_retained":old in records,"old_record_live":old in live,
            "successor_links":[[a,b] for a,b in observed["snapshot"]["successors"] if a==old],
            "successors":successors,"literal_conclusion_verdict":"ACCEPT" if complete and old not in live and old in records else "REFUSE"}

def replay(label,plan,case_id):
    runs={}
    for order,wire in plan["orders"].items():
        observed,h=execute(label+"-"+order,wire)
        verify(observed,plan)
        runs[order]={"input_sha256":h,"native_result":observed,"native_identity_projection":project(observed,case_id)}
    require(all(r["native_result"]==runs["forward"]["native_result"] and
                r["native_identity_projection"]==runs["forward"]["native_identity_projection"] for r in runs.values()),
            "orders/duplicates differ")
    return runs

def controls(cases):
    result=[]
    changed=copy.deepcopy(cases["GP-X159"])
    changed["inputs"]["history"][4]["replacement"]["prior"]="E-IV-PD-RESTRICT"
    result.append(("extra_explicitly_replaces_head",changed,"ACCEPT",
        "Separate repair explicitly supersedes the current replacement with EXTRA, leaving one live relation at IV->PD."))
    changed=copy.deepcopy(cases["GP-X159"])
    changed["inputs"]["objects"]["object-5"]["properties"]["target_context"]="IV"
    result.append(("extra_at_different_endpoint_pair",changed,"ACCEPT",
        "Separate endpoint control moves EXTRA to IV->IV; native keeps both live but only one is at IV->PD."))
    changed=copy.deepcopy(cases["GP-X161"])
    changed["inputs"]["history"][4]["replacement"]["prior"]=None
    result.append(("second_successor_link_missing",changed,"REFUSE",
        "Separate negative control retains C3 as a live independent record, but the second successor link is absent."))
    changed=copy.deepcopy(cases["GP-X161"])
    result.append(("both_split_links_repaired",changed,"ACCEPT",
        "Positive repair restores both exact native successor links without changing successor properties."))
    return result

def run(output):
    protected=[ROOT/p for p in ("oracle/PIN.json","oracle/ROUTES.json","corpus/LAYER-TAGS.json")]
    before={str(p):p.read_bytes() for p in protected}
    source=source_contract();exe_hash=sha(EXE.read_bytes())
    tags,routes=json.loads(protected[2].read_bytes()),json.loads(protected[1].read_bytes())
    cases,results={},[]
    for case_id in CASES:
        case,raw,row=checked_case(case_id,tags,routes);cases[case_id]=case
        plan=translate(case,sha(raw));runs=replay(case_id,plan,case_id)
        verdict=runs["forward"]["native_identity_projection"]["literal_conclusion_verdict"]
        require(verdict==case["expected"]["verdict"],"literal conclusion verdict differs")
        require((ROOT/"corpus/must"/(case_id+".json")).read_bytes()==raw,"fixture changed")
        results.append({"id":case_id,"source_sha256":sha(raw),"expected":case["expected"],
                        "attempted_conclusion":case["attempted_conclusion"],"observed":verdict,
                        "literal_bound_identities":plan["identities"],"literal_history":plan["history"],
                        "question":plan["question"],"identifier_ids":plan["identifier_ids"],
                        "native_inputs":plan["orders"],"runs":runs,"layer_entry":row,
                        "full_fixture_contract_executed":True,"status":"EXECUTED","full_fixture_contract":True})
    contrasts=[]
    for label,case,verdict,purpose in controls(cases):
        control_hash=digest(case);plan=translate(case,control_hash);runs=replay(label,plan,case["id"])
        require(runs["forward"]["native_identity_projection"]["literal_conclusion_verdict"]==verdict,
                "control must distinguish the exact native live/link contract")
        contrasts.append({"label":label,"purpose":purpose,"corpus_pass":False,"control_input_sha256":control_hash,
                          "literal_bound_identities":plan["identities"],"native_inputs":plan["orders"],"runs":runs})
    require(all(p.read_bytes()==before[str(p)] for p in protected),"protected metadata changed")
    require(source_contract()==source and sha(EXE.read_bytes())==exe_hash,"source/executable changed")
    report={"schema":"gp-phase2-residual-successors/v1","case_count":2,"corpus_native_executions":8,
            "control_scenarios":4,"control_native_executions":16,"g2_pass":False,"complete_ten_case_slice":False,
            "source_contract":source,"protected_input_hashes":{k:sha(v) for k,v in before.items()},
            "runner_path":str(EXE),"runner_sha256":exe_hash,
            "native_source_sha256":{n:sha((ROOT/"phase2/lean/GP50"/n).read_bytes()) for n in ("Events.lean","LifecycleRunner.lean")},
            "adapter_sha256":sha(Path(__file__).read_bytes()),
            "tests_sha256":sha((ROOT/"tests/test_phase2_residual_successors.py").read_bytes()),
            "cases":results,"controls":contrasts,
            "authority_boundary":"Admission.refuseAll: all literal declarations are inert citations, not checked truth. Held/supports remain empty.",
            "projection_boundary":"Compare complete native snapshots first, then project native live IDs/successor links through exact immutable literal identities. X159's refusal is the literal attempted-conclusion result from two native live relation records at IV->PD, not native MALFORMED or an added debt-audit surface. No host liveness prefilter or algebraic interpretation.",
            "null_prior_boundary":"Explicit replacement.prior=null is retained and hash-bound in EXTRA's custody record and emits no supersession event; no target ID is fabricated.",
            "successor_boundary":"X161 retains both exact links C->C2 and C->C3, both successor identities/properties and inactive historical C. Generic custody does not implement predecessor prose rendering."}
    output.write_bytes((json.dumps(report,indent=2)+"\n").encode("utf-8"))
    print("Residual successors: 2 unchanged fixtures, 8 native corpus folds and 16 separate controls; held empty.")
    return report

if __name__=="__main__":
    p=argparse.ArgumentParser()
    p.add_argument("--output",type=Path,default=ROOT/"reports/PHASE-2-RESIDUAL-SUCCESSORS.json")
    a=p.parse_args();run(a.output)
