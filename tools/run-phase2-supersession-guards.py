"""Finite native supersession guards over five unchanged lifecycle fixtures."""
import argparse
import ast
import copy
import hashlib
import json
from pathlib import Path
import subprocess

EXE_SUFFIX = ".exe" if __import__("os").name == "nt" else ""
ROOT = Path(__file__).resolve().parents[1]
EXE = ROOT / ("phase2/lean/.lake/build/bin/gp_lifecycle_runner" + EXE_SUFFIX)
SCRATCH = ROOT / "tmp/phase2-supersession-guards"
PIN = "ac4155787207e2847d248cffed7be871d5dcd577"
ORACLE_COMMITS = {PIN, __import__("json").loads((ROOT / "oracle/PIN.json").read_text(encoding="utf-8-sig")).get("public_commit", PIN)}
CASES = ("GP-X152","GP-X153","GP-X154","GP-X155","GP-X158")
IDS = {"IV":1,"PD":2,"E-IV-PD":3,"E-IV-PD-RESTRICT":4,"W-E":5,"EA":6,"EB":7,"E3":8,"GHOST":9}
HASHES = {
 "GP-X152":"8008dcad9acf0f48730013275929e411fdf4c2963f0f6ed7f7a52f1aed7f0e4b",
 "GP-X153":"c965316d66c25fdc2b62d80759ac2d8bf8c087203b803fb98a48e58ebe2c1653",
 "GP-X154":"384bafb0a8c7855319a3c99904f8aa4ec74e43e42cbb154ec6afc37e52c467fb",
 "GP-X155":"0c35824900da59cfbf879236b4b71b9c0863b49604b11e98249e223aa60c0c9c",
 "GP-X158":"4a32d4f96ac1b7c659cdd26508b96eb8b83cd9aa094e77289ec852d4feacc177"}
ANCHORS = {
 "GP-X152":("tests/test_supersession_noise.py",167,"test_tombstone_and_live_successor_are_mutually_exclusive"),
 "GP-X153":("tests/test_adversarial.py",3363,"test_an_edge_cannot_supersede_itself_or_a_record_that_is_not_there"),
 "GP-X154":("tests/test_supersession_noise.py",393,"test_a_dangling_supersession_is_refused_by_the_FOLD"),
 "GP-X155":("tests/test_supersession_noise.py",370,"test_two_edges_superseding_each_other_withdraw_nothing"),
 "GP-X158":("tests/test_supersession_noise.py",423,"test_a_declared_chain_of_three_edges_is_one_edge")}
ERRORS = {"GP-X152":"withdrawal and replacement: 3","GP-X153":"self supersession: 4",
          "GP-X154":"missing supersession endpoint: 9->4","GP-X155":"supersession cycle: 6"}
LIMITATION = "Frozen v0.37 lifecycle/binding contract, not a GP 0.50 held claim. No external backend. Receipt routes explicitly use fabricated historical backend descriptors; section arithmetic is replayed separately by the fold."

def require(ok, message):
    if not ok:
        raise ValueError(message)

def encoded(value):
    return json.dumps(value,sort_keys=True,separators=(",",":"),ensure_ascii=True)

def sha(raw):
    return hashlib.sha256(raw).hexdigest()

def digest(value):
    return sha(encoded(value).encode("utf-8"))

def fields(value, keys, message):
    require(isinstance(value,dict) and set(value)==set(keys),message)

def source_contract():
    checkout = ROOT / "oracle/checkout"
    git = ["git","-c","safe.directory="+str(checkout),"-C",str(checkout)]
    pin_raw = (ROOT / "oracle/PIN.json").read_bytes()
    require(json.loads(pin_raw)["commit"]==PIN,"pin changed")
    require(subprocess.check_output(git+["rev-parse","HEAD"],text=True).strip() in ORACLE_COMMITS,"checkout changed")
    result = {}
    for path in sorted({a[0] for a in ANCHORS.values()}):
        raw = subprocess.check_output(git+["show","HEAD:" +path])
        require((checkout/path).read_bytes()==raw,"pinned source changed")
        text = raw.decode("utf-8")
        functions = {n.name:n for n in ast.parse(text).body if isinstance(n,ast.FunctionDef)}
        for case_id,(p,line,name) in ANCHORS.items():
            if p!=path:
                continue
            node = functions[name]
            require(node.lineno==line,"source anchor moved")
            segment = "\n".join(text.splitlines()[node.lineno-1:node.end_lineno])
            needles = {
                "GP-X152":('pytest.raises(S.GraphError)','Nothing-replaces-it'),
                "GP-X153":('supersedes itself','not a edge in this graph','pytest.raises(S.GraphError)'),
                "GP-X154":('pytest.raises(S.GraphError)','not a edge in this graph','fold it too'),
                "GP-X155":('UNTYPED-EDGE:E-A','UNTYPED-EDGE:E-B','PARALLEL-EDGE:IV->PD'),
                "GP-X158":('assert not _rules(chain, C.R_PARALLEL)','assert _rules(undeclared, C.R_PARALLEL)')}[case_id]
            require(all(s in segment for s in needles),"named source contract changed")
            result[case_id]={"path":path,"line":line,"anchor":"def "+name+"(",
                            "file_sha256":sha(raw),"function_sha256":sha(segment.encode("utf-8"))}
    return {"commit":PIN,"pin_file_sha256":sha(pin_raw),"functions":result}

def checked_case(case_id,tags,routes):
    require(case_id in CASES,"uncommissioned fixture")
    raw = (ROOT/"corpus/must"/(case_id+".json")).read_bytes()
    case = json.loads(raw)
    row = next(r for r in tags["cases"] if r["id"]==case_id)
    require(sha(raw)==HASHES[case_id]==row["sha256"],"fixture bytes changed")
    require(row["primary_layer"]=="kernel" and row["g2_kernel_eligible"] is True
            and row["full_contract_required"] is True,"layer contract changed")
    path,line,name = ANCHORS[case_id]
    require(case["sources"]==[{"repository":"gp-v037","commit":PIN,"path":path,"line":line,
                              "anchor":"def "+name+"("}],"source pointers changed")
    require(case["id"]==case_id and case["expected"]["verdict"]==("ACCEPT" if case_id=="GP-X158" else "REFUSE"),
            "fixture expectation changed")
    require(routes["commit"]==PIN and routes["routes"][case_id]=={
        "kind":"lifecycle","action":"no_rule" if case_id in ("GP-X155","GP-X158") else "fold",
        "layer":"lifecycle_contract","limitation":LIMITATION},"route changed")
    return case,raw,row

def translate(case,raw_hash):
    fields(case,("schema_version","id","seed","title","situation","inputs","attempted_conclusion",
                 "expected","scope_or_region","sources"),"unknown fixture fields")
    require(case["id"] in CASES and type(case["schema_version"]) is int and case["schema_version"]==1,
            "unsupported fixture")
    inputs = case["inputs"]
    fields(inputs,("vocabulary","objects","history","question"),"unknown input fields")
    require(inputs["vocabulary"]=="lifecycle-scenario/v1","unsupported vocabulary")
    question = inputs["question"]
    expected_question = {"concerns":["unresolved_relation"]} if case["id"]=="GP-X155" else (
        {"concerns":["competing_relations"]} if case["id"]=="GP-X158" else {})
    require(question==expected_question,"unsupported literal concern query")
    objects,history = inputs["objects"],inputs["history"]
    require(isinstance(objects,dict) and objects and isinstance(history,list) and history,"invalid objects/history")
    names,withdrawals = {},set()
    for key,obj in objects.items():
        require(isinstance(key,str) and key,"invalid source key")
        fields(obj,("category","name","properties"),"unknown object fields")
        require(obj["name"] in IDS and obj["name"] not in names,"uncommissioned/ambiguous identifier")
        names[obj["name"]] = key
        p = obj["properties"]
        if obj["category"]=="context":
            fields(p,("description",),"unknown context properties")
        elif obj["category"]=="relation":
            if isinstance(p,dict) and set(p)=={"justification"}:
                withdrawals.add(key)
            else:
                require(isinstance(p,dict) and p.get("relation_class") in ("unspecified","subset_restriction"),
                        "unsupported relation class")
                keys = ("source_context","target_context","relation_class","justification","coordinate_action")
                fields(p,keys+(("unresolved_reason",) if p["relation_class"]=="unspecified" else ()),
                       "unknown relation properties")
                require(p["coordinate_action"]=="unchanged","unsupported coordinate action")
        else:
            raise ValueError("unsupported category")
        require(all(isinstance(v,str) and v for v in p.values()),"properties must retain literal strings")
    for key,obj in objects.items():
        if obj["category"]=="relation" and key not in withdrawals:
            for prop in ("source_context","target_context"):
                require(obj["properties"][prop] in names and
                        objects[names[obj["properties"][prop]]]["category"]=="context","unresolved relation context")
    steps = {}
    for step in history:
        require(isinstance(step,dict) and set(step) in ({"object"},{"object","replacement"}),"unknown history fields")
        key = step["object"]
        require(key in objects and (key not in steps or steps[key]==step),"inconsistent history object")
        steps[key] = step
        if "replacement" in step:
            r = step["replacement"]
            fields(r,("prior","change"),"unknown replacement fields")
            require(isinstance(r["prior"],str) and r["prior"] in IDS,"uncommissioned target identifier")
            require(objects[key]["category"]=="relation" and
                    r["change"]==("relation_withdrawal" if key in withdrawals else "relation_reclassification"),
                    "unsupported replacement annotation")
    require(set(steps)==set(objects),"history record loss")
    require(all("replacement" in steps[k] for k in withdrawals),"withdrawal annotation absent")
    # Self references, absent endpoints, conflicting withdrawal and cycles are sent to Lean intact.
    records,currents,identities,by_key = [],[],[],{}
    for key in sorted(objects,key=lambda k:IDS[objects[k]["name"]]):
        obj,step = objects[key],steps[key]
        identity = {"fixture":case["id"],"source_key":key,"object":copy.deepcopy(obj),
                    "history_step":copy.deepcopy(step),
                    "role":"withdrawal-custody" if key in withdrawals else "declaration-custody"}
        b = {"statementHash":digest(identity),"scopeHash":digest({"mode":"inert-supersession-custody"}),
             "modelHash":digest({"vocabulary":inputs["vocabulary"],"identifier":obj["name"]}),
             "inputHashes":[raw_hash,digest(obj),digest(step)],"authority":"gp50-inert-supersession-custody",
             "authorityVersion":1,"kernelVersion":1}
        current = {"claim":IDS[obj["name"]],"version":1,"binding":b}
        record = dict(current,id=IDS[obj["name"]],evidence={"kind":"citation","text":encoded(identity)})
        records.append(record);identities.append(identity);by_key[key]=record
        if key not in withdrawals:
            currents.append(current)
    def events(order):
        wire = []
        for step in order:
            key = step["object"]; record = by_key[key]
            wire.append({"kind":"declare_claim","claim":record["claim"]})
            if key not in withdrawals:
                wire.append({"kind":"current","value":{k:record[k] for k in ("claim","version","binding")}})
            wire.append({"kind":"warrant","value":copy.deepcopy(record)})
            if "replacement" in step:
                r = step["replacement"]
                wire.append({"kind":"retract","target":IDS[r["prior"]]} if key in withdrawals else
                            {"kind":"supersede","target":IDS[r["prior"]],"successor":record["id"]})
        return wire
    forward,reverse = events(history),events(list(reversed(history)))
    links = sorted({(IDS[s["replacement"]["prior"]],IDS[objects[k]["name"]]) for k,s in steps.items()
                    if "replacement" in s and k not in withdrawals})
    retracted = sorted({IDS[steps[k]["replacement"]["prior"]] for k in withdrawals})
    return {"records":records,"currents":currents,"identities":identities,"history":copy.deepcopy(history),
            "question":copy.deepcopy(question),"links":[list(e) for e in links],"retracted":retracted,
            "identifier_ids":{n:IDS[n] for n in names},
            "context_ids":sorted(IDS[n] for n,k in names.items() if objects[k]["category"]=="context"),
            "relation_ids":sorted(IDS[n] for n,k in names.items() if objects[k]["category"]=="relation" and k not in withdrawals),
            "orders":{label:{"schema_version":1,"events":wire} for label,wire in {
                "forward":forward,"reverse":reverse,"forward_duplicates":forward+copy.deepcopy(forward),
                "reverse_duplicates":reverse+copy.deepcopy(reverse)}.items()}}

def execute(label,wire):
    SCRATCH.mkdir(parents=True,exist_ok=True)
    path = SCRATCH/(label+".events.json")
    path.write_bytes((encoded(wire)+"\n").encode("utf-8"))
    result = subprocess.run([str(EXE),str(path)],cwd=ROOT,capture_output=True,text=True,encoding="utf-8",check=True)
    return json.loads(result.stdout),sha(path.read_bytes())

def expected_ok(plan):
    domain = sorted(plan["identifier_ids"].values())
    current_ids = {c["claim"] for c in plan["currents"]}
    dead = set(plan["retracted"])|{a for a,b in plan["links"]}
    live = [r["id"] for r in plan["records"] if r["id"] in current_ids and r["id"] not in dead]
    return {"status":"OK","admission":"refuseAll","resolve_fold_snapshot_equal":True,
            "snapshot":{"domain":domain,"currents":plan["currents"],"warrants":plan["records"],
                        "retracted":plan["retracted"],"successors":plan["links"]},
            "supports":[],"held":[],"held_queries":[{"claim":i,"held":False} for i in domain],
            "live_warrants":live}

def verify(observed,plan,error=None):
    if error is not None:
        require(observed=={"status":"MALFORMED","error":error},"native guard diagnostic differs")
        return None
    require(observed==expected_ok(plan),"complete native retained records/bindings/query differ")
    return {"live_context_ids":[i for i in observed["live_warrants"] if i in plan["context_ids"]],
            "live_relation_ids":[i for i in observed["live_warrants"] if i in plan["relation_ids"]]}

def repaired_controls(cases):
    result = []
    def add(label,case,description):
        result.append((label,case,description))
    a = copy.deepcopy(cases["GP-X152"])
    del a["inputs"]["objects"]["object-5"];a["inputs"]["history"].pop()
    add("replacement_without_withdrawal",a,"Remove withdrawal in separate control; retain reclassification.")
    a = copy.deepcopy(cases["GP-X152"])
    del a["inputs"]["objects"]["object-4"];a["inputs"]["history"].pop(3)
    add("withdrawal_without_replacement",a,"Remove reclassification in separate control; withdrawal stays inert.")
    a = copy.deepcopy(cases["GP-X153"]);del a["inputs"]["history"][2]["replacement"]
    add("self_link_removed",a,"Remove only the self supersession annotation in a separate control.")
    a = copy.deepcopy(cases["GP-X154"])
    a["inputs"]["objects"]["object-4"]=copy.deepcopy(a["inputs"]["objects"]["object-3"])
    a["inputs"]["objects"]["object-4"]["name"]="GHOST"
    a["inputs"]["history"].append({"object":"object-4"})
    add("missing_relation_declared",a,"Declare a complete same-category GHOST relation in a separate control.")
    a = copy.deepcopy(cases["GP-X155"]);del a["inputs"]["history"][2]["replacement"]
    add("cycle_broken_debt_retained",a,"Break one cycle link; both literal unresolved_reason fields remain. Construction acceptance does not claim debt clearance.")
    a = copy.deepcopy(cases["GP-X158"]);del a["inputs"]["history"][4]["replacement"]
    add("chain_link_missing_competing_heads",a,"Omit the final supersession in separate control: native live IDs expose two competing relation heads.")
    return result

def replay(label,plan,error=None):
    runs = {}
    for order,wire in plan["orders"].items():
        observed,h = execute(label+"-"+order,wire)
        query = verify(observed,plan,error)
        runs[order] = {"input_sha256":h,"native_result":observed,"native_live_query":query}
    require(all(r["native_result"]==runs["forward"]["native_result"] for r in runs.values()),
            "event orders/duplicates differ")
    return runs

def run(output):
    protected = [ROOT/p for p in ("oracle/PIN.json","oracle/ROUTES.json","corpus/LAYER-TAGS.json")]
    before = {str(p):p.read_bytes() for p in protected}
    source = source_contract();exe_hash = sha(EXE.read_bytes())
    tags,routes = json.loads(protected[2].read_bytes()),json.loads(protected[1].read_bytes())
    results,cases = [],{}
    for case_id in CASES:
        case,raw,row = checked_case(case_id,tags,routes);cases[case_id]=case
        plan = translate(case,sha(raw));runs = replay(case_id,plan,ERRORS.get(case_id))
        observed = runs["forward"]["native_result"]
        verdict = "REFUSE" if observed["status"]=="MALFORMED" else "ACCEPT"
        require(verdict==case["expected"]["verdict"],"native verdict differs")
        if case_id=="GP-X158":
            require(runs["forward"]["native_live_query"]=={"live_context_ids":[1,2],"live_relation_ids":[8]}
                    and observed["snapshot"]["successors"]==[[3,4],[4,8]],
                    "complete chain must have exactly one live relation head")
        require((ROOT/"corpus/must"/(case_id+".json")).read_bytes()==raw,"fixture modified")
        results.append({"id":case_id,"source_sha256":sha(raw),"expected":case["expected"],
                        "attempted_conclusion":case["attempted_conclusion"],"observed":verdict,
                        "literal_bound_identities":plan["identities"],"literal_history":plan["history"],
                        "question":plan["question"],"identifier_ids":plan["identifier_ids"],
                        "native_inputs":plan["orders"],"runs":runs,"layer_entry":row,
                        "full_attempted_conclusion_contract_executed":True,
                        "status":"EXECUTED","full_fixture_contract":True,
                        "native_snapshot_available":observed["status"]=="OK",
                        "construction_refusal":observed["status"]=="MALFORMED"})
    controls = []
    for label,case,purpose in repaired_controls(cases):
        control_hash = digest(case)
        plan = translate(case,control_hash);runs = replay(label,plan)
        controls.append({"label":label,"purpose":purpose,"corpus_pass":False,
                         "control_input_sha256":control_hash,"literal_bound_identities":plan["identities"],
                         "native_inputs":plan["orders"],"runs":runs})
    require(controls[-1]["runs"]["forward"]["native_live_query"]["live_relation_ids"]==[4,8],
            "omitted chain link must expose competing relation heads")
    require(all(p.read_bytes()==before[str(p)] for p in protected),"protected metadata changed")
    require(source_contract()==source and sha(EXE.read_bytes())==exe_hash,"source/executable changed")
    report = {"schema":"gp-phase2-supersession-guards/v1","case_count":5,"corpus_native_executions":20,
              "positive_and_contrast_controls":6,"control_native_executions":24,"g2_pass":False,
              "complete_ten_case_slice":False,"source_contract":source,
              "protected_input_hashes":{k:sha(v) for k,v in before.items()},
              "runner_path":str(EXE),"runner_sha256":exe_hash,
              "native_source_sha256":{name:sha((ROOT/"phase2/lean/GP50"/name).read_bytes())
                                     for name in ("Events.lean","LifecycleRunner.lean")},
              "adapter_sha256":sha(Path(__file__).read_bytes()),
              "tests_sha256":sha((ROOT/"tests/test_phase2_supersession_guards.py").read_bytes()),
              "cases":results,"controls":controls,
              "authority_boundary":"Admission.refuseAll. Complete source records are inert citations; held and supports stay empty in every accepted native state. Malformed states expose an error, not a invented partial snapshot.",
              "X155_diagnostic_boundary":"The predecessor accepts the cycle and retains both untyped findings plus a parallel-edge finding. Native resolve refuses construction before any snapshot or clearing can be produced. This earlier guard refuses the complete literal attempted conclusion 'Clear untyped debt with a closed supersession cycle'; it does not implement or claim reproduction of the predecessor defect-list query. Both unresolved_reason fields and reciprocal links are bound and supplied intact.",
              "reference_boundary":"GHOST has a stable numeric reference but no fabricated original declaration. Native missing-endpoint detection decides X154. Generic native custody does not claim a general relation-kind checker.",
              "binding_boundary":"Canonical JSON/SHA-256 binds each complete literal object and history step plus the unchanged fixture hash; Lean compares opaque IDs/bindings. No host guard removes self/missing/cyclic/conflicting events."}
    output.write_bytes((json.dumps(report,indent=2)+"\n").encode("utf-8"))
    print("Supersession guards: 5 unchanged fixtures, 20 native corpus folds and 24 separate controls; held empty.")
    return report

if __name__=="__main__":
    parser=argparse.ArgumentParser()
    parser.add_argument("--output",type=Path,default=ROOT/"reports/PHASE-2-SUPERSESSION-GUARDS.json")
    args=parser.parse_args()
    run(args.output)
