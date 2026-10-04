"""Missing-authority contracts with literal custody and separate checked replay controls."""
import argparse
import ast
import copy
import hashlib
import importlib.util
import json
from pathlib import Path
import subprocess

EXE_SUFFIX = ".exe" if __import__("os").name == "nt" else ""
ROOT=Path(__file__).resolve().parents[1]
SCRATCH=ROOT/"tmp/phase2-missing-authority"
BIN=ROOT/"phase2/lean/.lake/build/bin"
RUNNERS={"span":BIN/("gp_span_runner" + EXE_SUFFIX),"lifecycle":BIN/("gp_lifecycle_runner" + EXE_SUFFIX)}
PIN="ac4155787207e2847d248cffed7be871d5dcd577"
ORACLE_COMMITS = {PIN, __import__("json").loads((ROOT / "oracle/PIN.json").read_text(encoding="utf-8-sig")).get("public_commit", PIN)}
HISTORY_PIN="7991c9052f13e8dcaa78b5eae36f31663e080c1e"
CASES=("GP-A15","GP-A26","GP-X82")
IDS={"GP-A15":101,"GP-A26":102,"GP-X82":103}
HASHES={"GP-A15":"35279974aaa5fd8a1c1c7471bfa03b044fd50659888eda3e3ff3efc0925f5b68",
        "GP-A26":"32ee1d0bb8fa8bb6c5222312652709942a195eec905a7f5a3f8ad241311de6af",
        "GP-X82":"50e276b5b44ea4a5fcd77d37de80621c92ce5ce986feda830e35c44024e42806"}
X164_HASH="3380ad2566475144e05b162f3113e02ead4faf3ea5a92c568f9fa0b5e8a24fed"
HELPER=ROOT/"tools/run-phase2-slice.py"
spec=importlib.util.spec_from_file_location("reviewed_slice",HELPER)
helper=importlib.util.module_from_spec(spec)
spec.loader.exec_module(helper)
ROUTES={
 "GP-A15":{"kind":"join_fixture","layer":"graph_diagnostic","limitation":"Replays the pinned gamma-window historical fixture."},
 "GP-A26":{"kind":"unknown_certificate","layer":"declaration_validation"},
 "GP-X82":{"kind":"historical_review","family":"boundary","action":"promote_digest","layer":"historical_contract",
           "historical_commit":HISTORY_PIN,"limitation":"Pinned historical GP adapter on v0.37 runtime. No companion bindings or backend execution. This is a frozen scope/metadata contract, not theorem replay or new mathematical authority."}}

def require(ok,message):
    if not ok:
        raise ValueError(message)

def encoded(v):
    return json.dumps(v,sort_keys=True,separators=(",",":"),ensure_ascii=True)

def sha(raw):
    return hashlib.sha256(raw).hexdigest()

def digest(v):
    return sha(encoded(v).encode("utf-8"))

def fields(v,keys,message):
    require(isinstance(v,dict) and set(v)==set(keys),message)

def function_record(raw,name,line,needles):
    text=raw.decode("utf-8")
    node=next(n for n in ast.parse(text).body if isinstance(n,ast.FunctionDef) and n.name==name)
    require(node.lineno==line,"source anchor moved")
    segment="\n".join(text.splitlines()[node.lineno-1:node.end_lineno])
    require(all(s in segment for s in needles),"named source contract changed")
    return {"line":line,"anchor":"def "+name+"(","function_sha256":sha(segment.encode("utf-8"))}

def source_contract():
    checkout=ROOT/"oracle/checkout"
    git=["git","-c","safe.directory="+str(checkout),"-C",str(checkout)]
    require(json.loads((ROOT/"oracle/PIN.json").read_bytes())["commit"]==PIN,"pin changed")
    require(subprocess.check_output(git+["rev-parse","HEAD"],text=True).strip() in ORACLE_COMMITS,"checkout changed")
    result={}
    for path in ("SPEC.md","fixtures/gamma_window/graph.jsonl","tests/test_kernel.py","tests/test_verdict_provenance.py"):
        raw=subprocess.check_output(git+["show","HEAD:" +path])
        require((checkout/path).read_bytes()==raw,"pinned source modified")
        row={"commit":PIN,"file_sha256":sha(raw)}
        if path=="SPEC.md":
            line=raw.decode("utf-8").splitlines()[547]
            require("GI-BRIDGE" in line and "not one variable" in line and "print" in line,"GI-BRIDGE source changed")
            row.update(line=548,anchor="GI-BRIDGE",anchor_sha256=sha(line.encode("utf-8")))
        elif path.endswith(".jsonl"):
            line=raw.decode("utf-8").splitlines()[24]
            obj=json.loads(line)
            require(obj["id"]=="GI-BRIDGE" and obj["ev"]=="inference" and "print" in obj["cite"],"bridge record changed")
            row.update(line=25,anchor='"id": "GI-BRIDGE"',anchor_sha256=sha(line.encode("utf-8")),
                       literal_anchor_record=obj)
        elif path.endswith("test_kernel.py"):
            row.update(function_record(raw,"test_unknown_certificate_is_refused",211,("K.ScopeError",'"VIBES", "Q"')))
        else:
            row["functions"]=[function_record(raw,"test_fresh_epoch1_verdict_is_active",69,('["current"] is True',))]
        result[path]=row
    packet=ROOT/"docs/GP-0.50-REWORK-PACKET.md"
    packet_raw=packet.read_bytes();lines=packet_raw.decode("utf-8").splitlines()
    for line,anchor,needles in ((555,"| A15 |",("GI-BRIDGE","REFUSE: no admitted rule")),
                              (566,"| A26 |",("unknown certificate name","current receipt"))):
        require(anchor in lines[line-1] and all(s in lines[line-1] for s in needles),"packet anchor changed")
    result["packet"]={"file_sha256":sha(packet_raw),"anchors":[{"line":555,"text":lines[554]},
                                                             {"line":566,"text":lines[565]}]}
    history_raw=(ROOT/"oracle/history/PIN.json").read_bytes();history=json.loads(history_raw)
    require(history["commit"]==HISTORY_PIN and history["pinned_descendant"]==PIN,"historical pin changed")
    path="tests/test_jc_source_depth6_authority.py"
    file_row=next(r for r in history["files"] if r["path"]==path)
    raw=(ROOT/"oracle/history/checkout"/path).read_bytes()
    require(sha(raw)==file_row["sha256"]=="ceb621c769a0048828f08d38b0049394d32bf1acc886484ce82c22a6c836f655",
            "historical source bytes changed")
    require(hashlib.sha1(("blob "+str(len(raw))+"\0").encode()+raw).hexdigest()==file_row["git_blob"],
            "historical source blob binding changed")
    result[path]={"commit":HISTORY_PIN,"file_sha256":sha(raw),"git_blob":file_row["git_blob"],
                 "history_pin_sha256":sha(history_raw),**function_record(raw,
                 "test_intermediate_rung_commitment_is_not_promoted_to_polynomial_proof",73,
                 ("DIGEST_COMMITMENTS_ONLY","no replay of the 33-rung source march"))}
    return result

def checked_case(case_id,tags,routes):
    require(case_id in CASES,"uncommissioned fixture")
    raw=(ROOT/"corpus/must"/(case_id+".json")).read_bytes();case=json.loads(raw)
    row=next(r for r in tags["cases"] if r["id"]==case_id)
    require(sha(raw)==HASHES[case_id]==row["sha256"],"fixture bytes changed")
    require(case["id"]==case_id and case["expected"]["verdict"]=="REFUSE","fixture expectation changed")
    require(row["primary_layer"]=="kernel" and row["full_contract_required"] is True
            and row["g2_kernel_eligible"] is True,"layer contract changed")
    require(routes["commit"]==PIN and routes["routes"][case_id]==ROUTES[case_id],"route changed")
    return case,raw,row

def translate(case,raw_hash):
    fields(case,("schema_version","id","seed","title","situation","inputs","attempted_conclusion",
                 "expected","scope_or_region","sources"),"unknown fixture fields")
    require(case["id"] in CASES and type(case["schema_version"]) is int and case["schema_version"]==1,"unsupported fixture")
    p=case["inputs"]
    if case["id"]=="GP-A15":
        fields(p,("connecting_rule","shared_variables"),"unknown join inputs")
        require(p["connecting_rule"] is None and p["shared_variables"]==[],"unsupported connecting authority")
    elif case["id"]=="GP-A26":
        fields(p,("certificate_name","target_context","receipt"),"unknown certificate inputs")
        require(p["certificate_name"]=="VIBES" and p["target_context"]=="Q" and p["receipt"] is None,
                "unsupported certificate contract")
    else:
        fields(p,("equation","alpha","pin","source_binding","proposal"),"unknown digest inputs")
        require(all(isinstance(v,str) and v for v in p.values()) and p["source_binding"]=="digest commitments only"
                and p["proposal"]=="promote_digest","unsupported digest contract")
    key=IDS[case["id"]]
    identity={"role":"literal-fixture-custody","literal_fixture":copy.deepcopy(case)}
    b={"statementHash":digest({"literal_attempted_conclusion":case["attempted_conclusion"],
                              "literal_situation":case["situation"],"literal_inputs":p}),
       "scopeHash":digest({"literal_scope_or_region":case["scope_or_region"]}),
       "modelHash":digest({"literal_case_id":case["id"],"literal_objects_and_inputs":p}),
       "inputHashes":[raw_hash,digest(case),digest(p),digest({"literal_scope_or_region":case["scope_or_region"]})],
       "authority":"gp50-inert-missing-authority-custody","authorityVersion":1,"kernelVersion":1}
    current={"claim":key,"version":1,"binding":b}
    warrant=dict(current,id=key,evidence={"kind":"citation","text":encoded(identity)})
    return {"label":case["id"],"query_claim":key,"registry":{"schema_version":1,"clauses":[],"receipts":[]},
            "wire":{"schema_version":1,"events":[{"kind":"declare_claim","claim":key},
                 {"kind":"current","value":current},{"kind":"warrant","value":warrant}]},
            "held":[],"supports":[],"literal_identity":identity,"corpus_pass":True}

def positive():
    raw=(ROOT/"corpus/must/GP-X164.json").read_bytes()
    require(sha(raw)==X164_HASH,"X164 contrast fixture changed")
    registry,events,baseline,fidelity,query=helper.translate(json.loads(raw))
    require(baseline is None and query==1 and registry["clauses"][0]["generators"]==[helper.POLYNOMIALS["x"]]
            and registry["clauses"][0]["target"]==helper.POLYNOMIALS["x"]
            and registry["receipts"][0]["cofactors"]==[helper.ONE],"reviewed accepting contrast changed")
    return {"label":"separate_X164_checked_replay","query_claim":1,"registry":registry,"wire":events,
            "held":[1],"supports":[10],"corpus_pass":False,"source_sha256":sha(raw),"fidelity":fidelity}

def controls(row,checked):
    result=[]
    borrowed=copy.deepcopy(row);borrowed["registry"]=copy.deepcopy(checked["registry"])
    borrowed["wire"]["events"][-1]["value"]["evidence"]={"kind":"receipt","data":"receipt-1"}
    result.append(("borrowed_receipt_name",borrowed))
    key_only=copy.deepcopy(borrowed)
    key_only["wire"]["events"][0]["claim"]=1
    for event in key_only["wire"]["events"][1:]:
        event["value"]["claim"]=1
    key_only["query_claim"]=1
    result.append(("key_only_rebound",key_only))
    binding_only=copy.deepcopy(key_only)
    binding_only["wire"]["events"][-1]["value"]["binding"]=copy.deepcopy(checked["registry"]["clauses"][0]["binding"])
    result.append(("warrant_binding_only_rebound",binding_only))
    registered=copy.deepcopy(borrowed)
    receipt=copy.deepcopy(checked["registry"]["receipts"][0])
    warrant=registered["wire"]["events"][-1]["value"]
    receipt.update(name="registered-without-source-clause",claim=warrant["claim"],binding=copy.deepcopy(warrant["binding"]))
    registered["registry"]["receipts"].append(receipt)
    warrant["evidence"]["data"]=receipt["name"]
    result.append(("registered_receipt_without_clause",registered))
    for suffix,item in result:
        item.update(label=row["label"]+"-"+suffix,corpus_pass=False,
                    purpose="Separate adversarial reproduction control; never a mathematical encoding of the literal source claim.")
    return [v for _,v in result]

def write_input(label,suffix,value):
    SCRATCH.mkdir(parents=True,exist_ok=True)
    path=SCRATCH/(label+"."+suffix+".json")
    path.write_bytes((encoded(value)+"\n").encode("utf-8"))
    return path

def native(runner,paths):
    p=subprocess.run([str(runner),*map(str,paths)],cwd=ROOT,capture_output=True,text=True,encoding="utf-8",check=True)
    return json.loads(p.stdout)

def custody_expected(wire):
    events=wire["events"]
    currents=sorted({encoded(e["value"]):e["value"] for e in events if e["kind"]=="current"}.values(),key=lambda c:c["claim"])
    warrants=sorted({encoded(e["value"]):e["value"] for e in events if e["kind"]=="warrant"}.values(),key=lambda w:w["id"])
    domain=sorted({e["claim"] for e in events if e["kind"]=="declare_claim"}|{c["claim"] for c in currents})
    live=[w["id"] for w in warrants if any(all(w[k]==c[k] for k in ("claim","version","binding")) for c in currents)]
    return {"status":"OK","admission":"refuseAll","resolve_fold_snapshot_equal":True,
            "snapshot":{"domain":domain,"currents":currents,"warrants":warrants,"retracted":[],"successors":[]},
            "supports":[],"held":[],"live_warrants":live,"held_queries":[{"claim":k,"held":False} for k in domain]}

def verify(row,wire,observed,custody):
    require(custody==custody_expected(wire),"complete native custody/bindings/liveness differ")
    s=custody["snapshot"]
    expected={"status":"OK","held":row["held"],"supports":row["supports"],"domain":s["domain"],
              "live_warrants":custody["live_warrants"],"warrant_count":len(s["warrants"]),
              "current_count":len(s["currents"]),"retracted":[],"successors":[]}
    require(observed==expected,"native checked authority state differs")

def execute(row,label,wire):
    rp=write_input(label,"registry",row["registry"]);ep=write_input(label,"events",wire)
    observed=native(RUNNERS["span"],[rp,ep]);custody=native(RUNNERS["lifecycle"],[ep])
    verify(row,wire,observed,custody)
    return {"native_result":observed,"native_custody_result":custody,
            "query_claim":row["query_claim"],"query_held":row["query_claim"] in observed["held"],
            "inputs":{"registry_sha256":sha(rp.read_bytes()),"events_sha256":sha(ep.read_bytes())}}

def replay(row):
    forward=row["wire"]["events"];reverse=list(reversed(forward));runs={}
    for order,events in {"forward":forward,"reverse":reverse,"forward_duplicates":forward+copy.deepcopy(forward),
                         "reverse_duplicates":reverse+copy.deepcopy(reverse)}.items():
        runs[order]=execute(row,row["label"]+"-"+order,{"schema_version":1,"events":events})
    require(all(r["native_result"]==runs["forward"]["native_result"] and
                r["native_custody_result"]==runs["forward"]["native_custody_result"] for r in runs.values()),
            "orders/duplicates differ")
    return {"label":row["label"],"corpus_pass":row["corpus_pass"],"registry":row["registry"],
            "native_inputs":row["wire"],"literal_identity":row.get("literal_identity"),"runs":runs}

def run(output):
    protected=[ROOT/p for p in ("oracle/PIN.json","oracle/history/PIN.json","oracle/ROUTES.json","corpus/LAYER-TAGS.json",
                               "docs/GP-0.50-REWORK-PACKET.md")]
    before={str(p):p.read_bytes() for p in protected}
    source=source_contract();exe_hashes={k:sha(p.read_bytes()) for k,p in RUNNERS.items()}
    helper_hash=sha(HELPER.read_bytes());checked=positive()
    tags,routes=json.loads(protected[3].read_bytes()),json.loads(protected[2].read_bytes())
    cases,contrasts=[],[replay(checked)]
    for case_id in CASES:
        case,raw,layer=checked_case(case_id,tags,routes)
        row=translate(case,sha(raw));result=replay(row)
        verdict="ACCEPT" if result["runs"]["forward"]["query_held"] else "REFUSE"
        require(verdict==case["expected"]["verdict"],"native missing-authority verdict differs")
        result.update(id=case_id,source_sha256=sha(raw),expected=case["expected"],observed=verdict,layer_entry=layer,
                      full_fixture_contract_executed=True, full_fixture_contract=True, status="EXECUTED")
        cases.append(result)
        contrasts.extend(replay(c) for c in controls(row,checked))
        require((ROOT/"corpus/must"/(case_id+".json")).read_bytes()==raw,"fixture changed")
    require(all(p.read_bytes()==before[str(p)] for p in protected),"protected source/metadata changed")
    require(source_contract()==source and sha(HELPER.read_bytes())==helper_hash
            and all(sha(p.read_bytes())==exe_hashes[k] for k,p in RUNNERS.items()),"source/executable/helper changed")
    require(sha((ROOT/"corpus/must/GP-X164.json").read_bytes())==X164_HASH,"accepting contrast fixture changed")
    report={"schema":"gp-phase2-missing-authority/v1","case_count":3,"corpus_native_checked_folds":12,
            "corpus_native_custody_folds":12,"separate_contrast_scenarios":13,
            "contrast_native_checked_folds":52,"contrast_native_custody_folds":52,
            "g2_pass":False,"complete_ten_case_slice":False,"source_contract":source,
            "protected_input_hashes":{k:sha(v) for k,v in before.items()},
            "executables":{k:{"path":str(p),"sha256":exe_hashes[k]} for k,p in RUNNERS.items()},
            "native_source_sha256":{n:sha((ROOT/"phase2/lean/GP50"/n).read_bytes())
                                   for n in ("Runner.lean","LifecycleRunner.lean","BoundReplay.lean","PolyStub.lean")},
            "reviewed_adapter_sha256":helper_hash,"X164_contrast_source_sha256":checked["source_sha256"],
            "adapter_sha256":sha(Path(__file__).read_bytes()),
            "tests_sha256":sha((ROOT/"tests/test_phase2_missing_authority.py").read_bytes()),
            "cases":cases,"contrasts":contrasts,
            "authority_boundary":"Original fixtures are complete literal citation custody under an empty registered span authority. Native fold excludes citation evidence from held/supports; no fake algebraic statement, mathematical parser, connecting rule, certificate scope or source derivation is invented.",
            "snapshot_boundary":"Checked runner state summaries are paired with complete lifecycle snapshots from identical event-file bytes under refuseAll. Custody introspection does not supply authority.",
            "scope_boundary":"Literal BOTH/SCOPE, Q, VIBES and every equation/alpha/pin/source-binding string are preserved as opaque data and exact identity hashes, not interpreted geometry or polynomial truth.",
            "control_boundary":"Unchanged X164 x=1*x exact Rat replay is a separate accepting reproduction control, never an added corpus pass. Borrowed receipt names, key-only or warrant-only rebinding, and a receipt registered without a source clause cannot launder the original literal statements.",
            "historical_boundary":"X82 named test is verified against the historical PIN manifest SHA-256 and Git blob identity at its distinct pinned commit; no source march or intermediate polynomial replay is claimed."}
    output.write_bytes((json.dumps(report,indent=2)+"\n").encode("utf-8"))
    print("Missing authority: 3 unchanged fixtures, 12 checked+12 custody folds; 13 separate contrasts, 52+52 folds.")
    return report

if __name__=="__main__":
    p=argparse.ArgumentParser()
    p.add_argument("--output",type=Path,default=ROOT/"reports/PHASE-2-MISSING-AUTHORITY.json")
    a=p.parse_args();run(a.output)
