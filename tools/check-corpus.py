
"""Validate neutral cases, check pinned source pointers, and record actual legacy observations."""
import argparse, hashlib, json, os, subprocess, sys, traceback
from collections import Counter
from datetime import datetime, timezone
from pathlib import Path
import jsonschema

ROOT = Path(__file__).resolve().parents[1]
ORACLE = ROOT / "oracle/checkout"
PIN = json.loads((ROOT/"oracle/PIN.json").read_text(encoding="utf-8-sig"))["commit"]
os.environ["PYTHONDONTWRITEBYTECODE"] = "1"
sys.dont_write_bytecode = True
sys.path[:0] = [str(ORACLE), str(ORACLE/"tests")]

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def git(*args):
    return subprocess.check_output(["git","-C",str(ORACLE),*args],text=True).strip()

def validate():
    if git("rev-parse","HEAD") != PIN:
        raise ValueError("Wrong oracle revision")
    if git("status","--porcelain","--untracked-files=no"):
        raise ValueError("Pinned oracle tracked content is dirty")
    history = json.loads((ROOT/"oracle/history/PIN.json").read_text(encoding="utf-8"))
    if history["pinned_descendant"] != PIN:
        raise ValueError("Historical inputs name the wrong pinned descendant")
    historical_root = ROOT/"oracle/history/checkout"
    historical_paths = set()
    for item in history["files"]:
        path = (historical_root/item["path"]).resolve()
        if not path.is_relative_to(historical_root.resolve()):
            raise ValueError("Historical file escapes its snapshot")
        raw = path.read_bytes()
        blob = hashlib.sha1(b"blob "+str(len(raw)).encode()+b"\0"+raw).hexdigest()
        if sha(path) != item["sha256"] or len(raw) != item["bytes"] or blob != item["git_blob"]:
            raise ValueError("Historical oracle input changed: "+item["path"])
        historical_paths.add(item["path"])
    schema = json.loads((ROOT/"corpus/case.schema.json").read_text(encoding="utf-8"))
    validator = jsonschema.Draft202012Validator(schema)
    routes = json.loads((ROOT/"oracle/ROUTES.json").read_text(encoding="utf-8"))
    if routes["commit"] != PIN:
        raise ValueError("Oracle routes are for a different commit")
    cases, ids = [], set()
    for path in sorted((ROOT/"corpus/must").glob("*.json")):
        case = json.loads(path.read_text(encoding="utf-8"))
        validator.validate(case)
        if case["inputs"].get("vocabulary") == "lifecycle-scenario/v1":
            from lifecycle_inputs import decode
            decode(case["inputs"])
        if path.stem != case["id"] or case["id"] in ids:
            raise ValueError("Duplicate or mismatched case identifier")
        ids.add(case["id"])
        for source in case["sources"]:
            if source["repository"] == "gp-history":
                base = historical_root
                if source.get("commit") != history["commit"] or source["path"] not in historical_paths:
                    raise ValueError("Unbound historical source")
            else:
                base = ORACLE if source["repository"] == "gp-v037" else ROOT
                if source["repository"] == "gp-v037" and source.get("commit") != PIN:
                    raise ValueError("Unpinned source")
            source_path = (base/source["path"]).resolve()
            if not source_path.is_relative_to(base.resolve()):
                raise ValueError("Source path escapes its repository")
            lines = source_path.read_text(encoding="utf-8-sig").splitlines()
            if source["anchor"] not in lines[source["line"]-1]:
                raise ValueError("Stale source anchor: "+str(source))
        cases.append((case,path))
    if set(routes["routes"]) != ids:
        raise ValueError("Case and oracle-route identifiers differ")
    return cases, routes["routes"]

def decision(ok, reason, **extra):
    return {"observed_verdict":"ACCEPT" if ok else "REFUSE", "reason":str(reason), **extra}

def never_run(*args, **kwargs):
    raise RuntimeError("Corpus boundary probe unexpectedly attempted a CAS execution")

def probe(case, route):
    from grandportage import kernel as K, store as S, cas, ordered_sos as SOS, field as E, groebner as G
    kind = route["kind"]
    if kind == "operational_retained_observation":
        import importlib.util
        if sha(ROOT/"corpus/must"/(case["id"]+".json")) != route["case_sha256"]:
            raise ValueError("Admitted operational case bytes changed")
        spec = importlib.util.spec_from_file_location("operational_retained", ROOT/"tools/operational-retained-observation.py")
        adapter = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(adapter)
        observation = adapter.verify(case["id"], manifest_sha256=route["manifest_sha256"])
        candidate = json.loads((ROOT/"reports/operational-case-candidates"/(case["id"]+".json")).read_text(encoding="utf-8"))
        if case != candidate:
            raise ValueError("Admitted case differs from bound candidate")
        return {**observation, "status": "RETAINED_DIAGNOSTIC",
                "reason": "Retained operational evidence bindings verified; incident not freshly executed and no native verdict inferred."}
    if kind == "interval_admission":
        from interval_admission_probes import probe as interval_probe
        return interval_probe(case, route)
    if kind == "closure_fixture":
        from closure_fixture_probes import probe as closure_probe
        return closure_probe(case, route)
    if kind == "a24_collapsed_extension":
        from a24_collapsed_probe import probe as a24_probe
        return a24_probe(case, route)
    if kind == "ordinary_point_guard_diagnostic":
        from ordinary_point_guard_probes import probe as ordinary_guard_probe
        return ordinary_guard_probe(case, route)
    if kind == "unsupported_neutral_contract":
        # Record an expressiveness limit without creating a reference checker.
        if sha(ROOT/"corpus/must"/(case["id"]+".json")) != route["case_sha256"]:
            raise ValueError("Bound unsupported neutral case bytes changed")
        return {"observed_verdict": None, "status": "UNSUPPORTED",
                "reason": route["reason"], "oracle_called": False,
                "arithmetic_replayed": False, "lean_compiled": False,
                "premises_assumed_not_verified": True}
    if kind == "a27_unsupported_contract":
        # Keep scope-contract expectations without fabricating a legacy result.
        # Source and rationale: docs/A27-CORRECTED-CONTRACT.md.
        return {"observed_verdict": None, "status": "UNSUPPORTED",
                "reason": "Frozen oracle has no selected class-group/GRH receipt-admission projection; positive check premises are assumptions, not executed checks.",
                "oracle_called": False, "arithmetic_replayed": False,
                "premises_assumed_not_verified": True}
    if kind == "pending":
        return {"observed_verdict":None,"status":"PENDING","reason":route["reason"]}
    if kind == "advice_audit":
        text = (ORACLE/route["path"]).read_text(encoding="utf-8")
        return {"observed_verdict":None,"status":"DIAGNOSTIC_OBSERVED",
                "needles_found":{needle:needle in text for needle in route["needles"]},
                "reason":"Diagnostic wording reproduced from pinned source; no false held claim asserted."}
    if kind in ("transport","partition"):
        control = {}
        if route.get("control") == "target_membership":
            d = case["inputs"]
            control["target_membership"] = G.check_membership_identity(
                d["identity_difference"],d["target_ideal"],d["target_cofactors"],d["variables"],0)
        if route.get("control") == "unit_mod_three":
            G.check_membership_identity("1",case["inputs"]["generators"],case["inputs"]["cofactors"],["x"],0)
            control["rational_identity_replayed"] = True
            control["mod_three_identity"] = G.check_membership_identity("1",case["inputs"]["generators"],case["inputs"]["cofactors"],["x"],3)
        if route.get("control") == "witness_mod_three":
            from fractions import Fraction
            control["rational_substitution"] = 2*Fraction("1/2")-1 == 0
            control["mod_three_substitution"] = (2*2-1)%3 == 0
            if not all(control.values()):
                raise ValueError("Invalid specialization positive control")
        result = (K.transport if kind == "transport" else K.transport_over_partition)(**route["arguments"])
        return decision(result.licensed,result.reason,rule=result.rule,independent_control=control)
    if kind == "sos":
        data = case["inputs"]
        model = {"id":"M","compute_in":"Q","coefficient_domain":"Q","characteristic":0,
                 "ring_vars":data["variables"],"generators":data.get("model_generators",data.get("generators"))}
        certificate = {"method":SOS.METHOD,"ring_vars":data["variables"],
                       "generators":data.get("certificate_generators",data.get("generators")),
                       "squares":data["squares"],"cofactors":data["cofactors"]}
        try:
            receipt = SOS.verify(model,certificate)
        except SOS.OrderedSOSError as exc:
            return decision(False,exc,receipt_checked=False)
        result = E.instantiate({"kind":"ORDERED"},route["target"])
        return decision(result.allowed,result.reason,receipt_checked=True,receipt=receipt)
    if kind == "identifier":
        data = case["inputs"]
        declaration = data["declaration"]
        try:
            program = cas.CASProgram(dialect=cas.SINGULAR,ring="GP_R",ring_vars=data["variables"],
                       decls=[(declaration["name"],"poly" if route["shadow"] else "ideal",declaration["expression"])],
                       body=[],outputs=[declaration["name"]])
        except cas.IdentifierCollision as exc:
            return decision(False,exc,executed=False)
        return decision(True,"Identifier validation accepted; program was not executed.",executed=False)
    if kind == "division":
        try:
            cas.classify_identity(case["inputs"]["variables"],case["inputs"]["lhs"],
                                  case["inputs"]["rhs"],_runner=never_run)
        except cas.CASError as exc:
            return decision(False,exc,executed=False)
        raise RuntimeError("Unsupported division unexpectedly passed")
    if kind == "exact_ambient":
        d = case["inputs"]
        receipt = G.check_membership_identity("("+d["lhs"]+")-("+d["rhs"]+")",[],[],d["variables"],0)
        return decision(True,"Exact polynomial equality replayed with scalar denominators.",receipt=receipt)
    if kind == "kind_composition":
        try:
            K.check_conclusion_kind(K.NONEMPTY,[K.PREDICATE])
        except K.KindCompositionError as exc:
            return decision(False,exc)
        return decision(True,"Legacy pure transport accepted changed quantifier kind")
    if kind == "unknown_certificate":
        try:
            K.derive_scope(K.EMPTY,case["inputs"]["certificate_name"],case["inputs"]["target_context"])
        except K.ScopeError as exc:
            return decision(False,exc)
        return decision(True,"Legacy scope derivation accepted")
    if kind == "redeclaration":
        graph = S.Graph()
        records = case["inputs"].get("declarations")
        if records is None:
            records = [{"id":"A","description":case["inputs"]["description"]}]*2
        try:
            for r in records:
                graph.apply({"ev":"model","id":r["id"],"desc":r["description"]})
            graph.validate()
        except S.GraphError as exc:
            return decision(False,exc)
        return decision(True,"Fold retained one object.",model_count=len(graph.models))
    if kind == "disconnected":
        data = case["inputs"]
        graph = S.Graph()
        events = [{"ev":"model","id":mid,"desc":mid} for mid in ("A","B","C")]
        events += [{"ev":"edge","id":"E","src":data["map_source"],"dst":data["map_target"],
                    "type":K.NECESSARY_CONDITION,"why":"drops equations"},
                   {"ev":"claim","id":"CL","model":data["claim_object"],"kind":K.NONEMPTY,
                    "witness_kind":K.EXHIBITED,"statement":"a point"},
                   {"ev":"inference","id":"I","claim":"CL","path":[["E","ALONG"]],"asserted":"point of B"}]
        try:
            for e in events:
                graph.apply(e)
            graph.validate()
        except S.GraphError as exc:
            return decision(False,exc)
        return decision(True,"The disconnected graph folded")
    if kind == "stale_input":
        # Pinned oracle test helpers fabricate a backend descriptor: this is a
        # binding probe, never evidence that the declared backend actually ran.
        from test_verdict_provenance import _identity_graph, _verdict
        original = _identity_graph(case["inputs"]["old_ideal"][0])
        event = _verdict(original)
        changed = _identity_graph(case["inputs"]["new_ideal"][0])
        changed.apply(event)
        raw = changed.verdicts[event["id"]]
        return decision(bool(raw["current"]),raw.get("stale_reason","current"),
                        receipt_current=raw["current"],
                        claim_has_active_identity="identity_verdict" in changed.claims["C"])
    if kind == "expressibility":
        from test_adversarial import _hyperbola
        from grandportage import check as C
        findings = [f for f in C.run(_hyperbola({"eliminated":["y"]})) if f.rule == C.R_INEXPRESSIBLE]
        refused = any(f.severity == C.UNSOUND_CONCLUSION for f in findings)
        return decision(not refused,"; ".join(f.detail for f in findings),
                        findings=[{"rule":f.rule,"severity":f.severity} for f in findings])

    if kind == "join_fixture":
        from grandportage import check as C
        graph = S.load(str(ORACLE/"fixtures/gamma_window/graph.jsonl"))
        findings = [f for f in C.run(graph) if f.subject == "GI-BRIDGE"]
        refused = any(f.rule == C.R_TRANSPORT for f in findings)
        return decision(not refused,"; ".join(f.detail for f in findings),
                        findings=[{"rule":f.rule,"severity":f.severity} for f in findings])
    if kind == "unverified_attempt":
        from test_verdict_provenance import _identity_graph, _verdict
        graph = _identity_graph()
        event = _verdict(graph,verdict="UNVERIFIED")
        graph.apply(event)
        verdicts = [r.evidence.verdict for r in graph.authority_receipts.values()]
        supported = any(v.startswith("VERIFIED") for v in verdicts)
        return decision(supported,"UNVERIFIED remains visible but provides no positive verification.",
                        projected_verdict=graph.claims["C"].get("identity_verdict"),
                        receipt_wrapper_verdicts=verdicts)
    if kind == "laurent_zero":
        from test_laurent_lowering import _rows78_spec
        from grandportage import laurent_lowering as LL
        spec = _rows78_spec()
        spec["equalities"][0]["right"] = "ZERO"
        try:
            report = LL.verify(spec)
        except LL.LaurentLoweringError as exc:
            return decision(False,exc)
        return decision(True,"Laurent checker accepted",report=report)


    if kind == "alias_binding":
        from grandportage import format as F
        from test_verdict_provenance import _verdict
        def graph_for(mid):
            graph = S.Graph()
            graph.apply(F.meta_event())
            for name in case["inputs"]["identifiers"]:
                graph.apply({"ev":"model","id":name,"what":"same displayed equations",
                             "characteristic":0,"ring_vars":["x"],"generators":["x"]})
            graph.apply({"ev":"claim","id":"C","model":mid,"kind":K.IDENTITY,
                         "statement":"x vanishes","lhs":"x","rhs":"0",
                         "ring_vars":["x"],"identity_origin":K.DERIVED})
            return graph
        a,b = case["inputs"]["identifiers"]
        original = graph_for(a)
        event = _verdict(original)
        original.apply(event)
        changed = graph_for(b)
        changed.apply(event)
        raw = changed.verdicts[event["id"]]
        return decision(bool(raw["current"]),raw.get("stale_reason","current"),
                        original_current=original.verdicts[event["id"]]["current"],
                        destination_has_active_identity="identity_verdict" in changed.claims["C"])
    if kind == "point_universe":
        from grandportage import format as F
        d = case["inputs"]
        graph = S.Graph()
        graph.apply(F.meta_event())
        try:
            for mid,key in (("A","source_universe"),("B","target_universe")):
                model = {"ev":"model","id":mid,"what":"same equations",
                         "characteristic":0,"ring_vars":d["variables"],"generators":d["generators"]}
                if d[key] is not None:
                    model.update(coefficient_domain=d["coefficient_domain"],point_universe=d[key])
                graph.apply(model)
            graph.apply({"ev":"edge","id":"E","src":"A","dst":"B",
                         "type":K.EQUIVALENCE,"map_kind":K.IDENTITY_MAP,
                         "forward":{"x":"x"},"inverse":{"x":"x"},"ring_iso":True,
                         "why":"identity on the coordinate ring"})
            graph.validate()
        except S.GraphError as exc:
            return decision(False,exc)
        return decision(True,"Relation declaration folded.")
    if kind == "empty_anchor":
        from grandportage import format as F, check as C
        from test_empty_scope_anchor import _certificate, _claim
        d = case["inputs"]
        graph = S.Graph()
        graph.apply(F.meta_event())
        model = {"ev":"model","id":"M","desc":"combinatorial objects"}
        if d["coefficient_domain"]:
            model.update(characteristic=0,coefficient_domain=d["coefficient_domain"])
        for event in (model,_certificate(False),_claim(d["claimed_field"])):
            graph.apply(event)
        findings = [f for f in C.run(graph) if f.rule == C.R_EMPTY_SCOPE]
        return decision(not any(f.severity == C.UNSOUND_PREMISE for f in findings),
                        "; ".join(f.detail for f in findings),
                        findings=[{"rule":f.rule,"severity":f.severity} for f in findings])
    if kind == "membership":
        d = case["inputs"]
        try:
            receipt = G.check_membership_identity(d["target"],d["generators"],d["cofactors"],
                                                   d["variables"],d["characteristic"])
        except G.CertificateError as exc:
            return decision(False,exc)
        return decision(True,"Exact membership identity replayed.",receipt=receipt)
    if kind == "localization":
        from grandportage import localization as L
        d = case["inputs"]
        spec = {"schema":L.SCHEMA,"characteristic":0,"ring_vars":d["variables"],
                "generators":d["generators"],"guards":d["guards"],
                "expression":{"numerator":d["numerator"],"denominator_powers":d["denominator_powers"]},
                "certificate":{key:d[key] for key in ("localization_powers","membership_target","cofactors")}}
        try:
            receipt = L.verify(spec)
        except L.LocalizationError as exc:
            return decision(False,exc)
        return decision(receipt["verdict"] == L.VERIFIED,"Localization checker replayed.",receipt=receipt)
    if kind == "ring_iso":
        from grandportage import verify as V, format as F
        d = case["inputs"]
        graph = S.Graph()
        graph.apply(F.meta_event())
        for mid in ("A","B"):
            graph.apply({"ev":"model","id":mid,"what":mid,"characteristic":0,
                         "ring_vars":d["variables"],"generators":d["generators"]})
        graph.apply({"ev":"edge","id":"E","src":"A","dst":"B","type":K.EQUIVALENCE,
                     "map_kind":K.POLYNOMIAL,"why":"displayed maps","ring_iso":True,
                     "forward":d["forward"],"inverse":d["inverse"],
                     "ring_iso_certificate":{"schema":"mapped_ring_iso_v1",
                         "forward_cofactors":d["forward_cofactors"],"inverse_cofactors":d["inverse_cofactors"]}})
        verdict,why = V.ring_iso(graph,"E",_runner=never_run)
        return decision(verdict == V.ISO_VERIFIED,why,raw_verdict=verdict)
    if kind == "extension_witness":
        from grandportage import verify as V
        from test_number_field_witness import _graph, _model, _claim, _field
        d = case["inputs"]
        model = _model(d["point_universe"],d["generators"][0])
        model.update(ring_vars=d["variables"],open_conditions=d["guards"])
        graph = _graph([model,_claim(d["coordinate"],_field(d["field_polynomial"]))])
        verdict,why,receipt = V.point_witness(graph,"C",_runner=never_run)
        return decision(verdict == V.WITNESS_VERIFIED,why,raw_verdict=verdict,receipt=receipt)

    if kind in ("jc_cap_obstruction", "bounded_source_point"):
        from grandportage import coefficient_expansion as CE
        d = case["inputs"]
        parameter = d["parameter"]
        ring = d["source_variables"] + [parameter]
        if kind == "jc_cap_obstruction":
            point = {**d["other_retained_values"], **d["selected"], **d["forced"]}
        else:
            point = d["point"]
        images = {**point, parameter:parameter}
        residuals = [G.substitute_polynomial(eq,ring,images,0) for eq in d["source_equations"]]
        if any(not G.parse_polynomial(value,ring,0).is_zero for value in residuals):
            return decision(False,"The supplied source point fails an equation.",residuals=residuals)
        if kind == "bounded_source_point":
            degrees = {}
            for name,value in point.items():
                poly = G.parse_polynomial(value,[parameter],0)
                degrees[name] = max((m[0] for m in poly.terms),default=-1)
            fits = all(degrees[name] <= cap for name,cap in d["caps"].items())
            return decision(fits,"Exact source substitution and polynomial degree caps checked.",
                            residuals=residuals,degrees=degrees,caps=d["caps"])
        if d["cap"] != {"dm4":0}:
            raise ValueError("This source projection is specifically the cap-zero obstruction")
        obstruction = d["coefficient_obstruction"]
        coordinate = obstruction["variable"]
        bounded_images = {**point,"dm4":coordinate}
        equations = []
        for i,expression in enumerate(d["source_equations"]):
            equations.append({"id":["G1","G2","G3","G5"][i],"expression":expression,"degree":1,
                              "coverage":CE.COMPLETE,
                              "coefficients":obstruction["rows"] if i == 1 else {"0":"0","1":"0"}})
        spec = {"schema":CE.SCHEMA,"characteristic":0,"parameter":parameter,
                "coefficient_variables":[coordinate],"source_variables":d["source_variables"],
                "images":bounded_images,"bounded_variables":{"dm4":{"cap":0,"coefficients":[coordinate]}},
                "equations":equations}
        expansion = CE.verify(spec)
        rows = list(expansion["equations"][1]["checked_coefficients"].values())
        unit = G.check_membership_identity("1",rows,obstruction["unit_cofactors"],[coordinate],0)
        return decision(False,"The unrestricted source point verifies, but the complete cap-zero coefficient fiber contains 1.",
                        unrestricted_residuals=residuals,coefficient_expansion=expansion,unit_receipt=unit)
    if kind == "coefficient_expansion":
        from grandportage import coefficient_expansion as CE
        d = case["inputs"]
        keys = ("parameter","source_variables","coefficient_variables","images","bounded_variables","equations")
        spec = {"schema":CE.SCHEMA,"characteristic":0,**{key:d[key] for key in keys}}
        try:
            report = CE.verify(spec)
        except CE.CoefficientExpansionError as exc:
            return decision(False,exc)
        control = None
        if "counterexample_coefficients" in d:
            names = d["coefficient_variables"]
            values = d["counterexample_coefficients"]
            selected = [G.substitute_polynomial(row,names,values,0)
                        for row in report["equations"][0]["checked_coefficients"].values()]
            omitted = G.substitute_polynomial("a1*b1",names,values,0)
            if any(v != "0" for v in selected) or omitted != "1":
                raise ValueError("Invalid selected-coefficients counterexample")
            control = {"selected_rows":selected,"omitted_quadratic_row":omitted}
        return decision(d["requested_license"] in report["licenses"],
                        "Requested implication compared with the replayed license.",
                        receipt=report,counterexample=control)

    if kind == "historical_seam":
        import copy, importlib.util, tempfile
        historical = json.loads((ROOT/"oracle/history/PIN.json").read_text(encoding="utf-8"))
        if route["historical_commit"] != historical["commit"]:
            raise ValueError("Wrong historical adapter revision")
        path = ROOT/"oracle/history/checkout/experiments/jc_h3_source_depth6/original_pair_seam_adapter.py"
        spec = importlib.util.spec_from_file_location("historical_seam_probe",path)
        adapter = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(adapter)
        action = route["action"]
        report = adapter.verify_fixture(check_native_bindings=False)
        if action in ("conditional", "source_authority"):
            envelope = report["evidence_envelope"]
            accepted = (report["strict_original_source_supported"] if action == "source_authority" else
                        report["verdict"] == "VERIFIED_CONDITIONAL_ESYSTEM_SEAM" and
                        envelope["graph_effect"] == "NONE" and bool(envelope["outstanding_premises"]))
            return decision(accepted,"Historical conditional boundary inspected.",raw_report=report)
        fixture = json.loads(adapter.DEFAULT_FIXTURE.read_text(encoding="utf-8"))
        value = case["inputs"]["proposed_value"]
        try:
            if action in ("native_commit", "outer_digest"):
                fixture["native_commit" if action == "native_commit" else "authority_boundary"] = value
                raw = (json.dumps(fixture,indent=2,sort_keys=True,ensure_ascii=True)+"\n").encode()
                # Mirrors the historical mutation test: reach the revision
                # check independently of the separate immutable-byte guard.
                if action == "native_commit":
                    adapter.EXPECTED_FIXTURE_SHA256 = hashlib.sha256(raw).hexdigest()
                with tempfile.TemporaryDirectory(prefix="history-seam-",dir=ROOT/"tmp") as scratch:
                    target = Path(scratch)/"fixture.json"
                    target.write_bytes(raw)
                    adapter.verify_fixture(target,check_native_bindings=False)
            else:
                manifest = copy.deepcopy(fixture["manifest"])
                if action == "strict_authority":
                    manifest["authority"]["strict_original_source_supported"] = value
                elif action == "source_map":
                    next(s for s in manifest["stages"] if s["id"] == "target_pair_to_normalized_laurent_root").update(value)
                elif action == "serialized_pair":
                    manifest["source_problem"]["exact_pair_serialized"] = value
                elif action == "downstream_pin":
                    manifest["normalized_root_contract"]["pin_semantics"]["part_of_reduced_row_derivation"] = value
                elif action == "row_digest":
                    manifest["reduced_rows"][0]["sha256"] = value
                elif action == "drop_refusal":
                    manifest["authority"]["refusals"].remove(value)
                else:
                    raise ValueError("Unknown historical seam action")
                face = json.loads(adapter.FACE_FIXTURE.read_text(encoding="utf-8"))
                adapter._validate_manifest(manifest,face)
        except adapter.SeamAdapterError as exc:
            return decision(False,exc,baseline_verdict=report["verdict"],historical_commit=historical["commit"])
        return decision(True,"Historical seam validator accepted the proposed change.",historical_commit=historical["commit"])

    if kind == "native_witness_binding":
        import copy
        from grandportage import verify as V, provenance as P
        from test_number_field_witness import _graph, _model, _claim, _field
        d = case["inputs"]
        model = _model(d["point_universe"],d["generators"][0])
        model.update(ring_vars=d["variables"],open_conditions=d["guards"])
        claim = _claim(d["coordinate"],_field(d["field_polynomial"]))
        graph = _graph([model,claim])
        verdict,why,receipt = V.point_witness(graph,"C",_runner=never_run)
        if verdict != V.WITNESS_VERIFIED:
            raise ValueError("Native binding positive baseline did not verify")
        event = V._verdict_event(graph,"witness","C",verdict,why,receipt,
                                 execution=P.native_execution_provenance())
        graph.apply(event)
        if not graph.verdicts[event["id"]]["current"]:
            raise ValueError("Native baseline receipt did not become current")
        action = route["action"]
        changed_model = copy.deepcopy(model)
        if action == "model":
            changed_model.update(d["proposed_change"])
        changed = _graph([changed_model,copy.deepcopy(claim)])
        attacked = copy.deepcopy(event)
        if action == "verifier_version":
            attacked["verifier_version"] += 1
        elif action == "tamper_coordinate":
            attacked["representation"]["coordinates"]["x"] = d["proposed_change"]
            attacked.update(P.metadata(changed,"witness","C",verdict=verdict,
                verifier="verify.extension_point_witness",execution=P.native_execution_provenance(),
                representation=attacked["representation"]))
        elif action not in ("model","unchanged"):
            raise ValueError("Unknown native binding action")
        try:
            changed.apply(attacked)
        except S.GraphError as exc:
            return decision(False,exc,baseline_current=True,refused_at="graph_fold")
        raw = changed.verdicts[attacked["id"]]
        active = changed.claims["C"].get("witness_verdict") == V.WITNESS_VERIFIED
        return decision(bool(raw["current"]) and active,raw.get("stale_reason","native receipt current"),
                        baseline_current=True,receipt_current=raw["current"],active_witness=active)

    if kind == "formalization_ledger":
        import copy, importlib.util
        historical = json.loads((ROOT/"oracle/history/PIN.json").read_text(encoding="utf-8"))
        if route["historical_commit"] != historical["commit"]:
            raise ValueError("Wrong formalization-ledger revision")
        path = ROOT/"oracle/history/checkout/experiments/jc_formalization_transport/adapter.py"
        spec = importlib.util.spec_from_file_location("historical_formalization_probe",path)
        adapter = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(adapter)
        fixture = json.loads(adapter.DEFAULT_FIXTURE.read_text(encoding="utf-8"))
        edges = {e["id"]:e for e in fixture["edges"]}
        action = route["action"]
        if action == "assay":
            assay = next(a for a in fixture["assays"] if a["id"] == route["assay"])
            actual = adapter._run_assay(assay,edges)
            if actual["actual_verdict"] == adapter.INEXPRESSIBLE:
                return {"observed_verdict":None,"status":"UNSUPPORTED",
                        "reason":actual["reason"],"raw_verdict":actual["actual_verdict"]}
            return decision(actual["actual_verdict"] == adapter.LICENSED,actual["reason"],
                            raw_verdict=actual["actual_verdict"],graph_effect=adapter.GRAPH_EFFECT)
        edge = copy.deepcopy(edges["JC.EDGE.SLICE_TO_BLOCK_ONE_ZERO"])
        authorities = {a["id"]:copy.deepcopy(a) for a in fixture["authorities"]}
        if action == "omit_premise":
            edge["premise_ids"].remove("JC.PREM.ORDER_EIGHT_BOUNDED")
        elif action == "rebind_target":
            authorities[edge["authority_id"]]["target_object_id"] = "JC.SEM.RELAXED_SUMMIT_POINT"
        elif action != "retain":
            raise ValueError("Unknown formalization-ledger action")
        try:
            normalized = adapter._normalize_edge(edge,{o["id"] for o in fixture["objects"]},
                authorities,{p["id"] for p in fixture["premises"]})
        except adapter.FormalizationLedgerError as exc:
            if not str(exc).startswith(("EDG6:","EDG7:")):
                raise
            return decision(False,exc,graph_effect=adapter.GRAPH_EFFECT)
        return decision(True,"The theorem endpoints and all conditional premises remain bound.",
                        premise_ids=normalized["premise_ids"],graph_effect=adapter.GRAPH_EFFECT)

    if kind == "historical_paxis":
        import copy, importlib.util
        from grandportage import check as C, verify as V
        historical = json.loads((ROOT/"oracle/history/PIN.json").read_text(encoding="utf-8"))
        if route["historical_commit"] != historical["commit"]:
            raise ValueError("Wrong p-axis historical revision")
        path = ROOT/"oracle/history/checkout/tests/test_jc_p_axis_authority.py"
        spec = importlib.util.spec_from_file_location("historical_paxis_probe",path)
        helper = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(helper)
        adapter = helper.ADAPTER
        frozen, raw = helper._frozen()
        bound = adapter.authority_spec(frozen)
        data = case["inputs"]
        expected_inputs = {"variables":bound["ring_vars"],"generators":bound["generators"],
            "guards":bound["guards"],**bound["expression"],**bound["certificate"]}
        if any(data[key] != value for key,value in expected_inputs.items()):
            raise ValueError("Neutral p-axis inputs differ from the historical proof")
        action = route["action"]
        if action == "bytes":
            try:
                adapter.freeze_native({"schema":adapter.NATIVE_SCHEMA,"chart":"p"},
                    case["inputs"]["proposed_parent_bytes_utf8"].encode())
            except ValueError as exc:
                if "native p-window receipt changed" not in str(exc):
                    raise
                return decision(False,exc,backend_executed=False)
            return decision(True,"Native parent bytes accepted.",backend_executed=False)
        if action == "name":
            graph = adapter.graph_from_frozen(frozen,raw)
            cert = C.effective_certificate(graph.claims[adapter.EMPTY_CLAIM])
            return decision(cert is not None,"Effective certificate: "+str(cert),backend_executed=False)
        graph, event = helper._verified_graph()
        if not graph.verdicts[event["id"]]["current"]:
            raise ValueError("Historical p-axis binding baseline is not current")
        if action == "parent":
            licensed, trace = adapter.parent_refusal(graph)
            return decision(licensed,"Parent transport audited.",trace=trace,
                baseline_current=True,execution_descriptor="fabricated_historical_test_trace")
        if action not in ("unchanged","equation","guard","universe","chart","source"):
            raise ValueError("Unknown p-axis action")
        changed = helper._graph_with_axis_updates(case["inputs"].get("proposed_change",{}))
        changed.apply(copy.deepcopy(event))
        stored = changed.verdicts[event["id"]]
        effective = C.effective_certificate(changed.claims[adapter.EMPTY_CLAIM])
        return decision(bool(stored["current"]) and effective is not None,
            stored.get("stale_reason","Historical receipt remains current."),
            receipt_current=stored["current"],effective_certificate=effective,
            baseline_current=True,execution_descriptor="fabricated_historical_test_trace")

    if kind == "ordered_recording":
        from ordered_recording_probes import probe as ordered_probe
        return ordered_probe(case, route)
    if kind == "laurent_pipeline":
        from laurent_pipeline_probes import probe as pipeline_probe
        return pipeline_probe(case,route)
    if kind == "factor_composition":
        from factor_composition_probes import probe as factor_probe
        return factor_probe(case,route)
    if kind == "product_split":
        from product_split_probes import probe as product_probe
        return product_probe(case,route)
    if kind == "universe_boundary":
        from universe_boundary_probes import probe as universe_probe
        return universe_probe(case,route)
    if kind == "partition_embeddings":
        from partition_embedding_probes import probe as embedding_probe
        return embedding_probe(case,route)
    if kind == "partition_guards":
        from partition_guard_probes import probe as partition_probe
        return partition_probe(case,route)
    if kind == "mapped_ring":
        from mapped_ring_probes import probe as mapped_probe
        return mapped_probe(case,route)
    if kind == "output_membership":
        from output_membership_probes import probe as output_probe
        return output_probe(case,route)
    if kind == "section_receipt":
        from section_probes import probe as section_probe
        return section_probe(case,route)
    if kind == "compiler_slots":
        from compiler_slot_probes import probe as compiler_slot_probe
        return compiler_slot_probe(case,route)
    if kind == "launch_boundary":
        from launch_probes import probe as launch_probe
        return launch_probe(case,route)
    if kind == "replay_boundary":
        from replay_boundary_probes import probe as replay_boundary_probe
        return replay_boundary_probe(case,route)
    if kind == "artifact_storage":
        from artifact_probes import probe as artifact_probe
        return artifact_probe(case,route)
    if kind == "execution_envelope":
        from execution_probes import probe as execution_probe
        return execution_probe(case,route)
    if kind == "inventory_diagnostic":
        from inventory_probes import probe as inventory_probe
        return inventory_probe(case,route)
    if kind == "provenance_review":
        from provenance_probes import probe as provenance_probe
        return provenance_probe(case,route)
    if kind == "joint_premises":
        from joint_probes import probe as joint_probe
        return joint_probe(case,route)
    if kind == "lifecycle":
        from lifecycle_probes import probe as lifecycle_probe
        return lifecycle_probe(case,route)
    if kind == "current_algebra":
        from current_algebra_probes import probe as current_probe
        return current_probe(case,route)
    if kind == "membership_contraction":
        from membership_contraction_probes import probe as membership_contraction_probe
        return membership_contraction_probe(case,route)
    if kind == "structural_dispatch":
        from structural_dispatch_probes import probe as structural_dispatch_probe
        return structural_dispatch_probe(case,route)
    if kind == "zero_regime_arithmetic":
        from zero_regime_probes import probe as zero_regime_probe
        return zero_regime_probe(case,route)
    if kind == "dm4_zero_chart":
        from dm4_zero_chart_probes import probe as dm4_zero_chart_probe
        return dm4_zero_chart_probe(case,route)
    if kind == "receipt_partition":
        from receipt_partition_probes import probe as receipt_partition_probe
        return receipt_partition_probe(case,route)
    if kind == "q2_exact":
        from q2_exact_probes import probe as q2_exact_probe
        return q2_exact_probe(case,route)
    if kind == "q3_map":
        from q3_map_probes import probe as q3_map_probe
        return q3_map_probe(case,route)
    if kind == "base_cover_refutation":
        from base_cover_refutation_probes import probe as base_cover_probe
        return base_cover_probe(case,route)
    if kind == "historical_depth8_block":
        from historical_depth8_block_probes import probe as historical_depth8_block_probe
        return historical_depth8_block_probe(case,route)
    if kind == "historical_residual":
        from historical_residual_probes import probe as historical_residual_probe
        return historical_residual_probe(case,route)
    if kind == "historical_review":
        from historical_probes import probe as historical_probe
        return historical_probe(case,route)

    raise ValueError("Unknown oracle route: "+kind)

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--run-oracle",action="store_true")
    args = parser.parse_args()
    cases,routes = validate()
    print("Validated",len(cases),"cases, source anchors and pinned oracle identity.")
    if not args.run_oracle:
        return
    results = []
    for case,path in cases:
        route = routes[case["id"]]
        record = {"id":case["id"],"case_sha256":sha(path),"expected":case["expected"]["verdict"],
                  "layer":route["layer"],"route":route["kind"],"historical_commit":route.get("historical_commit"),"limitation":route.get("limitation")}
        try:
            record.update(probe(case,route))
            if record["observed_verdict"] is not None:
                same = record["observed_verdict"] == record["expected"]
                record["status"] = "AGREES" if same else (
                    "KNOWN_DIFFERENCE" if route.get("known_difference") else "REVIEW_REQUIRED")
                if not same:
                    record["difference_class"] = route.get("known_difference","untriaged")
        except Exception as exc:
            record.update(status="ERROR",observed_verdict=None,reason=str(exc),traceback=traceback.format_exc())
        results.append(record)
    stamp = datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%S%fZ")
    report = {"schema_version":1,"timestamp_utc":stamp,"oracle_commit":PIN,
              "oracle_path":str(ORACLE),"runner_sha256":sha(Path(__file__)),
              "closure_fixture_probe_sha256":sha(ROOT/"tools/closure_fixture_probes.py"),
              "a24_collapsed_probe_sha256":sha(ROOT/"tools/a24_collapsed_probe.py"),
              "ordinary_point_guard_probe_sha256":sha(ROOT/"tools/ordinary_point_guard_probes.py"),
              "guard_snapshot_probe_sha256":sha(ROOT/"tools/guard_snapshot_probes.py"),
              "cramer_exponent_probe_sha256":sha(ROOT/"tools/cramer_exponent_probes.py"),
              "interval_admission_probe_sha256":sha(ROOT/"tools/interval_admission_probes.py"),
              "operational_retained_adapter_sha256":sha(ROOT/"tools/operational-retained-observation.py"),
              "historical_probe_sha256":sha(ROOT/"tools/historical_probes.py"),
               "historical_residual_probe_sha256":sha(ROOT/"tools/historical_residual_probes.py"),
               "historical_depth8_block_probe_sha256":sha(ROOT/"tools/historical_depth8_block_probes.py"),
               "structural_dispatch_probe_sha256":sha(ROOT/"tools/structural_dispatch_probes.py"),
               "zero_regime_probe_sha256":sha(ROOT/"tools/zero_regime_probes.py"),
               "dm4_zero_chart_probe_sha256":sha(ROOT/"tools/dm4_zero_chart_probes.py"),
               "receipt_partition_probe_sha256":sha(ROOT/"tools/receipt_partition_probes.py"),
               "q2_exact_probe_sha256":sha(ROOT/"tools/q2_exact_probes.py"),
               "q3_map_probe_sha256":sha(ROOT/"tools/q3_map_probes.py"),
               "base_cover_refutation_probe_sha256":sha(ROOT/"tools/base_cover_refutation_probes.py"),
              "current_algebra_probe_sha256":sha(ROOT/"tools/current_algebra_probes.py"),
              "lifecycle_probe_sha256":sha(ROOT/"tools/lifecycle_probes.py"),
              "joint_probe_sha256":sha(ROOT/"tools/joint_probes.py"),
              "provenance_probe_sha256":sha(ROOT/"tools/provenance_probes.py"),
              "inventory_probe_sha256":sha(ROOT/"tools/inventory_probes.py"),
              "execution_probe_sha256":sha(ROOT/"tools/execution_probes.py"),
              "artifact_probe_sha256":sha(ROOT/"tools/artifact_probes.py"),
              "replay_boundary_probe_sha256":sha(ROOT/"tools/replay_boundary_probes.py"),
              "launch_probe_sha256":sha(ROOT/"tools/launch_probes.py"),
              "compiler_slot_probe_sha256":sha(ROOT/"tools/compiler_slot_probes.py"),
              "section_probe_sha256":sha(ROOT/"tools/section_probes.py"),
              "output_membership_probe_sha256":sha(ROOT/"tools/output_membership_probes.py"),
              "mapped_ring_probe_sha256":sha(ROOT/"tools/mapped_ring_probes.py"),
              "partition_guard_probe_sha256":sha(ROOT/"tools/partition_guard_probes.py"),
              "partition_embedding_probe_sha256":sha(ROOT/"tools/partition_embedding_probes.py"),
              "ordered_recording_probe_sha256":sha(ROOT/"tools/ordered_recording_probes.py"),
              "membership_contraction_probe_sha256":sha(ROOT/"tools/membership_contraction_probes.py"),
              "laurent_pipeline_probe_sha256":sha(ROOT/"tools/laurent_pipeline_probes.py"),
              "factor_composition_probe_sha256":sha(ROOT/"tools/factor_composition_probes.py"),
              "product_split_probe_sha256":sha(ROOT/"tools/product_split_probes.py"),
              "universe_boundary_probe_sha256":sha(ROOT/"tools/universe_boundary_probes.py"),
              "artifact_fixture_sha256":sha(ORACLE/"tests/test_artifacts.py"),
              "lifecycle_input_adapter_sha256":sha(ROOT/"tools/lifecycle_inputs.py"),
              "lifecycle_baseline_sha256":sha(ROOT/"oracle/LIFECYCLE-INPUT-BASELINE.json"),
              "routes_sha256":sha(ROOT/"oracle/ROUTES.json"),
              "historical_manifest_sha256":sha(ROOT/"oracle/history/PIN.json"),
              "schema_sha256":sha(ROOT/"corpus/case.schema.json"),
              "python":sys.version,"summary":dict(Counter(r["status"] for r in results)),
              "scope":"Layer-specific legacy observations, not GP 0.50 held claims or a completed G0 gate.",
              "results":results}
    history = ROOT/"reports/oracle-runs"
    history.mkdir(exist_ok=True)
    payload = json.dumps(report,indent=2,ensure_ascii=False)+"\n"
    with (history/(stamp+".json")).open("x",encoding="utf-8") as f:
        f.write(payload)
    (ROOT/"reports/ORACLE-RESULTS.json").write_text(payload,encoding="utf-8")
    print(json.dumps(report["summary"]))
    for result in results:
        if result["status"] in ("ERROR","REVIEW_REQUIRED","KNOWN_DIFFERENCE"):
            print(result["id"],result["status"],result["reason"][:180])
    if any(r["status"] in ("ERROR","REVIEW_REQUIRED") for r in results):
        raise SystemExit(1)

if __name__ == "__main__":
    main()
