"""Licence reconstruction over loaded state. Read-only; never mathematical authority."""
from collections import Counter
from copy import deepcopy
from . import check as C, kernel as K, provenance as P
from . import project_v2 as I

OBLIGATIONS = ("field_transport", "selected_structure", "expressibility", "predicate_rewrite",
               "preservation_evidence", "interpreter_requirements", "composition", "current_binding", "witness_custody")
LEAN_NAMES = {"partition_empty": "GrandPortage.IR.partition_empty",
              "partition_predicate": "GrandPortage.IR.partition_predicate",
              "family_reindex": "GrandPortage.IR.family_reindex","partition": "GrandPortage.IR.Licence.partition", "family": "GrandPortage.IR.Licence.family",
              "partition_admission": "GrandPortage.IR.partition_admission", "family_admission": "GrandPortage.IR.family_admission",
              "coverage_countermodel": "GrandPortage.IR.missing_partition_branch_countermodel",
              "semantic_kernel": "GrandPortage.SemanticLoss.integer_gaussian_kernel",
              "semantic_loss": "GrandPortage.SemanticLoss.integer_gaussian_no_loss"}

def lean_checks():
    return "import GrandPortage.SemanticLoss\nimport GrandPortage.IR\n\n" + "".join("#check "+v+"\n" for v in sorted(LEAN_NAMES.values()))

def obligation(status, fields=(), missing=None, interpretation=None, reason=None):
    return {"status": status, "fields": list(fields), "missing": missing,
            "interpretation": interpretation, "reason": reason}

def reified(*fields, reason=None):
    return obligation("REIFIED", fields, reason=reason)

def data_gap(missing, *fields):
    return obligation("DATA_GAP", fields, missing=missing)

def adapter_gap(interpretation, *fields):
    return obligation("ADAPTER_GAP", fields, interpretation=interpretation)

def _receipts(graph, cid):
    return [(rid, v) for rid,v in sorted(graph.verdicts.items()) if v.get("of")==cid]

def _current(graph, rid, receipt):
    try:
        current, reason = P.current_verdict(graph, receipt)
    except (ValueError, KeyError, TypeError) as exc:
        return False, str(exc)
    if not current: return False, reason
    if not receipt.get("current") or rid not in graph.authority_receipts:
        return False, "no loaded current authority receipt"
    return True, reason

def explain(graph, node, kind=None):
    """Recover data relationships; a REIFIED row is not a proved Python/Lean codec."""
    if node in graph.models:
        matches=[iid for iid,i in graph.inferences.items() if i.get("concludes_at")==node
                 and (kind is None or i.get("concludes_kind")==kind) and not i.get("superseded_by")]
        if len(matches)!=1: raise ValueError("model selection requires exactly one matching inference; name its id")
        node=matches[0]
    if node not in graph.claims and node not in graph.inferences: raise ValueError("unknown claim or inference: "+node)
    try:
        runtime_clean=set(C.clean_inferences(graph,C.run(graph)))
        load_issue=None
    except (KeyError, ValueError, TypeError) as exc:
        runtime_clean=set();load_issue=str(exc)
    def build(identifier, seen):
        if identifier in seen:
            return {"id":identifier,"node_kind":"cycle","complete":False,
                    "obligations":{name:adapter_gap("cyclic derivation", "inferences."+identifier) for name in OBLIGATIONS},"children":[]}
        seen=seen|{identifier}
        inference=graph.inferences.get(identifier)
        claim=graph.claims.get(identifier,{})
        kind_here=inference.get("concludes_kind") if inference else claim.get("kind")
        base="inferences."+identifier if inference else "claims."+identifier
        obs={name:reified(base, reason="not required for this node's rule") for name in OBLIGATIONS}
        children=[]; receipts=[];flags=[];parts={};mode="leaf"
        if inference is None:
            mid=claim.get("model"); model=graph.models.get(mid)
            if model is None:
                if claim.get("family") in graph.families:
                    parts["family"]=deepcopy(graph.families[claim["family"]])
                    obs["expressibility"]=adapter_gap("family claim interpretation",base,"families."+claim["family"])
                else: obs["expressibility"]=data_gap("model or family context",base)
            else:
                ctx=I.context(mid,model)
                obs["field_transport"]=reified("models."+mid) if not ctx["missing"] else data_gap(", ".join(ctx["missing"]),"models."+mid)
                if kind_here==K.PREDICATE:
                    obs["expressibility"]=(reified(base+".condition") if claim.get("condition") is not None
                                            else data_gap("machine-readable predicate formula",base+".statement"))
                elif kind_here==K.IDENTITY:
                    obs["expressibility"]=(reified(base+".lhs",base+".rhs",base+".identity_origin")
                        if all(claim.get(f) is not None for f in ("lhs","rhs","identity_origin"))
                        else data_gap("identity expressions and origin",base))
            records=_receipts(graph,identifier)
            for rid,receipt in records:
                active,why=_current(graph,rid,receipt)
                receipts.append({"id":rid,"current":active,"why":why,
                                 "fields":["verdicts."+rid,"authority_receipts."+rid]})
            active=[(rid,v) for rid,v in records if _current(graph,rid,v)[0] and str(v.get("verdict", "")).startswith("VERIFIED")]
            if not records:
                obs["interpreter_requirements"]=data_gap("retained interpreter receipt",base)
                obs["current_binding"]=data_gap("current bound receipt",base)
            elif not active:
                obs["current_binding"]=data_gap("current bound receipt",*["verdicts."+rid for rid,_ in records])
                obs["interpreter_requirements"]=adapter_gap("inactive retained receipt interpretation",*["verdicts."+rid for rid,_ in records])
            else:
                rid,v=active[-1]
                obs["current_binding"]=reified("verdicts."+rid+".input_fingerprint","authority_receipts."+rid)
                if v.get("representation") is None:
                    obs["interpreter_requirements"]=data_gap("retained interpreter representation","verdicts."+rid)
                elif (v.get("verifier"), v.get("verifier_version")) == ("verify.ordered_sos", 1) and set(v["representation"]) == {"method", "ring_vars", "generators", "squares", "cofactors"}:
                    # The interpreter identity and exact retained representation identify
                    # this conditional rule. A certificate tag alone never enters here.
                    parts["interpretation"]={"interpreter":"verify.ordered_sos/1",
                        "premises":["rational expression interpretation", "model equations vanish", "ordered target laws"],
                        "recovered":"current receipt establishes the rational SOS identity",
                        "scope":"conditional ordered contradiction; target-law interpretation remains a semantic premise"}
                    obs["interpreter_requirements"]=reified("verdicts."+rid+".verifier","verdicts."+rid+".representation",
                        reason="conditional ordered interpreter requirements recovered from current replay receipt")
                else:
                    obs["interpreter_requirements"]=adapter_gap("actual structural requirement discharge from this verifier representation",
                        "verdicts."+rid+".representation","verdicts."+rid+".verifier")
            if claim.get("certificate") and records and obs["interpreter_requirements"]["status"]!="REIFIED":
                flags.append("PROFILE_FROM_TAG")
            if kind_here==K.NONEMPTY and not claim.get("existential"):
                obs["witness_custody"]=(reified(base+".witness_point") if claim.get("witness_point") is not None
                                        else data_gap("chosen witness coordinates",base))
            runtime_licensed=bool(active)
        else:
            premises=inference.get("premises",[])
            for premise in premises:
                cid=premise.get("claim")
                if cid in graph.claims or cid in graph.inferences: children.append(build(cid,seen))
                else: obs["composition"]=data_gap("premise claim "+str(cid),base+".premises")
            parts["premises"]=deepcopy(premises)
            refs=[base+".premises"]
            if inference.get("via_partition"):
                mode="partition";pid=inference["via_partition"];p=graph.partitions.get(pid)
                if p is None: obs["composition"]=data_gap("partition record "+pid,base+".via_partition")
                else:
                    parts["partition"]=deepcopy(p);refs.append("partitions."+pid)
                    coverage=p.get("exhaustive")
                    if coverage not in graph.claims: obs["composition"]=data_gap("coverage claim "+str(coverage),"partitions."+pid)
                    elif not any(pr.get("claim")==coverage for pr in premises): obs["composition"]=data_gap("cited coverage premise",base+".premises")
                    elif p.get("exhaustive_verdict")!="VERIFIED": obs["composition"]=data_gap("current exhaustive coverage receipt","partitions."+pid)
                    else:
                        carried={graph.claims.get(pr.get("claim"),{}).get("model") for pr in premises
                                 if graph.claims.get(pr.get("claim"),{}).get("kind")==kind_here}
                        missing_branches=[branch for branch in p.get("branches",[]) if branch not in carried]
                        if missing_branches:
                            obs["composition"]=data_gap("branch licences: "+", ".join(missing_branches),base+".premises","partitions."+pid+".branches")
                        elif not any(_current(graph,rid,v)[0] and v.get("verdict")=="VERIFIED" for rid,v in _receipts(graph,pid)):
                            obs["composition"]=data_gap("current exhaustive coverage receipt","partitions."+pid)
                        else: obs["composition"]=reified(*refs,reason="explicit coverage claim and cross-model branches recovered")
            bridges=inference.get("family_bridges",{})
            if bridges:
                mode="family" if mode=="leaf" else mode+"+family"
                parts["family_bridges"]={}
                for cid,bid in bridges.items():
                    bridge=graph.family_bridges.get(bid)
                    if bridge is None: obs["composition"]=data_gap("family_bridge record "+bid,base+".family_bridges")
                    elif bridge.get("family") not in graph.families: obs["composition"]=data_gap("family record "+str(bridge.get("family")),"family_bridges."+bid)
                    else:
                        parts["family_bridges"][bid]=deepcopy(bridge)
                        if obs["composition"]["status"]=="REIFIED":
                            obs["composition"]=reified(base+".family_bridges","family_bridges."+bid,"families."+bridge["family"],reason="bounded member relation recovered")
            if mode=="leaf":mode="step"
            paths=[(eid,direction) for pr in premises for eid,direction in pr.get("path",[])]
            parts["paths"]=[]
            for eid,direction in paths:
                edge=graph.edges.get(eid)
                if edge is None:
                    obs["preservation_evidence"]=data_gap("edge "+eid,base+".premises");continue
                parts["paths"].append({"edge":eid,"direction":direction,"record":deepcopy(edge)})
                obs["field_transport"]=adapter_gap("per-step context/reach discharge","edges."+eid)
                obs["selected_structure"]=adapter_gap("selected-structure correspondence","edges."+eid)
                obs["preservation_evidence"]=adapter_gap("conditional preservation proof","edges."+eid)
                if kind_here==K.PREDICATE:
                    obs["predicate_rewrite"]=adapter_gap("composed predicate rewrite",base+".premises","edges."+eid)
            runtime_licensed=identifier in runtime_clean
            if not runtime_licensed:
                obs["current_binding"]=data_gap("currently licensed conclusion",base)
            else:
                obs["current_binding"]=reified(base+".premises",reason="current full checker admission; child receipt bindings recorded separately")
        complete=runtime_licensed and all(o["status"]=="REIFIED" for o in obs.values()) and all(c["complete"] for c in children)
        # Evaluate the emitted conditional transport profile independently of
        # full proof-tree reconstruction. A leaf has no transport step.
        covered = None
        if inference is not None:
            try:
                covered = C.audit_inference(graph, identifier)[0] and obs["composition"]["status"] == "REIFIED"
            except (KeyError, ValueError, TypeError):
                covered = None
        lost = ([] if inference is None or covered is True else
                [kind_here] if covered is False and kind_here in K.CLAIM_KINDS else None)
        return {"id":identifier,"kind":kind_here,"node_kind":mode,"runtime_licensed":runtime_licensed,
                "complete":complete,"obligations":obs,"children":children,"receipts":receipts,
                "flags":flags,"parts":parts,"lost":{"label":"unlicensed observations under available discharge",
                "vocabulary":[kind_here] if inference else [],"values":lost,
                "status":"NO_TRANSPORT_STEP" if inference is None else "COMPUTED" if covered is not None else "ADAPTER_GAP",
                "scope":"conditional runtime gate profile at the stated kind; independent of full tree completeness", "profile_covered":covered}}
    tree=build(node,set())
    if kind is not None and tree["kind"]!=kind: raise ValueError("requested kind does not match conclusion")
    totals=Counter();gaps=Counter()
    def visit(t):
        for o in t["obligations"].values():
            totals[o["status"]]+=1
            if o["status"]=="DATA_GAP": gaps[o["missing"]]+=1
        for c in t["children"]:visit(c)
    visit(tree)
    return {"schema":"grand-portage-explain/v1","authority":"DERIVED_READ_MODEL_ONLY","graph_effect":"NONE",
            "graph_format":graph.graph_format,"kernel_epoch":graph.kernel_epoch,"tree":tree,
            "totals":dict(totals),"data_gaps":dict(gaps),"loaded_state_issue":load_issue}

def render(report):
    lines=["Licence read model (no authority)"]
    def walk(t,depth):
        pad="  "*depth
        lines.append(pad+t["id"]+" ["+t["node_kind"]+"] "+("RECONSTRUCTED" if t["complete"] else "INCOMPLETE"))
        for name,o in t["obligations"].items():
            lines.append(pad+"  "+name+": "+o["status"]+" "+(o["missing"] or o["interpretation"] or o["reason"] or ", ".join(o["fields"])))
        if "lost" in t:lines.append(pad+"  "+t["lost"]["label"]+": "+(", ".join(t["lost"]["values"]) if t["lost"]["values"] is not None else "UNKNOWN"))
        for c in t["children"]:walk(c,depth+1)
    walk(report["tree"],0)
    return "\n".join(lines)+"\n"
