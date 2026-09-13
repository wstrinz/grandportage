"""Read-only IR-v2 projection attempt; never authority and never a graph writer.

PROJECTABLE means a diagnostic data skeleton, not a constructed Lean proof.
Missing semantics/discharge remains named; no profile is minted from a reach tag.
"""
from collections import Counter
from copy import deepcopy
import hashlib
import json

from . import check as C
from . import field as E
from . import groebner as G
from . import kernel as K
from . import provenance as P

SCHEMA = "grand-portage-ir-v2-projection/v0"
AUTHORITY = "DERIVED_READ_MODEL_ONLY"
LEAN_TYPES = {name: "GrandPortage.IR." + name for name in
              ("Claim", "Context", "Statement", "Step", "Evidence", "Binding", "Licence", "lost", "sound")}
LEAN_KINDS = {"EMPTY": "empty", "NONEMPTY": "nonempty", "PREDICATE": "predicate", "IDENTITY": "identity"}
PROFILE_CANDIDATES = {"UNIT_IDEAL_CERT": "unit", "ORDERED_SOS_CERT": "ordered"}
# References are executable obligations, not a claim that a Boolean proves them.
GATES = {
    "EMPTY": ["check.effective_certificate", "check._field_transport_decision"],
    "NONEMPTY": ["check._field_transport_decision", "check.check_unexhibited_witness"],
    "PREDICATE": ["check._field_transport_decision", "check.effective_selected_embedding_identity",
                  "check.condition_expressible_at", "check.structured_condition_closed",
                  "check.effective_geometric_closure", "check.effective_point_surjective",
                  "check.pullback_condition_across_edge", "check.rewrite_condition_across_equivalence"],
    "IDENTITY": ["check.effective_origin", "check.effective_ring_iso", "check.effective_exact_contraction",
                 "check.check_coefficients_in_base", "check.check_integral", "check.check_inexpressible"],
}


def canonical(value):
    return json.dumps(value, sort_keys=True, separators=(",", ":"), ensure_ascii=True)


def fingerprint(value):
    return "sha256:" + hashlib.sha256(canonical(value).encode("ascii")).hexdigest()


def row(identifier, candidate, missing=(), flags=()):
    return {"id": identifier, "status": "UNPROJECTABLE" if missing else "PROJECTABLE",
            "missing": sorted(set(missing)), "flags": sorted(set(flags)), "candidate": candidate}


def expression(text, variables, characteristic):
    """Bounded integer Expr encoding. Rational constants are explicit gaps.
    Normalization is the existing Python parser, not verified by this IR.
    """
    polynomial = G.parse_polynomial(text, variables, characteristic)
    total = 0
    result = {"zero": []}
    for powers, coefficient in sorted(polynomial.terms.items()):
        if getattr(coefficient, "denominator", 1) != 1:
            raise ValueError("rational_expression_adapter")
        coefficient = int(coefficient)
        total += abs(coefficient) + sum(powers) + 1
        # Each constructor contributes both a dictionary and a list level.
        # Leave room for the surrounding report below JSON's recursion limit.
        if total > 128:
            raise ValueError("expression_adapter_budget")
        scalar = {"zero": []}
        for _ in range(abs(coefficient)):
            scalar = {"add": [scalar, {"one": []}]}
        if coefficient < 0:
            scalar = {"neg": [scalar]}
        for index, power in enumerate(powers):
            for _ in range(power):
                scalar = {"mul": [scalar, {"var": index}]}
        result = {"add": [result, scalar]}
    return result


def context(mid, model):
    missing = ["context." + name for name in ("about", "point_universe", "ring_vars", "generators")
               if name not in model]
    try:
        compute = E.model_compute_in(model)
    except E.FieldError:
        compute = None
    if compute is None:
        missing.append("context.coefficient_domain")
    if not E.is_field_atom(model.get("about")):
        missing.append("context.about")
    if model.get("point_universe") not in E.POINT_UNIVERSES:
        missing.append("context.point_universe")
    if type(model.get("characteristic")) is not int:
        missing.append("context.characteristic")
    candidate = {"lean_type": LEAN_TYPES["Context"], "model": mid,
                 "about": model.get("about"), "coefficient_domain": compute,
                 "point_universe": model.get("point_universe"),
                 "selected": deepcopy(model.get("embedding")), "ring_variables": model.get("ring_vars"),
                 "characteristic": model.get("characteristic")}
    if not missing:
        try:
            candidate["equations"] = [expression(x, model["ring_vars"], model["characteristic"])
                                      for x in model["generators"]]
            candidate["guards"] = [expression(x, model["ring_vars"], model["characteristic"])
                                   for x in model.get("open_conditions", [])]
        except (ValueError, TypeError, G.CertificateError) as exc:
            missing.append("context.expression_interpretation:" + type(exc).__name__)
    return row(mid, candidate, missing)


def claim(cid, value, models):
    mid = value.get("model")
    missing = list(models[mid]["missing"]) if mid in models else ["claim.algebraic_model_context"]
    kind = value.get("kind")
    candidate = {"lean_type": LEAN_TYPES["Claim"], "model": mid, "kind": kind,
                 "context_ref": mid, "statement": None, "vocabulary": None}
    if kind not in LEAN_KINDS:
        missing.append("claim.kind_adapter:" + str(kind))
    elif kind == K.IDENTITY:
        candidate["vocabulary"] = {"family": "coordinate_ring", "model": mid,
                                   "origin": value.get("identity_origin")}
        if value.get("identity_origin") not in (K.AMBIENT, K.DERIVED):
            missing.append("claim.identity_origin")
        if value.get("lhs") is None or value.get("rhs") is None:
            missing.append("claim.identity_expression")
        elif mid in models and not models[mid]["missing"]:
            ctx = models[mid]["candidate"]
            try:
                candidate["statement"] = {"identity": [expression(value["lhs"], ctx["ring_variables"], ctx["characteristic"]),
                                                       expression(value["rhs"], ctx["ring_variables"], ctx["characteristic"])]}
            except (TypeError, ValueError, G.CertificateError):
                missing.append("claim.identity_expression")
    elif kind == K.PREDICATE:
        candidate["vocabulary"] = {"family": "structured_predicate", "model": mid}
        if value.get("condition") is None:
            missing.append("claim.predicate_interpretation")
        else:
            candidate["statement"] = {"predicate": fingerprint(value["condition"]),
                                      "retained_condition": deepcopy(value["condition"])}
    else:
        candidate["statement"] = {kind.lower(): []}
        candidate["vocabulary"] = {"family": "field_points", "model": mid,
                                   "chosen_witness": kind == K.NONEMPTY and value.get("witness_point") is not None}
    return row(cid, candidate, missing, ["VOCABULARY_INDEX_FROM_EXISTING_FIELDS"])


def step(eid, value):
    kind = value.get("type")
    missing = []
    if kind not in K.TRANSPORT or kind == K.UNTYPED:
        missing.append("step.relation_class")
    for key in ("src", "dst", "map_kind"):
        if not value.get(key):
            missing.append("step." + key)
    entries = []
    if kind in K.TRANSPORT:
        for direction, cells in K.TRANSPORT[kind].items():
            for claim_kind in LEAN_KINDS:
                entries.append({"kind": claim_kind, "direction": direction,
                                "kernel_rule": cells[claim_kind], "gates": GATES[claim_kind],
                                "discharge": "UNKNOWN", "justification": "NOT_PROJECTED"})
    return row(eid, {"lean_type": LEAN_TYPES["Step"], "source": value.get("src"),
                    "target": value.get("dst"), "relation_class": kind,
                    "map_kind": value.get("map_kind"), "profile": entries,
                    "profile_semantics": "kernel rule conjoined with referenced contextual gate functions"},
               missing, ["CONDITIONAL_PROFILE_FROM_CODE", "NO_PRESERVATION_PROOF_PROJECTED"])


def project(graph, source=None):
    """Consume a loaded graph without modifying it or re-running a verifier."""
    snapshot = {key: deepcopy(getattr(graph, key, {})) for key in
                ("models", "claims", "edges", "inferences", "verdicts", "evidence", "families", "partitions")}
    snapshot["graph_format"] = graph.graph_format
    snapshot["kernel_epoch"] = graph.kernel_epoch
    state = fingerprint(snapshot)
    models = {mid: context(mid, m) for mid, m in sorted(graph.models.items())}
    claims = {cid: claim(cid, c, models) for cid, c in sorted(graph.claims.items())}
    steps = {eid: step(eid, e) for eid, e in sorted(graph.edges.items())}
    evidence, bindings = {}, {}
    for cid, c in sorted(graph.claims.items()):
        tag = c.get("certificate")
        if tag:
            evidence["certificate:" + cid] = row("certificate:" + cid,
                {"lean_type": LEAN_TYPES["Evidence"], "claim": cid, "tag": tag,
                 "candidate_interpreter": PROFILE_CANDIDATES.get(tag), "requirement_profile": None},
                ["evidence.actual_requirement_discharge"], ["PROFILE_FROM_TAG"])
    for rid, receipt in sorted(graph.verdicts.items()):
        missing = ["evidence.actual_requirement_discharge"]
        is_current, why = P.current_verdict(graph, receipt)
        is_current = bool(is_current and receipt.get("current"))
        active = is_current and rid in graph.authority_receipts
        if not active:
            missing.append("binding.current_receipt")
        owner = receipt.get("of")
        c = graph.claims.get(owner, {})
        e = graph.edges.get(owner, {})
        endpoints = [c["model"]] if c.get("model") else [x for x in (e.get("src"), e.get("dst")) if x]
        if not endpoints:
            missing.append("binding.endpoints")
        backend = P.decode_backend_provenance(receipt.get("backend"), current_only=False) or {}
        runs = backend.get("executions", [])
        binding_missing = [x for x in missing if x.startswith("binding.")]
        for index, run in enumerate(runs):
            # A process-level banner is not a per-execution binary identity.
            if not run.get("binary_identity"):
                binding_missing.append("binding.per_execution_binary_identity")
            if not run.get("completion_identity"):
                binding_missing.append("binding.per_execution_completion_identity")
        if not receipt.get("input_fingerprint"):
            binding_missing.append("binding.payload_identity")
        bindings[rid] = row(rid, {"lean_type": LEAN_TYPES["Binding"], "endpoints": endpoints,
            "payload_identity": receipt.get("input_fingerprint"), "graph_state": state,
            "executions": deepcopy(runs), "current_under_loaded_state": active, "freshness_reason": why},
            binding_missing, ["GRAPH_STATE_CONTENT_SNAPSHOT"])
        flags = ["PROFILE_FROM_TAG"] if c.get("certificate") else []
        evidence[rid] = row(rid, {"lean_type": LEAN_TYPES["Evidence"], "artifact": receipt.get("artifact"),
            "interpreter": receipt.get("verifier"), "receipt": rid, "binding_ref": rid,
            "requirement_profile": None, "current_under_loaded_state": active},
            missing + binding_missing, flags)
    for eid, e in sorted(graph.evidence.items()):
        evidence["evidence:" + eid] = row("evidence:" + eid,
            {"lean_type": LEAN_TYPES["Evidence"], "method": e.get("method"), "for": e.get("for")},
            ["evidence.interpreter", "evidence.actual_requirement_discharge", "binding.replay_receipt"])
    licences = {}
    clean = set(C.clean_inferences(graph, C.run(graph)))
    for iid, inference in sorted(graph.inferences.items()):
        if inference.get("superseded_by"):
            continue
        licensed, trace = C.audit_inference(graph, iid)
        missing, leaves = [], []
        for premise in inference.get("premises", []):
            cid = premise.get("claim")
            if cid not in claims:
                missing.append("licence.premise_claim")
                continue
            missing.extend(claims[cid]["missing"])
            receipts = [rid for rid, r in graph.verdicts.items() if r.get("of") == cid]
            if not receipts:
                missing.append("licence.leaf_receipt")
            else:
                if not any(not evidence[rid]["missing"] for rid in receipts):
                    missing.append("licence.leaf_interpreter_or_binding")
            for edge_id, _direction in premise.get("path", []):
                missing.extend(steps[edge_id]["missing"])
            leaves.append({"claim": cid, "path": deepcopy(premise.get("path", [])), "receipts": receipts})
        if inference.get("via_partition") or inference.get("family_bridges"):
            missing.append("licence.nonlocal_composition_adapter")
        if trace:
            missing.append("licence.step_justification_and_discharge")
        if not licensed:
            missing.append("runtime.transport_refused")
        if iid not in clean:
            missing.append("runtime.full_check_refused")
        licences[iid] = row(iid, {"lean_type": LEAN_TYPES["Licence"], "runtime_path_licensed": licensed, "runtime_licensed": iid in clean,
            "conclusion_at": inference.get("concludes_at"), "premises": leaves,
            "trace": [list(t) for t in trace]}, missing)
    categories = {"models": models, "claims": claims, "steps": steps, "evidence": evidence,
                  "bindings": bindings, "licences": licences}
    counts = {name: dict(Counter(r["status"] for r in rows.values())) for name, rows in categories.items()}
    reasons = Counter(reason for rows in categories.values() for r in rows.values() for reason in r["missing"])
    certificate_rows = [r for r in evidence.values() if "PROFILE_FROM_TAG" in r["flags"]]
    # Denominator includes all tagged certificate declarations/receipts; other
    # verdicts and operational evidence are reported separately, never hidden.
    tagged_total = sum(bool(c.get("certificate")) for c in graph.claims.values()) + sum(
        bool(graph.claims.get(r.get("of"), {}).get("certificate")) for r in graph.verdicts.values())
    missing_context = sum(bool(r["missing"]) for r in models.values())
    return {"schema": SCHEMA, "authority": AUTHORITY, "graph_effect": "NONE", "source": source,
            "source_graph_format": graph.graph_format, "strict_format8_input": graph.graph_format == 8,
            "state_fingerprint": state, "counts": counts, "reason_counts": dict(sorted(reasons.items())),
            "profile_from_tag": {"count": len(certificate_rows), "denominator": tagged_total,
                                 "rate": len(certificate_rows)/tagged_total if tagged_total else None},
            "missing_model_context_fraction": missing_context/len(models) if models else None,
            "stop_for_missing_context": bool(models) and missing_context/len(models) > 0.1,
            "categories": categories}
