"""Bounded zero-route and legacy partition receipt diagnostics.

The legacy partition branch is deliberately not a native epoch-1 admission.
Negative partition outcomes record the legacy consumer's observed ACCEPT
against a fixed expected REFUSE and are marked known differences in routes.
"""
from grandportage import check as C
from grandportage import format as F
from grandportage import provenance as P
from grandportage import store as S
from grandportage import verify as V


def _ordered_certificate(d):
    return {
        "method": "rational_sos_cofactor_v1",
        "ring_vars": ["x"],
        "generators": ["x^2+1"],
        "squares": d["squares"],
        "cofactors": d["cofactors"],
    }


def _zero_step(case):
    d = case["inputs"]
    if (d["field"] != "R" or d["generators"] != ["x^2+1"]
            or d["certificate"] != "ORDERED_SOS_CERT"
            or d["squares"] != ["x"] or d["cofactors"] != ["-1"]
            or d["route_steps"] != []
            or d["attempted_authority"] != "EMPTY premise from zero-step audit alone"):
        raise ValueError("Unknown zero-step receipt interpretation")
    graph = S.Graph()
    graph.apply(F.meta_event())
    graph.apply(dict(ev="model", id="M", coefficient_domain="Q",
                     characteristic=0, point_universe="BASE", about="R",
                     compute_in="Q", ring_vars=["x"], generators=d["generators"]))
    graph.apply(dict(ev="claim", id="E", model="M", kind="EMPTY",
                     statement="no ordered-field zero", certificate=d["certificate"],
                     scope="R"))
    graph.apply(dict(ev="inference", id="ZERO", claim="E", path=d["route_steps"],
                     asserted="carry the emptiness premise"))
    graph.validate()
    before = C.audit_inference(graph, "ZERO")
    before_verdict = graph.claims["E"].get("certificate_verdict")
    before_reach = graph.claims["E"].get("certificate_reach")
    if before != (True, []) or before_verdict is not None or before_reach is not None:
        raise ValueError("Zero-step no-receipt control drifted")
    verdict, why, rep = V.ordered_sos(graph, "E", _ordered_certificate(d))
    if verdict != V.CERT_VERIFIED:
        raise ValueError("Positive ordered receipt did not replay")
    graph.apply(V._verdict_event(graph, "certificate", "E", verdict, why, rep,
                                 execution=P.native_execution_provenance()))
    graph.validate()
    after = C.audit_inference(graph, "ZERO")
    after_reach = graph.claims["E"].get("certificate_reach")
    if after != (True, []) or after_reach != {"kind": "ORDERED"}:
        raise ValueError("Positive receipt control lost ordered reach")
    return {
        "observed_verdict": "REFUSE",
        "reason": "The zero-step audit is true with no current certificate verdict or reach; only separate exact SOS replay earns ORDERED reach.",
        "zero_step_before_receipt": {"allowed": before[0], "trace": before[1],
                                     "certificate_verdict": before_verdict,
                                     "certificate_reach": before_reach},
        "positive_receipt_control": {"verdict": verdict, "reach": after_reach,
                                     "zero_step_still_allowed": after[0]},
        "native_held_claim_verdict": None,
        "authority_observation": "route_audit_vs_verifier_receipt",
        "external_execution": False,
    }


def _legacy_partition(case, route):
    d = case["inputs"]
    if (d["source_equations"] != ["x^2+1"]
            or d["branches"] != ["B1", "B2"]
            or d["identical_loci_cover"] is not True
            or d["cover_projection_supplied"] is not True
            or d["ordered_sos"] != {"squares": ["x"],
                                     "cofactors": ["-1"],
                                     "certificate": "ORDERED_SOS_CERT"}
            or d["field"] not in ("R", "C")
            or not isinstance(d["branch_receipts_recorded"], bool)):
        raise ValueError("Unknown legacy partition interpretation")
    native = S.Graph()
    native.apply(F.meta_event())
    try:
        native.apply(dict(ev="inference", id="NATIVE", via_partition="P",
                          premises=[{"claim": "E"}], concludes_kind="EMPTY",
                          asserted="native boundary control"))
    except S.GraphError as exc:
        schema_refusal = str(exc)
        if "unknown field" not in schema_refusal or "via_partition" not in schema_refusal:
            raise
    else:
        raise ValueError("Current epoch admitted the legacy partition field")
    graph = S.Graph()
    for mid in ("M", "B1", "B2"):
        graph.apply(dict(ev="model", id=mid, about=d["field"], compute_in="Q",
                         coefficient_domain="Q", characteristic=0,
                         point_universe="BASE", ring_vars=["x"],
                         generators=d["source_equations"]))
    graph.apply(dict(ev="claim", id="COVER", model="M", kind="PREDICATE",
                     statement="two identical copies cover the parent"))
    graph.apply(dict(ev="partition", id="P", parent="M", branches=d["branches"],
                     exhaustive="COVER", why="identical-locus cover isolates premise interpretation"))
    receipt_verdicts = []
    for bid in d["branches"]:
        cid = "E" + bid
        graph.apply(dict(ev="claim", id=cid, model=bid, kind="EMPTY",
                         statement="no ordered-field zero", certificate="ORDERED_SOS_CERT",
                         scope="ANY_ORDERED"))
        if d["branch_receipts_recorded"]:
            verdict, why, rep = V.ordered_sos(graph, cid, _ordered_certificate(d["ordered_sos"]))
            if verdict != V.CERT_VERIFIED:
                raise ValueError("Ordered branch receipt did not replay")
            graph.apply(V._verdict_event(graph, "certificate", cid, verdict, why, rep,
                                         execution=P.native_execution_provenance()))
            receipt_verdicts.append(verdict)
    graph.apply(dict(ev="inference", id="JOIN", via_partition="P",
                     premises=[{"claim": x} for x in ("EB1", "EB2", "COVER")],
                     concludes_kind="EMPTY", asserted="the parent has no points"))
    graph.validate()
    # This isolates the consumer as the retained _split helper did. It is not
    # a minted, persistent or backend-produced exhaustiveness receipt.
    graph.partitions["P"]["exhaustive_verdict"] = "VERIFIED"
    allowed, trace = C.audit_inference(graph, "JOIN")
    if not allowed or len(trace) != 1 or trace[0][1] != "COVERS":
        raise ValueError("Legacy partition consumer did not reproduce acceptance")
    if route["layer"] == "legacy_partition_ordered_R_positive":
        if d["field"] != "R" or not d["branch_receipts_recorded"]:
            raise ValueError("Positive ordered control changed")
    elif route["layer"] == "legacy_partition_ordered_C_gap":
        if d["field"] != "C" or not d["branch_receipts_recorded"]:
            raise ValueError("Complex reach control changed")
    elif route["layer"] == "legacy_partition_missing_receipts_gap":
        if d["field"] != "R" or d["branch_receipts_recorded"]:
            raise ValueError("Missing receipt control changed")
    else:
        raise ValueError("Unknown legacy partition layer")
    return {
        "observed_verdict": "ACCEPT",
        "reason": "The isolated legacy partition consumer accepts the supplied true cover and both named branch premises.",
        "legacy_consumer_allowed": allowed,
        "legacy_trace": trace,
        "native_sos_receipt_verdicts": receipt_verdicts,
        "branch_receipts_recorded": d["branch_receipts_recorded"],
        "target_field": d["field"],
        "complex_counterpoint": "i solves x^2+1=0" if d["field"] == "C" else None,
        "cover_projection_supplied_not_native_receipt": True,
        "current_epoch_schema_refusal": schema_refusal,
        "native_held_claim_verdict": None,
        "external_execution": False,
    }


def probe(case, route):
    control = case["inputs"]["control"]
    if control == "zero_step_vs_receipt":
        return _zero_step(case)
    if control == "legacy_partition_ordered_receipts":
        return _legacy_partition(case, route)
    raise ValueError("Unknown receipt/partition control")
