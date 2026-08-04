"""Deterministic fan-out merge assay for the consolidation release.

The logs are intentionally generated from one shared prefix and then folded in
both orders.  This is an assay, not an authority producer: its JSON report says
what the merge/read layers observed and cannot be imported as graph evidence.
"""

import argparse
import copy
import json
from pathlib import Path
import tempfile

from grandportage import backend as B
from grandportage import check as C
from grandportage import evidence as EV
from grandportage import format as F
from grandportage import groebner as G
from grandportage import kernel as K
from grandportage import store as S
from grandportage import verify as V


SCHEMA = "grand-portage-merge-assay/v1"


def _write(path, events):
    path.write_text(
        "".join(json.dumps(event, sort_keys=True) + "\n" for event in events),
        encoding="utf-8",
    )
    return str(path)


def _model(identifier, what, generators):
    return {
        "ev": "model",
        "id": identifier,
        "what": what,
        "characteristic": 0,
        "coefficient_domain": "Q",
        "point_universe": "ALGEBRAIC_CLOSURE",
        "ring_vars": ["x", "y"],
        "generators": list(generators),
        "open_conditions": ["x"],
    }


def affine_signature(model):
    """A conservative exact-syntax signature used only to expose alias debt."""
    variables = model.get("ring_vars") or []
    characteristic = model.get("characteristic", 0)
    generators = sorted(
        G.canonical_polynomial(value, variables, characteristic)
        for value in model.get("generators") or []
    )
    guards = sorted(
        G.canonical_polynomial(value, variables, characteristic)
        for value in model.get("open_conditions") or []
    )
    return EV.fingerprint({
        "characteristic": characteristic,
        "coefficient_domain": model.get("coefficient_domain"),
        "point_universe": model.get("point_universe"),
        "ring_vars": variables,
        "generators": generators,
        "open_conditions": guards,
        "chart": model.get("chart"),
    })


def _execution():
    trace = [{
        "semantic_input_fingerprint": B.semantic_fingerprint("merge-assay", []),
        "program_fingerprint": B.text_fingerprint("merge assay program"),
        "stdout_fingerprint": B.text_fingerprint("merge assay output"),
        "stderr_fingerprint": B.text_fingerprint(""),
        "artifact_fingerprint": B.semantic_fingerprint("merge-artifact", []),
        "returncode": 0,
        "aborted": False,
    }]
    return {
        "schema": 2,
        "contract": B.SINGULAR_CONTRACT,
        "implementation": B.SINGULAR_IMPLEMENTATION,
        "implementation_version": B.SINGULAR_IMPLEMENTATION_VERSION,
        "protocol_version": B.BACKEND_PROTOCOL_VERSION,
        "binary_version": "Singular merge-assay fixture",
        "executions": trace,
        "trace_fingerprint": B.semantic_fingerprint(
            "backend_execution_trace", trace),
    }


def _merge_both(a, b):
    forward, conflicts = S.merge_report([a, b])
    reverse, reverse_conflicts = S.merge_report([b, a])
    return forward, conflicts, reverse, reverse_conflicts


def run_assay(directory):
    directory = Path(directory)
    directory.mkdir(parents=True, exist_ok=True)
    meta = F.meta_event()

    seed = _model("SEED", "shared prefix", ["x*y-1"])
    alias_a = _write(directory / "alias-a.jsonl", [
        meta, seed, _model("FIBER-A", "agent A's name", ["x+y"]),
    ])
    alias_b = _write(directory / "alias-b.jsonl", [
        meta, seed, _model("FIBER-B", "agent B's name", ["y+x"]),
    ])
    alias_graph, alias_conflicts, alias_reverse, alias_reverse_conflicts = (
        _merge_both(alias_a, alias_b))
    by_signature = {}
    for identifier, model in alias_graph.models.items():
        by_signature.setdefault(affine_signature(model), []).append(identifier)
    duplicate_groups = [sorted(ids) for ids in by_signature.values()
                        if len(ids) > 1]

    normalized_a = _write(directory / "normalized-a.jsonl", [
        meta, seed, _model("NORMALIZED", "one object", ["x+y"]),
    ])
    normalized_b = _write(directory / "normalized-b.jsonl", [
        meta, seed, _model("NORMALIZED", "one object", ["y+x"]),
    ])
    _, normalized_conflicts = S.merge_report([normalized_a, normalized_b])
    normalized_equivalent = (
        G.canonical_polynomial("x+y", ["x", "y"])
        == G.canonical_polynomial("y+x", ["x", "y"])
    )

    old = _model("OLD", "the original object", ["x"])
    stale_claim = {
        "ev": "claim", "id": "USES-OLD", "model": "OLD",
        "kind": K.PREDICATE, "statement": "a statement at the old model",
        "established_by": "CITED", "ladder": "claimed",
    }
    replacement = _model("NEW", "the corrected object", ["x+y"])
    replacement.update({
        "supersedes": "OLD", "discharge_kind": K.RESTATE,
    })
    supersession_a = _write(directory / "supersession-a.jsonl", [
        meta, old, stale_claim,
    ])
    supersession_b = _write(directory / "supersession-b.jsonl", [
        meta, old, replacement,
    ])
    supersession_graph, supersession_conflicts, supersession_reverse, (
        supersession_reverse_conflicts) = _merge_both(
            supersession_a, supersession_b)
    stale_model_findings = [
        finding.as_dict() for finding in C.run(supersession_graph)
        if finding.rule == C.R_STALE_MODEL
    ]

    identity_model = _model("IDENTITY-MODEL", "identity assay", ["x"])
    identity_claim = {
        "ev": "claim", "id": "IDENTITY-CLAIM", "model": "IDENTITY-MODEL",
        "kind": K.IDENTITY, "statement": "x vanishes", "lhs": "x",
        "rhs": "0", "ring_vars": ["x", "y"],
        "identity_origin": K.DERIVED,
        "established_by": "RAN", "ladder": "exact-checked",
    }
    prefix_events = [meta, identity_model, identity_claim]
    prefix = S.Graph().apply_all(
        [(event, "<prefix>", index)
         for index, event in enumerate(prefix_events)]).validate()
    current = V._verdict_event(
        prefix, "claim", "IDENTITY-CLAIM", "VERIFIED_DERIVED",
        "x reduces to zero modulo (x)", execution=_execution())
    stale = copy.deepcopy(current)
    stale["id"] = current["id"] + ".old-epoch"
    stale["kernel_epoch"] = F.KERNEL_EPOCH - 1
    verdict_a = _write(directory / "verdict-a.jsonl", prefix_events + [stale])
    verdict_b = _write(directory / "verdict-b.jsonl", prefix_events + [current])
    verdict_graph, verdict_conflicts, verdict_reverse, verdict_reverse_conflicts = (
        _merge_both(verdict_a, verdict_b))
    verdict_states = {
        identifier: {
            "current": record["current"],
            "stale_reason": record["stale_reason"],
        }
        for identifier, record in sorted(verdict_graph.verdicts.items())
    }

    assert not alias_conflicts and not alias_reverse_conflicts
    assert set(alias_graph.models) == set(alias_reverse.models)
    assert not supersession_conflicts and not supersession_reverse_conflicts
    assert set(supersession_graph.models) == set(supersession_reverse.models)
    assert not verdict_conflicts and not verdict_reverse_conflicts
    assert verdict_states == {
        identifier: {
            "current": record["current"],
            "stale_reason": record["stale_reason"],
        }
        for identifier, record in sorted(verdict_reverse.verdicts.items())
    }

    return {
        "schema": SCHEMA,
        "authority": "DERIVED_ASSAY_ONLY",
        "cases": {
            "same_object_different_ids": {
                "merge": "COMPOSES",
                "duplicate_affine_signatures": duplicate_groups,
                "finding": "UNRESOLVED_ALIAS" if duplicate_groups else None,
            },
            "same_id_equivalent_normalization": {
                "merge": "REFUSES",
                "exactly_equivalent": normalized_equivalent,
                "conflict_fields": normalized_conflicts[0]["fields"],
            },
            "superseded_object_consumed_elsewhere": {
                "merge": "COMPOSES",
                "stale_model_findings": stale_model_findings,
            },
            "stale_and_current_verdicts": {
                "merge": "COMPOSES",
                "verdicts": verdict_states,
                "active_identity_verdict": verdict_graph.claims[
                    "IDENTITY-CLAIM"].get("identity_verdict"),
            },
        },
    }


def main(argv=None):
    parser = argparse.ArgumentParser()
    parser.add_argument("--output")
    parser.add_argument("--workdir")
    args = parser.parse_args(argv)
    if args.workdir:
        report = run_assay(args.workdir)
    else:
        with tempfile.TemporaryDirectory(prefix="gp-merge-assay-") as temp:
            report = run_assay(temp)
    payload = json.dumps(report, sort_keys=True, indent=2) + "\n"
    if args.output:
        Path(args.output).write_text(payload, encoding="utf-8")
    else:
        print(payload, end="")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
