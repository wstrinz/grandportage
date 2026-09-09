"""Read-only preflight observations; never rewrites the campaign's fixtures.

Run from the GP root: python review/v0.32-preflight/probe.py CAMPAIGN_ROOT
Use --live to run the two frozen D2 witness inputs three times through GP's CAS
boundary. This is an observation harness, not the future release acceptance gate.
"""
import argparse
import copy
import hashlib
import json
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[2]))
from grandportage import check as C, format as F, kernel as K, store as S


def fold(events):
    graph = S.Graph()
    graph.apply_all([(event, "<preflight>", n)
                     for n, event in enumerate([F.meta_event()] + events, 1)])
    return graph.validate()


def observe(events):
    try:
        graph = fold(events)
        findings = C.run(graph)
        return {"fold": "OK", "groups": len(graph.groups),
                "clean_inferences": C.clean_inferences(graph, findings),
                "findings": [{"id": f.fid, "severity": f.severity}
                             for f in findings]}
    except Exception as exc:
        return {"fold": type(exc).__name__, "detail": str(exc)}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("campaign", type=Path)
    parser.add_argument("--live", action="store_true")
    args = parser.parse_args()
    root = args.campaign
    paths = [
        "fixtures/D1-inference-on-family-claim/input.json",
        "fixtures/D3-inert-disposition/before.json",
        "fixtures/D3-inert-disposition/after.json",
    ]
    paths += [str(p.relative_to(root)).replace("\\", "/") for p in sorted(
        (root / "followup/field-class-probe").glob("*.json"))]
    paths += [str(p.relative_to(root)).replace("\\", "/") for p in sorted(
        (root / "transports").glob("*.json"))]
    paths += [str(p.relative_to(root)).replace("\\", "/") for p in sorted(
        (root / "misuse").glob("*.json"))]
    results = {}
    for name in paths:
        data = (root / name).read_bytes()
        results[name] = {"sha256_lf": hashlib.sha256(
            data.replace(b"\r\n", b"\n")).hexdigest(),
            **observe(json.loads(data))}
    ledger_path = root / "fixtures/ledger/graph.jsonl"
    ledger = S.load(str(ledger_path))
    findings = C.run(ledger)
    results["ledger"] = {
        "sha256_lf": hashlib.sha256(ledger_path.read_bytes().replace(
            b"\r\n", b"\n")).hexdigest(),
        "claims": len(ledger.claims),
        "live_claims": sum(not c.get("superseded_by")
                           for c in ledger.claims.values()),
        "findings": [{"id": f.fid, "severity": f.severity} for f in findings],
    }
    # Mutations are in memory; their sources remain byte-for-byte untouched.
    base = json.loads((root / "followup/field-class-probe/B2-C-to-R-legacy.json").read_bytes())
    variants = {}
    for kind in (K.BASE_EXTENSION, K.NECESSARY_CONDITION, K.RESTRICTION):
        events = copy.deepcopy(base)
        for event in events:
            if event.get("ev") == "edge":
                event["type"] = kind
        variants[kind] = observe(events)
    results["legacy_C_to_R_edge_mutations"] = variants
    results["model_change_classification"] = {
        field: K.classify_supersession({field: before}, {field: after}, "model")
        for field, before, after in [
            ("field", "Q", "R"), ("point_universe", "BASE", "ALGEBRAIC_CLOSURE"),
            ("characteristic", 0, 2), ("open_conditions", [], ["x"]),
            ("embedding", None, {"kind": "REAL"}),
        ]}
    old = {"ev": "model", "id": "OLD", "what": "same scheme",
           "characteristic": 0, "coefficient_domain": "Q",
           "point_universe": "BASE", "ring_vars": ["x"],
           "generators": ["x*x+1"]}
    new = dict(old, id="NEW", point_universe="ALGEBRAIC_CLOSURE",
               supersedes="OLD", discharge_kind="AMEND")
    results["native_universe_change_as_AMEND"] = observe([old, new])
    if args.live:
        from grandportage import cas
        results["singular"] = cas._singular_binary_version(timeout=20)
        runs = []
        for repeat in range(1, 4):
            for name in ("pass-96vars.json", "fail-97vars.json"):
                events = json.loads((root / "fixtures/D2-witness-substitution-scaling" / name).read_bytes())
                model = next(e for e in events if e.get("ev") == "model")
                claim = next(e for e in events if e.get("ev") == "claim")
                try:
                    ok, diagnostic = cas.check_witness(
                        model["ring_vars"], model["generators"],
                        claim["witness_point"], characteristic=0, timeout=30)
                    outcome = {"verified": ok, "failed": diagnostic["failed"]}
                except Exception as exc:
                    outcome = {"error": type(exc).__name__, "detail": str(exc)}
                runs.append({"repeat": repeat, "input": name, **outcome})
        results["D2_live_runs"] = runs
    print(json.dumps(results, indent=2, ensure_ascii=True))


if __name__ == "__main__":
    main()
