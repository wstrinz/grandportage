"""Bound-case integration for frozen guard and exact historical Cramer probes."""
import hashlib
import json
from functools import lru_cache
from pathlib import Path
ROOT = Path(__file__).resolve().parents[1]

@lru_cache(maxsize=2)
def run_family(family):
    if family == "guard":
        from guard_snapshot_probes import run
        report = run()
        if not report["passed"]:
            raise ValueError("Frozen guard replay failed its layer checks")
        return report
    from cramer_exponent_probes import run
    return run()

def probe(case, route):
    family = route["family"]
    folder = "guard-case-candidates" if family == "guard" else "cramer-case-candidates"
    raw = (ROOT/"corpus/must"/(case["id"]+".json")).read_bytes()
    candidate_raw = (ROOT/"reports"/folder/(case["id"]+".json")).read_bytes()
    if hashlib.sha256(raw).hexdigest() != route["case_sha256"] or raw != candidate_raw:
        raise ValueError("Frozen replay case differs from pinned candidate bytes")
    if json.loads(raw) != case:
        raise ValueError("Frozen replay case value changed")
    report = run_family(family)
    if family == "guard":
        control = next(c for c in report["controls"] if c["case"] == case["id"])
        outcome = control["outcome"]
        verdict = "ACCEPT" if outcome == "ACCEPT_DECLARATION_WITH_DEBT" else "REFUSE" if outcome == "REFUSE" else None
        if verdict is None:
            raise ValueError("Unexpected guard observation")
        return {"observed_verdict":verdict, "reason":"Frozen declaration/checker gate replayed; coverage and open-premise debt remain as recorded.",
                "control":control, "limited_contrast":report["limited_contrast"],
                "native_held_claim_verdict":None, "external_execution":False}
    exponent = case["inputs"]["asserted_clearing_exponent"]
    observations = report["observations"]
    if exponent == 1:
        verdict = "REFUSE" if observations["negative"]["remainder_is_nonzero"] else "ACCEPT"
    elif exponent == 2:
        verdict = "ACCEPT" if observations["positive"]["historical_clearing_exponent"] == 2 else "REFUSE"
    else:
        raise ValueError("Unbound clearing exponent")
    return {"observed_verdict":verdict, "reason":"Exact pinned Cramer replay: exponent two clears; exponent one has nonzero polynomial remainder.",
            "observations":observations, "bindings":report["bindings"],
            "native_held_claim_verdict":None, "external_execution":False,
            "limit":"Historical exact arithmetic only; no source equivalence, graph authority or general exponent theorem."}
