"""Replay A24 through the frozen native number-field witness checker.

This rejects only the offered collapsed point; it never proves model emptiness.
"""
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def probe(case, route):
    case_path = ROOT / "corpus/must" / (case["id"] + ".json")
    if sha(case_path) != route["case_sha256"] or json.loads(case_path.read_text(encoding="utf-8")) != case:
        raise ValueError("Bound A24 case changed")
    for path, expected in route["source_sha256"].items():
        if sha(ROOT / "oracle/checkout" / path) != expected:
            raise ValueError("Pinned A24 checker source changed: " + path)
    from grandportage import format as F, kernel as K, store as S, verify as V

    data = case["inputs"]
    def no_external_runner(*args, **kwargs):
        raise RuntimeError("Native A24 replay unexpectedly attempted external execution")

    def check(guards):
        graph = S.Graph()
        model = {"ev": "model", "id": "M", "what": "the explicitly supplied unit-edge equations",
                 "characteristic": 0, "coefficient_domain": data["coefficient_domain"],
                 "point_universe": data["point_universe"], "ring_vars": data["variables"],
                 "generators": data["equations"], "open_conditions": guards}
        claim = {"ev": "claim", "id": "C", "model": "M", "kind": K.NONEMPTY,
                 "witness_kind": K.EXHIBITED, "statement": "the offered point satisfies this model",
                 "witness_field": data["witness_field"], "witness_point": data["point"]}
        graph.apply_all([(event, "a24-neutral-projection", index) for index, event in enumerate(
            [F.meta_event(), model, claim], 1)])
        graph.validate()
        return V.point_witness(graph, "C", _runner=no_external_runner)

    plain, plain_reason, plain_receipt = check([])
    verdict, reason, receipt = check(data["nonzero_guards"])
    if plain != V.WITNESS_VERIFIED or plain_receipt is None:
        raise ValueError("A24 unguarded native positive contrast did not verify: " + str(plain_reason))
    if len(plain_receipt["equations"]) != 12 or any(e["value"] for e in plain_receipt["equations"]):
        raise ValueError("The positive contrast must check all twelve edge equations")
    if verdict not in (V.WITNESS_VERIFIED, V.WITNESS_REFUTED) or receipt is None:
        raise ValueError("A24 native checker returned no conclusive point observation: " + str(reason))
    if any(e["value"] for e in receipt["equations"]) or not receipt["guards"] or any(g["value"] for g in receipt["guards"]):
        raise ValueError("The recorded A24 contrast must fail the supplied guard only")
    return {"observed_verdict": "ACCEPT" if verdict == V.WITNESS_VERIFIED else "REFUSE",
            "reason": reason, "raw_verdict": verdict, "receipt": receipt,
            "positive_control": {"observed_verdict": "ACCEPT", "raw_verdict": plain,
                                 "reason": plain_reason, "receipt": plain_receipt},
            "production_function_called": "grandportage.verify.point_witness",
            "native_arithmetic_checker": "grandportage.number_field.check_extension_witness",
            "singular_executed": False, "campaign_executed": False,
            "held_authority_established": False,
            "limitation": "Exact extension-valued point substitution over an ALGEBRAIC_CLOSURE model. No selected real embedding or global nonexistence proof; no persisted verdict/admission event."}
