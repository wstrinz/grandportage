"""Direct selected-sign receipt success versus native interval admission."""
from grandportage import ordered as O, ordered_receipt as R, store as S, format as F

def probe(case, route):
    d = case["inputs"]
    model = {"ev":"model", "id":"M", "what":"selected root",
             "coefficient_domain":"Q", "characteristic":0,
             "point_universe":"REAL_CLOSURE", "ring_vars":["w"],
             "generators":[d["generator"]],
             "embedding":{"var":"w", "kind":"REAL",
                          "isolating_interval":dict(zip(("lo","hi"),d["interval"]))}}
    sign, receipt = O.selected_real_sign(model, d["expression"])
    checked = R.verify(model, d["expression"], receipt)
    if sign != 1 or checked != 1:
        raise ValueError("Expected exact positive endpoint control")
    graph = S.Graph()
    try:
        graph.apply_all([(e,"interval-control",i+1) for i,e in enumerate([F.meta_event(),model])])
        graph.validate()
        admitted, reason = True, "Ordered interval model admitted; direct sign and receipt both give +1."
    except S.GraphError as exc:
        if "lo < hi" not in str(exc):
            raise
        admitted, reason = False, str(exc)
    return {"observed_verdict":"ACCEPT" if admitted else "REFUSE",
            "reason":reason, "direct_producer_sign":sign,
            "direct_receipt_sign":checked, "native_model_admitted":admitted,
            "native_held_claim_verdict":None, "external_execution":False,
            "limit":"Tests native model admission, not standalone API rejection or a false mathematical sign."}
