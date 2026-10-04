"""Neutral structural-containment shortcut and fallback dispatch probes."""
from grandportage import groebner as G
from grandportage import kernel as K
from grandportage import provenance as P
from grandportage import store as S
from grandportage import verify as V


class _ForbiddenBackend:
    def __init__(self):
        self.calls = 0

    def classify_identity(self, *args, **kwargs):
        self.calls += 1
        raise AssertionError("injected fallback backend called")


def probe(case, route):
    d = case["inputs"]
    if (d["characteristic"] != 0 or d["ring_vars"] != ["x"]
            or d["relation"] != "NECESSARY_CONDITION"
            or d["map_kind"] != "IDENTITY"
            or d["backend_policy"] != "raise_on_dispatch"):
        raise ValueError("Unsupported structural-dispatch context")
    events = [
        dict(ev="model", id="SOURCE", what="source generator",
             characteristic=d["characteristic"], ring_vars=d["ring_vars"],
             generators=d["source_generators"]),
        dict(ev="model", id="SELECTED", what="selected generator",
             characteristic=d["characteristic"], ring_vars=d["ring_vars"],
             generators=d["selected_generators"]),
        dict(ev="edge", id="DROP", src="SOURCE", dst="SELECTED",
             type=K.NECESSARY_CONDITION, map_kind=K.IDENTITY_MAP,
             why="select a coefficient row"),
    ]
    graph = S.Graph()
    graph.apply_all([(event, "neutral structural control", index)
                     for index, event in enumerate(events)])
    graph.validate()
    eligible = P._eligible_structural_containment(graph, "DROP")
    backend = _ForbiddenBackend()
    requested = d["requested_observation"]
    if requested == "structural_shortcut":
        if not eligible:
            raise ValueError("Positive control lost structural eligibility")
        verdict, reason = V.containment(graph, "DROP", _backend=backend)
        if verdict != V.VERIFIED or backend.calls:
            raise ValueError("Structural shortcut failed or invoked backend")
        return {
            "observed_verdict": "ACCEPT",
            "reason": reason,
            "structurally_eligible": eligible,
            "native_containment_verdict": verdict,
            "injected_backend_calls": backend.calls,
            "external_execution": False,
        }
    if requested != "backend_fallback":
        raise ValueError("Unknown structural-dispatch observation")
    if eligible:
        raise ValueError("Changed generator remained structurally eligible")
    source = d["source_generators"][0]
    selected = d["selected_generators"][0]
    if (len(d["source_generators"]) != 1
            or len(d["selected_generators"]) != 1
            or source.get("terms") != [{"coefficient": "1", "powers": [["x", 1]]}]
            or selected.get("terms") != [{"coefficient": "999", "powers": [["x", 1]]}]):
        raise ValueError("Changed selected coefficient differs from neutral control")
    independent_identity = G.check_membership_identity(
        selected, [source], ["999"], d["ring_vars"], d["characteristic"])
    try:
        V.containment(graph, "DROP", _backend=backend)
    except AssertionError as exc:
        if str(exc) != "injected fallback backend called" or backend.calls != 1:
            raise
        return {
            "observed_verdict": "ACCEPT",
            "reason": "Literal structural inclusion failed and the injected backend path was called.",
            "structurally_eligible": eligible,
            "native_containment_verdict": None,
            "injected_backend_calls": backend.calls,
            "backend_exception": str(exc),
            "independent_exact_membership": independent_identity,
            "mathematical_noncontainment_established": False,
            "external_execution": False,
        }
    raise ValueError("Ineligible containment did not dispatch to the backend")
