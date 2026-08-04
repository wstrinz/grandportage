"""Backend-free containment for exact generator subsets in large rings."""

from grandportage import kernel as K
from grandportage import provenance as P
from grandportage import store as S
from grandportage import verify as V


def _graph(source_generators, target_generators, count=78):
    variables = ["x%d" % index for index in range(count)]
    graph = S.Graph()
    graph.apply_all([(event, "large", index) for index, event in enumerate([
        {
            "ev": "model", "id": "SOURCE", "what": "the full template",
            "characteristic": 0, "ring_vars": variables,
            "generators": source_generators,
        },
        {
            "ev": "model", "id": "SELECTED", "what": "selected rows",
            "characteristic": 0, "ring_vars": variables,
            "generators": target_generators,
        },
        {
            "ev": "edge", "id": "DROP", "src": "SOURCE",
            "dst": "SELECTED", "type": K.NECESSARY_CONDITION,
            "map_kind": K.IDENTITY_MAP, "why": "drop coefficient rows",
        },
    ])])
    graph.validate()
    return graph


class _NoBackend:
    def classify_identity(self, *args, **kwargs):
        raise AssertionError(
            "exact generator inclusion must not spawn a backend")


def test_exact_subset_verifies_in_a_ring_larger_than_search_checker_bound():
    graph = _graph(["x0+x77", "x1^2-x2", "x3"], ["x1^2-x2", "x3"])

    verdict, why = V.containment(graph, "DROP", _backend=_NoBackend())

    assert verdict == V.VERIFIED
    assert "unit-cofactor inclusion" in why
    assert P._eligible_structural_containment(graph, "DROP")


def test_identical_malformed_generators_do_not_earn_containment():
    graph = _graph(["not a polynomial!"], ["not a polynomial!"])

    verdict, why = V.containment(graph, "DROP", _backend=_NoBackend())

    assert verdict == V.UNVERIFIED
    assert "not a valid polynomial" in why
    assert not P._eligible_structural_containment(graph, "DROP")


def test_non_subset_still_uses_the_existing_backend_path():
    class RefusingBackend:
        def __init__(self):
            self.called = False

        def classify_identity(self, *args, **kwargs):
            self.called = True
            return K.DERIVED, {"reduced_modulo_ideal": "0"}

    backend = RefusingBackend()
    graph = _graph(["x0"], ["x0^2"])

    verdict, _ = V.containment(graph, "DROP", _backend=backend)

    assert verdict == V.VERIFIED
    assert backend.called