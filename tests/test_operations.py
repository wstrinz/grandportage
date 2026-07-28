"""The three structured operations, and the distinction that motivated two.

Experiment B narrowed this layer from sixteen constructors to three, and the
reasoning is in EXPERIMENT-B.md: hand declarations are 88% accurate, so
correctness alone does not pay for constructors. What these three earn is that
`Localize` and `SaturateClosure` derive DIFFERENT edge types from the same
intuition -- "the part where f is nonzero" -- and a live campaign typed both as
NECESSARY_CONDITION, getting one right by accident.
"""

import pytest

from grandportage import check as C
from grandportage import kernel as K
from grandportage import operations as O
from grandportage import store as S

RING = ["x", "y"]
HYP = ["x*y-1"]


def _fold(events):
    g = S.Graph().apply_all([(e, "t", i) for i, e in enumerate(events)])
    g.validate()
    return g


def test_localize_and_saturate_derive_different_types():
    """THE WHOLE REASON THESE TWO EXIST, and the error the corpus contains.

    Both answer "the part of V(I) where f is nonzero", and they are different
    objects:

        Localize          the OPEN locus. Same ideal, f inverted. Returning to
                          the ambient model drops an INEQUALITY -> RESTRICTION
        SaturateClosure   its CLOSURE, back in the ambient space. I : f^oo
                          contains I, so returning drops EQUATIONS
                          -> NECESSARY_CONDITION

    A live campaign typed a localisation (`E_LAUR`, K[x,y] -> K[x,y,y^-1]) as
    NECESSARY_CONDITION and a saturation (`E-G3_ELIM_NO_A5`, dropping the
    Rabinowitsch generator 1-w*a whose content is a != 0) the same way. One of
    those was right.
    """
    loc = O.localize("M", "y", "M_LOC", RING, HYP)
    sat = O.saturate_closure("M", "y", "M_SAT", RING, HYP)

    assert loc.events[1]["type"] == K.RESTRICTION
    assert sat.events[1]["type"] == K.NECESSARY_CONDITION
    assert loc.events[1]["type"] != sat.events[1]["type"], (
        "if these ever agree, the constructors have stopped distinguishing "
        "the two objects and the layer buys nothing")

    # A localisation changes no coordinates, so there is no substitution that
    # could introduce a denominator.
    assert loc.events[1]["map_kind"] == K.IDENTITY_MAP


def test_the_derived_type_is_inspectable():
    """The claim of this module is that the type is DERIVED. A reader must be
    able to check that without reading the code that acts on it."""
    for kind, (etype, why) in O.DERIVES.items():
        assert etype in K.ALL_TYPES, "%s derives an unknown type" % kind
        assert len(why) > 40, (
            "%s derives %s with no argument for it; a table entry that only "
            "names a type is the honour system with a lookup" % (kind, etype))


def test_eliminate_emits_the_closure_and_refuses_the_witness():
    """THE HYPERBOLA, which is the ten-minute demonstration of the whole idea.

    Eliminating `y` from `xy = 1` gives the ZERO ideal, so the closure of the
    image is all of A^1 -- while `x = 0` has no preimage at all. The CAS is
    right and the unsupported step is reading the closure as the image.

    So the constructor emits IMAGE_CLOSURE, whose AGAINST/NONEMPTY cell refuses
    an exhibited witness. The point is that the caller never chose that type:
    they said `eliminate(y)`, and the refusal followed.
    """
    op = O.eliminate("M_HYP", ["y"], "M_IMG", RING, HYP)
    assert op.events[1]["type"] == K.IMAGE_CLOSURE
    assert op.events[0]["ring_vars"] == ["x"], (
        "the target lives in the ring the eliminated variables left behind")

    g = _fold(
        [{"ev": "model", "id": "M_HYP", "what": "the hyperbola xy=1",
          "ring_vars": RING, "generators": HYP}]
        + op.events
        + [{"ev": "claim", "id": "C", "model": "M_IMG", "kind": K.NONEMPTY,
            "statement": "x=0 is a point of the closure",
            "witness_kind": "EXHIBITED", "established_by": "RAN",
            "ladder": "exact-checked"},
           {"ev": "inference", "id": "I", "claim": "C",
            "path": [["E-M_IMG", K.AGAINST]], "concludes_kind": K.NONEMPTY,
            "asserted": "so the hyperbola has a point with x = 0"}])

    refused = [f for f in C.run(g) if f.rule == C.R_TRANSPORT]
    assert refused, (
        "a closure point read as a source witness is Chevalley, and the "
        "edge the constructor chose exists to refuse it")


def test_eliminating_everything_is_refused():
    """A projection onto no variables has no target model, and returning one
    would be a confident answer about nothing."""
    with pytest.raises(ValueError) as exc:
        O.eliminate("M", ["x", "y"], "M2", RING, HYP)
    assert "no variables" in str(exc.value)


@pytest.mark.parametrize("make", [
    lambda: O.localize("M", "y", "M2", RING, HYP),
    lambda: O.saturate_closure("M", "y", "M2", RING, HYP),
    lambda: O.eliminate("M", ["y"], "M2", RING, HYP),
])
def test_every_constructor_emits_a_foldable_graph(make):
    """The events go through the ORDINARY write path, where every existing
    guard still applies. A constructor that emitted something the store
    refuses would be a second, weaker door into the graph."""
    op = make()
    g = _fold([{"ev": "model", "id": "M", "what": "the source",
                "ring_vars": RING, "generators": HYP}] + op.events)
    assert "M2" in g.models
    assert len(g.edges) == 1
    assert op.program.text.startswith("ring GP_R")
    assert op.verify_hint
