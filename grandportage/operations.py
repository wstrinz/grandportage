"""Structured operations: the program and the transport relation from one value.

THE POINT IS NOT ACCURACY.  Experiment B measured hand-declared relation types
across 57 live edges and found them 88% correct, with most of the remaining
errors in places no constructor can reach -- five of thirteen were edges where
NO OPERATION HAPPENED and the author correctly determined that nothing relates
the two models.  So "callers get the type wrong" does not, on its own, pay for
this layer.

What pays for it is that the caller stops writing the same thing twice.  A
constructor takes what the mathematician already knows -- which variables,
which polynomial -- and derives the target model, the edge, the CAS program and
the verification plan from it.  Typing becomes the thing that saves work rather
than the tax you pay afterwards.

WHY THESE THREE AND NOT SIXTEEN.  Experiment B named them:

    Localize / SaturateClosure   the two that actually got confused, with
                                 NECESSARY_CONDITION and with each other
    Eliminate                    zero observed mislabels, worst consequence
                                 when wrong

`AddEquations` and `DropEquations` have 27 live instances and zero mislabels.
The caller gets those right every time, so a constructor there buys nothing and
was not built.

THE DISTINCTION THAT MOTIVATED THE FIRST TWO, stated once because getting it
wrong is what the corpus shows people do:

    Localize(I, f)          the OPEN locus D(f): same ideal, f inverted.
                            Its points are points of V(I) with f != 0, so
                            going back to V(I) DROPS AN INEQUALITY.
                            -> RESTRICTION

    SaturateClosure(I, f)   the CLOSURE of that open locus, back in the
                            ambient space.  I : f^oo contains I, so the
                            saturated model is cut by MORE EQUATIONS, and
                            going back to V(I) drops them.
                            -> NECESSARY_CONDITION

Same input, same intuition ("the part where f is nonzero"), two different
models and two different edge types.  A live campaign typed both as
NECESSARY_CONDITION; one of those was right by accident.
"""

from . import cas
from . import kernel as K

# What each constructor emits as its transport relation.  Written as a table so
# the derivation is inspectable rather than buried in three functions -- the
# whole claim of this module is that the type is DERIVED, and a reader should
# be able to check that claim without reading the code that acts on it.
DERIVES = {
    "Localize": (K.RESTRICTION,
                 "the open locus D(f) has the same ideal with f inverted, so "
                 "returning to the ambient model drops the inequality f != 0 "
                 "and no equation"),
    "SaturateClosure": (K.NECESSARY_CONDITION,
                        "I : f^oo contains I, so the saturated model is cut "
                        "by more equations; returning to the ambient model "
                        "drops them"),
    "Eliminate": (K.IMAGE_CLOSURE,
                  "elimination returns the ideal of the ZARISKI CLOSURE of "
                  "the projection, which is not the image: a point of the "
                  "closure need not lift"),
}


class Operation(object):
    """What a constructor returns: events, a program, and what to verify.

    Deliberately a plain value.  It is not applied to a graph here, because a
    tool that both decides a relation and writes it leaves nobody holding the
    claim -- the same reason `cas.classify_identity` touches the graph not at
    all.  The caller sends `events` through the ordinary write path, where
    every existing guard still applies.
    """

    __slots__ = ("kind", "events", "program", "verify_hint", "derivation")

    def __init__(self, kind, events, program, verify_hint, derivation):
        self.kind = kind
        self.events = events
        self.program = program
        self.verify_hint = verify_hint
        self.derivation = derivation


def _model(mid, what, ring_vars, generators, **extra):
    ev = {"ev": "model", "id": mid, "what": what,
          "ring_vars": list(ring_vars), "generators": list(generators)}
    ev.update(extra)
    return ev


def _edge(eid, src, dst, kind, why_extra=""):
    etype, why = DERIVES[kind]
    return {"ev": "edge", "id": eid, "src": src, "dst": dst, "type": etype,
            "map_kind": (K.IDENTITY_MAP if etype == K.RESTRICTION
                         else K.POLYNOMIAL),
            "why": (why + ("  " + why_extra if why_extra else "")),
            "built_by_operation": kind}


def localize(src, f, produces, ring_vars, generators, characteristic=0):
    """The open locus where `f` does not vanish.

    Emits a RESTRICTION, because the ideal does not change: only the
    inequality does.  `map_kind` is IDENTITY_MAP for the same reason -- a
    localisation changes no coordinates, so there is no substitution that
    could introduce a denominator.
    """
    ev_model = _model(
        produces,
        "the open locus of %s where %s does not vanish" % (src, f),
        ring_vars, generators, open_conditions=[f])
    ev_edge = _edge("E-%s" % produces, produces, src, "Localize",
                    "The dropped condition is %s != 0." % f)
    prog = cas.CASProgram(
        cas.SINGULAR, ring="GP_R", ring_vars=list(ring_vars),
        decls=[("GP_I", "ideal", ",".join(generators)),
               ("GP_S", "ideal", "std(GP_I)")],
        body=[], outputs=["GP_S"], characteristic=characteristic)
    return Operation(
        "Localize", [ev_model, ev_edge], prog,
        "nothing to reduce: the ideal is unchanged by localisation, and the "
        "open condition is not an ideal-membership question",
        DERIVES["Localize"][1])


def saturate_closure(src, f, produces, ring_vars, generators,
                     characteristic=0):
    """The CLOSURE of the open locus, back in the ambient space.

    Emits a NECESSARY_CONDITION, because `I : f^oo` contains `I` -- the
    saturated model carries more equations, so returning to the source drops
    them.  This is the constructor that a live campaign conflated with
    `localize`, and the two produce different edge types from the same words.
    """
    ev_model = _model(
        produces,
        "the Zariski closure of the part of %s where %s does not vanish"
        % (src, f),
        ring_vars, ["<saturation of %s at %s>" % (src, f)],
        saturated_at=f)
    ev_edge = _edge("E-%s" % produces, produces, src, "SaturateClosure",
                    "Saturating at %s removes the components lying inside "
                    "V(%s)." % (f, f))
    prog = cas.CASProgram(
        cas.SINGULAR, ring="GP_R", ring_vars=list(ring_vars),
        decls=[("GP_I", "ideal", ",".join(generators)),
               ("GP_F", "poly", f),
               ("GP_SAT", "ideal", "sat(GP_I,GP_F)[1]"),
               ("GP_OUT", "ideal", "std(GP_SAT)")],
        body=[], outputs=["GP_OUT"], characteristic=characteristic)
    return Operation(
        "SaturateClosure", [ev_model, ev_edge], prog,
        "the target's generators come back from the run; once recorded, "
        "`gp verify` can check I(src) inside I(dst) by reduction",
        DERIVES["SaturateClosure"][1])


def eliminate(src, variables, produces, ring_vars, generators,
              characteristic=0):
    """Project away `variables`; what comes back is the CLOSURE of the image.

    THE CELL WHERE BEING WRONG COSTS MOST, which is why it is here despite
    zero observed mislabels in the corpus.  The hyperbola shows it in one
    line: eliminating `y` from `xy = 1` gives the zero ideal, so the closure
    is all of `A^1`, and `x = 0` is a point of the closure with no preimage.
    The CAS is right; the unsupported step is reading the closure as the
    image.

    The emitted edge is IMAGE_CLOSURE, whose AGAINST/NONEMPTY cell refuses a
    witness precisely so that reading cannot happen silently.
    """
    remaining = [v for v in ring_vars if v not in set(variables)]
    if not remaining:
        raise ValueError(
            "eliminating %s leaves no variables; there is no target model to "
            "project onto" % ", ".join(variables))
    ev_model = _model(
        produces,
        "the Zariski closure of the image of %s after eliminating %s"
        % (src, ", ".join(variables)),
        remaining, ["<elimination ideal of %s>" % src],
        eliminated=list(variables))
    ev_edge = _edge("E-%s" % produces, src, produces, "Eliminate",
                    "Eliminated: %s." % ", ".join(variables))
    prog = cas.CASProgram(
        cas.SINGULAR, ring="GP_R", ring_vars=list(ring_vars),
        decls=[("GP_I", "ideal", ",".join(generators)),
               ("GP_E", "ideal",
                "eliminate(GP_I,%s)" % "*".join(variables)),
               ("GP_OUT", "ideal", "std(GP_E)")],
        body=[], outputs=["GP_OUT"], characteristic=characteristic)
    return Operation(
        "Eliminate", [ev_model, ev_edge], prog,
        "a NONEMPTY at the target does NOT give a witness at the source; if "
        "you need one, exhibit a lift explicitly",
        DERIVES["Eliminate"][1])
