"""The transport kernel: the only place mathematical judgement is encoded.

Everything else in Grand Portage is data, bookkeeping or plumbing.  This module
is pure stdlib, imports nothing from the rest of the package, and has no I/O.

The kernel answers exactly one question:

    given an edge between two models, a direction of travel, and a claim,
    is moving that claim across that edge LICENSED?

It does not know what a Groebner basis is, what a matroid is, or what problem
you are working on.  It knows five relaxation types and four claim kinds.

Provenance: this is `whetstone/whetstone_dag.py`'s transport table, lifted out
of the JC(2) campaign it was written against, plus the SPECIALIZATION type that
`whetstone/MATROID_TRANSFER.md` sec.8 showed was forced by a second domain.
"""

# ---------------------------------------------------------------------------
# Edge types.  Edges point TIGHTER -> LOOSER: `src` is the more informative
# model, so V(src) subset V(dst) for every lossy type.  AGAINST = reasoning
# looser -> tighter, which is the direction emptiness travels and the direction
# that closes cells.
# ---------------------------------------------------------------------------
EQUIVALENCE = "EQUIVALENCE"
NECESSARY_CONDITION = "NECESSARY_CONDITION"
BASE_EXTENSION = "BASE_EXTENSION"
IMAGE_CLOSURE = "IMAGE_CLOSURE"
SPECIALIZATION = "SPECIALIZATION"

# Not a relaxation type: an explicitly recorded modelling DEBT.  An edge may be
# declared UNTYPED, but only with a reason, and the checker reports every one of
# them.  This exists so that "we have not typed this step" is a positive
# assertion in the graph rather than a missing row -- MODELLING_GAPS.md sec.4
# requirement 3.  It licenses nothing.
UNTYPED = "UNTYPED"

LOSSY_TYPES = (NECESSARY_CONDITION, BASE_EXTENSION, IMAGE_CLOSURE,
               SPECIALIZATION)
ALL_TYPES = (EQUIVALENCE,) + LOSSY_TYPES
DECLARABLE_TYPES = ALL_TYPES + (UNTYPED,)

ALONG = "ALONG"
AGAINST = "AGAINST"
DIRECTIONS = (ALONG, AGAINST)

# ---------------------------------------------------------------------------
# Claim kinds.
# ---------------------------------------------------------------------------
EMPTY = "EMPTY"          # this model has no points
# NONEMPTY = an EXHIBITED WITNESS: "here is a point of this model", not the
# weaker "some point exists".  The gloss used to read "usually an exhibited
# witness", and that "usually" was doing silent work -- the two readings
# transport differently and the table can only encode one.
#
# They diverge in EXACTLY ONE of the ten cells, IMAGE_CLOSURE/AGAINST:
#   existential  cl(S) nonempty => S nonempty, since cl(empty) = empty.  TRUE.
#   witness      0 lies in cl(G_m) and not in G_m.  FALSE -- this is Chevalley.
# Everywhere else the two agree, which is why the ambiguity was harmless for as
# long as it lasted.
#
# The witness reading is pinned because it is the one every claim in the corpus
# actually makes ("ML8 has an exact realization over Q(sqrt-3)", "R9 z = 4,5,6
# are exactly NON-EMPTY (exact witnesses)") and the one the discharge for that
# cell is written for ("exhibit a lift").  The cost -- refusing a genuine
# existential nonemptiness across an image closure -- is registered in
# discharge.KNOWN_CONSERVATISM.
NONEMPTY = "NONEMPTY"    # this model has a point, EXHIBITED (see above)
PREDICATE = "PREDICATE"  # a condition satisfied by every point of this model
IDENTITY = "IDENTITY"    # a rewriting valid in this model's coordinate ring
CLAIM_KINDS = (EMPTY, NONEMPTY, PREDICATE, IDENTITY)

# ---------------------------------------------------------------------------
# IDENTITY has two sub-kinds and conflating them was an unsound cell.
#
# An identity is a statement about a RING, and the ring map runs OPPOSITE to the
# point map.  For an edge src -> dst with V(src) subset V(dst), points go
# src -> dst but functions go O(dst) -> O(src).  So a relation holding in O(dst)
# PULLS BACK to O(src) always, while one holding in O(src) pushes forward only
# if the pullback is injective -- which NECESSARY_CONDITION explicitly is not.
#
#   COUNTEREXAMPLE.  A = Spec k[x]/(x) --NECESSARY_CONDITION--> B = Spec k[x].
#   The identity `x = 0` is valid in O(A) and false in O(B).  The table licensed
#   this ALONG for any denominator-free map, which is a false licence, not a
#   conservatism.  Denominator-freeness is a property of the MAP; whether an
#   identity survives is a property of where the identity CAME FROM.
#
# Hence the distinction, declared per claim:
#
#   DERIVED  the rewriting follows from THIS MODEL'S OWN equations.  It lives in
#            the quotient and pulls back only.
#   AMBIENT  the rewriting holds in the shared ambient coordinate ring, before
#            either model's ideal is imposed -- a definition, a substitution, a
#            change of variables.  It never depended on the tighter model's
#            equations, so it travels in both directions.
#
# The live example is the JC(2) shift dictionary (`CL-DICT`):
# d2 = h_2 - (3/8)h_1^2 is a DEFINITION relating ambient coordinates, which is
# why INF-SYZCOLL-DICT is sound.  It was passing on the strength of the
# denominator-free rule -- the right answer for a reason the table did not
# record, which is how a false licence survives a green suite.
# A third origin, and it is the one that makes the other two safe to require.
#
#   UNKNOWN  we have not established which.  Licenses only what BOTH of the
#            others license, and the checker reports it as a debt.
#
# This is `UNTYPED` applied to a claim instead of an edge, and for the same
# reason: "we have not worked this out" must be a POSITIVE ASSERTION in the
# graph rather than a missing field.  A missing field would have to be given a
# default, and any default silently writes a fact nobody vouched for into the
# one artifact that is supposed to BE the campaign state.  Defaulting to
# DERIVED would stamp "this rewriting came from the model's equations" onto a
# definitional dictionary -- false, unattributable, and indistinguishable from
# a real declaration three weeks later.
#
# UNKNOWN and a silent DERIVED default happen to license exactly the same
# transports today, because DERIVED is the weaker of the two wherever origin is
# consulted.  The difference is not what travels; it is whether the graph
# contains a claim nobody made, and whether the checker can see the question is
# still open and ASK.
#
# Unlike UNTYPED, UNKNOWN has a mechanical discharge: which origin holds is
# decided by a normal-form computation (see `cas.classify_identity`), so the
# checker can name the exact call that resolves it rather than asking the author
# to introspect.
UNKNOWN = "UNKNOWN"
DERIVED = "DERIVED"
AMBIENT = "AMBIENT"
IDENTITY_ORIGINS = (AMBIENT, DERIVED, UNKNOWN)

SCHEME = "SCHEME"        # the field-independent emptiness scope

# ---------------------------------------------------------------------------
# Certificate kinds, and whether the emptiness they certify BASE-CHANGES.
#
# This is the mechanism by which the kernel DERIVES an emptiness scope instead
# of trusting the label an author wrote.  1 in I over Q stays 1 in I over K; a
# nonzero rational resultant stays nonzero.  "This quadratic form has no zero
# because its discriminant is a non-square" does NOT survive adjoining the
# square root -- and that single row is the whole of the C08/C20 detection in
# the first domain and the whole of the ML8 detection in the second.
#
# Domains extend this registry through the graph (a `certificate` event); they
# do not edit this dict.
# ---------------------------------------------------------------------------
BUILTIN_CERTIFICATES = {
    "UNIT_IDEAL_CERT": True,            # 1 in I, exhibited over the base
    "NONZERO_RESULTANT": True,          # res in Q^*, hence in K^*
    "EXACT_VALUATION_COLLISION": True,  # an inequality between integers
    "DEGREE_COUNT": True,               # an inequality between integers
    "NONSQUARE_CLASS": False,           # field-relative by construction
    "NO_RATIONAL_POINT_SEARCH": False,  # field-relative by construction
}

# Map kinds.  Needed only for IDENTITY transport: rewriting a dictionary across
# a map is licensed when the map has no denominators.
POLYNOMIAL = "POLYNOMIAL"
RATIONAL = "RATIONAL"
IDENTITY_MAP = "IDENTITY_MAP"
MAP_KINDS = (POLYNOMIAL, RATIONAL, IDENTITY_MAP)

DENOMINATOR_FREE = (POLYNOMIAL, IDENTITY_MAP)

# Conditional rules, resolved by transport() against edge/claim attributes.
_SCHEME_SCOPE = "scheme_scope"
_MAP_POLYNOMIAL = "map_polynomial"
_CLOSED_CONDITION = "closed_condition"
# An identity pushed FORWARD along a non-injective pullback: licensed only when
# the rewriting never depended on the source model's equations.
_AMBIENT_IDENTITY = "ambient_identity"
# An identity reduced into positive characteristic: licensed only when its
# coefficients are integral at the prime.  `d2 = h_2 - (3/8)h_1^2` is a real
# claim in this repo's own fixture and it does not reduce mod 2.
_INTEGRAL_IDENTITY = "integral_identity"
# An identity across an EQUIVALENCE: licensed only when the equivalence is an
# isomorphism of coordinate rings, not merely a bijection on solutions.
_RING_ISOMORPHISM = "ring_isomorphism"
# An identity DESCENDING to a smaller coefficient field: licensed only when both
# sides are defined over that field.
#
# THE SAME QUESTION AS _INTEGRAL_IDENTITY, WEARING A DIFFERENT HAT.  Both ask:
# do this rewriting's coefficients live in the TARGET'S coefficient ring?  For
# SPECIALIZATION that ring is Z localized at p, and the answer is "is it
# p-integral".  For BASE_EXTENSION it is the base field k, and the answer is "is
# it defined over k".  They are consulted at exactly the two edge types that
# change the coefficient ring, which is why there are two constants and one
# idea.  Unify them into a declared coefficient ring once models carry fields as
# structured values rather than free text.
_COEFFICIENTS_IN_BASE = "coefficients_in_base"

# ===========================================================================
# THE TRANSPORT TABLE.  This is the whole type system.
# ===========================================================================
TRANSPORT = {
    EQUIVALENCE: {
        # The only type that forbids nothing -- except that it cannot forbid
        # nothing, because the evidence that earns it is about POINTS and
        # IDENTITY is about FUNCTIONS.
        #
        # `check_unjustified_equivalence` asks for a converse: a construction
        # recovering a point of the source from a point of the target.  That is
        # a bijection on solutions, and a bijection on solutions is NOT an
        # isomorphism of coordinate rings.
        #
        #   COUNTEREXAMPLE.  V(x^2) and V(x) have exactly the same solutions --
        #   the single point 0, with any converse you like.  But `x = 0` is a
        #   valid rewriting in k[x]/(x) and FALSE in k[x]/(x^2); x is not zero
        #   there, which is the entire content of a double root.
        #
        # This is reachable, not exotic: saturation and radicalization are
        # precisely this move, and `sat(I, nz)` is in this repository's own CAS
        # helper.  "I saturated, the solutions are unchanged" is a natural and
        # honest EQUIVALENCE declaration that does not preserve the ring.
        #
        # So IDENTITY crosses an EQUIVALENCE only when the edge declares itself
        # a RING ISOMORPHISM -- the algebra is the same, not merely the
        # solution set.  Every other cell is unaffected: those are about points,
        # and about points the converse is exactly the right evidence.
        ALONG:   {EMPTY: True, NONEMPTY: True, PREDICATE: True,
                  IDENTITY: _RING_ISOMORPHISM},
        AGAINST: {EMPTY: True, NONEMPTY: True, PREDICATE: True,
                  IDENTITY: _RING_ISOMORPHISM},
    },
    NECESSARY_CONDITION: {
        # tighter -> looser.  A point of the tighter model is a point of the
        # looser one; nothing else survives this direction.  IDENTITY needs the
        # rewriting to be AMBIENT: the pullback O(dst) -> O(src) is surjective
        # and not injective here, so a relation derived from src's own ideal
        # does not push forward.  See the k[x]/(x) counterexample above.
        ALONG:   {EMPTY: False, NONEMPTY: True, PREDICATE: False,
                  IDENTITY: _AMBIENT_IDENTITY},
        # looser -> tighter.  THIS is the direction that closes cells.  An
        # identity of any origin pulls back, because the ring map points this
        # way; the denominator-free condition is what keeps the expression
        # meaningful after substitution.
        AGAINST: {EMPTY: True, NONEMPTY: False, PREDICATE: True,
                  IDENTITY: _MAP_POLYNOMIAL},
    },
    BASE_EXTENSION: {
        # src = the model over the SMALL field k; dst = over the BIG field K.
        # NOTE THE REVERSED ASYMMETRY: here it is NONEMPTY that travels freely
        # ALONG (a k-point IS a K-point) and EMPTY that travels only with a
        # certificate.  Anyone who internalised "emptiness always transports"
        # from the other lossy types was primed to get this exactly backwards,
        # which is how the first domain shipped an erratum.
        # IDENTITY ALONG is unconditional and sound: k[x]/I tensor K = K[x]/I^e,
        # so a relation over the small field persists over the large one.
        #
        # IDENTITY AGAINST is DESCENT and is NOT unconditional -- this cell was
        # a false licence until it was gated.
        #
        #   COUNTEREXAMPLE.  x^2 + 1 = (x + i)(x - i) is a valid rewriting in
        #   Q(i)[x].  Transported AGAINST to the Q-model, `i` is not merely
        #   unproved -- it is NOT EXPRESSIBLE there.  The descended statement
        #   is not a false claim, it is not a claim.
        #
        # Descent is sound by faithful flatness exactly when both sides lie in
        # the base ring, which is a property of the CLAIM and not of the edge.
        ALONG:   {EMPTY: _SCHEME_SCOPE, NONEMPTY: True, PREDICATE: False,
                  IDENTITY: True},
        AGAINST: {EMPTY: True, NONEMPTY: False, PREDICATE: True,
                  IDENTITY: _COEFFICIENTS_IN_BASE},
    },
    IMAGE_CLOSURE: {
        # src = the true constructible image; dst = its Zariski closure.
        # A Zariski-CLOSED condition on the image does extend to the closure --
        # which is why elimination is a sound way to DERIVE equations even
        # though it is unsound as a source of witnesses.
        #
        # IDENTITY is licensed ALONG here and that is NOT an inconsistency with
        # the NECESSARY_CONDITION row: the image is DENSE in its closure, so the
        # pullback O(closure) -> O(image) is INJECTIVE and a relation vanishing
        # on the image vanishes on the closure.  This is the cell that shows a
        # uniform "identities only ever pull back" rule would be too strong --
        # the direction follows from a property of the map, not from the name of
        # the edge type.
        ALONG:   {EMPTY: False, NONEMPTY: True, PREDICATE: _CLOSED_CONDITION,
                  IDENTITY: _MAP_POLYNOMIAL},
        # A point of the closure need NOT lift: NONEMPTY does not travel here.
        # That single cell is Chevalley.
        AGAINST: {EMPTY: True, NONEMPTY: False, PREDICATE: True,
                  IDENTITY: _MAP_POLYNOMIAL},
    },
    SPECIALIZATION: {
        # generic fibre <-> special fibre of a scheme over Spec Z.
        #
        # ORIENTATION, PINNED HERE BECAUSE IT WAS NEVER STATED.  `src` is the
        # GENERIC fibre (characteristic 0), `dst` is the SPECIAL fibre
        # (characteristic p), so ALONG is REDUCTION mod p and AGAINST is
        # LIFTING to characteristic 0.  This matches the direction the CAS
        # adapter records -- you hold a char-0 model and produce a mod-p one --
        # and it is the only reading under which the two IDENTITY cells differ,
        # which they must.
        #
        # The MAXIMALLY LOSSY type -- it carries no existence statement in
        # either direction.  Pinned by four published matroid facts
        # (MATROID_TRANSFER.md sec.3): Fano is EMPTY over Q and NONEMPTY over
        # F_2, non-Fano is the reverse, so all four existence cells are
        # falsified by explicit counterexamples.
        #
        # IDENTITY is where this row was wrong in BOTH cells:
        #   ALONG (reduce mod p) is sound only when the identity's coefficients
        #   are INTEGRAL AT p.  Denominator-freeness of the MAP does not give
        #   that: `d2 = h_2 - (3/8)h_1^2` travels a polynomial map and does not
        #   reduce mod 2.
        #   AGAINST (lift to char 0) is unsound outright.  `p*x = 0` holds
        #   identically in characteristic p and lifts to nothing.
        ALONG:   {EMPTY: False, NONEMPTY: False, PREDICATE: False,
                  IDENTITY: _INTEGRAL_IDENTITY},
        AGAINST: {EMPTY: False, NONEMPTY: False, PREDICATE: False,
                  IDENTITY: False},
    },
    UNTYPED: {
        ALONG:   {k: False for k in CLAIM_KINDS},
        AGAINST: {k: False for k in CLAIM_KINDS},
    },
}


class Ruling(object):
    """The kernel's answer.  `rule` names the table cell, so a refusal can be
    routed to a discharge move without re-deriving why it was refused."""

    __slots__ = ("licensed", "reason", "rule", "etype", "direction", "kind")

    def __init__(self, licensed, reason, rule, etype, direction, kind):
        self.licensed = licensed
        self.reason = reason
        self.rule = rule
        self.etype = etype
        self.direction = direction
        self.kind = kind

    def __repr__(self):
        return "<Ruling %s %s/%s/%s>" % (
            "LICENSED" if self.licensed else "REFUSED",
            self.etype, self.direction, self.kind)


class ScopeError(ValueError):
    """An emptiness claim whose declared scope contradicts its certificate."""


def derive_scope(kind, certificate, declared_scope, certificates=None,
                 claim_id="<claim>"):
    """DERIVE an emptiness claim's scope from its certificate.

    This refuses to take the author's word for it, which is the single most
    load-bearing line in the whole system.  A claim whose certificate
    base-changes is SCHEME-scoped whatever the author wrote; a claim whose
    certificate does not base-change MUST carry an explicit field scope, and
    declaring it SCHEME is an error rather than a flag -- you cannot assert
    field-independence on the strength of a field-relative certificate.

    Non-emptiness claims keep whatever scope they declared: `NONEMPTY over R`
    is a fact about R and travels by the transport table, not by derivation.
    """
    certs = BUILTIN_CERTIFICATES if certificates is None else certificates
    if kind != EMPTY:
        return declared_scope
    if certificate is None:
        raise ScopeError(
            "EMPTY claim %s has no certificate.  An emptiness with no "
            "certificate has no derivable scope, and a scope taken on trust "
            "is exactly the failure this kernel exists to refuse." % claim_id)
    if certificate not in certs:
        raise ScopeError(
            "EMPTY claim %s cites unknown certificate kind %r.  Register it "
            "with a `certificate` event declaring whether it base-changes."
            % (claim_id, certificate))
    if certs[certificate]:
        return SCHEME
    if declared_scope in (None, SCHEME):
        raise ScopeError(
            "EMPTY claim %s cites a field-relative certificate (%s) but "
            "declares scope %r.  Name the field the certificate is relative to."
            % (claim_id, certificate, declared_scope))
    return declared_scope


class IdentityOriginError(ValueError):
    """An IDENTITY claim that does not say where its rewriting is valid."""


def derive_identity_origin(kind, origin, claim_id="<claim>"):
    """DERIVE where an IDENTITY claim's rewriting is valid.

    The structural twin of `derive_scope`.  There, an emptiness claim's SCOPE
    comes from its certificate and never from the author's label, because a
    scope taken on trust is the failure the kernel exists to refuse.  Here the
    question is the same shape: an identity's transport direction is decided by
    whether the rewriting came from the model's own equations, and until that is
    stated there is nothing to decide it from.

    Non-IDENTITY claims are unaffected and return None.

    A MISSING ORIGIN RAISES.  There is no default, and the argument against one
    is not that a default would be unsound -- DERIVED would in fact be the safe
    reading, since it licenses less than AMBIENT wherever origin is consulted.
    The argument is that a default writes an unattributable claim into the
    graph.  "The graph is the state": three weeks on, `origin: DERIVED` on a
    definitional dictionary is a false statement no one made, indistinguishable
    from one someone did.  UNKNOWN says the same thing about transport and the
    truth about provenance, and unlike a default it can be REPORTED, so the
    checker can go on asking until the question is actually settled.

    That is the same trade `UNTYPED` makes at the edge level, and it is what
    lets this be a required field without being an onerous one: the honest
    answer is always available.
    """
    if kind != IDENTITY:
        return None
    if origin in IDENTITY_ORIGINS:
        return origin
    if origin is not None:
        raise IdentityOriginError(
            "IDENTITY claim %s declares origin %r; known origins are %s."
            % (claim_id, origin, ", ".join(IDENTITY_ORIGINS)))
    raise IdentityOriginError(
        "IDENTITY claim %s does not say where its rewriting is valid, and "
        "there is no safe default: an identity's transport direction is "
        "decided by whether it came from this model's own equations, so with "
        "that unstated there is nothing to decide it from.\n"
        "  AMBIENT  the rewriting holds in the ambient coordinate ring, before "
        "any of this model's equations are imposed -- a definition, a "
        "substitution, a change of variables.  It travels in both directions.\n"
        "  DERIVED  the rewriting follows from THIS MODEL'S equations.  It "
        "restricts to tighter models but does not survive dropping them.\n"
        "  UNKNOWN  not yet established.  Legal, licenses only what both of "
        "the above license, and the checker will keep asking.\n"
        "You do not have to decide by hand: `cas_classify_identity` settles it "
        "by reducing LHS - RHS, and can also show the rewriting is false at "
        "this model, which neither origin would have caught."
        % claim_id)
def transport(etype, direction, kind, scope=None, certificate=None,
              map_kind=IDENTITY_MAP, zariski_closed=None,
              identity_origin=None, integral=None, ring_iso=None,
              coefficients_in_base=None):
    """Return a Ruling for moving a claim of `kind` across an edge of `etype`.

    Deliberately takes plain values rather than objects: the kernel must be
    callable from a test, a checker, a mutation harness or an MCP handler
    without any of them agreeing on a class.
    """
    if etype not in TRANSPORT:
        raise KeyError("unknown edge type %r (declarable: %s)"
                       % (etype, ", ".join(DECLARABLE_TYPES)))
    if direction not in DIRECTIONS:
        raise KeyError("unknown direction %r" % (direction,))
    if kind not in CLAIM_KINDS:
        raise KeyError("unknown claim kind %r" % (kind,))

    rule = TRANSPORT[etype][direction][kind]

    def ruling(ok, reason, rulename):
        return Ruling(ok, reason, rulename, etype, direction, kind)

    if etype == UNTYPED:
        return ruling(False,
                      "the edge is declared UNTYPED: no transport is licensed "
                      "across a step whose relaxation type has not been named",
                      "untyped")
    if rule is True:
        return ruling(True, "licensed by %s/%s/%s" % (etype, direction, kind),
                      "table")
    if rule is False:
        return ruling(False, "%s does NOT license %s in the %s direction"
                      % (etype, kind, direction), "table")
    if rule == _SCHEME_SCOPE:
        if scope == SCHEME:
            return ruling(True,
                          "licensed: the emptiness is certificate-backed (%s), "
                          "so it base-changes" % certificate, _SCHEME_SCOPE)
        return ruling(False,
                      "%s licenses EMPTY along the extension only at scope "
                      "SCHEME; this claim has scope %r (certificate %s, which "
                      "does not base-change)"
                      % (BASE_EXTENSION, scope, certificate), _SCHEME_SCOPE)
    if rule == _MAP_POLYNOMIAL:
        if map_kind in DENOMINATOR_FREE:
            return ruling(True, "licensed: the map is denominator-free (%s)"
                          % map_kind, _MAP_POLYNOMIAL)
        return ruling(False,
                      "IDENTITY rewriting needs a denominator-free map; this "
                      "edge's map is %s" % map_kind, _MAP_POLYNOMIAL)
    if rule == _COEFFICIENTS_IN_BASE:
        if coefficients_in_base:
            return ruling(True,
                          "licensed: both sides of the rewriting are defined "
                          "over the base field, so the relation descends by "
                          "faithful flatness", _COEFFICIENTS_IN_BASE)
        return ruling(False,
                      "descending a rewriting to a smaller coefficient field "
                      "needs both sides DEFINED OVER that field, and this "
                      "claim does not declare it.  x^2 + 1 = (x + i)(x - i) is "
                      "valid over Q(i); at the Q-model `i` is not merely "
                      "unproved, it is not expressible, so the descended "
                      "statement is not a claim at all",
                      _COEFFICIENTS_IN_BASE)
    if rule == _RING_ISOMORPHISM:
        if ring_iso:
            return ruling(True,
                          "licensed: the equivalence is declared an "
                          "ISOMORPHISM OF COORDINATE RINGS, so a rewriting "
                          "valid at one end is valid at the other",
                          _RING_ISOMORPHISM)
        return ruling(False,
                      "this EQUIVALENCE is not declared a ring isomorphism.  "
                      "The converse that earns an EQUIVALENCE is evidence "
                      "about POINTS, and an identity is a statement about "
                      "FUNCTIONS: V(x^2) and V(x) have the same single point "
                      "and any converse you like, yet `x = 0` holds in one "
                      "coordinate ring and is false in the other.  "
                      "Saturation and radicalization are exactly this step",
                      _RING_ISOMORPHISM)
    if rule == _AMBIENT_IDENTITY:
        if map_kind not in DENOMINATOR_FREE:
            return ruling(False,
                          "IDENTITY rewriting needs a denominator-free map; "
                          "this edge's map is %s" % map_kind, _MAP_POLYNOMIAL)
        if identity_origin == AMBIENT:
            return ruling(True,
                          "licensed: the rewriting is AMBIENT -- it holds in "
                          "the shared coordinate ring and never depended on "
                          "the source model's equations, so it survives "
                          "forgetting them", _AMBIENT_IDENTITY)
        return ruling(False,
                      "an identity DERIVED from the source model's own "
                      "equations does not push forward across %s: the pullback "
                      "O(dst) -> O(src) is not injective, so the relation need "
                      "not hold in the looser model (x = 0 is valid in "
                      "k[x]/(x) and false in k[x]).  Only an AMBIENT rewriting "
                      "travels this way" % etype, _AMBIENT_IDENTITY)
    if rule == _INTEGRAL_IDENTITY:
        if map_kind not in DENOMINATOR_FREE:
            return ruling(False,
                          "IDENTITY rewriting needs a denominator-free map; "
                          "this edge's map is %s" % map_kind, _MAP_POLYNOMIAL)
        if integral:
            return ruling(True,
                          "licensed: the identity's coefficients are integral "
                          "at the prime, so the relation reduces",
                          _INTEGRAL_IDENTITY)
        return ruling(False,
                      "reducing an identity mod p needs its coefficients to be "
                      "INTEGRAL AT p, which is a property of the CLAIM and not "
                      "of the map.  This claim does not declare integrality",
                      _INTEGRAL_IDENTITY)
    if rule == _CLOSED_CONDITION:
        if zariski_closed:
            return ruling(True,
                          "licensed: a Zariski-CLOSED condition on the image "
                          "extends to the closure by definition",
                          _CLOSED_CONDITION)
        return ruling(False,
                      "only Zariski-closed conditions extend from an image to "
                      "its closure; this predicate is not declared closed",
                      _CLOSED_CONDITION)
    raise AssertionError("unknown rule %r in the transport table" % (rule,))


# ---------------------------------------------------------------------------
# CASE SPLITS.  Not transport, and that is the point.
#
# Transport asks what survives crossing ONE edge.  A case split asks what
# follows from covering the parent with several branches at once, and no single
# edge licenses it -- individually each leg is REFUSED, correctly:
#
#     branch -> parent is NECESSARY_CONDITION with the branch tighter, and
#     EMPTY does not travel ALONG (one branch dying says nothing about the
#     parent).  Only ALL branches together, plus exhaustiveness, say anything.
#
# So this is a second inference rule sitting beside the table, and keeping it
# separate is deliberate: it is licensed by a declared PARTITION rather than by
# a relation between two models, and a reader should be able to see which of
# the two justified a step.
# ---------------------------------------------------------------------------
PARTITION_RULES = {
    # claim kind -> whether covering every branch carries it to the parent
    EMPTY: True,        # V(parent) = union of branches; all empty => empty
    PREDICATE: True,    # holds at every point of every branch => every point
    NONEMPTY: False,    # ONE branch suffices, and ordinary transport already
                        # licenses that ALONG a NECESSARY_CONDITION -- so
                        # requiring all branches here would be a false refusal
    IDENTITY: False,    # a rewriting is about a coordinate ring, and the
                        # parent's ring is not assembled from its branches'
}


def transport_over_partition(kind, branches_covered, exhaustive):
    """Rule a case split: does covering every branch carry `kind` to the parent?

    `branches_covered` is True when EVERY branch of the partition carries the
    claim kind; `exhaustive` is True when the partition's covering claim is
    present in the graph.

    Both are required, and the second is the one that gets skipped in practice:
    a split into cases nobody proved were all the cases proves nothing, and
    that premise is exactly what a live run left in a prose note.
    """
    if kind not in CLAIM_KINDS:
        raise KeyError("unknown claim kind %r" % (kind,))
    if not PARTITION_RULES[kind]:
        return Ruling(False,
                      "a case split does not carry %s to the parent; %s"
                      % (kind,
                         "one branch already suffices and ordinary transport "
                         "licenses it" if kind == NONEMPTY else
                         "the parent's coordinate ring is not assembled from "
                         "its branches'"),
                      "partition", "PARTITION", ALONG, kind)
    if not exhaustive:
        return Ruling(False,
                      "the partition does not carry a claim that its branches "
                      "COVER the parent, so a result on every branch is a "
                      "result about a union that may not be the whole",
                      "partition", "PARTITION", ALONG, kind)
    if not branches_covered:
        return Ruling(False,
                      "not every branch carries this claim, and a case split "
                      "reaches the parent only when no case is left open",
                      "partition", "PARTITION", ALONG, kind)
    return Ruling(True,
                  "licensed: every branch carries %s and the partition is "
                  "declared exhaustive, so the parent is covered" % kind,
                  "partition", "PARTITION", ALONG, kind)


# ---------------------------------------------------------------------------
# HOW KINDS COMPOSE WITHIN AN INFERENCE.
#
# The transport table says how a claim survives crossing a map.  It says
# nothing about how a conclusion relates to the PREMISES it was drawn from, and
# that omission was exploitable:
#
#     A NONEMPTY claim at a Zariski closure, pushed back to the image, is
#     correctly REFUSED -- that cell is Chevalley.  Record the same conclusion
#     as a PREDICATE and push it across the same edge and it is LICENSED,
#     because IMAGE_CLOSURE/AGAINST/PREDICATE is sound.  The `asserted` text
#     read "therefore the system HAS a solution" in both cases.  The checker
#     never reads `asserted`, so relabelling `kind` laundered an existence
#     claim through a cell that was never meant to carry one.
#
# Found by an agent probing the gate rather than by review, which is now the
# third time a field that DETERMINES transport and is taken on the author's
# word has been exploited (certificates, identity_origin, and now kind).
#
# The rule is nearly trivial, and reading the kinds as quantifiers is why:
#
#     NONEMPTY   exists x. phi(x)
#     EMPTY      not exists x. phi(x)
#     PREDICATE  forall x. phi(x)
#     IDENTITY   an equation in the coordinate ring
#
# YOU CANNOT GET AN EXISTENCE STATEMENT OUT OF A UNIVERSAL ONE.  So a
# conclusion's kind must appear among its premises' kinds; nothing else is
# derivable by transport alone.
#
# Deliberately NO escape hatch.  A general "this step is mathematics the tool
# does not type" flag would immediately become the next laundering route, and
# the project's own discipline is not to add a mechanism before a real case
# demands it.  If a campaign genuinely needs, say, EMPTY from two contradictory
# PREDICATEs, that case should surface as a refusal and be designed for
# deliberately -- the partition rule is exactly such a case, and it earned its
# construct by appearing twice in live runs.
# ---------------------------------------------------------------------------
# ---------------------------------------------------------------------------
# HOW A NONEMPTY CLAIM IS BACKED.
#
# The asymmetry is embarrassing once stated.  An EMPTY claim MUST carry a
# certificate and `derive_scope` refuses to guess -- emptiness is treated as
# the thing that needs proof.  A NONEMPTY claim, where the author LITERALLY
# HOLDS THE OBJECT, carried nothing at all:
#
#     "there's no registered kind for 'explicit rational witness' -- the
#      strongest evidence in this whole problem has to go in as free text...
#      a fabricated witness would type-check identically to a real one.  The
#      graph cannot currently distinguish 'I have the point' from 'I claim to
#      have the point'."
#
# -- an agent doing real work, finding this unprompted.
#
# And a witness is the CHEAPEST thing in this system to check.  Substituting a
# point into the generators and evaluating is arithmetic; it is less work than
# anything in the certificate registry, which is why leaving it on the honour
# system was the wrong trade rather than a pragmatic one.
#
#   EXHIBITED  the point is given, and can be checked by substitution
#   DERIVED    existence follows from something else recorded here
#   ASSERTED   claimed, not exhibited -- legal, reported as a debt
#
# ASSERTED is the UNTYPED bargain again: the honest answer is always available,
# which is what makes the field requirable rather than onerous.
# ---------------------------------------------------------------------------
EXHIBITED = "EXHIBITED"
ASSERTED = "ASSERTED"
WITNESS_KINDS = (EXHIBITED, DERIVED, ASSERTED)


class WitnessError(ValueError):
    """A NONEMPTY claim that does not say how its point is known."""


def derive_witness_kind(kind, witness_kind, claim_id="<claim>"):
    """How is this existence claim backed?  Non-NONEMPTY claims return None."""
    if kind != NONEMPTY:
        return None
    if witness_kind in WITNESS_KINDS:
        return witness_kind
    if witness_kind is not None:
        raise WitnessError(
            "NONEMPTY claim %s declares witness_kind %r; known kinds are %s."
            % (claim_id, witness_kind, ", ".join(WITNESS_KINDS)))
    raise WitnessError(
        "NONEMPTY claim %s does not say how its point is known.  An EMPTY "
        "claim must carry a certificate and this kernel refuses to guess its "
        "scope; an existence claim -- where you hold the object -- was on the "
        "honour system, so a fabricated witness typed identically to a real "
        "one.\n"
        "  EXHIBITED  the point is given. Put it in `witness`, and "
        "`cas_check_witness` will substitute it into the generators and tell "
        "you whether it is actually a solution. This is the cheapest check in "
        "the system; prefer it.\n"
        "  DERIVED    existence follows from something else recorded here.\n"
        "  ASSERTED   claimed, not exhibited. Legal, and reported as a debt "
        "until it is not." % claim_id)


class KindCompositionError(ValueError):
    """A conclusion whose kind its premises cannot yield."""


def check_conclusion_kind(declared, premise_kinds, iid="<inference>"):
    """The conclusion's kind must be among the premises' kinds."""
    if declared is None:
        return None
    if declared not in CLAIM_KINDS:
        raise KindCompositionError(
            "inference %s concludes kind %r; known kinds are %s"
            % (iid, declared, ", ".join(CLAIM_KINDS)))
    if declared in premise_kinds:
        return declared
    raise KindCompositionError(
        "inference %s declares it concludes %s, but its premises are %s and "
        "transport does not change a claim's kind.\n"
        "  Reading the kinds as quantifiers: NONEMPTY is 'there exists a "
        "point', PREDICATE is 'every point satisfies', EMPTY is 'there is no "
        "point'.  You cannot derive an existence statement from a universal "
        "one, and crossing an edge does not turn one into the other.\n"
        "  If the conclusion really is %s, it needs a premise that IS %s.  If "
        "the premise is what you have, then %s is what you may conclude -- and "
        "saying so keeps the weaker statement from being consumed downstream "
        "as the stronger one."
        % (iid, declared, ", ".join(sorted(set(premise_kinds))) or "(none)",
           declared, declared, " or ".join(sorted(set(premise_kinds)))))


def signature(etype):
    """The type's transport signature, as a comparable tuple.

    Used to assert that no two types are the same table wearing a different
    name, and that a proposed new type is actually needed.
    """
    return tuple((d, k, TRANSPORT[etype][d][k])
                 for d in DIRECTIONS for k in CLAIM_KINDS)
