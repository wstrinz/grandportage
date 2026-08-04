"""The transport kernel: the only place mathematical judgement is encoded.

Everything else in Grand Portage is data, bookkeeping or plumbing.  This module
is pure stdlib, imports nothing from the rest of the package, and has no I/O.

The kernel answers exactly one question:

    given an edge between two models, a direction of travel, and a claim,
    is moving that claim across that edge LICENSED?

It does not know what a Groebner basis is, what a matroid is, or what problem
you are working on.  It knows six relaxation types and four claim kinds.

Provenance: this is `whetstone/whetstone_dag.py`'s transport table, lifted out
of the JC(2) campaign it was written against, plus the SPECIALIZATION type that
`whetstone/MATROID_TRANSFER.md` sec.8 showed was forced by a second domain.
"""

# ---------------------------------------------------------------------------
# Edge types.  Inclusion-style edges point TIGHTER -> LOOSER: `src` is the more
# informative model, so V(src) subset V(dst) for every lossy type except
# SPECIALIZATION, whose fibres are not nested.  AGAINST = reasoning looser ->
# tighter, which is the direction emptiness travels and the direction that
# closes cells.
#
# A mapped EQUIVALENCE is the other non-inclusion presentation: `forward`
# carries source points to target points and `inverse` carries them back.  It
# licenses the same logical transports through that identification, without
# asserting literal containment in the coordinates as written.
# ---------------------------------------------------------------------------
EQUIVALENCE = "EQUIVALENCE"
NECESSARY_CONDITION = "NECESSARY_CONDITION"
BASE_EXTENSION = "BASE_EXTENSION"
IMAGE_CLOSURE = "IMAGE_CLOSURE"
SPECIALIZATION = "SPECIALIZATION"
# ---------------------------------------------------------------------------
# RESTRICTION -- the sixth type, and the first added by a live run rather than
# by review.
#
# A LIVE CAMPAIGN could not type one edge: a positivity cone sitting inside the
# real variety it was cut out of.  The step drops INEQUALITIES, and the other
# five all drop equations, change a coefficient ring, or project.  The campaign
# recorded it UNTYPED and carried the debt rather than guess.
#
# WHAT MAKES IT WORTH A TYPE IS THAT NECESSARY_CONDITION WOULD HAVE BEEN SOUND.
# Every cell NECESSARY_CONDITION licenses depends only on V(src) subset V(dst),
# and that containment genuinely holds here.  Nothing false would have been
# licensed.  The campaign chose UNTYPED anyway, and its report says why: the
# entire difference between a result holding GENERICALLY and holding EVERYWHERE
# lived in whether the cut was equational or semialgebraic, and
# NECESSARY_CONDITION is documented as "equations are dropped".  A sound label
# that hides the one distinction a campaign exists to make is still the wrong
# label -- and it is the ATTRACTOR, because it is sound and it makes the graph
# go green.
#
# The mathematics does diverge, in exactly one cell, and in the STRONGER
# direction.  NECESSARY_CONDITION refuses a DERIVED identity ALONG because
# O(dst) -> O(src) is a quotient by a larger ideal, so a relation coming from
# src's own equations does not push forward.  A semialgebraic restriction adds
# NO equations -- there is no larger ideal and no quotient.  The question stops
# being algebraic and becomes analytic: does a polynomial vanishing on a
# Euclidean-open piece vanish on the whole variety?
#
# It does, but only under a condition that can fail over R, which is why the
# cell is gated rather than open.  See _ZARISKI_DENSE.
# ---------------------------------------------------------------------------
RESTRICTION = "RESTRICTION"

# Not a relaxation type: an explicitly recorded modelling DEBT.  An edge may be
# declared UNTYPED, but only with a reason, and the checker reports every one of
# them.  This exists so that "we have not typed this step" is a positive
# assertion in the graph rather than a missing row -- MODELLING_GAPS.md sec.4
# requirement 3.  It licenses nothing.
UNTYPED = "UNTYPED"

LOSSY_TYPES = (NECESSARY_CONDITION, BASE_EXTENSION, IMAGE_CLOSURE,
               SPECIALIZATION, RESTRICTION)
ALL_TYPES = (EQUIVALENCE,) + LOSSY_TYPES
DECLARABLE_TYPES = ALL_TYPES + (UNTYPED,)

ALONG = "ALONG"
AGAINST = "AGAINST"
DIRECTIONS = (ALONG, AGAINST)

# What each type MEANS, printed wherever the table is.
#
# `gp table` used to print five names and their transport rows and nothing
# about what the names denote.  A foreign campaign then used SPECIALIZATION for
# an INDEX RESTRICTION -- running 3 of 527 cases -- because the name reads
# generically and the table never said otherwise.  The row happened to be
# uniformly NO, so the verdict was right by luck while the remediation text
# talked about Fano over F_2.
#
# The MCP schema always said "the characteristic changes".  The CLI did not,
# and the CLI is what someone reaches for first.
TYPE_MEANS = {
    EQUIVALENCE: "nothing is lost, and you can exhibit the converse",
    NECESSARY_CONDITION: "equations are dropped; the target is a strict "
                         "relaxation",
    BASE_EXTENSION: "the COEFFICIENT FIELD grows (k into K).  Not a change of "
                    "characteristic",
    IMAGE_CLOSURE: "an elimination or projection; you get the Zariski CLOSURE "
                   "of the image",
    SPECIALIZATION: "the CHARACTERISTIC changes (char 0 -> char p).  ONLY "
                    "that -- it is not a general-purpose 'restricted to a "
                    "sub-case' type.  For a case split use a `partition`; for "
                    "dropping conditions use NECESSARY_CONDITION",
    RESTRICTION: "INEQUALITIES are dropped, not equations.  src is a "
                 "semialgebraic subset of dst cut out by strict inequalities "
                 "-- a positivity cone, an open region, a nondegeneracy "
                 "condition -- in the SAME coordinates.  Use this rather than "
                 "NECESSARY_CONDITION whenever nothing was added to the ideal",
    UNTYPED: "not yet known.  Licenses nothing; requires debt_why",
}

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

# Structured exact-affine PREDICATE atoms. A conjunction of ZERO and NONZERO
# polynomial conditions is enough to type equations and algebraic open conditions
# without pretending to be a general logic.
CONDITION_RELATIONS = ("ZERO", "NONZERO")

# ---------------------------------------------------------------------------
# COUNT -- the fifth kind, and it exists only AT A FAMILY.
#
# A family is to its members as a model is to its points, so the four kinds
# above carry over unchanged as quantifiers over members.  What they cannot say
# is "exactly k of N", which is the deliverable of every census: "4 of 1567
# classes are generically 2-to-1", "3 of 40 have a reachable exceptional
# locus", "27 of 34 rows are open".
#
# It is kept off models deliberately.  "Exactly k points" is a statement about
# a variety that this kernel has no machinery for and no campaign has asked
# for, and admitting it would put a cardinality where the transport table
# expects a quantifier.
# ---------------------------------------------------------------------------
COUNT = "COUNT"

# WHICH VERDICTS DOES A TRIAGE METHOD PROVE?  `proves`, and it is a LIST.
#
# The question that made the family object worth building rather than merely
# convenient.  A census settles most of its cases with cheap tests, and a cheap
# test is usually asymmetric:
#
#   full Jacobian rank at ONE rational point  ->  PROVES generic full rank,
#                                                 because the witnessing minor
#                                                 is a nonzero polynomial
#   rank DEFICIENCY at that point             ->  evidence only
#
# One computation, two verdicts, one of them not established.  A live census
# knew this -- it took the max over several points and said in its own report
# that deficiency "is only evidence" -- and then reported 1220 cases as a
# single number, of which 852 were forced by parameter counting (a proof in
# both directions) and 368 rested on sampling.  The prose blurred a line the
# author had already seen.
#
# THIS STARTED AS AN ENUM -- POSITIVE / NEGATIVE / BOTH / NEITHER -- AND THE
# RETRODICTION FIXTURE KILLED IT.  A split has several groups, and POSITIVE
# cannot say WHICH of them the method establishes; the fixture asked and there
# was no answer that did not depend on group order.  Naming the proved groups
# says the same thing, says it unambiguously, and collapses four cases into
# one field:
#
#   proves: [every group]   the method decides -- what an enum called BOTH
#   proves: [one group]     asymmetric -- what an enum called POSITIVE
#   proves: []              screening only -- what an enum called NEITHER
#
# It must be DECLARED even when empty.  A missing `proves` is an author who was
# not asked the question; an empty one is an author who answered it.
#
# Evidence PROVENANCE -- ran it, read it, cited it -- is `established_by`, and
# a disposition gets that free by being a claim.  This axis is the new one.
# ---------------------------------------------------------------------------

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
    # A guard monomial lies in I, so 1 lies in the localized ideal and the
    # recorded principal-open model has no points.  This base-changes because
    # the same polynomial identity survives every coefficient extension.
    "LOCALIZED_UNIT_IDEAL_CERT": True,
    "NONZERO_RESULTANT": True,          # res in Q^*, hence in K^*
    "EXACT_VALUATION_COLLISION": True,  # an inequality between integers
    "DEGREE_COUNT": True,               # an inequality between integers
    "NONSQUARE_CLASS": False,           # field-relative by construction
    "NO_RATIONAL_POINT_SEARCH": False,  # field-relative by construction
    # A PROOF THAT EXISTS AND IS NOT CARRIED HERE.
    #
    # T5 pointed the tool at a foreign campaign and it had to record a refereed
    # theorem it deliberately kept out of scope.  EMPTY demands a certificate,
    # nothing in the registry meant "somebody proved this in a journal", so a
    # certificate was manufactured -- which the transcribing agent called the
    # worst stretch in its graph, correctly.
    #
    # base_changes=False is not a claim that the theorem is field-relative.  It
    # is a refusal to guess: the argument is not here, so nothing in this graph
    # can tell whether it survives enlarging the field.  The consequence is the
    # useful part -- `derive_scope` then FORCES the author to name the field the
    # cited result is stated over, which is exactly the question people skip
    # when quoting a theorem.
    #
    # Pair it with `established_by: CITED`.  The certificate says what kind of
    # argument closes the claim; `established_by` says you did not run it.
    "CITED_PROOF": False,
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
# A locally validated elimination may still omit equations. Exact-image
# forward transport needs the missing contraction-completeness direction.
_EXACT_IMAGE_IDENTITY = "exact_image_identity"
_CLOSED_EXACT_IMAGE = "closed_exact_image"
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

# ---------------------------------------------------------------------------
# THE ONE CELL WHERE A RESTRICTION IS STRONGER THAN A NECESSARY_CONDITION, and
# the condition that keeps it honest.
#
# A polynomial vanishing on a nonempty Euclidean-open subset U of an
# irreducible variety X vanishes on all of X -- so an IDENTITY established only
# on the restricted region pushes forward to the whole model.  That is a real
# and useful licence: it is what lets a computation done on a positivity cone
# be stated about the variety it sits in.
#
# IT CAN FAIL OVER R, WHICH IS WHY IT IS DECLARED RATHER THAN ASSUMED.  The
# argument needs the REAL points to be Zariski-dense in X, and they need not be:
#
#   COUNTEREXAMPLE.  X = V(x^2 + y^2) over R.  Over C this is two lines; its
#   real points are the single point (0,0).  A polynomial vanishing on a
#   "Euclidean-open piece" of that real locus vanishes on a point and says
#   nothing whatever about X.  x is such a polynomial and x = 0 is false on X.
#
# It also needs X IRREDUCIBLE -- on a reducible variety an open piece can miss a
# whole component, and a relation holding on one component says nothing about
# the others.
#
# So the edge must declare `zariski_dense`, meaning: dst is irreducible and its
# real points are Zariski-dense in it, so a relation holding on any nonempty
# open piece holds throughout.  Undeclared, the cell refuses.  This is the same
# shape as `ring_iso` on EQUIVALENCE and `coefficients_in_base` on
# BASE_EXTENSION -- a licence that is usually available, never automatic, and
# false exactly where somebody would have been surprised.
#
# ===========================================================================
# ALL OF WHICH IS RETRACTED.  Everything above this line is the reasoning that
# put `zariski_dense` on the cell, and it is kept because the way it was wrong
# is more useful than the fact that it was.
#
# THE CONDITION IS NOT SUFFICIENT.  An external review supplied a target that
# satisfies every word of it and breaks the conclusion anyway:
#
#   COUNTEREXAMPLE.  X : y^2 = x^2(x - 1) over R, the nodal cubic.
#     - IRREDUCIBLE over R: y^2 - x^2(x-1) factors only if x-1 is a square in
#       R(x), and it is not.
#     - REAL POINTS ZARISKI-DENSE in X: x^2(x-1) >= 0 forces x >= 1 or x = 0,
#       so X(R) is an infinite branch plus the isolated point (0,0), and an
#       infinite subset of an irreducible curve is dense in it.
#     - Now cut with x^2 + y^2 < 1/2.  The branch starts at x = 1, so the
#       restricted region U is exactly {(0,0)} -- nonempty, and relatively
#       Euclidean-OPEN in X(R) because the point is isolated.
#     - `x = 0` holds on all of U and is false on X at (1,0).
#
#   The gap: X(R) dense in X does NOT give an open PIECE of X(R) dense in X,
#   because X(R) can be disconnected with a zero-dimensional component.  The
#   density that matters is of U, not of X(R).
#
# AND THE DEEPER FAULT IS A TYPE ERROR, WHICH IS WHY THE FIX IS NOT A BETTER
# CONDITION.  A RESTRICTION drops inequalities and adds no equations: src and
# dst have the SAME RING and the SAME IDEAL.  This kernel defines IDENTITY as a
# rewriting valid in the coordinate ring -- lhs - rhs in I.  Same I at both
# ends, so an IDENTITY at src IS the IDENTITY at dst.  Unconditionally, for the
# same reason 3 = 3.
#
# The gate was never serving identities.  It was quietly serving a DIFFERENT
# claim -- "this relation was seen to vanish at every point of the region" --
# which is a pointwise statement, i.e. a PREDICATE.  And RESTRICTION/ALONG/
# PREDICATE is already False, correctly.  So the honest repair is to stop
# gating the identity and let the mis-typed claim be refused where it always
# should have been.
#
# WHAT REPLACES THE HESITATION.  A free gate that was checking nothing still
# made people stop, and removing it would be a practical regression even as a
# theoretical improvement.  So the stopping moves rather than vanishing:
# `verify.identity` decides lhs - rhs in I by reduction, `check` reports every
# IDENTITY that has not been put to that test, and a claim that is really a
# pointwise observation FAILS it -- x does not reduce modulo (y^2+x^2-x^3).
# The nodal cubic is refused by computation instead of by a declaration nobody
# could check.
#
# `_ZARISKI_DENSE` is retained as a field so old graphs keep folding, and is
# consulted by no cell.
# ===========================================================================
_ZARISKI_DENSE = "zariski_dense"

# ---------------------------------------------------------------------------
# THE EXISTENTIAL READING, and this is the register's own prescription cashed.
#
# NONEMPTY is pinned to the WITNESS reading -- "here is a point p" -- because
# that is the claim every entry in the corpus actually made.  The two readings
# diverge in exactly ONE cell, IMAGE_CLOSURE/AGAINST/NONEMPTY:
#
#   existential  cl(S) nonempty => S nonempty, since cl(empty) = empty.  TRUE.
#   witness      0 lies in cl(G_m) and not in G_m.  FALSE -- this is Chevalley.
#
# `discharge.KNOWN_CONSERVATISM` has carried that cell since v0.2 with a
# standing note: the refusal "is a false refusal only for an existential
# nonemptiness, WHICH NOTHING HAS YET RECORDED", and a pre-written upgrade --
# "when an existential claim first appears: a claim-level `existential` flag
# making this ONE cell conditional.  Not a second claim kind, which would add
# ten rows to distinguish one."
#
# A fourth domain recorded one.  A toric phase was asserted nonempty because
# its class is nonzero in the Chow ring, which FORCES a point without producing
# one -- an existence proof, not a witness.  The trigger the register named has
# occurred, so the upgrade it specified is earned rather than speculative, and
# it is implemented exactly as written: one flag, one cell.
#
# It is deliberately NOT a second claim kind and NOT a widening of any other
# cell.  Everywhere else the two readings agree, which is why the ambiguity was
# harmless for as long as it lasted.
# ---------------------------------------------------------------------------
_EXISTENTIAL = "existential"

# ---------------------------------------------------------------------------
# DERIVED POINT TRANSPORT.
#
# Every typed edge has a point relation from src to dst. Two independent
# capabilities determine the ordinary point claims:
#
#   total on src       every src point relates to a dst point
#   surjective on dst  every dst point relates to a src point
#
# Existential claims follow the relation and EMPTY runs contravariantly.
# PREDICATE has the same variance only after the endpoint predicates are
# reindexed or shown to correspond along the relation; that claim-typing
# obligation is separate. Three cells carry operation-specific authority
# beyond this relational core and are explicit overrides.
# IDENTITY is deliberately absent: it is a coordinate-ring claim.
# ---------------------------------------------------------------------------
_POINT_RELATION_CAPABILITIES = {
    EQUIVALENCE: (True, True),
    NECESSARY_CONDITION: (True, False),
    RESTRICTION: (True, False),
    BASE_EXTENSION: (True, False),
    IMAGE_CLOSURE: (True, False),
    SPECIALIZATION: (False, False),
    UNTYPED: (False, False),
}

_POINT_RULE_OVERRIDES = {
    (BASE_EXTENSION, ALONG, EMPTY): _SCHEME_SCOPE,
    (IMAGE_CLOSURE, ALONG, PREDICATE): _CLOSED_EXACT_IMAGE,
    (IMAGE_CLOSURE, AGAINST, NONEMPTY): _EXISTENTIAL,
}


def point_relation_capabilities(etype):
    """Return the baseline ``(total, point_surjective)`` pair for an edge."""
    try:
        return _POINT_RELATION_CAPABILITIES[etype]
    except KeyError:
        raise KeyError("unknown edge type %r" % (etype,))


def compile_point_rule(etype, direction, kind):
    """Compile one EMPTY/NONEMPTY/PREDICATE rule from point capabilities."""
    if direction not in DIRECTIONS:
        raise KeyError("unknown direction %r" % (direction,))
    override = _POINT_RULE_OVERRIDES.get((etype, direction, kind))
    if override is not None:
        return override
    total, surjective = point_relation_capabilities(etype)
    if kind == NONEMPTY:
        return total if direction == ALONG else surjective
    if kind in (EMPTY, PREDICATE):
        return surjective if direction == ALONG else total
    raise KeyError("point-rule derivation does not cover kind %r" % (kind,))


def _transport_row(etype, direction, identity_rule):
    row = {kind: compile_point_rule(etype, direction, kind)
           for kind in (EMPTY, NONEMPTY, PREDICATE)}
    row[IDENTITY] = identity_rule
    return row


# ===========================================================================
# THE TRANSPORT TABLE. Point cells are compiled above; identity cells remain
# explicit because their semantics lives in coordinate rings.
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
        ALONG: _transport_row(EQUIVALENCE, ALONG, _RING_ISOMORPHISM),
        AGAINST: _transport_row(EQUIVALENCE, AGAINST, _RING_ISOMORPHISM),
    },
    NECESSARY_CONDITION: {
        # tighter -> looser.  A point of the tighter model is a point of the
        # looser one; nothing else survives this direction.  IDENTITY needs the
        # rewriting to be AMBIENT: the pullback O(dst) -> O(src) is surjective
        # and not injective here, so a relation derived from src's own ideal
        # does not push forward.  See the k[x]/(x) counterexample above.
        ALONG: _transport_row(
            NECESSARY_CONDITION, ALONG, _AMBIENT_IDENTITY),
        # looser -> tighter.  THIS is the direction that closes cells.  An
        # identity of any origin pulls back, because the ring map points this
        # way; the denominator-free condition is what keeps the expression
        # meaningful after substitution.
        AGAINST: _transport_row(
            NECESSARY_CONDITION, AGAINST, _MAP_POLYNOMIAL),
    },
    RESTRICTION: {
        # src = the semialgebraic subset (a positivity cone, an open region);
        # dst = the variety it sits inside, IN THE SAME COORDINATES.
        #
        # The six point-cells are identical to NECESSARY_CONDITION's, because
        # they follow from V(src) subset V(dst) and nothing else -- which is
        # exactly why NECESSARY_CONDITION was the attractor for this edge and
        # why mislabelling it would have licensed nothing false.
        # IDENTITY ALONG IS UNCONDITIONAL, and it took an external review and a
        # nodal cubic to see that the gate here was answering a question nobody
        # had asked.  See the retraction above _ZARISKI_DENSE.
        ALONG: _transport_row(RESTRICTION, ALONG, True),
        # AGAINST/IDENTITY IS THE OTHER PLACE THIS DIFFERS, and it is
        # unconditional where NECESSARY_CONDITION needs a denominator-free map.
        # A restriction does not change coordinates at all -- it is a subset
        # inclusion, the identity on functions -- so there is no substitution to
        # go wrong.  A relation valid at every point of dst is valid at every
        # point of a subset of dst, and that is the whole argument.
        AGAINST: _transport_row(RESTRICTION, AGAINST, True),
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
        ALONG: _transport_row(BASE_EXTENSION, ALONG, True),
        AGAINST: _transport_row(
            BASE_EXTENSION, AGAINST, _COEFFICIENTS_IN_BASE),
    },
    IMAGE_CLOSURE: {
        # src = the true constructible image; dst = its Zariski closure.
        # A Zariski-CLOSED condition on the image does extend to the closure --
        # which is why elimination is a sound way to DERIVE equations even
        # though it is unsound as a source of witnesses.
        #
        # IDENTITY is licensed ALONG here and that is NOT an inconsistency with
        # the NECESSARY_CONDITION row.  THE ARGUMENT USED TO BE DENSITY and it
        # was the wrong argument twice over.
        #
        # It read: "the image is DENSE in its closure, so the pullback
        # O(closure) -> O(image) is INJECTIVE and a relation vanishing on the
        # image vanishes on the closure ... the direction follows from a
        # PROPERTY OF THE MAP".
        #
        #   * DENSITY IS NOT A PROPERTY OF THE MAP.  A set is dense in its own
        #     closure by the definition of closure.  Citing it as though the
        #     map earned it dresses a tautology as a hypothesis, which is how
        #     `zariski_dense` -- this project's other free gate -- survived as
        #     long as it did.
        #
        #   * IT CONCLUDES ABOUT POINTS AND THE CLAIM IS ABOUT AN IDEAL.
        #     "Vanishes on the closure" and "lies in the closure's ideal" agree
        #     only when that ideal is radical, and an elimination ideal need
        #     not be.  `verify.identity` decides MEMBERSHIP, by reduction.
        #     lean/GrandPortage/ImageClosure.lean has the gap as `radMem_mem`.
        #
        # THE HONEST ARGUMENT IS THE ELIMINATION THEOREM, at the level the tool
        # actually works at: I(dst) = I(src) cap k[remaining], so a rewriting
        # in I(src) that is a SENTENCE IN THE TARGET RING is in I(dst) by
        # membership, and the converse holds because that intersection sits
        # inside I(src).  Both directions are exact and neither needs density,
        # reducedness, or anything about the map.
        #
        # WHAT IT DOES NEED IS EXPRESSIBILITY, and nothing checked it: `x*y = 1`
        # is true on the hyperbola and is not a sentence in k[x].  That is now
        # INEXPRESSIBLE-CONCLUSION in `check`, and it puts this gate in the same
        # class as `coefficients_in_base` -- an artifact of claims being strings
        # rather than terms, which is why the formalisation could not see it.
        #
        # `_MAP_POLYNOMIAL` STAYS.  It is not the condition the elimination
        # theorem needs, and it is not dead either: `operations.eliminate` mints
        # these edges from a projection, whose map is polynomial always, but a
        # hand-declared IMAGE_CLOSURE along a RATIONAL map can introduce
        # denominators in the pullback and this refuses it.  Two real
        # conditions; only one of them used to be checked.
        ALONG: _transport_row(
            IMAGE_CLOSURE, ALONG, _EXACT_IMAGE_IDENTITY),
        # A point of the closure need NOT lift: NONEMPTY does not travel here.
        # That single cell is Chevalley.
        AGAINST: _transport_row(
            IMAGE_CLOSURE, AGAINST, _MAP_POLYNOMIAL),
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
        #
        #   AND INTEGRAL COEFFICIENTS ARE NOT ENOUGH EITHER.  An external review
        #   found this cell licensing a false transport, and the field that
        #   fixes it was already built and simply never consulted here.
        #
        #     COUNTEREXAMPLE.  A = Z_(p)[x]/(px).  On the generic fibre p is a
        #     unit, so A[1/p] = Q[x]/(x) and `x = 0` holds.  Its coefficients
        #     are as integral as coefficients get -- the coefficient is 1.  But
        #     A/pA = F_p[x], where `x = 0` is false.
        #
        #   The integrality that matters is not the identity's but its
        #   DERIVATION's.  You get `x = 0` by writing x = (1/p)*(px), and the
        #   1/p is the whole problem: the ideal-membership certificate is not
        #   p-integral, which is the same thing as x being p-torsion in A.
        #
        #   So this cell must consult `identity_origin`, exactly as
        #   _AMBIENT_IDENTITY does two rules above it.  An AMBIENT rewriting has
        #   no derivation beyond itself, so its coefficients ARE the whole
        #   question and reduction is term-by-term.  A DERIVED one rides on a
        #   certificate this kernel cannot see.
        #   AGAINST (lift to char 0) is unsound outright.  `p*x = 0` holds
        #   identically in characteristic p and lifts to nothing.
        ALONG: _transport_row(
            SPECIALIZATION, ALONG, _INTEGRAL_IDENTITY),
        AGAINST: _transport_row(SPECIALIZATION, AGAINST, False),
    },
    UNTYPED: {
        ALONG: _transport_row(UNTYPED, ALONG, False),
        AGAINST: _transport_row(UNTYPED, AGAINST, False),
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


class KernelRefusal(ValueError):
    """Base class for every refusal the kernel raises at fold time.

    Exists so no call site has to ENUMERATE them.  Four of the five subclasses
    below were added in one week and none was added to the CLI's or the MCP
    server's except-clause, so a graph that tripped them produced a Python
    traceback instead of the refusal message -- and a crashing checker is
    indistinguishable from a checker nobody ran.

    That is the same defect as the unvalidated `severity_override` fixed days
    earlier, recreated four times over by the fixes that followed it.  A base
    class makes the next one handled by default, which an enumeration cannot.
    """


class ScopeError(KernelRefusal):
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


class IdentityOriginError(KernelRefusal):
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
              coefficients_in_base=None, zariski_dense=None,
              existential=None, image_complete=True, exact_contraction=None,
              geometric_closure=None, point_surjective=False,
              target_expressible=False):
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

    # `image_complete` is the epoch-2 compatibility argument. Epoch 3 splits
    # exact coordinate-ring contraction from geometric point-closure
    # authority; callers that use the old argument intentionally set both.
    if exact_contraction is None:
        exact_contraction = image_complete
    if geometric_closure is None:
        geometric_closure = image_complete
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
    if rule == _EXISTENTIAL:
        if existential:
            return ruling(
                True,
                "licensed: this NONEMPTY is EXISTENTIAL -- it asserts a point "
                "exists without holding one -- and the closure of the empty "
                "set is empty, so a nonempty closure forces a nonempty image",
                _EXISTENTIAL)
        return ruling(
            False,
            "a point of the Zariski closure need not lift to the image "
            "(Chevalley): 0 lies in the closure of G_m and not in G_m.  That "
            "is decisive for a WITNESS -- a claim holding a specific point -- "
            "and it is NOT decisive for an existence proof, because "
            "cl(empty) = empty, so a nonempty closure does force a nonempty "
            "image.  If this claim exhibits a point, the refusal stands and "
            "the discharge is to lift it.  If it only proves one EXISTS, "
            "declare `existential: true` and say how existence was "
            "established without a witness",
            _EXISTENTIAL)
    if rule == _ZARISKI_DENSE:
        if zariski_dense:
            return ruling(
                True,
                "licensed: the edge declares dst irreducible with its real "
                "points Zariski-dense, so a polynomial relation holding on a "
                "nonempty open piece holds throughout", _ZARISKI_DENSE)
        return ruling(
            False,
            "a rewriting established only on the restricted region pushes "
            "forward only if a polynomial vanishing there vanishes on all of "
            "the target.  That needs the target IRREDUCIBLE with its REAL "
            "points Zariski-dense in it, and over R that can fail: V(x^2+y^2) "
            "has one real point, and `x = 0` holds on it while being false on "
            "the variety.  Declare `zariski_dense` on the edge if the "
            "condition holds -- it usually does, and it is never automatic",
            _ZARISKI_DENSE)
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
        if not integral:
            return ruling(False,
                          "reducing an identity mod p needs its coefficients to "
                          "be INTEGRAL AT p, which is a property of the CLAIM "
                          "and not of the map.  This claim does not declare "
                          "integrality", _INTEGRAL_IDENTITY)
        if identity_origin == AMBIENT:
            return ruling(True,
                          "licensed: the rewriting is AMBIENT, so it has no "
                          "derivation beyond itself and its coefficients are "
                          "the whole question -- being integral at the prime, "
                          "it reduces term by term", _INTEGRAL_IDENTITY)
        return ruling(False,
                      "this identity's COEFFICIENTS are integral at p, but it "
                      "is %s rather than AMBIENT, and for a rewriting that "
                      "follows from the model's own equations the coefficients "
                      "are not the whole question -- its DERIVATION must be "
                      "p-integral too.  In Z_(p)[x]/(px), `x = 0` holds on the "
                      "generic fibre with coefficient 1, and is false mod p: "
                      "you get it from x = (1/p)*(px), and that 1/p never "
                      "appears in the identity itself.  Equivalently x is "
                      "p-torsion.  This kernel cannot see the certificate, so "
                      "it refuses"
                      % (identity_origin or UNKNOWN), _INTEGRAL_IDENTITY)
    if rule == _EXACT_IMAGE_IDENTITY:
        if map_kind not in DENOMINATOR_FREE:
            return ruling(False,
                          "IDENTITY rewriting needs a denominator-free map; "
                          "this edge's map is %s" % map_kind,
                          _MAP_POLYNOMIAL)
        if exact_contraction:
            return ruling(True,
                          "licensed: the map is denominator-free and the "
                          "target has exact image/contraction authority",
                          _EXACT_IMAGE_IDENTITY)
        return ruling(False,
                      "the elimination output is certified only in the "
                      "no-invention direction J subset inclusion^-1(I). "
                      "Moving a source-derived identity ALONG needs the open "
                      "completeness direction inclusion^-1(I) subset J",
                      _EXACT_IMAGE_IDENTITY)
    if rule == _CLOSED_EXACT_IMAGE:
        if point_surjective and target_expressible:
            return ruling(True,
                          "licensed: every target point has a checked lift and "
                          "the structured predicate is expressible entirely in "
                          "the target coordinates; closedness is not required",
                          _CLOSED_EXACT_IMAGE)
        if not zariski_closed:
            detail = (
                "the map has point-lifting authority, but this predicate has "
                "no structured target-expressibility proof"
                if point_surjective else
                "only Zariski-closed conditions extend from an image to its "
                "closure; this predicate is not declared or structurally "
                "established closed")
            return ruling(False, detail, _CLOSED_CONDITION)
        if geometric_closure:
            return ruling(True,
                          "licensed: the condition is Zariski-closed and the "
                          "target has independently established geometric image-closure "
                          "authority", _CLOSED_EXACT_IMAGE)
        return ruling(False,
                      "a closed condition extends to the actual closure, but "
                      "this elimination has no independent geometric point-closure "
                      "certificate; exact contraction alone does not settle "
                      "base-relative image closure",
                      _CLOSED_EXACT_IMAGE)
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


class WitnessError(KernelRefusal):
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


# ---------------------------------------------------------------------------
# EVIDENCE GRADING.  Two axes, and fusing them is why the field rotted.
#
# `ladder` licenses nothing and never has -- the checker never grades evidence
# and the ladder never licenses a transport, deliberately, because conflating
# them is how a project ends up with an `independently-audited` predicate
# imported across an edge that forbids it.  That stays true.  What follows is
# about whether the RECORD is honest, not about soundness.
#
# T5 pointed the tool at a campaign that had never heard of it.  That campaign
# had independently invented its own evidence discipline -- every claim tagged
# [ARTIFACT], [SOURCE] or [NOT CHECKED] -- and when its reasoning was
# transcribed, `ladder` came back with SEVEN distinct values and ZERO overlap
# with the five it declares.  Some were paragraphs:
#
#     "CLASSICAL -- not one of RECON's three tags.  These are textbook facts
#      used as negative controls in recon/sos_gate.m2; RECON does not establish
#      them and does not tag them."
#
# The field was unvalidated free text, so a careful user filled it with prose
# rather than noticing it was a closed set.  That is the fourth instance of one
# pattern -- certificates, identity_origin, kind, ladder -- a field whose value
# is taken on the author's word.  The first three were found by exploitation;
# this one by a stranger simply trying to use it.
#
# THE DIAGNOSIS IS THAT THERE ARE TWO QUESTIONS AND ONE SLOT:
#
#     established_by   how did you come to believe this?  Did you RUN it, READ
#                      it, take it from a CITATION, or fail to reach it?
#     ladder           how strong is the evidence, weakest first?
#
# RECON needed both and had one field, so it wrote both into that field plus
# caveats.  Separating them costs one enum and buys a CROSS-CHECK -- the first
# thing about evidence grading this tool has ever been able to verify.
# ---------------------------------------------------------------------------
RAN = "RAN"                    # executed here, and it produced this
READ = "READ"                  # read from source or a file, not executed
CITED = "CITED"                # taken from a paper or an external authority
NOT_REACHED = "NOT_REACHED"    # out of reach in this environment
# DERIVED -- proved HERE from premises that were read or cited.
#
# THE ONE PLACE A LIVE SESSION HAD SOMETHING TRUE TO SAY AND NO WAY TO SAY IT.
# It established that a corner's direction is determined by m + n, from Prop
# 3.5's valuation identity plus two definitions -- new mathematics, none of it
# in the source, none of it run.  RAN is false (no computation), CITED is false
# (no authority asserts it), NOT_REACHED is false.  It graded the claim READ
# and said in the note that this overstates the source's involvement.
#
# That is the failure this axis exists to prevent, wearing the opposite sign:
# not evidence claiming more than it has, but a real derivation forced to
# borrow somebody else's authority because the vocabulary had no word for
# "mine".
DERIVED = "DERIVED"
ESTABLISHED_BY = (RAN, READ, CITED, DERIVED, NOT_REACHED)

# `derivation-checked` -- the argument was made HERE and a computation
# confirmed its arithmetic, without the computation having established it.
#
# ADDING `DERIVED` TO ONE AXIS LEFT THE OTHER TOO NARROW, and a live session
# found the gap immediately: it proved a result, wrote a script that re-checked
# every number in the proof, and had nowhere above `claimed` to put it --
# because `exact-checked` asserts a checker ESTABLISHED the claim, which would
# be false.  So a proof with its arithmetic verified sat on the same rung as a
# bare assertion, next to a claim whose only support was a citation.
#
# It is deliberately NOT in LADDER_ASSERTS_A_RUN.  That set exists to catch a
# grade claiming a run nobody recorded; this grade claims a run CONFIRMED an
# argument, which is a weaker and different thing, and the argument is what
# carries the claim.
LADDER = ("open", "claimed", "derivation-checked", "exact-checked",
          "independently-audited", "certified")

# Combinations that cannot both be true.  Not a soundness rule -- nothing here
# licenses a transport -- but a record that says two incompatible things about
# its own evidence is worse than one that says nothing.
IMPOSSIBLE_EVIDENCE = {
    (NOT_REACHED, "exact-checked"):
        "a gated checker cannot have verified something you could not run",
    (NOT_REACHED, "independently-audited"):
        "a second implementation cannot have agreed with a run that did not "
        "happen",
    (NOT_REACHED, "certified"):
        "nothing was certified by a computation that was out of reach",
    (CITED, "exact-checked"):
        "a citation is not a checker run.  If you re-ran it, that is RAN; if "
        "you are relying on the authors, the grade is `claimed`",
    (CITED, "independently-audited"):
        "reading one paper is not a second implementation agreeing",
    (READ, "exact-checked"):
        "reading source establishes what the code SAYS, not that running it "
        "produced this.  A checker that was not run has checked nothing",
    (DERIVED, "exact-checked"):
        "a derivation is an argument, not a checker run.  If a computation "
        "confirmed it, the grade is RAN and the derivation is what you ran it "
        "against",
    (CITED, "derivation-checked"):
        "a citation is somebody else's argument.  `derivation-checked` says "
        "YOU made the argument and checked its arithmetic",
    (NOT_REACHED, "derivation-checked"):
        "nothing was checked by a computation that was out of reach",
    (DERIVED, "independently-audited"):
        "one derivation is not a second implementation agreeing.  Two people "
        "deriving it separately is a REPLICATION -- record that as evidence",
}

# ---------------------------------------------------------------------------
# THE HALF-GRADE.  Both evidence fields were optional on the reasoning that
# grading licenses nothing, so an ungraded claim is merely ungraded.  That is
# true of a claim with NO grade.  It is false of a claim with HALF a grade.
#
# `exact-checked` and above are not opinions about strength.  Each one asserts
# that something HAPPENED -- a checker ran, a second implementation agreed, a
# certificate was produced.  Left alone in the record, that assertion is the
# one part of the evidence layer nothing can check, because every rule that
# could contradict it lives in IMPOSSIBLE_EVIDENCE and every key there needs
# an `established_by` to match on.  Omit the field and the cross-check does
# not fire; it evaluates `(None, "exact-checked")`, which is in no table.
#
# Found in a live campaign: all fourteen of its claims graded themselves
# `exact-checked` with no `established_by`, so IMPOSSIBLE_EVIDENCE -- "the
# first thing about evidence grading this tool has ever been able to verify" --
# never evaluated once in a full session.  That session's central structural
# result rested on an unrecorded script, and its own report had to catch that
# by hand.  The tool had the mechanism and the mechanism was switched off by an
# absent field.
#
# So this is the fifth instance of one pattern, with a mutation.  The first
# four -- certificates, identity_origin, kind, ladder -- were fields whose
# VALUE was taken on the author's word.  This is a field whose ABSENCE
# disables the check on a neighbouring field's value.  Optionality is not
# neutral when another rule keys on it.
#
# The rule is narrow on purpose: `open` and `claimed` claim no event, so they
# stay free.  Only a grade that says a run happened has to name the run.
# ---------------------------------------------------------------------------
LADDER_ASSERTS_A_RUN = ("exact-checked", "independently-audited", "certified")


class EvidenceError(KernelRefusal):
    """A claim whose declared evidence contradicts itself."""


def check_evidence(established_by, ladder, claim_id="<claim>"):
    """Validate the two evidence axes and refuse impossible combinations.

    An UNGRADED claim is fine -- unlike certificates and witnesses, evidence
    grading licenses nothing, so both fields may be absent together.  What is
    refused is a grade that is WRONG, and a HALF grade: a `ladder` at
    `exact-checked` or above asserts that a run happened, and must name it,
    because IMPOSSIBLE_EVIDENCE can only contradict a named one.
    """
    if established_by is not None and established_by not in ESTABLISHED_BY:
        raise EvidenceError(
            "claim %s declares established_by %r; known values are %s.  This "
            "records HOW you came to believe the claim, not how strong it is "
            "-- strength is `ladder`."
            % (claim_id, established_by, ", ".join(ESTABLISHED_BY)))
    if ladder is not None and ladder not in LADDER:
        raise EvidenceError(
            "claim %s declares ladder %r, which is not one of %s.\n"
            "  `ladder` is a STRENGTH ordering and a closed set. If you are "
            "recording how the claim was established -- ran it, read it, could "
            "not reach it -- that is `established_by`. If you are recording a "
            "limitation, that is `caveat`, which is free text and carried "
            "verbatim.\n"
            "  This field was unvalidated until a foreign campaign filled it "
            "with seven values and no overlap with these five."
            % (claim_id, ladder, ", ".join(LADDER)))
    if established_by is None and ladder in LADDER_ASSERTS_A_RUN:
        blocked = [b for b in ESTABLISHED_BY
                   if (b, ladder) in IMPOSSIBLE_EVIDENCE]
        survives = [b for b in ESTABLISHED_BY if b not in blocked]
        raise EvidenceError(
            "claim %s grades itself %s without an `established_by`.\n"
            "  %s is not an opinion about strength -- it asserts that "
            "something HAPPENED. Say what:\n"
            "    RAN          you executed it here and it produced this\n"
            "    READ         you read a source or a file, without running it\n"
            "    CITED        you are relying on a paper or an authority\n"
            "    NOT_REACHED  it was out of reach in this environment\n"
            "  Against THIS grade, {%s} would be refused and only {%s} can "
            "stand -- so naming it costs you an honest answer to `how` and may "
            "cost you the grade. If nothing here backs it, it is `claimed`.\n"
            "  Both fields may be omitted TOGETHER -- an ungraded claim is "
            "merely ungraded. What cannot stand is half a grade, because every "
            "rule that could contradict this one matches on `established_by`, "
            "so leaving it out does not weaken the claim, it silences the "
            "check."
            % (claim_id, ladder, ladder,
               ", ".join(blocked) or "nothing is",
               ", ".join(survives)))
    why = IMPOSSIBLE_EVIDENCE.get((established_by, ladder))
    if why:
        raise EvidenceError(
            "claim %s says it was established by %s and grades itself %s, and "
            "those cannot both be true: %s."
            % (claim_id, established_by, ladder, why))
    return established_by, ladder


class KindCompositionError(KernelRefusal):
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


# ---------------------------------------------------------------------------
# SUPERSESSION FOR CLAIMS AND INFERENCES.
#
# Edges have had `supersedes` + `discharge_kind` since v0.2.  Claims and
# inferences had nothing, and a live campaign paid for it in the ordinary way:
# a missing OPTIONAL attribute was noticed at check time, redeclaration with
# different content is a hard fold error, so the campaign had to mint new ids
# for the claim AND for the inference that referenced it.  The permanent cost
# was two entities that are dead but indistinguishable from live ones, a note
# explaining the situation to a human, and a baseline entry reading
# "superseded, not carried on its merits" -- which dilutes what a baseline
# entry means for every other entry in the file.
#
# THE HAZARD IS THE WORD "ONLY".  That campaign's actual amendment was
# described, accurately, as "same claim, with coefficients_in_base declared".  But
# `coefficients_in_base` is exactly what licenses an IDENTITY to cross a
# BASE_EXTENSION.  "I only added an attribute" is the sentence through which a
# transport-determining field arrives unexamined, and this project has now
# found five separate defects that all reduce to a field whose value was taken
# on the author's word.
#
# So AMEND is not a declaration, it is a COMPUTATION.  The tool holds both
# versions of the claim and can see for itself whether anything that licenses a
# transport moved.  An author who writes AMEND over a changed certificate is
# refused and told which field they changed.
# ---------------------------------------------------------------------------
AMEND = "AMEND"          # nothing that licenses anything changed
RELICENSE = "RELICENSE"  # an attribute that determines transport changed
RESTATE = "RESTATE"      # the statement, kind or model itself changed
RETRACT = "RETRACT"      # withdrawn, and nothing replaces it
SUPERSESSION_KINDS = (AMEND, RELICENSE, RESTATE, RETRACT)


def supersession_help(entity="claim"):
    """The four kinds, explained once so `gp why` and the refusal agree.

    EXTRACTED RATHER THAN RESTATED.  This text lived only inside
    `check_supersession_kind`'s error, so it reached you exactly when you had
    already got it wrong and never when you were deciding.  A second copy would
    be a second thing to rot -- this file has watched five README cells
    document licences withdrawn two versions earlier -- so the refusal now
    calls this too.
    """
    lic = (INFERENCE_LICENSING_FIELDS if entity == "inference"
           else LICENSING_FIELDS)
    return (
        "  AMEND      nothing that licenses a transport changed -- a "
        "citation, a caveat, an evidence grade\n"
        "  RELICENSE  an attribute that DECIDES transport changed: %s\n"
        "  RESTATE    what it %s changed\n"
        "  RETRACT    withdrawn, and nothing replaces it\n"
        "\n"
        "  AMEND IS COMPUTED, NOT DECLARED. The tool holds both versions and "
        "checks for itself whether a licensing field moved, so writing AMEND "
        "over a changed certificate is refused and tells you which field you "
        "changed. That guard exists because \"I only added an attribute\" is "
        "the sentence through which a transport-determining field arrives "
        "unexamined."
        "\n\n"
        # THE OTHER HALF OF THE VOCABULARY, which this omitted entirely.
        #
        # The four kinds above are for CLAIMS and INFERENCES. Edges use a
        # DISJOINT set, and `gp why supersession` -- the canonical explainer --
        # never mentioned it. A live session read the documented list, wrote
        # RETRACT on an edge, and was refused by a message that named the valid
        # values and the reason the vocabularies differ.
        #
        # The refusal was excellent. That is the problem: the author had to FAIL
        # ONCE to learn something this function exists to tell them, which is
        # the same shape as the defect this docstring already describes -- text
        # that reaches you when you have got it wrong and never when you are
        # deciding.
        "AN EDGE USES A DIFFERENT AND DISJOINT VOCABULARY -- DERIVE, RETYPE,\n"
        "ACCEPT, WITHDRAW -- because an edge supersession says what happened to the\n"
        "OBLIGATION the old edge carried, while a claim or inference\n"
        "supersession says what CHANGED about the record.\n"
        "\n"
        "  DERIVE     the missing mathematics now exists and the edge is\n"
        "             replaced by one that carries it\n"
        "  RETYPE     the relation was mis-typed; the new edge states the\n"
        "             one that actually holds\n"
        "  ACCEPT     the obligation is knowingly carried, with a reason\n"
        "  WITHDRAW   the declaration was not an edge; nothing replaces it,\n"
        "             and live traffic must be retracted or rerouted\n"
        "\n"
        "  These four words apply only to edges."
        % (", ".join(lic), "asserts" if entity == "inference" else "states"))

# Fields whose value decides what a claim licenses.  Split in two because the
# refusal is different: change what the claim SAYS and it is a different claim
# (RESTATE); change what backs it and the claim is the same sentence with
# different transport behind it (RELICENSE), which is the quieter and more
# dangerous of the two.
IDENTIFYING_FIELDS = ("kind", "model", "statement")
# `lhs`/`rhs`/`ring_vars` ARE LICENSING, and phase 3 shipped without saying so.
# A live session superseded a claim with a FALSE `lhs`, everything else
# byte-identical, under `AMEND` -- and the checker reported "Nothing that
# licenses a transport changed, so the argument stands as checked."  That
# sentence was false: the rewriting is what `identity_origin` is DERIVED from,
# and the origin decides transport.  The guard that exists to stop "I only
# added an attribute" from smuggling a licensing field past review was defeated
# by the field the same release added.
LICENSING_FIELDS = ("certificate", "scope", "identity_origin",
                    "lhs", "rhs", "ring_vars",
                    "coefficients_in_base", "witness_kind", "condition")

# The same split for an inference.  What it ASSERTS identifies it; what it
# RESTS ON licenses it.  Swapping a premise or re-routing a path leaves the
# sentence at the bottom identical and changes everything above it, which is
# precisely the change that most needs a second look.
INFERENCE_IDENTIFYING_FIELDS = ("asserted", "concludes_kind")
INFERENCE_LICENSING_FIELDS = ("premises",)

# And for a MODEL, which had no supersession machinery at all -- `supersedes`
# on one was accepted with no existence check, no self-check, no back-pointer
# and no discharge kind, exactly the state edges were in before they were
# fixed.  A live session changed a model, was not refused, and then could not
# see the change in `gp show` or `gp history`.
#
# THE ANCHOR IS THE WORST OBJECT TO BE ABLE TO CHANGE INVISIBLY.  Every claim
# sits at a model and every edge runs between two, so a model that moves under
# them takes the meaning of everything attached to it with no signal anywhere.
#
# `what` identifies it: change what the model IS and it is a different model.
# `ring_vars` and `generators` LICENSE, and not by analogy -- `verify.
# containment` reduces one model's generators modulo another's, and
# `verify.identity` reduces a rewriting modulo the model's ideal.  Changing
# either changes what a verification means, which is precisely the "I only
# added an attribute" hazard the claim version exists to catch.
# A NOTE'S CONTENT IS ALL IT HAS, so any change to it is a RESTATE and there
# is nothing a note can LICENSE -- it is prose the checker never reads.
NOTE_IDENTIFYING_FIELDS = ("text",)
NOTE_LICENSING_FIELDS = ()

# EVIDENCE, DOUBT AND CITATION were left out of the supersession machinery when
# they landed, and a live session walked into the consequence: `check` told it
# to add `answered` to a doubt and `decides` to an evidence record, refused the
# redeclaration, named SUPERSESSION as the move -- and then accepted the
# supersession, printed "declared 1 event(s)", and DID NOTHING.  The original
# records kept firing.
#
# The worst error class there is: told the move, accepted the move, reported
# success, no-op.  Worse than a refusal, because nothing signals it.
#
# What IDENTIFIES each is what it is about; what LICENSES is the field that
# changes what it does.  `answered` retires a doubt and `decides` changes what
# an enumeration may be read as supporting, so both are licensing -- adding
# either is a RELICENSE, which is exactly the second look they deserve.
# THE THIRD TIME A KIND WAS LEFT OUT OF SUPERSESSION, so the remaining four go
# in together and a gate below keeps the list honest.
#
# A live session superseded a PARTITION to repoint its exhaustiveness claim,
# reported that it "worked", and it did not -- partitions were not superedable
# either, so the old one stayed live and went on demanding a retired id. The
# same silent no-op that had just been fixed for evidence, doubts and
# citations, in a kind nobody thought to check.
#
# What LICENSES, in each case, is the field that decides what the record lets
# through: a certificate's base_changes decides whether an emptiness survives
# a field extension; a partition's exhaustive is the whole of its coverage
# claim; a family's members decide what a COUNT is counting.
CERTIFICATE_IDENTIFYING_FIELDS = ("why",)
CERTIFICATE_LICENSING_FIELDS = ("base_changes",)

PARTITION_IDENTIFYING_FIELDS = ("parent", "branches")
PARTITION_LICENSING_FIELDS = ("exhaustive",)

FAMILY_IDENTIFYING_FIELDS = ("count", "enumeration")
FAMILY_LICENSING_FIELDS = ("members",)

SAME_AS_IDENTIFYING_FIELDS = ("models",)
SAME_AS_LICENSING_FIELDS = ()

EVIDENCE_IDENTIFYING_FIELDS = ("for", "method", "ran")
EVIDENCE_LICENSING_FIELDS = ("decides", "agrees_with")

DOUBT_IDENTIFYING_FIELDS = ("about", "kind")
DOUBT_LICENSING_FIELDS = ("severity", "answered", "quote")

CITATION_IDENTIFYING_FIELDS = ("cites", "resolves_to")
CITATION_LICENSING_FIELDS = ("hazard",)

MODEL_IDENTIFYING_FIELDS = ("what",)
MODEL_LICENSING_FIELDS = ("ring_vars", "generators")

# And for an EDGE.  Exactly the fields `transport` reads off one -- not `type`
# alone, which was the first version of this list and repeated the very mistake
# the claim version was written to avoid.  An EQUIVALENCE gaining `ring_iso`,
# or a RESTRICTION gaining `zariski_dense`, keeps its type and changes which
# cells it opens; a `map_kind` moving off IDENTITY_MAP closes one.
EDGE_LICENSING_FIELDS = (
    "type", "map_kind", "ring_iso", "zariski_dense", "forward", "inverse")


def is_mapped_equivalence(edge):
    """Whether an EQUIVALENCE is asserted through a coordinate change.

    Such an edge relates ``x`` to ``forward(x)``.  It is not the separate
    assertion that the solution sets, in the coordinates as written, are
    literally contained in one another.
    """
    maps = (edge.get("forward"), edge.get("inverse"))
    return bool(edge.get("type") == EQUIVALENCE and all(
        isinstance(mapping, dict) and mapping and all(
            isinstance(k, str) and k.strip()
            and isinstance(v, str) and v.strip()
            for k, v in mapping.items())
        for mapping in maps))


class SupersessionError(KernelRefusal):
    """A supersession whose declared kind does not match what changed."""


# THE FIELD SPLIT PER RECORD KIND, at module level so a gate can check that
# every superedable kind has one.  Inside the function it was unreachable,
# and a kind with no entry silently falls back to a CLAIM's fields -- which
# grades its changes against the wrong list rather than failing.
FIELD_SPLITS = {

    "inference": (INFERENCE_IDENTIFYING_FIELDS,
                  INFERENCE_LICENSING_FIELDS),
    "model": (MODEL_IDENTIFYING_FIELDS, MODEL_LICENSING_FIELDS),
    "note": (NOTE_IDENTIFYING_FIELDS, NOTE_LICENSING_FIELDS),
    "evidence": (EVIDENCE_IDENTIFYING_FIELDS, EVIDENCE_LICENSING_FIELDS),
    "doubt": (DOUBT_IDENTIFYING_FIELDS, DOUBT_LICENSING_FIELDS),
    "citation": (CITATION_IDENTIFYING_FIELDS, CITATION_LICENSING_FIELDS),
    "certificate": (CERTIFICATE_IDENTIFYING_FIELDS,
                    CERTIFICATE_LICENSING_FIELDS),
    "partition": (PARTITION_IDENTIFYING_FIELDS,
                  PARTITION_LICENSING_FIELDS),
    "family": (FAMILY_IDENTIFYING_FIELDS, FAMILY_LICENSING_FIELDS),
    "same_as": (SAME_AS_IDENTIFYING_FIELDS, SAME_AS_LICENSING_FIELDS),
}


def classify_supersession(old, new, entity="claim"):
    """What ACTUALLY changed between two versions of a claim or inference.

    Returns (kind, fields).  Pure inspection -- it reads the two records and
    reports the strongest category of change it finds, so nothing here depends
    on what the author believes they did.
    """
    ident, lic = FIELD_SPLITS.get(
        entity, (IDENTIFYING_FIELDS, LICENSING_FIELDS))
    moved = [f for f in ident if old.get(f) != new.get(f)]
    if moved:
        return RESTATE, moved
    moved = [f for f in lic if old.get(f) != new.get(f)]
    if moved:
        return RELICENSE, moved
    return AMEND, []


def check_supersession_kind(old, new, declared, claim_id="<claim>",
                            entity="claim"):
    """Refuse a supersession whose declared kind understates what changed.

    ONE DIRECTION ONLY.  Declaring a change smaller than it is gets refused;
    declaring it larger does not, because over-declaring costs a second look
    and under-declaring costs the second look that was needed.
    """
    lic = (INFERENCE_LICENSING_FIELDS if entity == "inference"
           else LICENSING_FIELDS)
    if declared not in SUPERSESSION_KINDS:
        raise SupersessionError(
            "%s %s supersedes %r with discharge_kind %r; known kinds are "
            "%s.\n%s"
            % (entity, claim_id, old.get("id"), declared,
               ", ".join(SUPERSESSION_KINDS), supersession_help(entity)))
    if declared == RETRACT:
        return declared
    actual, moved = classify_supersession(old, new, entity)
    rank = {AMEND: 0, RELICENSE: 1, RESTATE: 2}
    if rank[declared] < rank[actual]:
        raise SupersessionError(
            "%s %s supersedes %s and calls it %s, but %s changed, which is "
            "%s.\n"
            "  %s\n"
            "  The tool compares the two records rather than taking the word "
            "for it, because 'I only added an attribute' is how a field that "
            "DECIDES transport arrives without being looked at. Declare %s, or "
            "leave the field alone."
            % (entity, claim_id, old.get("id"), declared,
               ", ".join("`%s`" % f for f in moved),
               actual,
               ("Re-routing an argument is not bookkeeping: the premises and "
                "their paths are the entire reason the conclusion is licensed, "
                "and the sentence at the bottom looks identical either way."
                if entity == "inference" else
                "A licensing attribute is not bookkeeping: `certificate` "
                "decides whether emptiness survives a base change, "
                "`identity_origin` and `coefficients_in_base` decide whether a "
                "rewriting crosses one at all, `condition` decides whether a "
                "predicate factors through retained coordinates, and "
                "`witness_kind` decides whether a point is a point or an "
                "assertion.")
               if actual == RELICENSE else
               "Something that says a different thing is a different %s, and "
               "everything that used the old one has to be looked at again."
               % entity,
               actual))
    return declared
