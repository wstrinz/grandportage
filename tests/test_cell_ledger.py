"""GATE 0 -- every cell in the transport table is argued for.

The mutation suite asks "does editing this field change a verdict?", which is a
real and unusual question, but it PRESUPPOSES the verdicts are right.  It cannot
catch a cell that is confidently wrong, and one was: the old
`test_identity_transport_turns_on_the_map_and_nothing_else` asserted an unsound
cell as its oracle, and 171 green checks went on agreeing with it.

So this file asks the other question.  One test per cell, and each carries in
its docstring either

    PROOF     -- why the licence is sound, from the relation's own definition
    REFUTED   -- an explicit mathematical counterexample
    CONDITION -- the exact side condition, plus what it excludes

`test_every_cell_has_a_ledger_row` fails if a cell exists with no row here, so a
new type or claim kind cannot be added without arguing for its eight cells.

CONVENTION THROUGHOUT.  An edge points src -> dst with V(src) subset V(dst):
src is the TIGHTER, more informative model.  ALONG is src -> dst.  AGAINST is
dst -> src.  Points travel src -> dst; FUNCTIONS travel dst -> src, because the
ring map O(dst) -> O(src) runs opposite the point map.  That single asymmetry is
what the IDENTITY row is about and what the table used to get wrong.
"""

import itertools

import pytest

from grandportage import kernel as K

# Every cell asserted below, as (etype, direction, kind) -> expected licensed.
# Filled by the @cell decorator so the completeness test cannot drift from the
# tests themselves.
LEDGER = {}


def cell(etype, direction, kind, licensed, **kw):
    """Register a ledger row and return a decorator that checks it."""
    def deco(fn):
        LEDGER[(etype, direction, kind)] = (licensed, kw, fn.__doc__ or "")

        def wrapped():
            r = K.transport(etype, direction, kind, **kw)
            assert r.licensed is licensed, (
                "%s/%s/%s expected licensed=%s, got %s: %s"
                % (etype, direction, kind, licensed, r.licensed, r.reason))
            fn()
        wrapped.__name__ = fn.__name__
        wrapped.__doc__ = fn.__doc__
        return wrapped
    return deco


# ===========================================================================
# EQUIVALENCE
# ===========================================================================
@cell(K.EQUIVALENCE, K.ALONG, K.EMPTY, True)
def test_eq_along_empty():
    """PROOF.  V(src) = V(dst), so one is empty iff the other is."""


@cell(K.EQUIVALENCE, K.AGAINST, K.EMPTY, True)
def test_eq_against_empty():
    """PROOF.  Equality is symmetric."""


@cell(K.EQUIVALENCE, K.ALONG, K.NONEMPTY, True)
def test_eq_along_nonempty():
    """PROOF.  The converse construction carries the witness."""


@cell(K.EQUIVALENCE, K.AGAINST, K.NONEMPTY, True)
def test_eq_against_nonempty():
    """PROOF.  Symmetric; the converse is what the type asserts exists."""


@cell(K.EQUIVALENCE, K.ALONG, K.PREDICATE, True)
def test_eq_along_predicate():
    """PROOF.  Same point set, so a condition on all points of one is a
    condition on all points of the other."""


@cell(K.EQUIVALENCE, K.AGAINST, K.PREDICATE, True)
def test_eq_against_predicate():
    """PROOF.  Symmetric."""


@cell(K.EQUIVALENCE, K.ALONG, K.IDENTITY, False, identity_origin=K.AMBIENT)
def test_eq_along_identity_without_ring_iso():
    """REFUTED.  A point-level equivalence need not preserve the ring.

    V(x^2) and V(x) have exactly the same solutions -- the single point 0 --
    so a converse exists.  But `x = 0` holds in k[x]/(x) and is FALSE in
    k[x]/(x^2): x is not zero there, which is the content of a double root.
    Saturation and radicalization are exactly this step.

    Note the origin is AMBIENT here and the cell is still refused -- the ring
    condition is independent of the origin condition.
    """


@cell(K.EQUIVALENCE, K.ALONG, K.IDENTITY, True, ring_iso=True)
def test_eq_along_identity_with_ring_iso():
    """CONDITION: ring_iso.  PROOF given it.  An isomorphism of coordinate
    rings carries a relation to a relation, in either direction.  EXCLUDES
    every equivalence justified only by a bijection on points."""


@cell(K.EQUIVALENCE, K.AGAINST, K.IDENTITY, True, ring_iso=True)
def test_eq_against_identity_with_ring_iso():
    """PROOF.  A ring isomorphism is invertible, so symmetric."""


# ===========================================================================
# NECESSARY_CONDITION -- src is tighter; dst drops equations
# ===========================================================================
@cell(K.NECESSARY_CONDITION, K.ALONG, K.EMPTY, False)
def test_nc_along_empty():
    """REFUTED.  V(x, y) is empty over no field... take instead V(1) subset
    V(x): the tighter model may be empty while the looser is not.  Concretely
    V(x, x-1) = {} and V(x) = {0}: emptiness of the tighter says nothing about
    the looser, which is precisely where counterexamples would live."""


@cell(K.NECESSARY_CONDITION, K.AGAINST, K.EMPTY, True)
def test_nc_against_empty():
    """PROOF.  V(src) subset V(dst).  If V(dst) is empty so is V(src).
    THIS IS THE DIRECTION THAT CLOSES CELLS and the reason the type exists."""


@cell(K.NECESSARY_CONDITION, K.ALONG, K.NONEMPTY, True)
def test_nc_along_nonempty():
    """PROOF.  V(src) subset V(dst): a point of the tighter model IS a point of
    the looser one."""


@cell(K.NECESSARY_CONDITION, K.AGAINST, K.NONEMPTY, False)
def test_nc_against_nonempty():
    """REFUTED.  V(x) subset V(x*y) and (0,1) is a point of V(x*y)... take
    V(x, y) subset V(x): (0, 5) lies in V(x) but not in V(x, y).  A witness in
    the relaxation need not satisfy the dropped equations."""


@cell(K.NECESSARY_CONDITION, K.ALONG, K.PREDICATE, False)
def test_nc_along_predicate():
    """REFUTED.  Every point of V(x, y) satisfies `y = 0`; not every point of
    V(x) does.  A predicate proved using the dropped equations is a fact about
    the tighter model only."""


@cell(K.NECESSARY_CONDITION, K.AGAINST, K.PREDICATE, True)
def test_nc_against_predicate():
    """PROOF.  A condition satisfied by every point of the larger set is
    satisfied by every point of the subset."""


@cell(K.NECESSARY_CONDITION, K.ALONG, K.IDENTITY, False,
      map_kind=K.POLYNOMIAL, identity_origin=K.DERIVED)
def test_nc_along_identity_derived():
    """REFUTED, and this cell was WRONG until v0.2.

    A = Spec k[x]/(x) --NECESSARY_CONDITION--> B = Spec k[x].
    The rewriting `x = 0` is valid in O(A) and false in O(B).

    The old rule licensed this for any denominator-free map, and the inclusion
    of a point into a line is as denominator-free as maps get.  Denominator-
    freeness is a property of the MAP; whether an identity survives is a
    property of where the identity CAME FROM.  The ring map O(B) -> O(A) is
    surjective and not injective, so relations pull back and do not push
    forward.
    """


@cell(K.NECESSARY_CONDITION, K.ALONG, K.IDENTITY, True,
      map_kind=K.POLYNOMIAL, identity_origin=K.AMBIENT)
def test_nc_along_identity_ambient():
    """CONDITION: AMBIENT origin + denominator-free map.

    PROOF given them.  An ambient rewriting holds in the shared coordinate ring
    before either model's ideal is imposed, so it is unaffected by dropping
    equations.  The JC(2) shift dictionary is this case.

    SUFFICIENT, NOT NECESSARY -- see discharge.KNOWN_CONSERVATISM.  The exact
    condition is that LHS - RHS lies in the TARGET'S ideal, which a DERIVED
    identity can also satisfy.  Registered as a deliberate conservatism.
    """


@cell(K.NECESSARY_CONDITION, K.ALONG, K.IDENTITY, False,
      map_kind=K.POLYNOMIAL, identity_origin=K.UNKNOWN)
def test_nc_along_identity_unknown():
    """PROOF.  UNKNOWN must license exactly the intersection of what AMBIENT
    and DERIVED license, and DERIVED is refused here."""


@cell(K.NECESSARY_CONDITION, K.ALONG, K.IDENTITY, False,
      map_kind=K.RATIONAL, identity_origin=K.AMBIENT)
def test_nc_along_identity_rational_map():
    """CONDITION: the map must be denominator-free even for an ambient
    rewriting.  Substituting through a rational map can introduce a pole, so
    the rewritten expression need not be an element of the target ring at
    all."""


@cell(K.NECESSARY_CONDITION, K.AGAINST, K.IDENTITY, True,
      map_kind=K.POLYNOMIAL, identity_origin=K.DERIVED)
def test_nc_against_identity():
    """PROOF, and it needs NO origin condition.

    The ring map O(dst) -> O(src) points this way.  A relation holding in the
    looser model's coordinate ring maps to a relation in the tighter one,
    whatever its origin -- restricting is always safe.  Denominator-freeness is
    still required so the substituted expression lands in the target ring.
    """


# ===========================================================================
# BASE_EXTENSION -- src over small k, dst over big K
# ===========================================================================
@cell(K.BASE_EXTENSION, K.ALONG, K.EMPTY, False, scope="Q")
def test_be_along_empty_field_relative():
    """REFUTED.  x^2 + 1 = 0 has no solution over R and does over C.  A
    field-relative emptiness does not base-change.  THIS IS THE CELL WHOSE
    REVERSAL SHIPPED AN ERRATUM in the parent project."""


@cell(K.BASE_EXTENSION, K.ALONG, K.EMPTY, True, scope=K.SCHEME,
      certificate="UNIT_IDEAL_CERT")
def test_be_along_empty_scheme_scoped():
    """CONDITION: scope SCHEME, derived from a base-changing certificate.
    PROOF given it: 1 in I over k stays 1 in I over K, since the syzygy
    exhibiting it has coefficients in k.  EXCLUDES square-class and
    rational-point-search certificates, which are field-relative by
    construction."""


@cell(K.BASE_EXTENSION, K.ALONG, K.NONEMPTY, True)
def test_be_along_nonempty():
    """PROOF.  A k-point IS a K-point.  NOTE THE REVERSED ASYMMETRY: here
    NONEMPTY travels freely along the arrow and EMPTY does not, the opposite of
    every other lossy type."""


@cell(K.BASE_EXTENSION, K.AGAINST, K.EMPTY, True)
def test_be_against_empty():
    """PROOF.  If there is no K-point there is certainly no k-point, since
    k embeds in K."""


@cell(K.BASE_EXTENSION, K.AGAINST, K.NONEMPTY, False)
def test_be_against_nonempty():
    """REFUTED.  x^2 + 1 = 0 has a C-point and no R-point.  A point over the
    extension need not descend."""


@cell(K.BASE_EXTENSION, K.ALONG, K.PREDICATE, False)
def test_be_along_predicate():
    """REFUTED.  'x^2 + 1 has no root' holds over R and fails over C.  A
    predicate proved over the small field need not survive the extension."""


@cell(K.BASE_EXTENSION, K.AGAINST, K.PREDICATE, True)
def test_be_against_predicate():
    """PROOF.  A condition on every K-point holds in particular on every
    k-point, since the k-points are a subset."""


@cell(K.BASE_EXTENSION, K.ALONG, K.IDENTITY, True)
def test_be_along_identity():
    """PROOF.  k[x]/I tensor K = K[x]/I^e, so a relation over k persists over
    the extension.  Unconditional, and the asymmetry with AGAINST is real:
    going UP needs nothing, coming DOWN needs the terms to exist downstairs."""


@cell(K.BASE_EXTENSION, K.AGAINST, K.IDENTITY, False)
def test_be_against_identity_undeclared():
    """REFUTED without the condition, and this row USED TO SAY `True`.

    The earlier version admitted in prose that the condition existed and was
    "not currently checked", then asserted the cell licensed anyway.  An
    independent reviewer transported `x^2 + 1 = (x + i)(x - i)` from a Q(i)
    model down to a Q model with zero findings -- where `i` is not merely
    unproved but NOT EXPRESSIBLE, so the descended statement is not a false
    claim, it is not a claim.

    THE GATE DID NOT CATCH IT: `test_every_ledger_row_carries_an_argument`
    greps for the word CONDITION, and an UNENFORCED condition contains it just
    as an enforced one does.  A ledger can certify that an argument was made,
    not that the code implements it -- which is why the cell-value assertion in
    the `cell` decorator, not the docstring, is the load-bearing part.
    """


@cell(K.BASE_EXTENSION, K.AGAINST, K.IDENTITY, True, coefficients_in_base=True)
def test_be_against_identity_defined_over_base():
    """CONDITION: both sides defined over the base field.  PROOF given it:
    k -> K is faithfully flat, so k[x]/I -> K[x]/I^e is injective and a relation
    among elements of the base that holds upstairs holds downstairs.

    EXCLUDES any rewriting naming an element of the extension -- which is not a
    corner case but the whole reason people extend the field."""


# ===========================================================================
# IMAGE_CLOSURE -- src = constructible image, dst = its Zariski closure
# ===========================================================================
@cell(K.IMAGE_CLOSURE, K.ALONG, K.EMPTY, False)
def test_ic_along_empty():
    """KNOWN CONSERVATISM, not a proof.  cl(empty) = empty makes this sound.
    The cell is derived from the generic inclusion, and the case is unreachable
    in practice because asserting the image is empty means computing the
    constructible image.  Registered in discharge.KNOWN_CONSERVATISM."""


@cell(K.IMAGE_CLOSURE, K.AGAINST, K.EMPTY, True)
def test_ic_against_empty():
    """PROOF.  The image is contained in its closure, so an empty closure
    forces an empty image."""


@cell(K.IMAGE_CLOSURE, K.ALONG, K.NONEMPTY, True)
def test_ic_along_nonempty():
    """PROOF.  A point of the image lies in the closure."""


@cell(K.IMAGE_CLOSURE, K.AGAINST, K.NONEMPTY, False)
def test_ic_against_nonempty():
    """REFUTED under the WITNESS reading of NONEMPTY, which is the pinned one.

    G_m = A^1 minus the origin has Zariski closure all of A^1, which contains 0.
    But 0 is not in the image, so an exhibited point of the closure need not
    lift.  Elimination is sound for DERIVING equations and unsound as a source
    of witnesses.

    CORRECTED AFTER INDEPENDENT REVIEW.  This row previously said only
    "REFUTED -- THIS CELL IS CHEVALLEY" with the same counterexample, and that
    argument refutes the WITNESS reading while the cell as glossed
    ("this model has a point, usually an exhibited witness") also admitted the
    EXISTENTIAL reading -- under which the cell is TRUE, since cl(empty) = empty
    makes it the exact contrapositive of IMAGE_CLOSURE/ALONG/EMPTY two rows up.

    So the cell was right and the argument was aimed at the wrong statement.
    No test could catch that, because a test checks a verdict and not a reason;
    a reader caught it.  `kernel.NONEMPTY` now pins the witness reading and
    `discharge.KNOWN_CONSERVATISM` registers what pinning it costs.
    """


@cell(K.IMAGE_CLOSURE, K.ALONG, K.PREDICATE, False)
def test_ic_along_predicate_not_closed():
    """REFUTED for a non-closed predicate.  `x != 0` holds at every point of
    G_m and fails at 0, which is in the closure.  An open condition does not
    extend."""


@cell(K.IMAGE_CLOSURE, K.ALONG, K.PREDICATE, True,
      zariski_closed=True, image_complete=True)
def test_ic_along_predicate_closed():
    """CONDITION: the predicate is Zariski-closed.  PROOF given it: a closed
    condition satisfied on a set is satisfied on its closure, by definition of
    closure.  EXCLUDES strict inequalities and nonvanishing side conditions."""


@cell(K.IMAGE_CLOSURE, K.AGAINST, K.PREDICATE, True)
def test_ic_against_predicate():
    """PROOF.  A condition on every point of the closure holds on the image,
    a subset."""


@cell(K.IMAGE_CLOSURE, K.ALONG, K.IDENTITY, True, map_kind=K.POLYNOMIAL,
      identity_origin=K.DERIVED, image_complete=True)
def test_ic_along_identity():
    """PROOF, AND IT IS THE EXCEPTION THAT SHOWS THE RULE IS ABOUT MAPS.

    Unlike NECESSARY_CONDITION, IDENTITY travels ALONG here with no origin
    condition -- because the image is DENSE in its closure, so the pullback
    O(closure) -> O(image) is INJECTIVE.  A polynomial vanishing on a dense
    subset vanishes on the closure.

    This is why a uniform "identities only ever pull back" rule would be too
    strong, and why the right long-term shape derives the direction from
    properties of the map rather than from the name of the edge type.
    """


@cell(K.IMAGE_CLOSURE, K.AGAINST, K.IDENTITY, True, map_kind=K.POLYNOMIAL,
      identity_origin=K.DERIVED)
def test_ic_against_identity():
    """PROOF.  Restriction from the closure to the image, always safe."""


# ===========================================================================
# SPECIALIZATION -- src = generic fibre (char 0), dst = special fibre (char p)
# ALONG is REDUCTION mod p; AGAINST is LIFTING to characteristic 0.
# ===========================================================================
@pytest.mark.parametrize("direction", list(K.DIRECTIONS))
@pytest.mark.parametrize("kind", [K.EMPTY, K.NONEMPTY, K.PREDICATE])
def test_specialization_carries_no_existence_statement(direction, kind):
    """REFUTED, all six cells, by two published matroid facts.

    The Fano plane is realizable over F_2 and NOT over Q; the non-Fano matroid
    is realizable over Q and NOT over F_2.  So EMPTY and NONEMPTY each have an
    explicit counterexample in each direction, and PREDICATE follows: 'is
    realizable' is a predicate that flips.

    MATROID_TRANSFER.md sec.3.  These four facts are what forced the type to
    exist as a fifth row rather than being folded into BASE_EXTENSION.
    """
    assert not K.transport(K.SPECIALIZATION, direction, kind).licensed


@cell(K.SPECIALIZATION, K.ALONG, K.IDENTITY, True, map_kind=K.POLYNOMIAL,
      integral=True, identity_origin=K.AMBIENT)
def test_sp_along_identity_integral():
    """CONDITION: coefficients integral at p AND the rewriting is AMBIENT.
    PROOF given both: an ambient relation has no derivation beyond itself, so
    its coefficients are the whole question and it reduces term by term."""


@cell(K.SPECIALIZATION, K.ALONG, K.IDENTITY, False, map_kind=K.POLYNOMIAL,
      integral=True, identity_origin=K.DERIVED)
def test_sp_along_identity_derived():
    """REFUTED with integral coefficients but a DERIVED origin.

    THE LEDGER CAUGHT THIS ONE LATE.  The cell above carried a PROOF -- 'a
    p-integral relation reduces term by term' -- which is true of the identity
    and says nothing about how the identity was obtained.  An external review
    supplied the counterexample:

        A = Z_(p)[x]/(px).   Generic fibre A[1/p] = Q[x]/(x), so `x = 0`.
                             Special fibre A/pA = F_p[x], so `x != 0`.

    The coefficient of x is 1, which is integral at every prime.  What is not
    integral is the DERIVATION: x = (1/p)*(px).  Equivalently, x is p-torsion
    in A, and torsion is exactly what dies in the generic localization while
    surviving mod p.

    So `integral` and `identity_origin` are both load-bearing here, and only
    the first was consulted.  `identity_origin` already existed -- it gates
    NECESSARY_CONDITION/ALONG/IDENTITY two rules away in the same function --
    which makes this a COVERAGE defect rather than a missing-field one: a
    licensing field checked in one cell and ignored in another that needed it.
    """


@cell(K.SPECIALIZATION, K.ALONG, K.IDENTITY, False, map_kind=K.POLYNOMIAL,
      integral=True, identity_origin=K.UNKNOWN)
def test_sp_along_identity_unknown_origin():
    """REFUTED with an undeclared origin, which keeps a standing invariant.

    The kernel's note on `identity_origin` records that UNKNOWN and a silent
    DERIVED default license exactly the same transports, DERIVED being the
    weaker reading wherever origin is consulted.  Adding a consultation here
    would break that invariant if UNKNOWN were treated as AMBIENT, so it is
    not: an undeclared origin refuses, same as DERIVED.
    """


@cell(K.SPECIALIZATION, K.ALONG, K.IDENTITY, False, map_kind=K.POLYNOMIAL,
      integral=False)
def test_sp_along_identity_not_integral():
    """REFUTED without integrality, and this is a live claim in this repo.

    CL-DICT asserts d2 = h_2 - (3/8)h_1^2.  That does not reduce mod 2: the
    coefficient 3/8 is not 2-integral.  The old rule gated this cell on the MAP
    being denominator-free, which it is -- integrality is a property of the
    CLAIM, and the two were conflated.
    """


@cell(K.SPECIALIZATION, K.AGAINST, K.IDENTITY, False, map_kind=K.POLYNOMIAL,
      integral=True)
def test_sp_against_identity():
    """REFUTED outright, in every case.

    `p*x = 0` holds identically in characteristic p and lifts to nothing in
    characteristic 0.  Integrality does not help: the relation is not the
    reduction of anything.  The old table licensed this whenever the map was
    denominator-free, i.e. always in practice.
    """


# ===========================================================================
# RESTRICTION -- src = a semialgebraic subset, dst = the variety it sits in,
# IN THE SAME COORDINATES.  The cut is by strict inequalities: a positivity
# cone, an open region, a nondegeneracy condition.  Nothing is added to the
# ideal, which is the entire difference from NECESSARY_CONDITION.
#
# The six point-cells below are identical to NECESSARY_CONDITION's, and that
# is not an oversight -- they follow from V(src) subset V(dst) and nothing
# else.  It is why the live campaign that forced this type reported that
# labelling its positivity-cone edge NECESSARY_CONDITION would have been SOUND,
# and why it chose UNTYPED anyway.
# ===========================================================================
@cell(K.RESTRICTION, K.ALONG, K.EMPTY, False)
def test_restriction_along_empty():
    """REFUTED. The positive-definite cone of 1x1 matrices is nonempty, and so
    is the line it sits in -- but take instead the empty region cut by x > 0
    and x < 0 inside the line. src is empty and dst is not. Emptiness of a
    subset says nothing about the set."""


@cell(K.RESTRICTION, K.AGAINST, K.EMPTY, True)
def test_restriction_against_empty():
    """PROOF. V(src) subset V(dst). If dst has no points then neither does any
    subset of it. Same argument as NECESSARY_CONDITION AGAINST/EMPTY, and for
    the same reason: it uses containment and nothing else."""


@cell(K.RESTRICTION, K.ALONG, K.NONEMPTY, True)
def test_restriction_along_nonempty():
    """PROOF. An exhibited point of the restricted region is a point of the
    ambient model, unchanged -- the coordinates are the same ones, so there is
    nothing to transport it THROUGH. A positive-definite matrix is a
    symmetric matrix."""


@cell(K.RESTRICTION, K.AGAINST, K.NONEMPTY, False)
def test_restriction_against_nonempty():
    """REFUTED. Sigma = diag(1, -1) is a real symmetric matrix and is not
    positive definite. A point of the ambient model need not satisfy the
    inequalities, which is what makes the restriction a restriction."""


@cell(K.RESTRICTION, K.ALONG, K.PREDICATE, False)
def test_restriction_along_predicate():
    """REFUTED. `det Sigma > 0` holds at every point of the PD cone and fails
    at diag(1,-1) in the ambient model. A universal statement about a subset
    is silent about the points outside it -- and THIS IS THE CELL THE TYPE
    EXISTS TO PROTECT, since a result proved off an exceptional locus and then
    read as a global one is a recurring error in the applied literature."""


@cell(K.RESTRICTION, K.AGAINST, K.PREDICATE, True)
def test_restriction_against_predicate():
    """PROOF. If every point of dst satisfies P, then in particular every
    point of the subset does. Instantiation, nothing more."""


@cell(K.RESTRICTION, K.ALONG, K.IDENTITY, True)
def test_restriction_along_identity():
    """PROOF, unconditional, and this cell used to be gated on a condition that
    was both insufficient and beside the point.

    A RESTRICTION drops inequalities and adds no equations: src and dst have
    the SAME ring and the SAME ideal. This kernel defines IDENTITY as a
    rewriting valid in the coordinate ring -- lhs - rhs in I. Same I at both
    ends, so an IDENTITY at src IS the IDENTITY at dst. There is nothing to
    gate.

    WHAT THE OLD GATE WAS, AND WHY IT WENT. It required dst irreducible with
    its real points Zariski-dense, on the argument that a polynomial vanishing
    on a nonempty Euclidean-open piece vanishes throughout. An external review
    broke it with the nodal cubic:

        X : y^2 = x^2(x - 1) over R.  Irreducible. X(R) is an infinite branch
        (x >= 1) plus the ISOLATED point (0,0), so X(R) is Zariski-dense in X.
        Cut by x^2 + y^2 < 1/2 the region U is exactly {(0,0)}, nonempty and
        relatively open. `x = 0` holds on U and fails on X at (1,0).

    X(R) dense in X does not make an open PIECE of X(R) dense in X. But the
    repair is not a sharper condition, because the gate was serving the wrong
    claim: "vanishes at every point of the region" is POINTWISE, i.e. a
    PREDICATE, and RESTRICTION/ALONG/PREDICATE is already False. The gate let a
    mis-typed claim through a door that was never meant for it.

    THE HESITATION MOVED RATHER THAN VANISHING. `verify.identity` decides
    lhs - rhs in I by reduction and `check` reports untested identities, so the
    nodal cubic is now refused by computation -- x does not reduce modulo
    (y^2 + x^2 - x^3) -- instead of by a declaration nobody could check."""


@cell(K.RESTRICTION, K.AGAINST, K.IDENTITY, True)
def test_restriction_against_identity():
    """PROOF, and unconditional where NECESSARY_CONDITION needs a
    denominator-free map.

    A restriction does not change coordinates: it is a subset inclusion, the
    identity on functions. So there is no substitution that could introduce a
    denominator or fail to be defined. A rewriting valid at every point of dst
    is valid at every point of a subset of dst.

    `store` enforces the premise by refusing a RESTRICTION whose map_kind is
    not IDENTITY_MAP -- the licence and the argument for it must not drift
    apart."""


# ===========================================================================
# UNTYPED
# ===========================================================================
@pytest.mark.parametrize("direction", list(K.DIRECTIONS))
@pytest.mark.parametrize("kind", list(K.CLAIM_KINDS))
def test_untyped_licenses_nothing(direction, kind):
    """PROOF, trivially.  No relation has been named, so nothing is licensed.
    The value of the row is that it is DECLARABLE: a recorded hole rather than
    a missing one."""
    assert not K.transport(K.UNTYPED, direction, kind).licensed


# The two parametrized blocks above cover their cells uniformly, so their rows
# are registered HERE, at import time, rather than as a side effect of running.
# A completeness gate that only holds when the whole file runs in definition
# order is not a gate -- `pytest <file>::test_every_cell_has_a_ledger_row` alone
# would have passed vacuously, which is the exact vacuity failure mode the
# source campaign has logged three times.
for _d, _k in itertools.product(K.DIRECTIONS, (K.EMPTY, K.NONEMPTY,
                                               K.PREDICATE)):
    LEDGER[(K.SPECIALIZATION, _d, _k)] = (
        False, {}, test_specialization_carries_no_existence_statement.__doc__)
for _d, _k in itertools.product(K.DIRECTIONS, K.CLAIM_KINDS):
    LEDGER[(K.UNTYPED, _d, _k)] = (
        False, {}, test_untyped_licenses_nothing.__doc__)


# ===========================================================================
# COMPLETENESS -- the gate on the gate
# ===========================================================================
def test_every_cell_has_a_ledger_row():
    """No cell may exist without an argument for it.

    This is what makes the file a GATE rather than a collection.  Adding a type
    or a claim kind without arguing for its cells fails here, which is the
    discipline whetstone used for its coverage rule: a detection cannot be
    added without a corresponding entry in the honest-limitations register.
    """
    every = set(itertools.product(K.DECLARABLE_TYPES, K.DIRECTIONS,
                                  K.CLAIM_KINDS))
    missing = sorted(every - set(LEDGER))
    assert not missing, (
        "%d transport cells have no ledger row, so nothing in this repository "
        "argues they are correct:\n  %s"
        % (len(missing), "\n  ".join("%s / %s / %s" % m for m in missing)))


def test_every_ledger_row_carries_an_argument():
    """A row whose docstring does not say PROOF, REFUTED or CONDITION is a
    restatement of the table, not an argument for it."""
    weak = sorted(k for k, (_lic, _kw, doc) in LEDGER.items()
                  if not any(w in doc for w in
                             ("PROOF", "REFUTED", "CONDITION", "CONSERVATISM")))
    assert not weak, (
        "these ledger rows assert a verdict without arguing for it:\n  %s"
        % "\n  ".join("%s / %s / %s" % k for k in weak))


@cell(K.IMAGE_CLOSURE, K.AGAINST, K.NONEMPTY, True, existential=True)
def test_ic_against_nonempty_existential():
    """CONDITION discharged, and the condition was PRESCRIBED FOUR VERSIONS
    BEFORE IT WAS NEEDED.

    PROOF given it. `cl(empty) = empty`, so a nonempty closure forces a
    nonempty image. This is the exact contrapositive of IMAGE_CLOSURE / ALONG /
    EMPTY.

    The cell above it -- the same cell without the flag -- stays REFUTED, and
    the two rows together are the whole content of the distinction: 0 lies in
    the closure of G_m and not in G_m, which kills the WITNESS reading and says
    nothing about the existential one.

    `KNOWN_CONSERVATISM` carried this since v0.2 with the trigger named in
    advance -- a false refusal "only for an existential nonemptiness, which
    nothing has yet recorded" -- and the repair specified: a claim-level flag
    making this ONE cell conditional, not a second claim kind. A fourth domain
    recorded the first one: a toric phase asserted nonempty because its class
    is nonzero in the Chow ring, which forces a point without producing one.

    `store` refuses `existential` together with an EXHIBITED witness. A claim
    that HAS the point is refused here for the opposite and equally good
    reason, so being both is not a stronger claim, it is two claims.
    """
