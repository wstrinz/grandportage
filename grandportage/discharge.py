"""Discharge moves: from a refused edge to a named work item.

This is the part that makes a campaign drive itself, and it is worth being
precise about how little intelligence is involved.  It is a lookup table.

A typed failure is localized and named: "edge E8 is BASE_EXTENSION and the
emptiness it carries has a field-relative certificate" is not a vague sense
that something is off, it is a work item with an address.  Each table cell has
a canonical next move, so the loop is:

    compute -> type the step -> checker localizes the refusal ->
    look up the move -> dispatch -> repeat

That is a work queue derived from a type error, which is how a build system
with autofix behaves.  What makes it work is that the failure is specific
enough to name the move; vague failures do not generate work.

The honest limit, and it should be read every time this module is quoted: THIS
ROUTES ATTENTION TO WHERE AN EQUATION IS MISSING.  IT DOES NOT FIND THE
EQUATION.  Every actual advance in the source campaign was an equation, and the
only claim here is that a typed graph shortens the search for which one.
"""

from . import kernel as K

_GENERIC = ("Re-examine this step: the transport it needs is not licensed by "
            "the type it was given.  Either the type is wrong (prove the "
            "stronger relation) or the step is wrong (do not take it).")

# ---------------------------------------------------------------------------
# WHAT KIND OF MOVE CLOSES AN OBLIGATION.
#
# CEGAR-shaped: a refusal should name the refinement that legitimately resolves
# it, and only that refinement should count.  The pieces existed and could not
# talk to each other -- the discharge for GI-G4-CAP-EXTRAPOLATION read
#
#     "DISCHARGE BY DERIVING Delta'_4, not by naming a relaxation"
#
# which says exactly the right thing and enforces nothing, because it is prose.
# A live run then discharged it by naming a relaxation.
#
# So discharges gain a KIND, and a baseline entry may pin which kinds it will
# accept.  An obligation recorded as `admits: ["DERIVE"]` cannot be cleared by
# retyping: the only exit is the one the obligation asked for.
#
#   DERIVE   supply the missing mathematics.  The refusal goes away because the
#            thing it was waiting for now exists.
#   RETYPE   the relation was mis-stated and the true one licenses the step.
#            Legitimate, and the move most likely to be reached for when the
#            mathematics is hard.
#   ACCEPT   carry it deliberately, in the open, with a reason.
#
# `RETYPE` READS AS "I CHANGED THE TYPE FIELD" AND DOES NOT MEAN THAT, which is
# a naming problem worth recording rather than a bug.  A campaign retyped an
# UNTYPED edge to RESTRICTION -- literally editing the `type` field -- and its
# own prose says "and this is the retype".  The correct kind was DERIVE: the
# edge had never been MIS-STATED, its `why` described the step correctly, and
# what it lacked was a vocabulary word that meant "drops inequalities".  Its own
# discharge_hint had asked for exactly that, so the refusal went away because
# the thing it was waiting for now existed.
#
# The author, reading `RETYPE` the natural way and finding it not quite right,
# reached past both and wrote `RELICENSE` -- a CLAIM kind, which edges do not
# take, and which was silently accepted until edges got their supersession
# validated.  Three plausible words, one correct, and the incorrect ones are
# incorrect for reasons the names actively obscure.
#
# Renaming is the obvious repair and is not free: `admits` pins in live
# baselines name these strings, so a rename rewrites recorded obligations in
# campaign logs.  Left as a decision, flagged here so it is not rediscovered.
# ---------------------------------------------------------------------------
DERIVE = "DERIVE"
RETYPE = "RETYPE"
ACCEPT = "ACCEPT"
DISCHARGE_KINDS = (DERIVE, RETYPE, ACCEPT)

# (edge type, direction, claim kind) -> the canonical next move.
MOVES = {
    (K.BASE_EXTENSION, K.ALONG, K.EMPTY): (
        "Produce a certificate that BASE-CHANGES -- exhibit 1 in the ideal over "
        "the base field, or a resultant nonzero in the base field -- and the "
        "emptiness transports unchanged.  If no such certificate exists, the "
        "claim is a fact about {src_field} only: restate it at that scope and "
        "stop consuming it as geometric emptiness.  Check whether the target "
        "model has points over the larger field before spending anything: if "
        "it does, the conclusion is not merely unproved, it is false."),
    (K.BASE_EXTENSION, K.AGAINST, K.NONEMPTY): (
        "REQUIRED: a point whose coordinates lie in the smaller field.  A "
        "point over the larger field need not descend, so either exhibit one "
        "downstairs or accept the witness as a statement about the larger "
        "field alone.\n"
        "  ILLUSTRATION, which may not be your case: in the source campaign "
        "the obstruction to descent was a square class, and for arithmetic "
        "problems it is often a square class or a Galois cocycle.  If your "
        "obstruction is something else -- rounding, a projection, a numerical "
        "solver's output -- the requirement above is still exactly what has to "
        "be met."),
    (K.BASE_EXTENSION, K.ALONG, K.PREDICATE): (
        "A predicate proved over the small field need not hold over the "
        "extension.  Re-derive it over the extension, or show it is defined by "
        "equations with coefficients in the base and is stable under the "
        "Galois action."),

    (K.NECESSARY_CONDITION, K.ALONG, K.PREDICATE): (
        "The predicate holds in the tighter model; you are importing it into "
        "the looser one.  Either re-derive it in the target model from that "
        "model's own equations, or exhibit the converse and retype the edge "
        "EQUIVALENCE.  Until one of those, the predicate is a fact about "
        "{src} and every conclusion drawn from it in {dst} is unsound."),
    (K.NECESSARY_CONDITION, K.AGAINST, K.NONEMPTY): (
        "The witness lives in the relaxation, not in the source.  Lift it to "
        "{dst} explicitly -- that means satisfying the conditions the edge "
        "DROPS ({drops}) -- or read it as what it soundly is: a hard stop on "
        "emptiness spend for {src} and nothing more."),
    (K.NECESSARY_CONDITION, K.ALONG, K.EMPTY): (
        "Emptiness of the tighter model says nothing about the looser one; the "
        "looser model is where the counterexamples would live.  If you need "
        "{dst} closed, find an equation that holds in {dst}."),

    (K.IMAGE_CLOSURE, K.AGAINST, K.NONEMPTY): (
        "ARTIFACT-CANDIDATE, not a solver-time problem.  A point of the "
        "Zariski closure need not lift to the image (Chevalley).  Either "
        "exhibit a lift, or refine the model by the open conditions that cut "
        "the constructible image out of its closure.  Do not buy more solver "
        "time for this cell: no monomial order and no amount of RAM can turn "
        "a closure point into a preimage."),
    (K.IMAGE_CLOSURE, K.ALONG, K.PREDICATE): (
        "Only Zariski-CLOSED conditions extend from an image to its closure.  "
        "Show the predicate is closed (it is cut out by equations, with no "
        "strict inequality and no nonvanishing side condition) and declare it "
        "so, or restrict the conclusion to the image itself."),

    (K.IMAGE_CLOSURE, K.ALONG, K.EMPTY): (
        "The kernel refuses this cell generically, from V(src) subset V(dst) "
        "alone.  See KNOWN_CONSERVATISM: closure of the empty set is empty, so "
        "the step is in fact sound and this is a deliberate false refusal on an "
        "unreachable cell.  If you have genuinely computed the constructible "
        "image and found it empty, record it as a note and override."),

    (K.SPECIALIZATION, K.ALONG, K.EMPTY): None,     # filled below
    (K.SPECIALIZATION, K.AGAINST, K.EMPTY): None,
    (K.SPECIALIZATION, K.ALONG, K.NONEMPTY): None,
    (K.SPECIALIZATION, K.AGAINST, K.NONEMPTY): None,
    (K.SPECIALIZATION, K.ALONG, K.PREDICATE): None,
    (K.SPECIALIZATION, K.AGAINST, K.PREDICATE): None,
}

# Filled after the move texts are defined, below.
_CONDITIONAL_IDENTITY_CELLS = [
    (K.EQUIVALENCE, K.ALONG, K.IDENTITY),
    (K.EQUIVALENCE, K.AGAINST, K.IDENTITY),
    (K.NECESSARY_CONDITION, K.ALONG, K.IDENTITY),
    (K.SPECIALIZATION, K.ALONG, K.IDENTITY),
    (K.SPECIALIZATION, K.AGAINST, K.IDENTITY),
    (K.RESTRICTION, K.ALONG, K.IDENTITY),
]

_SPECIALIZATION_MOVE = (
    "REQUIRED: redo the computation in the target characteristic, or produce a "
    "good-reduction / flatness argument at this prime that makes the step an "
    "EQUIVALENCE.  No relaxation type carries an existence statement across a "
    "change of characteristic, and that is a theorem rather than a gap in this "
    "table.\n"
    "  FIRST, THOUGH -- CHECK THE TYPE IS RIGHT.  SPECIALIZATION means the "
    "CHARACTERISTIC changes, and nothing else.  It is not a general 'restricted "
    "to a sub-case' type, and it has been reached for that way: running 3 of "
    "527 indices is not a specialization.  For a case split declare a "
    "`partition`; for dropping conditions use NECESSARY_CONDITION.  This row "
    "is uniformly NO, so a mistyped edge here gets the right verdict for the "
    "wrong reason and the advice below will not fit.\n"
    "  ILLUSTRATION: Fano is empty over Q and nonempty over F_2, non-Fano the "
    "reverse, so all four existence cells have explicit counterexamples.  A "
    "mod-p run is RECONNAISSANCE: it may direct effort, it may never close a "
    "case.")

for _key in list(MOVES):
    if MOVES[_key] is None:
        MOVES[_key] = _SPECIALIZATION_MOVE

# The three cells v0.2 made conditional.  Without these rows every one of them
# fell through to `_IDENTITY_MOVE`, which names the DENOMINATOR-FREE condition
# -- so an edge already declared POLYNOMIAL was told to make its map polynomial.
# A work queue pointing at a locked door is the same defect
# `_UNTYPED_TRAFFIC_MOVE` was written to fix, and it invites exactly the
# retype-to-silence-the-warning move that REVIEW.md names as failure mode 2.
_RING_ISO_MOVE = (
    "This EQUIVALENCE is not declared a ring isomorphism, and a rewriting is a "
    "statement about FUNCTIONS. The converse that earns an EQUIVALENCE is "
    "evidence about POINTS, and points do not determine the coordinate ring: "
    "V(x^2) and V(x) have the same single solution while `x = 0` holds in one "
    "and is false in the other.\n"
    "  If {src} -> {dst} really is invertible ON THE COORDINATE RING -- a "
    "linear change of variables, a re-presentation of the same ideal -- declare "
    "`ring_iso: true` and say what the inverse is.\n"
    "  If the step is a saturation, a radicalization, or anything else that "
    "preserves solutions while changing the ring, then it does NOT carry "
    "rewritings, and the other three claim kinds still travel across it "
    "unaffected.")

_AMBIENT_IDENTITY_MOVE = (
    "This rewriting is recorded as DERIVED from {src}'s own equations, and "
    "this step DROPS equations, so it cannot be assumed to survive: `x = 0` is "
    "valid in k[x]/(x) and false in k[x].\n"
    "  Three ways forward. (1) If the rewriting is really a DEFINITION -- a "
    "substitution or change of variables true before any of {src}'s equations "
    "are imposed -- it is AMBIENT, and `cas_classify_identity` will confirm "
    "that by reducing LHS - RHS to 0 in the polynomial ring. (2) If it genuinely "
    "follows from equations that {dst} KEEPS, that is sound but is not what the "
    "claim-level origin can express; see KNOWN_CONSERVATISM. (3) Otherwise use "
    "the rewriting only in {src}, where it holds.")

_INTEGRAL_IDENTITY_MOVE = (
    "Reducing a rewriting into characteristic p needs TWO things, and which "
    "one you are missing decides what to do.\n"
    "\n"
    "  (1) COEFFICIENTS INTEGRAL AT p. A property of the claim, not of the "
    "map: `d2 = h_2 - (3/8)h_1^2` travels a polynomial map and does not reduce "
    "mod 2. Clear the denominators and record what that costs, or declare "
    "`integral: true` once you have checked no coefficient has p in its "
    "denominator, or keep the rewriting in characteristic 0.\n"
    "\n"
    "  (2) AN AMBIENT ORIGIN. Integral coefficients are not enough on their "
    "own, because a DERIVED rewriting also rides on the derivation that "
    "produced it, and THAT can carry the p. In Z_(p)[x]/(px) the relation "
    "`x = 0` holds on the generic fibre with coefficient 1, and is false mod p "
    "-- because you get it from x = (1/p)*(px). Equivalently x is p-torsion.\n"
    "  The move is to re-derive the rewriting AMBIENTLY: show LHS - RHS "
    "reduces to 0 in the polynomial ring itself, before any of {src}'s "
    "equations are imposed. `cas_classify_identity` decides that outright and "
    "returns AMBIENT when it holds, so this is a computation rather than a "
    "declaration. If it comes back DERIVED, the rewriting genuinely depends on "
    "equations whose integrality this kernel cannot see, and the honest moves "
    "are to exhibit a p-integral certificate by hand and record it as a note, "
    "or to keep the rewriting in characteristic 0.")

_IDENTITY_MOVE = (
    "Rewriting a dictionary across this edge needs a DENOMINATOR-FREE map, and "
    "this edge's map is {map_kind}.  Either exhibit the rewriting as a "
    "polynomial transform (in the source campaign the row transform was "
    "polynomial and that single attribute separated the sound leg from the "
    "unsound one), or clear denominators and record what that costs.")

_ZARISKI_DENSE_MOVE = (
    "An IDENTITY established only on the restricted region pushes forward when "
    "a polynomial vanishing there vanishes on the whole target -- which needs "
    "{dst} IRREDUCIBLE with its REAL points Zariski-dense in it.\n"
    "  If that holds, declare `zariski_dense: true` on this edge and the "
    "rewriting crosses.  It usually does hold: a nonempty Euclidean-open "
    "subset of an irreducible real variety with a smooth real point is "
    "Zariski-dense in it.\n"
    "  BEFORE DECLARING IT, check the target is not a case where it fails.  "
    "V(x^2 + y^2) over R has real locus a single point; `x = 0` holds on every "
    "open piece of that locus and is false on the variety.  A REDUCIBLE target "
    "fails for a different reason: an open piece can miss a whole component, "
    "and a relation holding on one component says nothing about the others.\n"
    "  THIS IS NOT THE DENOMINATOR QUESTION.  A restriction changes no "
    "coordinates, so no map_kind, no substitution and no clearing of "
    "denominators is involved anywhere in this cell.  Do not spend anything on "
    "making the map polynomial; it already is the identity.")

_RESTRICTION_PREDICATE_MOVE = (
    "THIS IS THE GENERIC-VERSUS-GLOBAL BOUNDARY, and the refusal is the point "
    "of the type rather than an obstacle to route around.\n"
    "  A predicate proved at every point of {src} is silent about the points "
    "of {dst} outside it.  Taking a stability condition, a bound or a "
    "recovery result established on a positivity cone and stating it of "
    "the ambient model is the standard applied error: the result holds off an "
    "exceptional locus, and the locus is a denominator nobody wrote down.\n"
    "  There is no side condition that repairs this and no certificate to "
    "produce.  Either state the predicate AT {src}, where it is true and where "
    "its users can see the hypothesis -- or prove it again at {dst}, which is "
    "a different and usually harder theorem.\n"
    "  If what you want is the exceptional locus itself, that is a separate "
    "model: declare it, and record what is true there.")

# RESTRICTION/ALONG/IDENTITY NO LONGER REFUSES, so it has no move.  The cell
# was gated on a declared `zariski_dense` until the condition was found both
# insufficient (the nodal cubic satisfies it and breaks the conclusion) and
# beside the point (a restriction shares its ideal, so the identity is the same
# statement at both ends).  `_ZARISKI_DENSE_MOVE` is kept below as the record
# of advice this project once gave and has withdrawn -- it told callers to
# declare a field that now gates nothing, which is worse than no advice.
MOVES[(K.RESTRICTION, K.ALONG, K.PREDICATE)] = _RESTRICTION_PREDICATE_MOVE
MOVES[(K.RESTRICTION, K.ALONG, K.EMPTY)] = (
    "Emptiness of a restricted region says nothing about the model it sits in: "
    "the points ruled out by the inequalities are exactly the ones that were "
    "never examined.  Either re-run the emptiness argument at {dst} without "
    "the inequality constraints, or state the emptiness at {src} and stop "
    "consuming it as emptiness of {dst}.  Check first whether {dst} has points "
    "outside the region -- if it does, the wider claim is not merely unproved, "
    "it is false.")
MOVES[(K.RESTRICTION, K.AGAINST, K.NONEMPTY)] = (
    "A point of {dst} need not satisfy the inequalities that cut out {src} -- "
    "that is what makes this a restriction.  Exhibit a point that DOES satisfy "
    "them (for a positivity cone, check the defining minors are strictly "
    "positive at your witness, not merely nonzero), or keep the witness as a "
    "statement about {dst} alone.")

MOVES[(K.EQUIVALENCE, K.ALONG, K.IDENTITY)] = _RING_ISO_MOVE
MOVES[(K.EQUIVALENCE, K.AGAINST, K.IDENTITY)] = _RING_ISO_MOVE
MOVES[(K.NECESSARY_CONDITION, K.ALONG, K.IDENTITY)] = _AMBIENT_IDENTITY_MOVE
MOVES[(K.SPECIALIZATION, K.ALONG, K.IDENTITY)] = _INTEGRAL_IDENTITY_MOVE
MOVES[(K.SPECIALIZATION, K.AGAINST, K.IDENTITY)] = (
    "A rewriting valid in characteristic p does not lift to characteristic 0, "
    "ever: `p*x = 0` holds identically mod p and is the reduction of nothing. "
    "There is no side condition that repairs this. Re-derive the rewriting in "
    "characteristic 0 from that model's own equations, or keep it where it "
    "holds. A mod-p run is RECONNAISSANCE.")

# Rule-level moves, for findings that are not a transport refusal.
RULE_MOVES = {
    # An OPEN PREMISE SLOT.  Nothing was traversed, so no transport cell has an
    # opinion and no side condition would help -- the argument names a claim
    # the graph does not contain, deliberately, because entering a claim
    # nobody has established would have been the worse of the two escapes.
    "(missing)": (
        "SUPPLY THE MISSING CLAIM, or stop asserting the conclusion.  This is "
        "not a transport refusal and there is no edge to retype: the argument "
        "declares a premise it does not have, and says so on purpose.\n"
        "  The slot names the KIND and the MODEL it needs. Establish exactly "
        "that and record it, and this argument becomes checkable in the "
        "ordinary way.\n"
        "  If it cannot be established, that is the finding -- and the slot is "
        "how it stays visible. Do not close it by writing the claim as though "
        "it held; a graph that states a falsehood is worse than one that "
        "states a gap. Withdraw the conclusion instead, or weaken it to "
        "something the premises you DO have will carry."),
    # A CASE SPLIT THAT DOES NOT COVER ITS PARENT.  Also not a transport
    # refusal, and pointedly not the same remedy as a missing premise: nothing
    # is absent from the graph, the argument is simply not yet an argument
    # about the parent.
    "(partition)": (
        "COVER EVERY BRANCH, or conclude about a branch instead of the parent. "
        "A case split reaches the parent only when NO case is left open -- one "
        "branch dying says nothing whatever about the others, which is why no "
        "single edge licenses this step and the partition carries it.\n"
        "  Settle the branches the finding names, or narrow the conclusion to "
        "the branches you have. Both are honest; asserting the parent from a "
        "proper subset of its cases is not.\n"
        "  If a branch cannot be settled, declare it as an OPEN SLOT rather "
        "than omitting it. The coverage verdict is identical -- a slot settles "
        "nothing, deliberately -- but the graph then says WHICH case is open "
        "and why, instead of leaving a reader to diff the branch list against "
        "the premises.\n"
        "  And check the exhaustiveness claim is among the premises. That the "
        "branches cover the parent is itself a claim, and it is the one a case "
        "analysis most often assumes."),
    "TAINT": (
        "This model was BUILT by a step the type system refuses, so every "
        "conclusion drawn inside it is suspect even where its own transport is "
        "licensed.  Discharge the building inference first -- that is the only "
        "repair.  Re-deriving the downstream claims in an untainted model is "
        "the fallback, and it is a full redo, not a patch."),
    "COVERAGE": (
        "Declare a component on axis {axis} at {missing}, or state positively "
        "that the model imposes nothing there and accept that conclusions read "
        "at those indices are unbounded.  Look first at what the model already "
        "imposes and reads there -- the missing condition is usually visible in "
        "the divisor of a gauge the model uses but does not constrain."),
    "REFINEMENT-TYPE": (
        "A refinement (src = dst + equations) is a NECESSARY_CONDITION edge "
        "read AGAINST the arrow.  Retype it, or -- if it is genuinely not a "
        "refinement -- drop the `refinement` flag and say what the step really "
        "does."),
    K.UNTYPED: (
        "Name the relaxation.  What does this step LOSE?  Nothing -> "
        "EQUIVALENCE (and you must be able to exhibit the converse).  "
        "Equations -> NECESSARY_CONDITION.  A larger coefficient field -> "
        "BASE_EXTENSION.  An elimination or a projection -> IMAGE_CLOSURE.  "
        "A change of characteristic -> SPECIALIZATION.  Until it is named, no "
        "conclusion crosses this edge."),
}

# The discharge for TRAFFIC over an untyped edge, as opposed to the untyped
# edge itself.
#
# The first version offered only "name the relaxation", and a first-time user
# pointed out that this is THE ONE EXIT THAT IS CLOSED BY CONSTRUCTION: if they
# could name the relaxation there would be no obligation to record.  They were
# doing something the design intends -- recording a residual obligation AS a
# type error, which is exactly the shape of the four obligations already in
# their graph -- and the tool answered with a wall whose only signposted door
# was locked.
#
# So both moves are named.  The order matters: typing it is still the real
# repair, and accepting is explicitly framed as carrying a debt in the open
# rather than as making a warning go away.
_UNTYPED_TRAFFIC_MOVE = (
    "You have drawn a conclusion across a step whose relaxation is not named, "
    "so nothing licenses it.  TWO legitimate moves:\n"
    "  (1) TYPE THE EDGE, if you can.  What does {src} -> {dst} LOSE?  "
    "Nothing (converse exhibitable) -> EQUIVALENCE.  Equations -> "
    "NECESSARY_CONDITION.  A larger field -> BASE_EXTENSION.  An elimination "
    "or projection -> IMAGE_CLOSURE.  A change of characteristic -> "
    "SPECIALIZATION.  Getting the DIRECTION right is part of this and is a "
    "real claim about which model holds more information.\n"
    "  (2) CARRY IT DELIBERATELY.  If the point of recording this was to put a "
    "residual obligation ON THE RECORD as a type error -- a legitimate and "
    "intended use -- accept it with a reason:\n"
    "        gp accept --only {fid} -m \"<why it cannot be typed yet>\"\n"
    "      It stops blocking, stays visible in `gp check` forever, and the "
    "reason lands in a file a reviewer reads.  This is carrying a debt in the "
    "open, NOT clearing it.\n"
    "  The edge already records why it is untyped: {debt_why}")

# Cells where the kernel is knowingly stricter than the mathematics, kept as
# data so that "we refuse this soundly" and "we refuse this out of caution" are
# never confused, and so that removing one is a deliberate act.
KNOWN_CONSERVATISM = [
    {
        "cell": (K.IMAGE_CLOSURE, K.ALONG, K.EMPTY),
        "kernel_says": False,
        "truth": "sound -- the closure of the empty set is empty",
        "why_kept": (
            "The cell is derived from the generic inclusion V(src) subset "
            "V(dst), which does not license ALONG-EMPTY for any lossy type.  "
            "Special-casing it would make the closure row inconsistent with "
            "the rule the other rows follow, for a cell that is unreachable in "
            "practice: asserting the constructible image is empty requires "
            "computing the constructible image, which is the thing nobody "
            "computes.  Inherited from whetstone_dag.py unchanged so that the "
            "retrodiction gate stays an exact regression."),
    },
    {
        "cell": (K.NECESSARY_CONDITION, K.ALONG, K.IDENTITY),
        # The cell is CONDITIONAL, not a flat False: it licenses an AMBIENT
        # rewriting and refuses a DERIVED one.  The conservatism is in the
        # condition, not in the cell being closed.
        "kernel_says": K._AMBIENT_IDENTITY,
        "truth": (
            "AMBIENT is SUFFICIENT but not NECESSARY.  The exact condition for "
            "a rewriting at M to survive into a looser M' is that LHS - RHS "
            "lies in M''s ideal.  An identity that is DERIVED at M can still "
            "cross, whenever it follows from equations M' KEEPS.  Verified: "
            "`x = 0` is DERIVED at V(x,y) and reduces to 0 at V(x)."),
        "why_kept": (
            "AMBIENT is the only claim-level answer that is good for EVERY "
            "edge -- a universal certificate -- and the exact test is "
            "edge-relative.  Going edge-relative needs the TARGET'S IDEAL, and "
            "a model in this system currently carries desc, cite, chart, "
            "universe, declares, touches and reads: it is a DESCRIPTION, not "
            "an object with equations.  Requiring machine-readable ideals on "
            "every model is a change to what a model IS, not a kernel tweak.\n"
            "  Cost so far: zero.  Two IDENTITY claims exist across the whole "
            "corpus -- CL-KSYZ-ID and CL-DICT, both AMBIENT, both licensed -- "
            "and none at all in the matroid domain, the gamma-window graph or "
            "the live first-run campaign.  This conservatism has never once "
            "refused anything.\n"
            "  THE UPGRADE PATH, when a real false refusal appears: put the "
            "evidence on the INFERENCE, not the model.  An inference declares "
            "that it checked the difference lies in the target's ideal, with "
            "the computation attached, and that unlocks this one cell.  Same "
            "shape as `certificate` on an EMPTY claim: one optional field, no "
            "new notion of model.  Do NOT reach for this before a campaign "
            "actually hits the refusal -- the whole point of registering the "
            "conservatism is that it is visible when it starts to bite."),
    },
    {
        # THE UPGRADE THIS ENTRY SPECIFIED HAS LANDED, so the cell is no
        # longer a blanket refusal and this row records a DISCHARGED
        # conservatism rather than a live one.
        #
        # The entry stood since v0.2 saying the refusal "is a false refusal
        # only for an existential nonemptiness, WHICH NOTHING HAS YET
        # RECORDED", and prescribed the repair in advance: a claim-level flag
        # making this ONE cell conditional. A fourth domain then recorded the
        # first existential nonemptiness -- a toric phase asserted nonempty
        # because its class is nonzero in the Chow ring, which forces a point
        # without producing one. Trigger named before the fact, condition met,
        # repair implemented as written.
        #
        # It stays in the register because the CONSERVATISM is still real for
        # a witness claim, which is every other claim in the corpus: that
        # refusal is Chevalley and is not going anywhere.
        "cell": (K.IMAGE_CLOSURE, K.AGAINST, K.NONEMPTY),
        "kernel_says": "existential",
        "truth": (
            "Sound under the EXISTENTIAL reading of NONEMPTY, unsound under the "
            "WITNESS reading, and the table can encode only one.  If NONEMPTY "
            "means 'some point exists' then cl(S) nonempty implies S nonempty, "
            "because cl(empty) = empty -- the exact contrapositive of the "
            "IMAGE_CLOSURE/ALONG/EMPTY row above, which is registered here for "
            "the same reason.  If it means 'here is the point p' it is false: "
            "0 lies in the closure of G_m and not in G_m, which is Chevalley."),
        "why_kept": (
            "The witness reading is pinned (see kernel.NONEMPTY) because it is "
            "the one every claim in the corpus actually makes, and the one this "
            "cell's discharge is written for -- 'exhibit a lift' is advice to "
            "someone holding a point, not to someone holding an existence "
            "proof.  So the refusal is right for every claim the system has "
            "ever carried and is a false refusal only for an existential "
            "nonemptiness, which nothing has yet recorded.\n"
            "  FOUND BY INDEPENDENT REVIEW, and note what was wrong: the CELL "
            "was right and the ARGUMENT for it was not.  The Gate 0 row refuted "
            "'this specific point lifts' while the cell as stated said "
            "something weaker.  No test could have caught it, because a test "
            "checks a verdict and not a reason -- which is the whole argument "
            "for the ledger carrying prose a human reads.\n"
            "  UPGRADE, when an existential claim first appears: a claim-level "
            "`existential` flag making this ONE cell conditional.  Not a second "
            "claim kind, which would add ten rows to distinguish one."),
    },
]

# THE MIRROR OF THE ABOVE, and its absence is why a false licence survived.
#
# KNOWN_CONSERVATISM registers cells where the kernel is STRICTER than the
# mathematics.  There was no register for the opposite -- a cell knowingly
# LOOSER -- so when BASE_EXTENSION/AGAINST/IDENTITY was identified as licensing
# a false descent, the admission went into a test docstring and appeared in no
# `gp check`, no `gp table`, and no design document.  It then survived a review
# that was specifically hunting it, and an external reviewer had to find it
# again from the mathematics.
#
# This list is EMPTY, and that is the point: that cell was FIXED rather than
# registered.  The slot exists so the next one cannot hide in a docstring, and
# `gp table` prints both registers, so a reader sees "we refuse this out of
# caution" and "we license this knowing better" side by side -- or sees that the
# second is empty.
#
# AN ENTRY HERE IS A BUG WITH A DEADLINE, NOT A DESIGN DECISION.  It means the
# tool will confidently license something its own authors believe is false,
# which is this project's stated failure mode occurring inside the project.
KNOWN_UNSOUND = []


def discharge_for(rule_or_type, direction=None, kind=None, graph=None,
                  edge=None, axis=None, missing=None, fid=None,
                  traffic=False, hints=()):
    """The canonical next move for a finding.  Never returns empty.

    `traffic=True` means "a conclusion was drawn ACROSS this edge", as opposed
    to "this edge exists and is untyped".  The two need different advice and
    conflating them is what produced a discharge naming only the closed exit.
    """
    if rule_or_type == K.UNTYPED and traffic:
        move = _UNTYPED_TRAFFIC_MOVE
    elif rule_or_type in RULE_MOVES:
        move = RULE_MOVES[rule_or_type]
    else:
        move = MOVES.get((rule_or_type, direction, kind))
        if move is None and kind == K.IDENTITY:
            move = _IDENTITY_MOVE
        if move is None:
            move = _GENERIC

    fields = {
        "src": "(source)", "dst": "(target)", "drops": "(undeclared)",
        "map_kind": "(unknown)", "src_field": "its own field",
        "axis": axis or "(axis)",
        "missing": ", ".join(str(m) for m in (missing or [])) or "(indices)",
        "fid": fid or "<finding id>",
        "debt_why": "(none recorded)",
    }
    if edge:
        fields["src"] = edge.get("src", fields["src"])
        fields["dst"] = edge.get("dst", fields["dst"])
        fields["map_kind"] = edge.get("map_kind", fields["map_kind"])
        drops = edge.get("drops") or []
        fields["drops"] = "; ".join(drops) if drops else "(none declared)"
        fields["debt_why"] = edge.get("debt_why") or "(none recorded)"
        if graph is not None:
            srcm = graph.models.get(edge.get("src")) or {}
            fields["src_field"] = srcm.get("field") or "its own field"
    try:
        move = move.format(**fields)
    except (KeyError, IndexError):
        pass
    # AN EDGE MAY SUPPLY WHAT THE TABLE CANNOT KNOW.
    #
    # Every move above is keyed to a CELL, so it can state the requirement
    # exactly and can only illustrate the remedy generically.  T5 watched that
    # go wrong twice in four findings: Galois cocycles offered for a
    # floating-point rounding failure, mod-p flatness for an index restriction.
    # The refusals were right and the advice was for a different problem.
    #
    # The requirement belongs to the cell and stays there.  The remedy belongs
    # to the campaign, and the campaign is the only thing that knows it -- so
    # an edge can say what would actually close a refusal across it, and that
    # is appended rather than replacing the requirement.
    # EVERY OBJECT INVOLVED, not only the edge.
    #
    # THE ONE ARTIFACT WITH EVIDENCE OF WORKING.  A campaign returning cold
    # after a context boundary reported that the `discharge_hint` written on an
    # edge by the previous session "came back verbatim in every refusal, and it
    # named the remedy precisely enough to execute", and called it "the only
    # artifact in the campaign that did real cross-session handoff work.
    # Nothing in the prose files did that."
    #
    # The same session found that every prose claim about the tool's vocabulary
    # had ROTTED within one session, while this string had not -- because it is
    # attached to the object it is about and surfaced at the moment the object
    # blocks you, instead of sitting in a file somebody has to think to open.
    #
    # In Cognitive Dimensions terms this is SECONDARY NOTATION: author-supplied
    # annotation the system does not interpret.  The finding is that the
    # secondary notation outperformed every piece of primary notation for
    # handoff, which is a known phenomenon with a known implication -- support
    # it deliberately rather than treating it as decoration.  Only edges could
    # carry one.  Now anything can.
    for label, text in (hints or ()):
        move += "\n  FOR THIS %s, the campaign says: %s" % (label.upper(), text)
    if edge and edge.get("discharge_hint"):
        move += ("\n  FOR THIS EDGE, the campaign says: %s"
                 % edge["discharge_hint"])
    return move
