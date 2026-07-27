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
        "A point over the larger field need not descend.  Exhibit a point with "
        "coordinates in the smaller field, or accept the witness as a statement "
        "about the larger field alone.  If descent is what you need, the "
        "obstruction is usually a square class or a Galois cocycle -- name it."),
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
]

_SPECIALIZATION_MOVE = (
    "NO relaxation type carries an existence statement across a change of "
    "characteristic, and that is a theorem, not a gap in this table: Fano is "
    "empty over Q and nonempty over F_2, non-Fano is the reverse, so all four "
    "existence cells have explicit counterexamples.  Redo the computation in "
    "the target characteristic, or produce a good-reduction / flatness "
    "argument at this prime that makes the step an EQUIVALENCE.  A mod-p run "
    "is RECONNAISSANCE: it may direct effort, it may never close a case.")

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
    "Reducing a rewriting into characteristic p needs its COEFFICIENTS to be "
    "integral at p. That is a property of the claim, not of the map, and a "
    "denominator-free map does not supply it: `d2 = h_2 - (3/8)h_1^2` travels a "
    "polynomial map and does not reduce mod 2.\n"
    "  Clear the denominators and record what that costs, or declare "
    "`integral: true` once you have checked no coefficient has p in its "
    "denominator, or keep the rewriting in characteristic 0.")

_IDENTITY_MOVE = (
    "Rewriting a dictionary across this edge needs a DENOMINATOR-FREE map, and "
    "this edge's map is {map_kind}.  Either exhibit the rewriting as a "
    "polynomial transform (in the source campaign the row transform was "
    "polynomial and that single attribute separated the sound leg from the "
    "unsound one), or clear denominators and record what that costs.")

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
        "cell": (K.IMAGE_CLOSURE, K.AGAINST, K.NONEMPTY),
        "kernel_says": False,
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
                  traffic=False):
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
        return move.format(**fields)
    except (KeyError, IndexError):
        return move
