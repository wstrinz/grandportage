"""RETRODICTION GATE for the family object -- written BEFORE it exists.

The classification results below are real and already written down in prose, in
two independent campaigns.  The question this file decides is not "does the
design work" but "does each rule catch its own error", and each rule is
required to earn its place by catching one.

    injected error                          must be caught by
    ------------------------------------    ------------------
    evidence read as proof (852 vs 368)     DIRECTION
    "8 of 9" read as 8 open rows            CROSS-CUT
    a residue asserted, not derived         COVERAGE
    a count with no completeness claim      ENUMERATION

A rule that cannot catch its own injected error does not ship.  That is the
whole point of writing this first: the alternative is deciding by taste whether
`sound_direction` is worth a required field, and taste is what the retrodiction
gate exists to replace.

THE TWO SOURCES.

n = 4 LSEM census.  1567 isomorphism classes of mixed graphs on 4 nodes,
34,752 labelled.  The triage is a TREE, not a partition:

    1567 --+-- finite-to-one   347 --+-- HTC-settled       343
           |                         +-- residue             4   <- the result
           +-- not f2o       1220 --+-- forced by counting  852   <- a PROOF
                                    +-- rank-deficient      368   <- EVIDENCE

The last split is the one that matters.  Full Jacobian rank at ONE rational
point PROVES generic full rank -- the witnessing minor is a nonzero polynomial.
Rank DEFICIENCY at a point is only evidence.  The campaign knew this and said
so; its prose reports 1220 as one number anyway.

JC(2) frontier.  34 candidate counterexamples, and the class of nine carries
TWO cross-cutting decompositions of the SAME nine rows -- by status (2 settled
+ 7 open) and by invariant (8 sharing (a,b,t) + 1 at (3,5,4)).  Both settled
rows are (2,3,4) rows, so a result proved for "eight of the nine" buys SIX
genuinely open rows, not eight.  That error was caught by hand.
"""

import pytest

from grandportage import check as C
from grandportage import kernel as K
from grandportage import store as S


def _graph(events):
    g = S.Graph()
    for i, ev in enumerate(events):
        g.apply(ev, lineno=i)
    return g.validate()


def _rules(g, rule):
    return {f.fid: f for f in C.run(g) if f.rule == rule}


# ===========================================================================
# The n = 4 census, as it actually happened.
# ===========================================================================
ENUM = {"ev": "claim", "id": "CL-N4-ENUM", "family": "F-N4",
        "kind": K.PREDICATE,
        "statement": "there are exactly 1567 isomorphism classes; orbit sizes "
                     "sum to 34,752 = 543 labelled DAGs x 64 bigraphs",
        "established_by": "RAN", "ladder": "exact-checked",
        "cite": "n4/census4.py, orbit-sum check"}

FAMILY = {"ev": "family", "id": "F-N4", "count": 1567,
          "desc": "isomorphism classes of mixed graphs on 4 nodes with "
                  "acyclic directed part",
          "enumeration": "CL-N4-ENUM"}

# Split one: is the parametrisation generically finite-to-one?
D_JAC = {"ev": "claim", "id": "D-JAC", "family": "F-N4", "kind": "COUNT",
         "statement": "347 of 1567 classes are generically finite-to-one",
         "splits": "F-N4",
         "groups": [{"id": "G-F2O", "verdict": "generically finite-to-one",
                     "settles": 347},
                    {"id": "G-NOT", "verdict": "not finite-to-one",
                     "settles": 1220}],
         "method": "full Jacobian rank at a random rational point",
         "proves": ["G-F2O"],
         "why": "full rank at ONE rational point proves generic full rank -- "
                "the witnessing minor is a nonzero polynomial. Rank DEFICIENCY "
                "at a point is only evidence.",
         "established_by": "RAN", "ladder": "exact-checked"}

# Split two, inside the finite-to-one group.
D_HTC = {"ev": "claim", "id": "D-HTC", "family": "F-N4", "kind": "COUNT",
         "statement": "343 of the 347 are settled by the half-trek criterion",
         "splits": "G-F2O",
         "groups": [{"id": "G-HTC", "verdict": "rationally identifiable",
                     "settles": 343},
                    {"id": "G-RES", "verdict": "HTC-inconclusive",
                     "settles": 4,
                     "exhibited": ["M-R1", "M-R2", "M-R3", "M-R4"]}],
         "method": "half-trek criterion (Foygel-Draisma-Drton), max-flow",
         "proves": ["G-HTC"],
         "why": "HTC is a SUFFICIENT graphical condition for generic rational "
                "identifiability. Inconclusive means the criterion does not "
                "apply, never that the parameter is unidentifiable.",
         "established_by": "RAN", "ladder": "exact-checked"}

# Split three, inside the NOT-finite-to-one group.  This is the one the prose
# reports as a single number and should not.
D_NOT = {"ev": "claim", "id": "D-NOT", "family": "F-N4", "kind": "COUNT",
         "statement": "of the 1220, 852 are forced by parameter counting",
         "splits": "G-NOT",
         "groups": [{"id": "G-COUNT", "verdict": "npar > 10, forced",
                     "settles": 852},
                    {"id": "G-DEFIC", "verdict": "npar <= 10, rank-deficient "
                                                 "at every point sampled",
                     "settles": 368}],
         "method": "parameter count against dim(Sigma-space) = 10",
         "proves": ["G-COUNT"],
         "why": "npar > dim(Sigma) forces positive-dimensional fibres, which "
                "is a proof in both directions; the remaining 368 rest on "
                "sampling and are a different kind of statement.",
         "established_by": "RAN", "ladder": "exact-checked"}

CENSUS = [FAMILY, ENUM, D_JAC, D_HTC, D_NOT]


def test_the_census_triage_is_expressible_at_all():
    """THE POSITIVE CONTROL, and it comes first for the usual reason: a gate
    that only ever refuses proves nothing about the thing it is gating.

    Every number here is real. If the design cannot hold a classification that
    a campaign already completed, it is the wrong design and no amount of
    catching injected errors redeems it.
    """
    g = _graph(CENSUS)
    assert not C.run(g), (
        "the census's own triage, as performed, must fold and check clean")
    assert g.families["F-N4"]["count"] == 1567


def test_ENUMERATION_a_family_with_no_completeness_claim_is_refused():
    """1567 is an assertion. Somebody counted, and the counting can be wrong.

    The census DID check it -- orbit sizes sum to 34,752 -- and that check had
    nowhere to live, so it appeared in prose and in a `note`. A family-level
    result rests on the enumeration being complete, and an uncounted family
    makes every count downstream of it meaningless.
    """
    naked = [dict(FAMILY)]
    del naked[0]["enumeration"]
    g = _graph(naked + [D_JAC])
    found = _rules(g, C.R_FAMILY)
    assert found, "a family with no enumeration claim must be reported"
    assert "1567" in str(list(found.values())[0].detail)


def test_COVERAGE_a_split_whose_groups_do_not_total_its_parent():
    """The residue asserted rather than derived.

    This is the JC(2) frontier's error in miniature: "32 open" was an assertion
    that happened to total, and five rows settled in the literature were inside
    it. Coverage cannot catch a paper nobody mentioned -- no tool can -- but it
    catches the arithmetic, which is the half that is checkable.

    RECURSIVE, because the census triage is a TREE. `sum(settles) == count`
    over all dispositions was my first rule and it is simply wrong here: D-HTC
    splits a GROUP of 347, not the family of 1567.
    """
    bad = dict(D_HTC)
    bad["groups"] = [{"id": "G-HTC", "verdict": "rationally identifiable",
                      "settles": 343},
                     {"id": "G-RES", "verdict": "HTC-inconclusive",
                      "settles": 9}]        # 343 + 9 != 347
    g = _graph([FAMILY, ENUM, D_JAC, bad])
    found = _rules(g, C.R_FAMILY)
    assert found, "343 + 9 does not total the 347 it claims to split"
    detail = " ".join(f.detail for f in found.values())
    assert "347" in detail and "352" in detail, (
        "it must show the arithmetic, not merely object")


def test_DIRECTION_a_negative_verdict_from_a_positive_only_method():
    """THE 852/368 LINE, and the rule I was least sure earned its keep.

    `D-JAC`'s method proves the POSITIVE verdict only: full rank at one point
    is a nonzero polynomial. Rank deficiency at a point is evidence. So the
    1220 "not finite-to-one" is not established by that method, and the census
    knew it -- the split into 852 forced-by-counting and 368 rest-on-sampling
    exists precisely because the author felt the difference and had nowhere to
    record it.

    Using the negative side of a POSITIVE-only method must be refused.
    """
    g = _graph(CENSUS + [
        {"ev": "claim", "id": "CL-BAD", "family": "F-N4", "kind": K.PREDICATE,
         "statement": "1220 classes are not generically finite-to-one",
         "rests_on": "G-NOT",
         "established_by": "RAN", "ladder": "exact-checked"}])
    found = _rules(g, C.R_DIRECTION)
    assert found, ("a claim resting on the negative side of a POSITIVE-only "
                   "method must be refused")
    f = list(found.values())[0]
    assert "evidence" in f.detail.lower()
    assert "screens is not a method that decides" in f.discharge
    assert "D-JAC" in f.detail and "does not list" in f.detail, (
        "it must name the disposition and the group it declined to prove")


def test_DIRECTION_the_same_claim_is_fine_off_a_BOTH_method():
    """The discrimination, without which the rule is a blanket ban.

    `G-COUNT` -- npar > dim(Sigma-space) -- forces positive-dimensional fibres
    and proves it in both directions. Resting the negative verdict on THAT is
    sound, and the design must say so, or an author learns only that families
    complain.
    """
    g = _graph(CENSUS + [
        {"ev": "claim", "id": "CL-OK", "family": "F-N4", "kind": K.PREDICATE,
         "statement": "852 classes have positive-dimensional fibres",
         "rests_on": "G-COUNT",
         "established_by": "RAN", "ladder": "exact-checked"}])
    assert not _rules(g, C.R_DIRECTION)


# ===========================================================================
# The JC(2) class of nine -- a SECOND domain, and the cross-cut error.
# ===========================================================================
NINE = [
    {"ev": "family", "id": "F-NINE", "count": 9,
     "desc": "the class rows: b0 = 4a0, so C is a monomial and t = 4",
     "enumeration": "CL-NINE-ENUM",
     "members": ["R-5-20-a", "R-5-20-b", "R-8-32", "R-9-36", "R-10-40",
                 "R-75-125", "R-A", "R-B", "R-C"]},
    {"ev": "claim", "id": "CL-NINE-ENUM", "family": "F-NINE",
     "kind": K.PREDICATE,
     "statement": "exactly 9 of GGV5's 34 rows satisfy b0 = 4a0",
     "established_by": "RAN", "ladder": "exact-checked",
     "cite": "corner_atlas.json"},
    # Decomposition one: by status.
    {"ev": "claim", "id": "D-STATUS", "family": "F-NINE", "kind": "COUNT",
     "statement": "2 of the 9 are settled (Moh, both at (5,20)); 7 are open",
     "splits": "F-NINE",
     "groups": [{"id": "G-SETTLED", "verdict": "settled in the literature",
                 "settles": 2, "exhibited": ["R-5-20-a", "R-5-20-b"]},
                {"id": "G-OPEN", "verdict": "open", "settles": 7,
                 "exhibited": ["R-8-32", "R-9-36", "R-10-40", "R-75-125",
                               "R-A", "R-B", "R-C"]}],
     "method": "literature sweep",
     "proves": [],
     "why": "that Moh's rows are ruled out is CITATION-LEVEL; [M] has not been "
            "read here, and a sweep cannot prove a row is open.",
     "established_by": "CITED", "ladder": "claimed"},
    # Decomposition two: by invariant.  CROSS-CUTS the first.
    {"ev": "claim", "id": "D-INVAR", "family": "F-NINE", "kind": "COUNT",
     "statement": "8 of the 9 share (a,b,t) = (2,3,4); (75,125) is (3,5,4)",
     "splits": "F-NINE",
     "groups": [{"id": "G-234", "verdict": "(a,b,t) = (2,3,4)", "settles": 8,
                 "exhibited": ["R-5-20-a", "R-5-20-b", "R-8-32", "R-9-36",
                               "R-10-40", "R-A", "R-B", "R-C"]},
                {"id": "G-354", "verdict": "(a,b,t) = (3,5,4)", "settles": 1,
                 "exhibited": ["R-75-125"]}],
     "method": "corner arithmetic",
     "proves": ["G-234", "G-354"],
     "why": "the invariant is computed from the corner, not inferred",
     "established_by": "RAN", "ladder": "exact-checked"},
]


def test_the_two_decompositions_both_fold_and_both_total():
    """The positive control for cross-cutting: a family may carry SEVERAL
    independent decompositions, each total in its own right. Neither is `the`
    partition, and forcing a choice would have made this campaign inexpressible.
    """
    g = _graph(NINE)
    assert not _rules(g, C.R_FAMILY)


def test_CROSSCUT_a_result_over_one_decomposition_is_not_a_count_in_another():
    """THE ERROR, and it is real: caught by hand in a live project.

    A transfer result was proved for the 8 rows sharing (a,b,t) = (2,3,4) and
    read as buying 8 open rows. Both SETTLED rows are (2,3,4) rows, so it buys
    SIX. The handoff records the correction in its own words:

        "So the 'transfers to eight of the nine' result buys 6 genuinely open
        rows, not 8 -- the other two are already-settled and serve as controls."

    The intersection is computable here ONLY because both groups name their
    members. That is what decides `exhibited` vs a bare count: you cannot
    intersect two decompositions you merely counted.
    """
    g = _graph(NINE + [
        {"ev": "claim", "id": "CL-BUYS", "family": "F-NINE", "kind": "COUNT",
         "statement": "the transfer settles 8 genuinely open rows",
         "rests_on": "G-234", "counts_against": "G-OPEN", "asserts_count": 8,
         "established_by": "RAN", "ladder": "exact-checked"}])
    found = _rules(g, C.R_CROSSCUT)
    assert found, "8 (2,3,4)-rows intersect 7 open rows in only 6"
    f = list(found.values())[0]
    assert "6" in f.detail, "it must compute the true intersection"


def test_CROSSCUT_is_refused_outright_when_the_members_are_only_counted():
    """And when you cannot compute it, you may not assert it.

    At 1567 classes nobody lists members, so no cross-cut claim is available
    there -- correctly. Silently allowing the assertion because the arithmetic
    is unavailable is how "8 of 9" became "8 open rows" in the first place.
    """
    anon = [dict(d) for d in NINE]
    for d in anon:
        for grp in d.get("groups", []):
            grp.pop("exhibited", None)
    g = _graph(anon + [
        {"ev": "claim", "id": "CL-BUYS", "family": "F-NINE", "kind": "COUNT",
         "statement": "the transfer settles 8 genuinely open rows",
         "rests_on": "G-234", "counts_against": "G-OPEN", "asserts_count": 8,
         "established_by": "RAN", "ladder": "exact-checked"}])
    found = _rules(g, C.R_CROSSCUT)
    assert found
    assert "named" in " ".join(f.detail for f in found.values()).lower()
