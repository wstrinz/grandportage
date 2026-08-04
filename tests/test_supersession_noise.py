"""GATE -- findings that outlived the defect they were about.

A campaign found this in the only way it can be found: by reading its own
baseline.  `E-IV-PD` was UNTYPED and carried a DEBT.  `E-IV-PD-RESTRICT` later
superseded it with a real type, which is exactly what the discharge asked for
-- and `UNTYPED-EDGE:E-IV-PD` reported every run afterwards, forever, until the
only way to get a green gate was a baseline entry whose stated reason was
"this cannot be discharged, only carried".  That sentence was false about that
debt.  The same rule that says a hole is worth recording had made a repaired
hole unrecordable as repaired.  `check_parallel_edges` did the same arithmetic
one level up: a fully declared chain of three edges still reported three
parallel edges, and answering the finding's own discharge only bought a
severity downgrade.

Every test here is an ATTACK, not a restatement.  The dangerous half of this
repair is the obvious one -- if a superseded record stops being audited, then
`supersedes` is a delete key, and someone in a hurry gets a clean gate by
declaring one.  So the replacements are given the SAME defect, or an unrelated
one, or none at all and a cycle instead, and the assertion is that each is
still caught.
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


# The two models of the live incident, and the edge between them that was
# declared UNTYPED because the relation genuinely was not known yet.
MODELS = [
    {"ev": "model", "id": "IV", "desc": "the interval-valued system"},
    {"ev": "model", "id": "PD", "desc": "the positive-definite locus"},
]
UNTYPED_OLD = {"ev": "edge", "id": "E-IV-PD", "src": "IV", "dst": "PD",
               "type": "UNTYPED", "why": "the step is not yet characterised",
               "map_kind": K.IDENTITY_MAP,
               "debt_why": "nobody has derived what this inclusion loses"}
RETYPED = {"ev": "edge", "id": "E-IV-PD-RESTRICT", "src": "IV", "dst": "PD",
           "type": "RESTRICTION", "why": "the cut-out subset, same coordinates",
           "map_kind": K.IDENTITY_MAP,
           "supersedes": "E-IV-PD", "discharge_kind": "RETYPE"}

# A claim at PD, so a path read AGAINST E-IV-PD starts where the claim is.
CLAIM = {"ev": "claim", "id": "C-PD", "model": "PD", "kind": K.PREDICATE,
         "statement": "the bound holds on PD"}


def _rider(iid, eid, **extra):
    """An inference that rides `eid` AGAINST, carrying the PD claim to IV."""
    ev = {"ev": "inference", "id": iid, "claim": "C-PD",
          "path": [[eid, K.AGAINST]], "concludes_kind": K.PREDICATE,
          "asserted": "so the bound holds on IV as well"}
    ev.update(extra)
    return ev


# ===========================================================================
# TOMBSTONES. Retraction is lifecycle state, not a replacement object.
# ===========================================================================
def test_minimal_inference_retract_is_not_a_live_successor():
    inference = {"ev": "inference", "id": "I", "claim": "C-PD",
                 "path": [], "concludes_kind": K.PREDICATE,
                 "asserted": "the bound holds on PD"}
    retract = {"ev": "inference", "id": "R-I", "supersedes": "I",
               "discharge_kind": K.RETRACT,
               "why": "the argument was a probe and retains no conclusion"}
    g = _graph(MODELS + [CLAIM, inference, retract])

    assert g.inference_order == ["I"]
    assert "R-I" not in g.inferences
    assert g.inferences["I"]["retracted_by"] == "R-I"
    assert ("inference", "R-I") in g.retractions
    assert "I" not in C.clean_inferences(g, C.run(g))


def test_legacy_full_shaped_inference_retract_folds_as_a_tombstone():
    inference = {"ev": "inference", "id": "I", "claim": "C-PD",
                 "path": [], "concludes_kind": K.PREDICATE,
                 "asserted": "the bound holds on PD"}
    legacy = {"ev": "inference", "id": "R-I", "claim": "C-PD",
              "path": [], "concludes_kind": K.PREDICATE,
              "asserted": "retracted after the clause-zero probe",
              "supersedes": "I", "discharge_kind": K.RETRACT}
    g = _graph(MODELS + [CLAIM, inference, legacy])

    assert g.inference_order == ["I"]
    assert "R-I" not in g.inferences
    assert g.retractions[("inference", "R-I")]["why"].startswith("retracted")


def test_edge_withdraw_retires_a_declaration_without_minting_an_edge():
    withdraw = {"ev": "edge", "id": "W-E", "supersedes": "E-IV-PD",
                "discharge_kind": "WITHDRAW",
                "why": "the models are related by a span, not containment"}
    g = _graph(MODELS + [UNTYPED_OLD, withdraw])

    assert set(g.edges) == {"E-IV-PD"}
    assert g.edges["E-IV-PD"]["withdrawn_by"] == "W-E"
    assert C.withdrawn_edges(g) == {"E-IV-PD"}
    assert not _rules(g, C.R_UNTYPED)


def test_withdrawing_an_edge_does_not_hide_live_traffic():
    withdraw = {"ev": "edge", "id": "W-E", "supersedes": "E-IV-PD",
                "discharge_kind": "WITHDRAW",
                "why": "this relation was never containment"}
    g = _graph(MODELS + [UNTYPED_OLD, CLAIM,
                         _rider("I-RIDES", "E-IV-PD"), withdraw])

    stale = _rules(g, C.R_STALE_PATH)["STALE-PATH:I-RIDES:E-IV-PD"]
    assert stale.severity == C.UNSOUND_PREMISE
    assert "I-RIDES" in C.live_crossings(g, ["E-IV-PD"])


def test_unridden_untyped_failed_containment_is_debt_until_withdrawn():
    models = [
        {"ev": "model", "id": "A", "what": "a", "ring_vars": ["x"],
         "generators": ["x^2"]},
        {"ev": "model", "id": "B", "what": "b", "ring_vars": ["x"],
         "generators": ["x^3"]},
    ]
    edge = {"ev": "edge", "id": "E", "src": "A", "dst": "B",
            "type": K.UNTYPED, "why": "relation not characterised",
            "debt_why": "literal containment may be the wrong relation",
            "containment": "NOT_BY_IDEAL",
            "containment_why": "x^3 does not reduce modulo x^2"}
    g = _graph(models + [edge])
    finding = _rules(g, C.R_CONTAINMENT)["CONTAINMENT:E"]

    assert finding.severity == C.DEBT
    assert "licenses no cell" in finding.detail
    assert "WITHDRAW" in finding.discharge


def test_tombstone_and_live_successor_are_mutually_exclusive():
    withdraw = {"ev": "edge", "id": "W-E", "supersedes": "E-IV-PD",
                "discharge_kind": "WITHDRAW", "why": "not an edge"}
    with pytest.raises(S.GraphError) as exc:
        _graph(MODELS + [UNTYPED_OLD, RETYPED, withdraw])
    assert "Nothing-replaces-it" in str(exc.value)

def test_lifecycle_tombstones_are_visible_on_cli_mcp_and_folded_json(
        tmp_path, capsys):
    import json
    from grandportage import cli, mcp

    inference = _rider("I", "E-IV-PD")
    retract = {"ev": "inference", "id": "R-I", "supersedes": "I",
               "discharge_kind": K.RETRACT,
               "asserted": "argument abandoned"}
    withdraw = {"ev": "edge", "id": "W-E", "src": "IV", "dst": "PD",
                "type": K.UNTYPED, "map_kind": K.IDENTITY_MAP,
                "supersedes": "E-IV-PD",
                "discharge_kind": "WITHDRAW", "why": "not an edge"}
    S.append(MODELS + [UNTYPED_OLD, CLAIM, inference, retract, withdraw],
             str(tmp_path))

    assert cli.main(["--root", str(tmp_path), "show"]) == 0
    shown = capsys.readouterr().out
    assert "[WITHDRAWN by W-E]" in shown
    assert "[RETRACTED by R-I]" in shown

    assert cli.main(["--root", str(tmp_path), "events", "--folded"]) == 0
    folded = json.loads(capsys.readouterr().out)
    assert {t["id"] for t in folded["tombstones"]} == {"R-I", "W-E"}
    assert "R-I" not in folded["inferences"]
    assert "W-E" not in folded["edges"]

    body = mcp.h_portage_show({}, str(tmp_path))["content"][0]["text"]
    assert "[WITHDRAWN by W-E]" in body
    assert "[RETRACTED by R-I]" in body



# ===========================================================================
# VERIFIER PROVENANCE ACROSS SUPERSESSION.
# ===========================================================================
def test_verify_declines_a_live_edge_with_a_superseded_endpoint(tmp_path):
    from grandportage import verify as V

    events = [
        {"ev": "model", "id": "SRC", "what": "source",
         "characteristic": 0, "ring_vars": ["x", "y"],
         "generators": ["x*y"]},
        {"ev": "model", "id": "OLD", "what": "saturation",
         "characteristic": 0, "ring_vars": ["x", "y"],
         "generators": ["y"]},
        {"ev": "model", "id": "NEW", "what": "saturation",
         "characteristic": 0, "ring_vars": ["x", "y"],
         "generators": ["y"], "supersedes": "OLD",
         "discharge_kind": K.RELICENSE},
        {"ev": "edge", "id": "E", "src": "OLD", "dst": "SRC",
         "type": K.NECESSARY_CONDITION, "map_kind": K.POLYNOMIAL,
         "why": "saturation adds equations"},
    ]
    S.append(events, str(tmp_path))

    def never(program, timeout):
        raise AssertionError("a stale endpoint reached the CAS")

    results = V.verify_all(str(tmp_path), record=False, _runner=never)
    assert results
    assert all(verdict == V.UNVERIFIED for _subject, _oid, verdict, _why in results)
    why = "\n".join(item[3] for item in results)
    assert "OLD" in why and "NEW" in why and "repoint" in why
    assert "until that computation has run" not in why

    g = S.load(S.graph_path(str(tmp_path)))
    findings = C.run(g)
    assert any(f.rule == C.R_STALE_MODEL and f.subject == "E" for f in findings)
    assert not [f for f in findings if f.rule == C.R_CONTAINMENT]


def _containment_supersession(changed_dst=False, direct=None):
    models = [
        {"ev": "model", "id": "A", "what": "a", "ring_vars": ["x"],
         "generators": ["x^2"]},
        {"ev": "model", "id": "B", "what": "b", "ring_vars": ["x"],
         "generators": ["x^3"]},
        {"ev": "model", "id": "C", "what": "c", "ring_vars": ["x"],
         "generators": ["x^4"]},
    ]
    old = {"ev": "edge", "id": "E-OLD", "src": "A", "dst": "B",
           "type": K.EQUIVALENCE, "why": "claimed reversible",
           "converse_witness": "a proposed inverse",
           "containment": "NOT_BY_IDEAL",
           "containment_why": "x^3 does not reduce modulo x^2"}
    new = {"ev": "edge", "id": "E-NEW", "src": "A",
           "dst": "C" if changed_dst else "B", "type": K.UNTYPED,
           "why": "relation being repaired", "debt_why": "not classified",
           "supersedes": "E-OLD", "discharge_kind": "RETYPE"}
    if direct:
        new["containment"], new["containment_why"] = direct
    return _graph(models + [old, new])


def test_retyped_edge_cites_predecessor_containment_when_endpoints_match():
    g = _containment_supersession()
    finding = _rules(g, C.R_CONTAINMENT)["CONTAINMENT:E-NEW"]
    assert finding.severity == C.DEBT
    assert "E-OLD" in finding.detail
    assert "x^3 does not reduce" in finding.detail
    assert "author's word" not in finding.detail


def test_containment_evidence_does_not_follow_changed_endpoints_or_beat_direct():
    changed = _containment_supersession(changed_dst=True)
    finding = _rules(changed, C.R_CONTAINMENT)["CONTAINMENT:E-NEW"]
    assert "author's word" in finding.detail
    assert "E-OLD" not in finding.detail

    direct = _containment_supersession(
        direct=("VERIFIED", "checked directly on the successor"))
    assert "CONTAINMENT:E-NEW" not in _rules(direct, C.R_CONTAINMENT)


def test_literal_containment_does_not_flow_into_a_mapped_successor():
    """A coordinate change supersedes the literal-inclusion question itself."""
    g = _graph([
        {"ev": "model", "id": "A", "what": "a", "ring_vars": ["x"],
         "generators": ["x-1"]},
        {"ev": "model", "id": "B", "what": "b", "ring_vars": ["x"],
         "generators": ["x+1"]},
        {"ev": "edge", "id": "E-OLD", "src": "A", "dst": "B",
         "type": K.UNTYPED, "why": "proposed literal relation",
         "debt_why": "not classified", "containment": "NOT_BY_IDEAL",
         "containment_why": "x+1 does not reduce modulo x-1"},
        {"ev": "edge", "id": "E-NEW", "src": "A", "dst": "B",
         "type": K.EQUIVALENCE, "why": "x maps to -x",
         "forward": {"x": "-x"}, "inverse": {"x": "-x"},
         "supersedes": "E-OLD", "discharge_kind": "RETYPE"},
    ])
    assert not _rules(g, C.R_CONTAINMENT)


def test_mapped_predecessor_does_not_suppress_a_literal_successor():
    """Dropping maps creates a fresh literal-inclusion obligation."""
    g = _graph([
        {"ev": "model", "id": "A", "what": "a", "ring_vars": ["x"],
         "generators": ["x-1"]},
        {"ev": "model", "id": "B", "what": "b", "ring_vars": ["x"],
         "generators": ["x+1"]},
        {"ev": "edge", "id": "E-OLD", "src": "A", "dst": "B",
         "type": K.EQUIVALENCE, "why": "x maps to -x",
         "forward": {"x": "-x"}, "inverse": {"x": "-x"}},
        {"ev": "edge", "id": "E-NEW", "src": "A", "dst": "B",
         "type": K.UNTYPED, "why": "now asserted literally",
         "debt_why": "not classified", "supersedes": "E-OLD",
         "discharge_kind": "RETYPE"},
    ])
    finding = _rules(g, C.R_CONTAINMENT)["CONTAINMENT:E-NEW"]
    assert "author's word" in finding.detail


# ===========================================================================
# UNTYPED-EDGE.  The debt that could not be discharged, only carried.
# ===========================================================================
def test_an_untyped_edge_that_was_retyped_stops_reporting_as_live_debt():
    """PROOF that the incident is fixed, with its own positive control.

    Before: the debt was reported whether or not it had been discharged, so
    the finding no longer distinguished the two states of the world it exists
    to distinguish.  A rule that reports the same thing after the repair as
    before it is not measuring the repair.
    """
    open_debt = _graph(MODELS + [UNTYPED_OLD])
    assert "UNTYPED-EDGE:E-IV-PD" in _rules(open_debt, C.R_UNTYPED), (
        "the control has to actually be reported, or this proves nothing")

    discharged = _graph(MODELS + [UNTYPED_OLD, RETYPED])
    assert not _rules(discharged, C.R_UNTYPED), (
        "the debt was discharged BY the retyping; reporting it forever is "
        "what forced a baseline entry saying it could never be discharged")


def test_a_replacement_that_is_also_untyped_is_still_caught():
    """REFUTED: that `supersedes` withdraws the finding rather than the edge.

    The move a tired author makes at the end of a session is to declare the
    successor and not the mathematics.  If withdrawal were about the FINDING,
    replacing an untyped edge with another untyped edge would clear the debt
    while leaving the graph in exactly the state that produced it -- one
    UNTYPED step between the same two models, and now a clean gate.
    """
    g = _graph(MODELS + [UNTYPED_OLD,
        {"ev": "edge", "id": "E-IV-PD-2", "src": "IV", "dst": "PD",
         "type": "UNTYPED", "why": "successor, and no better understood",
         "debt_why": "still nobody has derived what this loses",
         "supersedes": "E-IV-PD", "discharge_kind": "RETYPE"}])
    found = _rules(g, C.R_UNTYPED)
    assert "UNTYPED-EDGE:E-IV-PD-2" in found, (
        "the replacement is audited in its own right; a successor carrying "
        "the same defect must still be reported")
    assert "UNTYPED-EDGE:E-IV-PD" not in found
    assert found["UNTYPED-EDGE:E-IV-PD-2"].severity == C.DEBT


def test_two_edges_superseding_each_other_withdraw_nothing():
    """The adversary's version, and the fold does not refuse it.

    `_apply_edge` requires `discharge_kind` and writes no back-pointer, so
    nothing stops two edges naming each other.  Read as a set -- "every id
    that appears in some `supersedes`" -- both are dead, both findings vanish,
    and the graph they vanish from contains no current edge at all.  Deadness
    has to mean REPLACED BY SOMETHING LIVE or it means deleted on request.
    """
    g = _graph(MODELS + [
        {"ev": "edge", "id": "E-A", "src": "IV", "dst": "PD",
         "type": "UNTYPED", "why": "a", "debt_why": "unknown",
         "supersedes": "E-B", "discharge_kind": "RETYPE"},
        {"ev": "edge", "id": "E-B", "src": "IV", "dst": "PD",
         "type": "UNTYPED", "why": "b", "debt_why": "unknown",
         "supersedes": "E-A", "discharge_kind": "RETYPE"}])
    assert set(_rules(g, C.R_UNTYPED)) == {"UNTYPED-EDGE:E-A",
                                           "UNTYPED-EDGE:E-B"}
    assert "PARALLEL-EDGE:IV->PD" in _rules(g, C.R_PARALLEL), (
        "neither edge was replaced, so they are still two edges joining one "
        "pair of models with nothing saying which binds")


def test_a_dangling_supersession_is_refused_by_the_FOLD():
    """A typo must not withdraw a finding by accident.

    `supersedes: "E-IV-PB"` is one keystroke from the real id and reads, to a
    human skimming, exactly like the repair.

    THE PROTECTION MOVED EARLIER AND GOT LOUDER.  This used to survive the fold
    and be reported by `check_supersession`, which was already enough to stop
    the rule honouring it.  Once supersession resolution moved into `validate()`
    -- where every other cross-reference is checked -- a dangling `supersedes`
    became what it always was: a referentially broken graph, in the same class
    as an inference naming a claim that does not exist.

    A finding can be accepted and carried. A graph whose references do not
    resolve cannot be acted on at all, so refusing it is the honest answer.
    """
    with pytest.raises(S.GraphError) as exc:
        _graph(MODELS + [UNTYPED_OLD,
            {"ev": "edge", "id": "E-IV-PD-RESTRICT", "src": "IV", "dst": "PD",
             "type": "RESTRICTION", "why": "the cut-out subset",
             "supersedes": "E-IV-PB", "discharge_kind": "RETYPE"}])
    assert "not a edge in this graph" in str(exc.value)
    assert "fold it too" in str(exc.value), (
        "the message must say what to do when the older edge is in a log you "
        "have not merged, which is the innocent version of this")


# ===========================================================================
# PARALLEL-EDGE.  A dead edge is not a second opinion.
# ===========================================================================
def test_a_declared_chain_of_three_edges_is_one_edge():
    """PROOF: doing what the discharge asks must change the finding.

    The discharge reads "Name which edge is authoritative. If the newer one
    supersedes the older, say so with `supersedes`."  A campaign that did
    that, twice, still read "3 edges join IV -> PD" on every run -- so the
    rule asked for a declaration and then declined to read it.
    """
    chain = _graph(MODELS + [UNTYPED_OLD, RETYPED,
        {"ev": "edge", "id": "E-IV-PD-NC", "src": "IV", "dst": "PD",
         "type": "NECESSARY_CONDITION", "why": "the inclusion, restated",
         "supersedes": "E-IV-PD-RESTRICT", "discharge_kind": "RETYPE"}])
    assert not _rules(chain, C.R_PARALLEL), (
        "two of the three were replaced by a live edge; one edge joins these "
        "models and the graph says so")

    undeclared = _graph(MODELS + [UNTYPED_OLD,
        {"ev": "edge", "id": "E-IV-PD-NC", "src": "IV", "dst": "PD",
         "type": "NECESSARY_CONDITION", "why": "typed successor"}])
    assert _rules(undeclared, C.R_PARALLEL), (
        "the control: the same two edges with nothing declared between them "
        "are still the hole T1 went through")


def test_a_replacement_parallel_to_a_live_edge_is_still_reported():
    """REFUTED: that superseding ONE of several edges settles the question.

    Declaring a successor answers "which of these two binds" and says nothing
    about a third edge nobody mentioned.  If the count simply dropped the dead
    edge and stopped there, a graph with two live, undeclared, contradictory
    edges between one pair of models would report nothing at all -- and it
    would have got there by declaring a supersession.
    """
    g = _graph(MODELS + [UNTYPED_OLD, RETYPED,
        {"ev": "edge", "id": "E-IV-PD-EQ", "src": "IV", "dst": "PD",
         "type": "EQUIVALENCE", "why": "a second, unrelated route",
         "converse_witness": "the inverse construction"}])
    par = _rules(g, C.R_PARALLEL)["PARALLEL-EDGE:IV->PD"]
    assert "2 edges join" in par.detail
    assert "E-IV-PD-RESTRICT" in par.detail and "E-IV-PD-EQ" in par.detail
    assert "E-IV-PD [" not in par.detail, (
        "the withdrawn edge is not one of the two competing types")


def test_an_edge_that_live_traffic_still_rides_is_not_withdrawn():
    """The quiet version of the attack, and the reason withdrawal is not
    enough on its own.

    Supersession DELIBERATELY DOES NOT REPOINT ANYTHING, so an argument keeps
    riding the edge it was checked against.  Declare a successor over a
    permissive dead edge and the old licence still flows: the inference is
    licensed by a relation the graph says has been replaced, `check_transport`
    sees a licensed step and stays silent, and this finding is the only thing
    in the system that would mention it.  So traffic keeps an edge in the
    count whatever its successor claims.
    """
    g = _graph(MODELS + [CLAIM,
        {"ev": "edge", "id": "E-IV-PD-EQ", "src": "IV", "dst": "PD",
         "type": "EQUIVALENCE", "why": "asserted reversible",
         "converse_witness": "the inverse construction"},
        {"ev": "edge", "id": "E-IV-PD-NC", "src": "IV", "dst": "PD",
         "type": "NECESSARY_CONDITION", "why": "it was only ever an inclusion",
         "supersedes": "E-IV-PD-EQ", "discharge_kind": "RETYPE"},
        _rider("I-RIDES-DEAD", "E-IV-PD-EQ")])
    assert not [f for f in C.run(g) if f.rule == C.R_TRANSPORT], (
        "the premise of this test: the dead EQUIVALENCE licenses the step, so "
        "no other rule is reporting it")
    par = _rules(g, C.R_PARALLEL)["PARALLEL-EDGE:IV->PD"]
    assert "E-IV-PD-EQ" in par.detail and "I-RIDES-DEAD" in par.detail
    assert par.severity == C.UNSOUND_PREMISE, (
        "an argument riding a withdrawn edge is traffic over a relation "
        "nobody stands behind any more")


def test_a_withdrawn_edge_whose_only_rider_was_withdrawn_too_is_gone():
    """The positive control for the traffic guard: a campaign that moved its
    argument onto the new edge has finished the job, and the rule must be
    able to see a finished job.

    A superseded inference is not traffic.  Counting it would keep the old
    route looking load-bearing forever, which is the same permanent line in
    the baseline this whole gate is about.
    """
    g = _graph(MODELS + [CLAIM,
        {"ev": "edge", "id": "E-IV-PD-EQ", "src": "IV", "dst": "PD",
         "type": "EQUIVALENCE", "why": "asserted reversible",
         "converse_witness": "the inverse construction"},
        {"ev": "edge", "id": "E-IV-PD-NC", "src": "IV", "dst": "PD",
         "type": "NECESSARY_CONDITION", "why": "it was only ever an inclusion",
         "supersedes": "E-IV-PD-EQ", "discharge_kind": "RETYPE"},
        _rider("I-OLD", "E-IV-PD-EQ"),
        _rider("I-NEW", "E-IV-PD-NC", supersedes="I-OLD",
               discharge_kind=K.RESTATE)])
    assert not _rules(g, C.R_PARALLEL)
    assert C.live_crossings(g, ["E-IV-PD-EQ"]) == [], (
        "the withdrawn argument is not traffic; the only thing still holding "
        "the old edge in the graph would be a rider nobody stands behind")
    assert C.live_crossings(g, ["E-IV-PD-NC"]) == ["I-NEW"], (
        "and the re-routed argument now rides the live edge, where it is "
        "audited against the type it actually crosses")


def test_superseding_something_else_entirely_buys_no_downgrade():
    """REFUTED: that carrying a `supersedes` field is itself mitigating.

    The rule used to drop the severity to DEBT -- below the blocking floor --
    for any group containing an edge with a `supersedes`, without asking what
    it superseded.  So an edge that replaced something in a different corner
    of the graph bought a downgrade for a parallelism nobody had declared
    anything about: an override purchased with an unrelated sentence, which is
    the shape of the defect this rule was written to catch.
    """
    g = _graph(MODELS + [CLAIM,
        {"ev": "model", "id": "FAR", "desc": "somewhere else entirely"},
        {"ev": "edge", "id": "E-FAR", "src": "PD", "dst": "FAR",
         "type": "NECESSARY_CONDITION", "why": "unrelated"},
        {"ev": "edge", "id": "E-IV-PD-EQ", "src": "IV", "dst": "PD",
         "type": "EQUIVALENCE", "why": "asserted reversible",
         "converse_witness": "the inverse construction"},
        {"ev": "edge", "id": "E-IV-PD-NC", "src": "IV", "dst": "PD",
         "type": "NECESSARY_CONDITION", "why": "an inclusion",
         "supersedes": "E-FAR", "discharge_kind": "RETYPE"},
        _rider("I-RIDES", "E-IV-PD-EQ")])
    par = _rules(g, C.R_PARALLEL)["PARALLEL-EDGE:IV->PD"]
    assert par.severity == C.UNSOUND_PREMISE
    assert "2 edges join" in par.detail


def test_withdrawal_is_computed_from_live_successors_only():
    """The unit behind both rules, stated on its own so a later change to
    either one cannot quietly lose it.

    An edge is withdrawn when a LIVE edge replaces it -- transitively, since
    a chain retires everything behind its head -- and never merely because
    its id appears in somebody's `supersedes`.
    """
    chain = _graph(MODELS + [UNTYPED_OLD, RETYPED,
        {"ev": "edge", "id": "E-IV-PD-NC", "src": "IV", "dst": "PD",
         "type": "NECESSARY_CONDITION", "why": "restated",
         "supersedes": "E-IV-PD-RESTRICT", "discharge_kind": "RETYPE"}])
    assert C.withdrawn_edges(chain) == {"E-IV-PD", "E-IV-PD-RESTRICT"}

    cycle = _graph(MODELS + [
        {"ev": "edge", "id": "E-A", "src": "IV", "dst": "PD",
         "type": "UNTYPED", "why": "a", "debt_why": "unknown",
         "supersedes": "E-B", "discharge_kind": "RETYPE"},
        {"ev": "edge", "id": "E-B", "src": "IV", "dst": "PD",
         "type": "UNTYPED", "why": "b", "debt_why": "unknown",
         "supersedes": "E-A", "discharge_kind": "RETYPE"}])
    assert C.withdrawn_edges(cycle) == set(), (
        "a closed cycle names no current edge, so it retires nothing")


# ===========================================================================
# STALE-PATH.  The precondition that makes the silence above safe.
# ===========================================================================
def test_a_live_inference_riding_a_withdrawn_edge_is_reported():
    """THE MISSING COMPLEMENT of STALE-PREMISE, and the safety precondition for
    every rule that now goes quiet on a withdrawn edge.

    Supersession never repoints anything, so an inference goes on riding the
    old edge after a better one is declared. Before this rule, four
    edge-attribute rules could fall silent on that edge and NOTHING anywhere
    said live traffic still crossed it.
    """
    g = _graph(MODELS + [UNTYPED_OLD, RETYPED, CLAIM, _rider("I", "E-IV-PD")])
    found = {f.fid: f for f in C.run(g) if f.rule == C.R_STALE_PATH}
    assert "STALE-PATH:I:E-IV-PD" in found
    f = found["STALE-PATH:I:E-IV-PD"]
    assert f.severity == C.UNSOUND_PREMISE, (
        "UNTYPED -> RESTRICTION changes what the edge licenses, so the "
        "argument was audited against cells the current edge does not open")
    assert "UNEXAMINED" in f.detail
    assert "E-IV-PD-RESTRICT" in f.discharge, "it must name the replacement"


def test_a_stale_path_is_only_DEBT_when_nothing_licensing_moved():
    """The severity turns on the same question as STALE-PREMISE. A successor
    that only gained a `converse_witness` licenses exactly what its predecessor
    did, so the argument stands as checked and the pointer is merely stale.

    This is the case a live campaign actually hit: discharging
    UNJUSTIFIED-EQUIVALENCE requires superseding, which is the right move and
    must not be punished as though the mathematics had changed.
    """
    eq = {"ev": "edge", "id": "E-EQ", "src": "IV", "dst": "PD",
          "type": K.EQUIVALENCE, "why": "reversible", "cite": "asserted"}
    eq2 = dict(eq, id="E-EQ-2", converse_witness="the explicit inverse",
               supersedes="E-EQ", discharge_kind="DERIVE")
    g = _graph(MODELS + [eq, eq2, CLAIM, _rider("I", "E-EQ")])
    found = [f for f in C.run(g) if f.rule == C.R_STALE_PATH]
    assert len(found) == 1
    assert found[0].severity == C.DEBT, (
        "adding a converse opens no new cell; punishing the repair at the "
        "blocking floor would make doing the right thing cost more than not")
    assert "only the pointer is stale" in found[0].detail


def test_a_withdrawn_edge_carrying_live_traffic_keeps_its_own_findings():
    """The two halves have to agree. If STALE-PATH reports the traffic, the
    edge-attribute rules may go quiet; if the edge is ridden they must NOT,
    because a withdrawn EQUIVALENCE that a live inference still rides goes on
    licensing silently and this is the only thing that would say so."""
    eq = {"ev": "edge", "id": "E-EQ", "src": "IV", "dst": "PD",
          "type": K.EQUIVALENCE, "why": "asserted reversible"}
    eq2 = {"ev": "edge", "id": "E-EQ-2", "src": "IV", "dst": "PD",
           "type": K.NECESSARY_CONDITION, "why": "it was never reversible",
           "supersedes": "E-EQ", "discharge_kind": "RETYPE"}
    ridden = _graph(MODELS + [eq, eq2, CLAIM, _rider("I", "E-EQ")])
    assert "UNJUSTIFIED-EQUIVALENCE:E-EQ" in _rules(
        ridden, "UNJUSTIFIED-EQUIVALENCE"), (
        "still ridden, so the finding must stay")
    unridden = _graph(MODELS + [eq, eq2])
    assert not _rules(unridden, "UNJUSTIFIED-EQUIVALENCE"), (
        "withdrawn and unridden: the defect was repaired by replacing it")
