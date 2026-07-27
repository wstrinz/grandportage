"""GATE 1 -- one regression per defect confirmed in the v0.2 review.

Every test here corresponds to something that WAS TRUE of this code and is not
any more.  They are written as attacks, not as restatements of the fix: each one
does the thing an adversary (or a tired author) would do, and asserts it is
refused.  A test that merely re-asserts the current table would have passed
against the broken version too, which is how the old
`test_identity_transport_turns_on_the_map_and_nothing_else` survived.

The kernel-level cells live in `test_cell_ledger.py`.  This file covers the
BOUNDARY and BOOKKEEPING defects -- the ones that were invisible to the
mathematics and therefore to every existing test.
"""

import json
import os

import pytest

from grandportage import cas
from grandportage import check as C
from grandportage import hook as H
from grandportage import kernel as K
from grandportage import store as S


def _graph(events):
    g = S.Graph()
    for i, ev in enumerate(events):
        g.apply(ev, lineno=i)
    return g.validate()


TWO_MODELS = [
    {"ev": "model", "id": "TIGHT", "desc": "with equations"},
    {"ev": "model", "id": "LOOSE", "desc": "equations dropped"},
]


# ===========================================================================
# THE CAS BOUNDARY.  cas.py's own docstring claimed "there is no string path to
# a solver".  There were two.
# ===========================================================================
def test_body_cannot_shadow_a_ring_variable():
    """THE ORIGINAL DEFECT, rebuilt through the field nobody validated.

    `poly g0 = ...` shadowing the ring variable g0 is what produced confident
    false UNIT verdicts at every prime, propagating to 17 rows across two
    documents.  `assert_no_identifier_collision` catches it in `decls`.  It went
    straight through `body`.
    """
    with pytest.raises(cas.IdentifierCollision) as exc:
        cas.CASProgram(cas.SINGULAR, ring="R", ring_vars=["g0", "x"],
                       decls=[("I", "ideal", "g0*x")],
                       body=["poly g0 = 1;"], outputs=["I"])
    assert "DECLARES" in str(exc.value)


def test_declaration_expression_cannot_carry_a_second_statement():
    """The same defect through the other half of the same field.

    The identifier was validated; the text beside it was not, so a statement
    list in one expression smuggled in an unchecked declaration.
    """
    with pytest.raises(cas.IdentifierCollision) as exc:
        cas.CASProgram(cas.SINGULAR, ring="R", ring_vars=["g0", "x"],
                       decls=[("I", "ideal", "g0*x; poly g0 = 1")],
                       body=[], outputs=["I"])
    assert "more than one statement" in str(exc.value)


@pytest.mark.parametrize("stmt", ["execute(str(1));", "kill I;", "setring R2;",
                                  "LIB \"poly.lib\";"])
def test_body_cannot_reach_around_the_identifier_check(stmt):
    """`execute` runs a string as Singular source, `kill` destroys a name,
    `setring` changes the base ring, `LIB` loads code.  Any of them reaches
    around the check rather than through it."""
    with pytest.raises(cas.IdentifierCollision):
        cas.CASProgram(cas.SINGULAR, ring="R", ring_vars=["x"],
                       decls=[("I", "ideal", "x")], body=[stmt],
                       outputs=["I"])


def test_the_decl_type_field_cannot_carry_a_declaration():
    """FOUND BY INDEPENDENT REVIEW OF v0.2, and it is the same mistake one layer
    out: the first fix validated the identifier half and the expression half of
    a decl triple, and left the TYPE half interpolated raw -- exactly as the
    ORIGINAL guard validated the identifier and waved through the text beside
    it.

    Confirmed against real Singular before the fix: the honest program returned
    `GP_G[1]=g0` and the smuggled one returned `GP_G[1]=1` -- a false unit
    ideal, exit 0, no `? error`, parsing cleanly.
    """
    with pytest.raises(cas.IdentifierCollision) as exc:
        cas.CASProgram(cas.SINGULAR, ring="R", ring_vars=["g0", "x"],
                       decls=[("GP_I", "poly g0 = 1; ideal", "g0")],
                       body=[], outputs=["GP_I"])
    assert "not a singular type" in str(exc.value)


@pytest.mark.parametrize("stmt", [
    "// harmless\npoly g0 = 1;",
    "// harmless\nexecute(\"int Z=1\");",
    "// harmless\nkill GP_I;",
])
def test_a_comment_prefix_does_not_defeat_the_statement_rules(stmt):
    """`_FIRST_TOKEN` anchors at the start and failed OPEN when it did not
    match, so a leading `//` made every statement rule vacuous.  The `execute`
    case actually ran when tested against Singular."""
    with pytest.raises(cas.IdentifierCollision):
        cas.CASProgram(cas.SINGULAR, ring="R", ring_vars=["g0", "x"],
                       decls=[("GP_I", "ideal", "g0")], body=[stmt],
                       outputs=["GP_I"])


@pytest.mark.parametrize("kw", [
    {"ring": "R", "ring_vars": ["g0", "x),dp; poly g0 = 1;//"]},
    {"ring": "R = 0,(g0),dp; poly g0 = 1; ring S", "ring_vars": ["g0"]},
])
def test_the_ring_line_cannot_be_closed_and_extended(kw):
    """`ring %s = %d,(%s),dp;` interpolates the ring name and the variables with
    no quoting and neither was checked.  This one reached the solver THROUGH THE
    MCP TOOL: `cas_ideal_is_unit` passes `ring_vars` straight down, so an
    ordinary-looking call recorded a model and an edge for a false unit-ideal
    verdict."""
    with pytest.raises(cas.IdentifierCollision) as exc:
        cas.CASProgram(cas.SINGULAR, decls=[("GP_I", "ideal", "g0")],
                       body=[], outputs=["GP_I"], **kw)
    assert "bare identifier" in str(exc.value)


def test_ring_iso_is_declarable_through_the_supported_path():
    """v0.2 taught the kernel to READ `ring_iso` and gave nobody a way to WRITE
    it: absent from the MCP edge schema, hard-rejected by `Transport.from_dict`
    as an unknown field, never emitted by `events()`.  So an honest ring
    isomorphism could not be declared through the supported path at all, while a
    raw `portage_declare` could assert it unaudited.  A gate unreachable from
    the front door and open at the back is not a gate."""
    import grandportage.mcp as M
    assert "ring_iso" in M.EDGE_SCHEMA["properties"]
    t = cas.Transport.from_dict({"src": "A", "type": K.EQUIVALENCE,
                                 "why": "re-presentation of the same ideal",
                                 "ring_iso": True})
    _model, edge = t.events("E", "B", "desc")
    assert edge["ring_iso"] is True


def test_ring_iso_is_meaningless_on_a_lossy_edge():
    with pytest.raises(cas.TransportNotDeclared):
        cas.Transport(src="A", type=K.NECESSARY_CONDITION, why="drops eqs",
                      ring_iso=True)


@pytest.mark.parametrize("cell,wanted", [
    ((K.EQUIVALENCE, K.ALONG, K.IDENTITY), "ring_iso"),
    ((K.NECESSARY_CONDITION, K.ALONG, K.IDENTITY), "AMBIENT"),
    ((K.SPECIALIZATION, K.ALONG, K.IDENTITY), "integral"),
])
def test_a_refused_identity_cell_names_its_own_condition(cell, wanted):
    """All three cells v0.2 made conditional fell through to the catch-all
    IDENTITY move, which names the DENOMINATOR-FREE condition -- so an edge
    already declared POLYNOMIAL was advised to make its map polynomial.
    Self-contradictory, undischargeable, and it invites retyping the map to
    silence the warning, which is REVIEW.md's failure mode 2."""
    from grandportage.discharge import discharge_for
    etype, direction, kind = cell
    move = discharge_for(etype, direction, kind,
                         edge={"src": "S", "dst": "D", "map_kind": "POLYNOMIAL"})
    assert wanted in move
    assert "denominator-free map; this edge's map is" not in move


def test_legal_programs_still_pass():
    """A check that rejects everything is worse than no check.  The shapes this
    repository actually emits must survive."""
    cas.CASProgram(cas.SINGULAR, ring="R", ring_vars=["x", "y"],
                   decls=[("I", "ideal", "x-1,y-2"),
                          ("G", "ideal", "std(I)")],
                   body=["I = std(I);"], outputs=["G"])


def _fake_run(returncode=0, stdout="@@GP_G:\n1\n", stderr="", aborted=False,
              abort_reason=None):
    def runner(program, timeout):
        return {"returncode": returncode, "stdout": stdout, "stderr": stderr,
                "aborted": aborted, "abort_reason": abort_reason,
                "argv": ["fake"]}
    return runner


def _program():
    return cas.CASProgram(cas.SINGULAR, ring="R", ring_vars=["x"],
                          decls=[("GP_I", "ideal", "x"),
                                 ("GP_G", "ideal", "std(GP_I)")],
                          body=[], outputs=["GP_G"])


EDGE = {"src": "TIGHT", "type": "NECESSARY_CONDITION", "why": "drops eqs"}


def test_a_nonzero_exit_is_not_a_verdict(tmp_path):
    """Only 124, 137 and 139 were treated as aborts.  Every other nonzero exit
    fell through to the OK branch and was read for a verdict, provided the
    output happened to parse -- which it does whenever the solver got far enough
    to print its markers before dying."""
    with pytest.raises(cas.CASError) as exc:
        cas.run_cas(_program(), edge=EDGE, produces="M", describes="d",
                    root=str(tmp_path), _runner=_fake_run(returncode=3))
    assert "not a verdict" in str(exc.value)


def test_an_aborted_run_mints_no_model(tmp_path):
    """An unfinished run used to append BOTH the produced model and the
    semantic edge, so the graph asserted that a model existed and related to
    its source in a stated way, on the strength of a computation that never
    returned."""
    result = cas.run_cas(_program(), edge=EDGE, produces="M", describes="d",
                         root=str(tmp_path),
                         _runner=_fake_run(returncode=124, aborted=True,
                                           abort_reason="timeout"))
    assert result["verdict"] == "ABORTED"
    graph = S.load(S.graph_path(str(tmp_path)))
    assert "M" not in graph.models, "an aborted run created a model"
    assert not graph.edges, "an aborted run created a semantic edge"
    assert graph.notes, "the attempt should still be recorded as provenance"


def test_a_clean_run_still_records(tmp_path):
    """The positive control: the guard must not have broken recording."""
    S.append([{"ev": "model", "id": "TIGHT", "desc": "source"}],
             root=str(tmp_path))
    cas.run_cas(_program(), edge=EDGE, produces="M", describes="d",
                root=str(tmp_path), _runner=_fake_run())
    graph = S.Graph()
    for ev, n in S.load_events(S.graph_path(str(tmp_path))):
        graph.apply(ev, lineno=n)
    assert "M" in graph.models and graph.edges


# ===========================================================================
# THE CERTIFICATE REGISTRY.  `derive_scope` reads it to decide
# field-independence, and it was writable from any graph.
# ===========================================================================
def test_a_graph_cannot_redefine_a_builtin_certificate():
    """The registry seeds from BUILTIN_CERTIFICATES but the redeclaration guard
    started empty, so the built-ins were never protected by it.  Flipping
    UNIT_IDEAL_CERT to base_changes=false silently downgrades every
    SCHEME-scoped emptiness in a campaign; flipping one true mints
    field-independence nobody proved.  Neither produced a finding."""
    with pytest.raises(S.GraphError) as exc:
        _graph([{"ev": "certificate", "id": "UNIT_IDEAL_CERT",
                 "base_changes": False, "why": "hostile redefinition"}])
    assert "BUILT-IN" in str(exc.value)


def test_restating_a_builtin_with_the_same_verdict_is_still_legal():
    """Idempotent redeclaration is the whole merge story; the guard must not
    break branches that legitimately restate what they rely on."""
    g = _graph([{"ev": "certificate", "id": "UNIT_IDEAL_CERT",
                 "base_changes": True, "why": "restated by a branch"}])
    assert g.certificates["UNIT_IDEAL_CERT"] is True


def test_a_new_certificate_name_is_still_registrable():
    """Domains extend the registry through the graph.  That must keep working."""
    g = _graph([{"ev": "certificate", "id": "MY_CERT", "base_changes": False,
                 "why": "field-relative by construction"}])
    assert g.certificates["MY_CERT"] is False


# ===========================================================================
# WITNESS POLARITY.  Two fields with opposite meanings shared one name.
# ===========================================================================
def test_a_strictness_witness_cannot_justify_an_equivalence():
    """`witness` was documented as evidence the step is NOT an equivalence, and
    `check_unjustified_equivalence` accepted it as documentation THAT it is.
    The better the counterexample, the more thoroughly it silenced the
    warning."""
    g = _graph(TWO_MODELS + [
        {"ev": "edge", "id": "E", "src": "TIGHT", "dst": "LOOSE",
         "type": "EQUIVALENCE", "why": "reversible",
         "strictness_witness": "a point of LOOSE that is not in TIGHT"}])
    fids = {f.rule for f in C.run(g)}
    assert "UNJUSTIFIED-EQUIVALENCE" in fids, (
        "a strictness witness must not count as documentation")
    assert "SELF-REFUTING-EQUIVALENCE" in fids, (
        "an equivalence carrying its own counterexample is its own finding")


def test_a_converse_witness_does_justify_an_equivalence():
    """The positive control: the field that genuinely documents an equivalence
    must still do so, or the rule is just noise."""
    g = _graph(TWO_MODELS + [
        {"ev": "edge", "id": "E", "src": "TIGHT", "dst": "LOOSE",
         "type": "EQUIVALENCE", "why": "reversible",
         "converse_witness": "given a point of LOOSE, this construction "
                             "recovers a point of TIGHT"}])
    assert not [f for f in C.run(g) if "EQUIVALENCE" in f.rule]


def test_a_converse_witness_on_a_lossy_edge_is_refused_at_declaration():
    """If the converse really is exhibitable the type is wrong; if it is not,
    the field is.  Either way it should not fold quietly."""
    with pytest.raises(cas.TransportNotDeclared):
        cas.Transport(src="A", type=K.NECESSARY_CONDITION, why="drops eqs",
                      converse_witness="here is the converse")


# ===========================================================================
# TAINT.  It was one pass over built_by, so it stopped at the first generation.
# ===========================================================================
def test_taint_reaches_the_second_generation():
    """A refused inference builds M1.  A perfectly LICENSED inference reasons
    from a claim in M1 and builds M2.  M2 rests on the same defect, and the
    single pass reported only M1 -- the generation where a reader stops looking,
    because the step that produced it is clean.
    """
    events = [
        {"ev": "model", "id": "SRC", "desc": "source"},
        {"ev": "model", "id": "M1", "desc": "first generation"},
        {"ev": "model", "id": "M2", "desc": "second generation"},
        # A refused step: NONEMPTY does not travel AGAINST a NECESSARY_CONDITION.
        {"ev": "edge", "id": "E1", "src": "SRC", "dst": "M1",
         "type": "NECESSARY_CONDITION", "why": "drops equations"},
        {"ev": "claim", "id": "C1", "model": "M1", "kind": "NONEMPTY",
         "statement": "a witness in the relaxation", "scope": "Q"},
        {"ev": "inference", "id": "BAD", "claim": "C1",
         "path": [["E1", "AGAINST"]], "asserted": "so SRC has a point"},
        {"ev": "built_by", "model": "M1", "inference": "BAD"},
        # A clean step drawing on M1, building M2.
        {"ev": "edge", "id": "E2", "src": "M1", "dst": "M2",
         "type": "NECESSARY_CONDITION", "why": "drops more equations"},
        {"ev": "inference", "id": "CLEAN", "claim": "C1",
         "path": [["E2", "ALONG"]], "asserted": "the witness is a point of M2"},
        {"ev": "built_by", "model": "M2", "inference": "CLEAN"},
    ]
    g = _graph(events)
    findings = C.run(g)
    assert C.audit_inference(g, "CLEAN")[0], "CLEAN must itself be licensed"
    tainted = {f.subject for f in findings if f.rule == C.R_TAINT}
    assert tainted == {"M1", "M2"}, (
        "taint must reach a fixed point, not stop at the first generation; "
        "got %s" % sorted(tainted))
    second = [f for f in findings if f.subject == "M2"][0]
    assert "already tainted" in second.detail


# ===========================================================================
# BASELINE.  Keyed by a finding id that is stable by construction.
# ===========================================================================
def _campaign(tmp_path, edge_type):
    path = S.graph_path(str(tmp_path))
    os.makedirs(os.path.dirname(path), exist_ok=True)
    events = TWO_MODELS + [
        {"ev": "edge", "id": "E", "src": "TIGHT", "dst": "LOOSE",
         "type": edge_type, "why": "some step", "map_kind": "POLYNOMIAL",
         "debt_why": "not yet worked out"},
        {"ev": "claim", "id": "CL", "model": "LOOSE", "kind": "NONEMPTY",
         "statement": "a witness", "scope": "Q"},
        {"ev": "inference", "id": "INF", "claim": "CL",
         "path": [["E", "AGAINST"]], "asserted": "so TIGHT has a point"},
    ]
    with open(path, "w", encoding="utf-8") as fh:
        for ev in events:
            fh.write(json.dumps(ev, sort_keys=True) + "\n")
    return S.load(path)


def test_an_acceptance_does_not_survive_the_finding_changing_meaning(tmp_path):
    """`fid` is "RULE:subject" and therefore stable by construction, so an
    acceptance went on suppressing a finding after the edge it rides was
    retyped.  What a reviewer agreed to carry and what was still being carried
    drifted apart, silently, in the file humans read as the authoritative record
    of what a campaign knows it is holding."""
    g = _campaign(tmp_path, "UNTYPED")
    findings = C.run(g)
    H.save_baseline(str(tmp_path), findings, note="carried deliberately")
    blocked, _ = H.evaluate(str(tmp_path))
    assert not blocked, "the accepted finding should be suppressed"

    # Same finding id; different meaning.
    g2 = _campaign(tmp_path, "NECESSARY_CONDITION")
    same = {f.fid for f in C.run(g2)} & {f.fid for f in findings}
    assert same, "the test needs a finding whose id survives the retype"
    blocked, message = H.evaluate(str(tmp_path))
    assert blocked, "a changed finding must reopen its acceptance"
    assert "STALE" in message
    assert "carried deliberately" in message, (
        "the reason originally given must be shown, so the reviewer can judge "
        "whether it still applies")


# ===========================================================================
# IDENTITY ORIGIN.  A required field with an honest answer always available.
# ===========================================================================
def test_a_rewriting_naming_the_extension_cannot_descend():
    """FOUND BY INDEPENDENT REVIEW.  The reviewer's exact attack.

    `x^2 + 1 = (x + i)(x - i)` is a valid rewriting over Q(i).  Transported
    AGAINST a BASE_EXTENSION to the Q-model, `i` is not merely unproved -- it is
    not expressible there, so the descended statement is not a false claim, it
    is not a claim.  The cell was unconditional `True` and produced zero
    findings.
    """
    events = [
        {"ev": "model", "id": "M_Q", "desc": "over Q", "field": "Q"},
        {"ev": "model", "id": "M_K", "desc": "over Q(i)", "field": "Q(i)"},
        {"ev": "edge", "id": "E1", "src": "M_Q", "dst": "M_K",
         "type": "BASE_EXTENSION", "why": "adjoins i"},
        {"ev": "claim", "id": "CL", "model": "M_K", "kind": "IDENTITY",
         "statement": "x^2 + 1 = (x + i)*(x - i)",
         "identity_origin": "AMBIENT"},
        {"ev": "inference", "id": "INF", "claim": "CL",
         "path": [["E1", "AGAINST"]],
         "asserted": "so the factorisation holds over Q"},
    ]
    g = _graph(events)
    ok, _ = C.audit_inference(g, "INF")
    assert not ok, "a rewriting naming i must not descend to Q"
    assert [f for f in C.run(g) if f.rule == C.R_TRANSPORT]


def test_a_base_rational_rewriting_still_descends():
    """The positive control.  Descent is genuinely sound when both sides lie in
    the base -- faithful flatness -- and that is the common case, so refusing it
    would trade a rare false licence for a frequent false refusal."""
    r = K.transport(K.BASE_EXTENSION, K.AGAINST, K.IDENTITY,
                    coefficients_in_base=True)
    assert r.licensed


def test_the_unsound_register_is_empty_and_visible():
    """KNOWN_CONSERVATISM had no mirror, so a knowingly-false licence lived in a
    test docstring, appeared in no `gp check` or `gp table`, and survived a
    review hunting exactly that.

    The register must stay EMPTY -- an entry means the tool confidently licenses
    something its authors believe is false -- and it must be PRINTED even when
    empty, because "(none)" is a positive assertion and a missing section is
    not.
    """
    from grandportage.discharge import KNOWN_UNSOUND
    assert KNOWN_UNSOUND == [], (
        "a cell is registered as knowingly unsound: %s.  That is a bug with a "
        "deadline, not a design decision." % KNOWN_UNSOUND)


def test_the_fold_does_not_depend_on_concatenation_order(tmp_path):
    """FOUND BY INDEPENDENT REVIEW.  `_apply_claim` derives an emptiness scope
    against the certificates registered SO FAR, so a branch declaring a claim
    before the branch registering its certificate failed to fold.

    `store.load`'s own docstring says "Order does not matter for the result",
    and DESIGN.md sec.1.1 sells merging as concatenating logs and folding again.
    Neither held across a certificate boundary -- and an unfoldable graph makes
    `hook.evaluate` fail CLOSED, so the wrong order blocks every subsequent tool
    call rather than warning.
    """
    cert = [{"ev": "certificate", "id": "MY_CERT", "base_changes": True,
             "why": "an inequality between integers"}]
    claim = [{"ev": "model", "id": "M", "desc": "m"},
             {"ev": "claim", "id": "C1", "model": "M", "kind": "EMPTY",
              "statement": "empty", "certificate": "MY_CERT"}]
    paths = {}
    for name, evs in (("a_cert.jsonl", cert), ("b_claim.jsonl", claim)):
        p = tmp_path / name
        p.write_text("\n".join(json.dumps(e) for e in evs), encoding="utf-8")
        paths[name] = str(p)
    forward = S.load(paths["a_cert.jsonl"], paths["b_claim.jsonl"])
    reverse = S.load(paths["b_claim.jsonl"], paths["a_cert.jsonl"])
    assert forward.claims["C1"]["scope"] == K.SCHEME
    assert reverse.claims["C1"]["scope"] == K.SCHEME, (
        "folding the same two branches in the other order must give the same "
        "graph, or 'merging is concatenating logs' is false")


def test_a_carried_finding_is_visibly_carried(tmp_path):
    """THE T3 REPAIR.  A fresh agent handed a campaign whose nine findings had
    all been examined and accepted reported "gate failing, five live blockers"
    -- the exact inverse.  It was not careless: no read path showed
    acceptances, and `portage_check`'s `full` parameter was declared in the MCP
    schema and never read by its handler.

    The distinction between "this campaign is broken" and "this campaign is
    healthy and carrying known debt" is most of the difference between a
    campaign and a mess, and nothing surfaced it.
    """
    g = _campaign(tmp_path, "UNTYPED")
    findings = C.run(g)
    H.save_baseline(str(tmp_path), findings, note="known, carried on purpose")
    accepted = H.read_baseline(str(tmp_path))["accepted"]
    out = C.render(findings, accepted)
    assert "CARRIED" in out
    assert "known, carried on purpose" in out, (
        "the REASON is the part a reviewer needs; an unexplained mark is no "
        "better than silence")
    assert "No LIVE findings" in out
    # And with nothing accepted, the same findings must read as live.
    assert "CARRIED" not in C.render(findings, {})


def test_accepting_one_finding_does_not_rewrite_every_other_reason(tmp_path):
    """`gp accept -m "..."` without `--only` overwrote the per-finding `why` of
    every already-accepted finding, replacing a version-controlled record of
    distinct reasons with one sentence.  Same family as the `--only` baseline
    wipe in REVIEW.md sec.7.4, narrower only because the ids survive -- and the
    reasons are the part a reviewer actually reads."""
    g = _campaign(tmp_path, "UNTYPED")
    findings = C.run(g)
    H.save_baseline(str(tmp_path), findings, note="original reasoning")
    H.save_baseline(str(tmp_path), findings, note="a later, vaguer note")
    whys = {e.get("why")
            for e in H.read_baseline(str(tmp_path))["accepted"].values()}
    assert whys == {"original reasoning"}, (
        "a bulk accept must not overwrite reasons already recorded; got %s"
        % whys)


@pytest.mark.parametrize("bad", ["VERY_BAD", "debt", ""])
def test_an_unknown_severity_override_is_a_graph_error_not_a_crash(bad):
    """An arbitrary string reached `check.run`'s sort key and raised KeyError
    there, so `gp check` and the hook CRASHED rather than reporting a malformed
    graph -- and a crashing checker is indistinguishable from one nobody ran."""
    events = TWO_MODELS + [
        {"ev": "edge", "id": "E", "src": "TIGHT", "dst": "LOOSE",
         "type": "NECESSARY_CONDITION", "why": "drops eqs"},
        {"ev": "claim", "id": "CL", "model": "LOOSE", "kind": "NONEMPTY",
         "statement": "a point", "scope": "Q"},
        {"ev": "inference", "id": "INF", "claim": "CL",
         "path": [["E", "AGAINST"]], "asserted": "so TIGHT has a point",
         "severity_override": bad, "severity_why": "because"},
    ]
    if not bad:                      # falsy: no override at all, must fold
        _graph(events)
        return
    with pytest.raises(S.GraphError) as exc:
        _graph(events)
    assert "severities are" in str(exc.value)


def test_store_severities_match_the_checker():
    """`store.C_SEVERITIES` is written out rather than imported, to keep the
    store the bottom layer.  Pinned here so the two cannot drift -- the same
    trick the CAS boundary uses for its identifier check."""
    assert list(S.C_SEVERITIES) == list(C.SEVERITY_ORDER)


# ===========================================================================
# TYPED DISCHARGE AND SUPERSESSION.  The CEGAR step.
# ===========================================================================
def _obligation(tmp_path, admits=None):
    """A campaign carrying a refusal, optionally pinned to one discharge."""
    path = S.graph_path(str(tmp_path))
    os.makedirs(os.path.dirname(path), exist_ok=True)
    evs = [
        {"ev": "model", "id": "CHART", "desc": "the chart"},
        {"ev": "model", "id": "LEDGER", "desc": "the chart plus a cap"},
        {"ev": "edge", "id": "E-OLD", "src": "CHART", "dst": "LEDGER",
         "type": "UNTYPED", "why": "relation unknown",
         "debt_why": "the cap slope is not derived"},
        {"ev": "claim", "id": "CL", "model": "LEDGER", "kind": "PREDICATE",
         "statement": "the cap",
         "cite": "NOT DERIVED. Recorded so using it is a type error."},
        {"ev": "inference", "id": "INF", "claim": "CL",
         "path": [["E-OLD", "AGAINST"]], "asserted": "the chart obeys the cap"},
    ]
    with open(path, "w", encoding="utf-8") as fh:
        fh.write("\n".join(json.dumps(e) for e in evs) + "\n")
    f = [x for x in C.run(S.load(path)) if x.rule == C.R_TRANSPORT][0]
    H.save_baseline(str(tmp_path), [f],
                    note="DISCHARGE BY DERIVING the cap, not by naming a "
                         "relaxation")
    if admits:
        doc = H.read_baseline(str(tmp_path))
        doc["accepted"][f.fid]["admits"] = list(admits)
        with open(H.baseline_path(str(tmp_path)), "w", encoding="utf-8") as fh:
            json.dump({"accepted": doc["accepted"], "note": doc.get("note", "")},
                      fh, indent=2)
    return path


def _supersede(path, kind):
    with open(path, "a", encoding="utf-8") as fh:
        fh.write(json.dumps({
            "ev": "edge", "id": "E-NEW", "src": "CHART", "dst": "LEDGER",
            "type": "NECESSARY_CONDITION", "why": "typed successor",
            "supersedes": "E-OLD", "discharge_kind": kind}) + "\n")


def test_a_supersession_cannot_route_around_the_discharge_it_inherits(tmp_path):
    """THE CEGAR STEP, and the exact move a blind run made.

    The discharge recorded against the live obligation read, verbatim:
    "DISCHARGE BY DERIVING Delta'_4, not by naming a relaxation." That is
    exactly right and enforced nothing, because it was prose in a baseline
    file -- so the run discharged it by naming a relaxation, declaring a
    parallel edge with a permissive type, and every check stayed green.

    A refusal should name the refinement that legitimately resolves it, and
    only that refinement should count.
    """
    path = _obligation(tmp_path, admits=["DERIVE"])
    _supersede(path, "RETYPE")
    accepted = H.read_baseline(str(tmp_path))["accepted"]
    sup = [f for f in C.run(S.load(path), accepted)
           if f.rule == C.R_SUPERSEDE]
    assert len(sup) == 1
    assert sup[0].severity == C.UNSOUND_PREMISE
    assert "admits only DERIVE" in sup[0].detail
    assert "not by naming a relaxation" in sup[0].detail, (
        "the original reason must be shown, so the reader can judge whether "
        "the supersession answers it")


def test_the_admitted_discharge_passes(tmp_path):
    """The positive control: supplying what the obligation asked for clears
    it. A gate that refuses every exit is not a gate."""
    path = _obligation(tmp_path, admits=["DERIVE"])
    _supersede(path, "DERIVE")
    accepted = H.read_baseline(str(tmp_path))["accepted"]
    assert not [f for f in C.run(S.load(path), accepted)
                if f.rule == C.R_SUPERSEDE]


def test_an_unpinned_obligation_accepts_any_discharge(tmp_path):
    """Pinning is opt-in. An obligation that never said how it must be closed
    does not get to complain about how it was."""
    path = _obligation(tmp_path)
    _supersede(path, "RETYPE")
    accepted = H.read_baseline(str(tmp_path))["accepted"]
    assert not [f for f in C.run(S.load(path), accepted)
                if f.rule == C.R_SUPERSEDE]


def test_superseding_without_saying_how_is_a_fold_error(tmp_path):
    """Supersession TRANSFERS obligations rather than clearing them, so it has
    to state what it supplies."""
    path = _obligation(tmp_path)
    with open(path, "a", encoding="utf-8") as fh:
        fh.write(json.dumps({
            "ev": "edge", "id": "E-NEW", "src": "CHART", "dst": "LEDGER",
            "type": "NECESSARY_CONDITION", "why": "successor",
            "supersedes": "E-OLD"}) + "\n")
    with pytest.raises(S.GraphError) as exc:
        S.load(path)
    assert "discharge_kind" in str(exc.value)


# ===========================================================================
# CASE PARTITIONS.  The gap two independent agents walked into.
# ===========================================================================
PARTITION = [
    {"ev": "model", "id": "PARENT", "desc": "the object under investigation"},
    {"ev": "model", "id": "B2", "desc": "the gamma=2 case"},
    {"ev": "model", "id": "B3", "desc": "the gamma=3 case"},
    {"ev": "claim", "id": "C-COVER", "model": "PARENT", "kind": "PREDICATE",
     "statement": "gamma is in {2,3}"},
    {"ev": "partition", "id": "P", "parent": "PARENT", "branches": ["B2", "B3"],
     "exhaustive": "C-COVER", "why": "gamma takes exactly one of two values"},
    {"ev": "claim", "id": "CE2", "model": "B2", "kind": "EMPTY",
     "statement": "case 2 is dead", "certificate": "UNIT_IDEAL_CERT"},
    {"ev": "claim", "id": "CE3", "model": "B3", "kind": "EMPTY",
     "statement": "case 3 is dead", "certificate": "UNIT_IDEAL_CERT"},
]


def _split(premises, kind="EMPTY"):
    return _graph(PARTITION + [
        {"ev": "inference", "id": "J", "via_partition": "P",
         "premises": [{"claim": c} for c in premises],
         "concludes_kind": kind, "asserted": "so the parent is empty"}])


def test_a_case_split_is_licensed_by_the_partition_not_by_an_edge():
    """No single edge licenses a case split, and the kernel is RIGHT to refuse
    each leg: branch -> parent is a NECESSARY_CONDITION with the branch
    tighter, and EMPTY does not travel ALONG, because one branch dying says
    nothing about the parent.

    Only all branches together, plus exhaustiveness, say anything -- so this is
    a second inference rule beside the transport table, and it is kept separate
    so a reader can see which of the two justified a step.
    """
    g = _split(["CE2", "CE3", "C-COVER"])
    ok, trace = C.audit_inference(g, "J")
    assert ok
    assert g.inferences["J"]["concludes_at"] == "PARENT"
    assert trace[0][1] == "COVERS", "the step is over the partition, not an edge"


def test_a_case_split_with_a_branch_left_open_is_refused_by_name():
    """The refusal has to say WHICH case is open, or it is just a no."""
    ok, trace = C.audit_inference(_split(["CE2", "C-COVER"]), "J")
    assert not ok
    assert "B3" in trace[0][3]


def test_a_case_split_without_exhaustiveness_is_refused():
    """A split into cases nobody proved were ALL the cases proves nothing --
    and that premise is exactly what a live run left in a prose note."""
    ok, trace = C.audit_inference(_split(["CE2", "CE3"]), "J")
    assert not ok
    assert "COVER" in trace[0][3]


def test_a_partition_must_name_a_real_claim_as_its_exhaustiveness():
    """The whole point is that the completeness premise can be seen by a rule.
    A note would not be."""
    with pytest.raises(S.GraphError) as exc:
        _graph([e for e in PARTITION if e.get("id") != "C-COVER"])
    assert "not a note" in str(exc.value)


def test_a_branch_edge_drawn_from_parent_to_branch_is_flagged():
    """A branch is `parent AND condition`, so V(branch) is a SUBSET of
    V(parent) and the edge runs BRANCH -> PARENT.

    Drawn the other way the graph asserts the parent sits inside each branch --
    and since branches are alternatives, that holds only if the parent is
    empty, which is what the split is trying to decide. Both live agents drew
    it backwards, and a result about one of three cases was recorded as a
    result about all of them.
    """
    g = _graph(PARTITION + [
        {"ev": "edge", "id": "E-BAD", "src": "PARENT", "dst": "B3",
         "type": "NECESSARY_CONDITION", "why": "the gamma=3 chart"}])
    bad = [f for f in C.run(g) if f.rule == C.R_PARTITION
           and f.subject == "E-BAD"]
    assert len(bad) == 1 and bad[0].severity == C.UNSOUND_PREMISE

    good = _graph(PARTITION + [
        {"ev": "edge", "id": "E-OK", "src": "B3", "dst": "PARENT",
         "type": "NECESSARY_CONDITION", "why": "the gamma=3 case of the parent"}])
    assert not [f for f in C.run(good) if f.rule == C.R_PARTITION
                and f.subject == "E-OK"]


def test_a_fully_covered_partition_prompts_for_the_conclusion():
    """When every branch is dead the parent's emptiness FOLLOWS, and leaving it
    unrecorded means the step lives in whoever's head assembled it."""
    prompts = [f for f in C.run(_graph(PARTITION)) if f.rule == C.R_PARTITION]
    assert len(prompts) == 1 and prompts[0].severity == C.DEBT
    assert "premises" in prompts[0].discharge
    # ...and stops once the inference exists.
    assert not [f for f in C.run(_split(["CE2", "CE3", "C-COVER"]))
                if f.rule == C.R_PARTITION]


# ===========================================================================
# MULTI-PREMISE INFERENCES.  The graph used to record chains but not joins.
# ===========================================================================
THREE_MODELS = TWO_MODELS + [{"ev": "model", "id": "SIDE", "desc": "elsewhere"}]


def test_an_argument_can_now_combine_two_premises():
    """THE ACCEPTANCE TEST, taken from a live run that could not do this.

    A blind agent's central case analysis was
    `(gamma=4 branch EMPTY) AND (gamma in {2,3,4}) => gamma in {2,3}`.
    `inference.claim` was a single string, so the completeness premise had
    nowhere to go and ended up in a `note`, where nothing types it -- the
    checker reported the conclusion as clean while the fact that made it valid
    was invisible.

    Both premises must be typed, both transports audited, and both must arrive
    at the same model.
    """
    g = _graph(THREE_MODELS + [
        {"ev": "edge", "id": "E1", "src": "TIGHT", "dst": "LOOSE",
         "type": "NECESSARY_CONDITION", "why": "drops equations"},
        {"ev": "edge", "id": "E2", "src": "TIGHT", "dst": "SIDE",
         "type": "NECESSARY_CONDITION", "why": "drops other equations"},
        {"ev": "claim", "id": "C-MAIN", "model": "LOOSE", "kind": "PREDICATE",
         "statement": "every point satisfies P"},
        {"ev": "claim", "id": "C-SIDE", "model": "SIDE", "kind": "PREDICATE",
         "statement": "the completeness premise"},
        {"ev": "inference", "id": "JOIN", "premises": [
            {"claim": "C-MAIN", "path": [["E1", "AGAINST"]]},
            {"claim": "C-SIDE", "path": [["E2", "AGAINST"]]}],
         "concludes_kind": "PREDICATE",
         "asserted": "P and the completeness premise together give Q"},
    ])
    i = g.inferences["JOIN"]
    assert len(i["premises"]) == 2
    assert i["concludes_at"] == "TIGHT", "both premises must land together"
    ok, trace = C.audit_inference(g, "JOIN")
    assert ok and len(trace) == 2, (
        "every leg is audited, not just the first: %s" % trace)


def test_premises_that_never_meet_are_a_fold_error():
    """The reason conjunction is safe to offer.

    `GI-BRIDGE` -- the defect this project exists to catch -- is a BAD JOIN:
    two computations sharing no variable, welded by a sentence. Adding
    conjunction would reintroduce it, except that a join is only expressible
    when its premises PROVABLY MEET at a common model.

    So a good join becomes expressible and a bad one becomes a FOLD ERROR,
    which is strictly stronger than a finding: the log will not load at all.
    """
    with pytest.raises(S.GraphError) as exc:
        _graph(THREE_MODELS + [
            {"ev": "edge", "id": "E1", "src": "TIGHT", "dst": "LOOSE",
             "type": "NECESSARY_CONDITION", "why": "drops equations"},
            {"ev": "claim", "id": "C-MAIN", "model": "TIGHT",
             "kind": "NONEMPTY", "statement": "a point", "scope": "Q"},
            {"ev": "claim", "id": "C-FAR", "model": "SIDE", "kind": "PREDICATE",
             "statement": "an unrelated fact"},
            {"ev": "inference", "id": "BRIDGE", "premises": [
                {"claim": "C-MAIN", "path": [["E1", "ALONG"]]},
                {"claim": "C-FAR", "path": []}],
             "asserted": "therefore the two are connected"}])
    msg = str(exc.value)
    assert "do not meet" in msg
    assert "LOOSE" in msg and "SIDE" in msg, (
        "the error must name where each premise actually arrived")


def test_a_refused_leg_refuses_the_whole_argument():
    """An argument is only as licensed as its weakest leg -- and before the
    multi-premise form the extra legs were not in the graph to be audited."""
    g = _graph(THREE_MODELS + [
        {"ev": "edge", "id": "E1", "src": "TIGHT", "dst": "LOOSE",
         "type": "NECESSARY_CONDITION", "why": "drops equations"},
        {"ev": "edge", "id": "E2", "src": "TIGHT", "dst": "SIDE",
         "type": "NECESSARY_CONDITION", "why": "drops other equations"},
        {"ev": "claim", "id": "C-OK", "model": "LOOSE", "kind": "PREDICATE",
         "statement": "fine"},
        # NONEMPTY does NOT travel AGAINST a NECESSARY_CONDITION.
        {"ev": "claim", "id": "C-BAD", "model": "SIDE", "kind": "NONEMPTY",
         "statement": "a witness in the relaxation", "scope": "Q"},
        {"ev": "inference", "id": "JOIN", "premises": [
            {"claim": "C-OK", "path": [["E1", "AGAINST"]]},
            {"claim": "C-BAD", "path": [["E2", "AGAINST"]]}],
         "concludes_kind": "PREDICATE", "asserted": "both, therefore Q"},
    ])
    ok, trace = C.audit_inference(g, "JOIN")
    assert not ok
    assert [t[2] for t in trace] == [True, False], (
        "the first leg is licensed and the second is not: %s" % trace)


def test_the_single_premise_form_still_works_unchanged():
    """Backward compatibility is not a courtesy here -- every fixture, every
    retrodiction and two live campaign graphs use the old shape."""
    g = _graph(TWO_MODELS + [
        {"ev": "edge", "id": "E", "src": "TIGHT", "dst": "LOOSE",
         "type": "NECESSARY_CONDITION", "why": "drops equations"},
        {"ev": "claim", "id": "CL", "model": "LOOSE", "kind": "PREDICATE",
         "statement": "P"},
        {"ev": "inference", "id": "INF", "claim": "CL",
         "path": [["E", "AGAINST"]], "asserted": "so P holds tighter"}])
    i = g.inferences["INF"]
    assert i["premises"] == [{"claim": "CL", "path": [("E", "AGAINST")]}]
    assert i["claim"] == "CL" and i["concludes_at"] == "TIGHT"


def test_declaring_both_forms_at_once_is_refused():
    """Two sources of truth for the same field is how they drift apart."""
    with pytest.raises(S.GraphError):
        _graph(TWO_MODELS + [
            {"ev": "edge", "id": "E", "src": "TIGHT", "dst": "LOOSE",
             "type": "NECESSARY_CONDITION", "why": "w"},
            {"ev": "claim", "id": "CL", "model": "LOOSE", "kind": "PREDICATE",
             "statement": "P"},
            {"ev": "inference", "id": "INF", "claim": "CL", "path": [],
             "premises": [{"claim": "CL", "path": []}], "asserted": "x"}])


# ===========================================================================
# THE T1 DEFECTS.  A live blind run produced all three of these, and every one
# needed a human auditor to find.  They now fail at declaration.
# ===========================================================================
def test_a_parallel_edge_cannot_silently_override_a_refusal():
    """THE HOLE T1 WENT THROUGH.

    The fold refuses a CONFLICTING REDECLARATION of an edge id, and that
    guarantee held perfectly -- so an agent wanting to retype an edge declared a
    NEW one with the same endpoints and the type it wanted, honestly labelled a
    "TYPED SUCCESSOR".

    Append-only prevents MUTATION and permits SUPERSESSION, and supersession has
    the same licensing effect with none of the visibility.  In the live case an
    UNTYPED edge was refusing a claim whose own cite read "NOT DERIVED. Recorded
    so that using it is a type error rather than a habit", and the parallel edge
    handed that claim a licence while `gp check` went on printing the refusal.
    """
    g = _graph(TWO_MODELS + [
        {"ev": "edge", "id": "E-OLD", "src": "TIGHT", "dst": "LOOSE",
         "type": "UNTYPED", "why": "not yet known",
         "debt_why": "the relation has not been derived"},
        {"ev": "edge", "id": "E-NEW", "src": "TIGHT", "dst": "LOOSE",
         "type": "NECESSARY_CONDITION", "why": "typed successor"},
    ])
    par = [f for f in C.run(g) if f.rule == C.R_PARALLEL]
    assert len(par) == 1
    assert "E-OLD" in par[0].detail and "E-NEW" in par[0].detail
    assert "supersedes" in par[0].discharge


def test_one_edge_between_two_models_is_not_a_finding():
    """The positive control: the ordinary case must stay silent."""
    g = _graph(TWO_MODELS + [
        {"ev": "edge", "id": "E", "src": "TIGHT", "dst": "LOOSE",
         "type": "NECESSARY_CONDITION", "why": "drops equations"}])
    assert not [f for f in C.run(g) if f.rule == C.R_PARALLEL]


def test_a_conclusion_at_a_model_proven_empty_is_flagged_vacuous():
    """Every predicate holds of the empty set, so a PREDICATE concluding at a
    model the graph proves EMPTY says nothing -- while reading as a result,
    carrying an evidence grade, and counting as a CLEAN inference.

    The source campaign has logged this failure mode three times; a live run
    produced a fourth, recording a cap slope `exact-checked` at a model the
    same batch proved empty, with the claim's own statement hedging "would
    read".  Graded TRIAGE: vacuous truths are true, and the damage is to the
    reader who counts them as evidence.
    """
    g = _graph(TWO_MODELS + [
        {"ev": "edge", "id": "E", "src": "TIGHT", "dst": "LOOSE",
         "type": "NECESSARY_CONDITION", "why": "drops equations"},
        {"ev": "claim", "id": "C-EMPTY", "model": "TIGHT", "kind": "EMPTY",
         "statement": "no points here", "certificate": "UNIT_IDEAL_CERT"},
        {"ev": "claim", "id": "C-PRED", "model": "LOOSE", "kind": "PREDICATE",
         "statement": "every point satisfies P"},
        {"ev": "inference", "id": "INF", "claim": "C-PRED",
         "path": [["E", "AGAINST"]],
         "asserted": "so every point of the tighter model satisfies P"},
    ])
    findings = C.run(g)
    vac = [f for f in findings if f.rule == C.R_VACUOUS]
    assert len(vac) == 1 and vac[0].subject == "INF"
    assert vac[0].severity == C.TRIAGE
    # And it must still count as a clean transport -- the point is that being
    # licensed and being informative are different questions.
    assert "INF" in C.clean_inferences(g, findings)


def test_a_model_built_by_reasoning_inside_itself_is_flagged():
    """`built_by` records that a model owes its existence to an inference. If
    that inference's premise lives IN the model it builds, the provenance is
    circular and the taint rule has no antecedent to follow."""
    g = _graph(TWO_MODELS + [
        {"ev": "edge", "id": "E", "src": "TIGHT", "dst": "LOOSE",
         "type": "NECESSARY_CONDITION", "why": "drops equations"},
        {"ev": "claim", "id": "CL", "model": "TIGHT", "kind": "NONEMPTY",
         "statement": "a point", "scope": "Q"},
        {"ev": "inference", "id": "INF", "claim": "CL",
         "path": [["E", "ALONG"]], "asserted": "the point is in LOOSE"},
        {"ev": "built_by", "model": "TIGHT", "inference": "INF"},
    ])
    sb = [f for f in C.run(g) if f.rule == C.R_SELF_BUILT]
    assert len(sb) == 1 and sb[0].subject == "TIGHT"


def test_an_identity_with_no_origin_does_not_fold():
    """There is no safe default, and the argument is not that a default would
    be unsound -- DERIVED would be safe.  It is that a default writes an
    unattributable claim into the artifact that IS the campaign state."""
    with pytest.raises(K.IdentityOriginError) as exc:
        _graph(TWO_MODELS + [
            {"ev": "claim", "id": "CL", "model": "TIGHT", "kind": "IDENTITY",
             "statement": "x = 0"}])
    msg = str(exc.value)
    assert "AMBIENT" in msg and "DERIVED" in msg and "UNKNOWN" in msg
    assert "cas_classify_identity" in msg, (
        "the refusal must name the computation that settles it, or UNKNOWN is "
        "just nagging")


def test_unknown_is_a_legal_answer_that_reports_as_debt():
    """The UNTYPED bargain, one level down: the honest answer is always
    available, which is what makes the field requirable."""
    g = _graph(TWO_MODELS + [
        {"ev": "claim", "id": "CL", "model": "TIGHT", "kind": "IDENTITY",
         "statement": "x = 0", "identity_origin": "UNKNOWN"}])
    debts = [f for f in C.run(g) if f.rule == C.R_IDENTITY_ORIGIN]
    assert len(debts) == 1
    assert debts[0].severity == C.DEBT
    assert "AMBIENT" in debts[0].discharge and "DERIVED" in debts[0].discharge


def test_an_unknown_origin_blocks_the_widening_but_not_the_restriction():
    """UNKNOWN licenses exactly what BOTH origins license -- which is the
    restriction and not the widening."""
    events = TWO_MODELS + [
        {"ev": "edge", "id": "E", "src": "TIGHT", "dst": "LOOSE",
         "type": "NECESSARY_CONDITION", "why": "drops equations",
         "map_kind": "POLYNOMIAL"},
        {"ev": "claim", "id": "CT", "model": "TIGHT", "kind": "IDENTITY",
         "statement": "x = 0", "identity_origin": "UNKNOWN"},
        {"ev": "claim", "id": "CL", "model": "LOOSE", "kind": "IDENTITY",
         "statement": "y = y", "identity_origin": "UNKNOWN"},
        {"ev": "inference", "id": "WIDEN", "claim": "CT",
         "path": [["E", "ALONG"]], "asserted": "x = 0 in the looser model"},
        {"ev": "inference", "id": "RESTRICT", "claim": "CL",
         "path": [["E", "AGAINST"]], "asserted": "y = y in the tighter model"},
    ]
    g = _graph(events)
    assert not C.audit_inference(g, "WIDEN")[0]
    assert C.audit_inference(g, "RESTRICT")[0]
