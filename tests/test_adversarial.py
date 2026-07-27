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
import sys

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
        {"ev": "claim", "id": "C1", "model": "M1", "kind": "NONEMPTY", "witness_kind": "EXHIBITED",
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
        {"ev": "claim", "id": "CL", "model": "LOOSE", "kind": "NONEMPTY", "witness_kind": "EXHIBITED",
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
        {"ev": "claim", "id": "CL", "model": "LOOSE", "kind": "NONEMPTY", "witness_kind": "EXHIBITED",
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
# DISCHARGE QUALITY.  T5's remaining findings -- fixed so the NEXT run's data
# is interpretable, not because they were cosmetic.
# ===========================================================================
def test_a_cited_proof_has_a_certificate_and_must_name_its_field():
    """T5's worst stretch. A refereed theorem had to be recorded as EMPTY,
    EMPTY demands a certificate, and nothing in the registry meant "somebody
    proved this in a journal" -- so one was manufactured.

    CITED_PROOF's base_changes=False is not a claim that the theorem is
    field-relative. It is a refusal to guess: the argument is not here, so
    nothing in the graph can tell whether it survives enlarging the field. The
    consequence is the useful part -- the author is forced to name the field
    the cited result is stated over, which is the question people skip when
    quoting a theorem.
    """
    g = _graph([
        {"ev": "model", "id": "M", "desc": "the tensor", "field": "C"},
        {"ev": "claim", "id": "CT", "model": "M", "kind": "EMPTY",
         "statement": "border rank > 15", "certificate": "CITED_PROOF",
         "scope": "C", "established_by": "CITED", "ladder": "claimed"}])
    assert g.claims["CT"]["scope"] == "C"
    with pytest.raises(K.ScopeError):
        _graph([{"ev": "model", "id": "M", "desc": "x"},
                {"ev": "claim", "id": "CT", "model": "M", "kind": "EMPTY",
                 "statement": "x", "certificate": "CITED_PROOF"}])


def test_the_table_says_what_specialization_means():
    """A foreign campaign used SPECIALIZATION for an INDEX RESTRICTION --
    running 3 of 527 cases -- because the name reads generically and `gp table`
    printed transport rows without saying what any name denotes. The row is
    uniformly NO, so the verdict was right by luck while the advice talked
    about Fano over F_2."""
    assert "CHARACTERISTIC" in K.TYPE_MEANS[K.SPECIALIZATION]
    assert "partition" in K.TYPE_MEANS[K.SPECIALIZATION], (
        "it must say where a case split SHOULD go, or the reader picks the "
        "next-closest wrong type")
    assert set(K.TYPE_MEANS) == set(K.DECLARABLE_TYPES)
    from grandportage.discharge import discharge_for
    move = discharge_for(K.SPECIALIZATION, K.AGAINST, K.PREDICATE)
    assert "CHECK THE TYPE IS RIGHT" in move


def test_an_edge_can_supply_the_remedy_the_table_cannot_know():
    """Two of four T5 findings gave advice for a different problem -- Galois
    cocycles for a floating-point rounding failure, mod-p flatness for an index
    restriction. The refusals were right; the remediation was not.

    The REQUIREMENT belongs to the cell and stays there. The REMEDY belongs to
    the campaign, which is the only thing that knows it.
    """
    from grandportage.discharge import discharge_for
    hint = "round the SDP Gram matrix to rationals and re-verify in Macaulay2"
    move = discharge_for(K.BASE_EXTENSION, K.AGAINST, K.NONEMPTY,
                         edge={"src": "QQ", "dst": "RR",
                               "discharge_hint": hint})
    assert move.startswith("REQUIRED:"), (
        "the cell's requirement must lead; a campaign hint supplements it")
    assert hint in move
    # And the generic illustration must be marked as one.
    plain = discharge_for(K.BASE_EXTENSION, K.AGAINST, K.NONEMPTY)
    assert "ILLUSTRATION" in plain and "may not be your case" in plain


# ===========================================================================
# MIGRATION.  The bill for "blank raises", and it came due all at once.
# ===========================================================================
def _stale(tmp_path, events):
    p = S.graph_path(str(tmp_path))
    os.makedirs(os.path.dirname(p), exist_ok=True)
    with open(p, "w", encoding="utf-8") as fh:
        for e in events:
            fh.write(json.dumps(e) + "\n")
    return p


def test_migrate_fills_a_missing_required_field_with_its_ignorance_value(tmp_path):
    """`witness_kind` and the `ladder` vocabulary stopped THREE live campaign
    logs from folding, including the T1 blind run's own output. Hand-editing an
    append-only log is what this project refuses to make people do, and at
    every version bump it would be the first thing anyone had to do.

    The no-silent-defaults principle survives because ASSERTED is not a guess.
    It is true: the claim was recorded before anyone was asked.
    """
    from grandportage import cli
    _stale(tmp_path, [
        {"ev": "model", "id": "M", "desc": "m"},
        {"ev": "claim", "id": "CL", "model": "M", "kind": "NONEMPTY",
         "statement": "a point", "scope": "Q"}])
    with pytest.raises(K.WitnessError):
        S.load(S.graph_path(str(tmp_path)))
    assert cli.main(["--root", str(tmp_path), "migrate"]) == 0
    g = S.load(S.graph_path(str(tmp_path)))
    assert g.claims["CL"]["witness_kind"] == K.ASSERTED
    # ...and the graph is now LOUDER, not quieter.
    assert [f for f in C.run(g) if f.rule == C.R_WITNESS]


def test_migrate_refuses_to_repair_a_value_that_is_wrong_not_missing(tmp_path):
    """An invalid `ladder` might belong in `established_by`, or in `caveat`, or
    be a genuine strength claim. Only the author knows, so migrate reports and
    leaves it alone -- and exits nonzero so it cannot be skipped.

    Confirmed against the real T5 graph, which still does not fold for exactly
    this reason.
    """
    from grandportage import cli
    _stale(tmp_path, [
        {"ev": "model", "id": "M", "desc": "m"},
        {"ev": "claim", "id": "CL", "model": "M", "kind": "PREDICATE",
         "statement": "P", "ladder": "ARTIFACT"}])
    assert cli.main(["--root", str(tmp_path), "migrate"]) == 1
    # untouched
    raw = open(S.graph_path(str(tmp_path)), encoding="utf-8").read()
    assert '"ladder": "ARTIFACT"' in raw or '"ladder":"ARTIFACT"' in raw


def test_migrate_dry_run_writes_nothing(tmp_path):
    """A migration that rewrites a version-controlled log had better be
    inspectable first."""
    from grandportage import cli
    p = _stale(tmp_path, [
        {"ev": "model", "id": "M", "desc": "m"},
        {"ev": "claim", "id": "CL", "model": "M", "kind": "IDENTITY",
         "statement": "x = 0"}])
    before = open(p, encoding="utf-8").read()
    cli.main(["--root", str(tmp_path), "migrate", "--dry-run"])
    assert open(p, encoding="utf-8").read() == before


def test_migrate_is_idempotent(tmp_path):
    """Running it twice must not churn a version-controlled file."""
    from grandportage import cli
    p = _stale(tmp_path, [
        {"ev": "model", "id": "M", "desc": "m"},
        {"ev": "claim", "id": "CL", "model": "M", "kind": "IDENTITY",
         "statement": "x = 0"}])
    cli.main(["--root", str(tmp_path), "migrate"])
    once = open(p, encoding="utf-8").read()
    cli.main(["--root", str(tmp_path), "migrate"])
    assert open(p, encoding="utf-8").read() == once
    assert S.load(p).claims["CL"]["identity_origin"] == K.UNKNOWN


# ===========================================================================
# EVIDENCE GRADING.  Two axes, and fusing them is why the field rotted.
# ===========================================================================
def _claim(**kw):
    base = {"ev": "claim", "id": "CL", "model": "TIGHT", "kind": "PREDICATE",
            "statement": "P holds"}
    base.update(kw)
    return _graph(TWO_MODELS + [base])


def test_ladder_is_a_closed_set_and_is_now_enforced():
    """FOUND BY T5, and not by exploitation -- by a stranger trying to use it.

    Pointed at a campaign that had never heard of the tool, `ladder` came back
    with SEVEN distinct values and ZERO overlap with the five it declares, some
    of them paragraphs. It was unvalidated free text, so a careful user filled
    it with prose rather than noticing it was a closed set.

    Fourth instance of one pattern -- certificates, identity_origin, kind,
    ladder -- a field whose value is taken on the author's word.
    """
    with pytest.raises(K.EvidenceError) as exc:
        _claim(ladder="ARTIFACT")
    msg = str(exc.value)
    assert "established_by" in msg and "caveat" in msg, (
        "the refusal must route the value to the field it belongs in, or the "
        "user simply picks another wrong word")


@pytest.mark.parametrize("by,ladder", [
    ("NOT_REACHED", "exact-checked"),
    ("NOT_REACHED", "independently-audited"),
    ("CITED", "exact-checked"),
    ("CITED", "independently-audited"),
    ("READ", "exact-checked"),
])
def test_impossible_evidence_combinations_are_refused(by, ladder):
    """THE PAYOFF OF SPLITTING THE AXES: evidence grading became checkable for
    the first time, without licensing anything.

    A gated checker cannot have verified something you could not run. A
    citation is not a checker run. Reading source establishes what the code
    SAYS, not that running it produced this. None of these is a soundness rule
    -- `ladder` still licenses nothing -- but a record that says two
    incompatible things about its own evidence is worse than one saying
    nothing.
    """
    with pytest.raises(K.EvidenceError) as exc:
        _claim(established_by=by, ladder=ladder)
    assert "cannot both be true" in str(exc.value)


def test_honest_evidence_combinations_pass():
    """The positive control. A grading scheme that refuses every combination
    would just push people back to leaving it blank."""
    for by, ladder in [("RAN", "exact-checked"), ("READ", "claimed"),
                       ("CITED", "claimed"), ("NOT_REACHED", "open"),
                       ("RAN", "independently-audited")]:
        _claim(established_by=by, ladder=ladder)


def test_evidence_is_optional_because_it_licenses_nothing():
    """Unlike certificates and witnesses, an ungraded claim is merely ungraded
    rather than unsound -- so blank must stay legal. What is refused is a grade
    that is WRONG."""
    g = _claim()
    assert g.claims["CL"].get("ladder") is None
    # Both axes blank together stays legal.  It is HALF a grade that does not.
    _claim(established_by=K.RAN)


@pytest.mark.parametrize("ladder", K.LADDER_ASSERTS_A_RUN)
def test_a_grade_that_asserts_a_run_must_name_the_run(ladder):
    """FIFTH INSTANCE OF THE PATTERN, WITH A MUTATION.

    The first four -- certificates, identity_origin, kind, ladder -- were
    fields whose VALUE was taken on the author's word.  This is a field whose
    ABSENCE switched off the check on a neighbouring field's value.  Every key
    in IMPOSSIBLE_EVIDENCE matches on `established_by`, so omitting it means
    the pair evaluated is `(None, "exact-checked")`, which is in no table and
    contradicts nothing.  Optionality is not neutral when another rule keys on
    it.

    FOUND IN A LIVE CAMPAIGN, where all fourteen of its claims graded
    themselves exact-checked with no established_by -- so the cross-check,
    described in the kernel as "the first thing about evidence grading this
    tool has ever been able to verify", never evaluated once in a full
    session.  That session's central structural result rested on an unrecorded
    script, and its own report had to catch that by hand.

    `open` and `claimed` assert no event and stay free; only a grade that says
    a run happened has to say which.
    """
    with pytest.raises(K.EvidenceError) as exc:
        _claim(ladder=ladder)
    msg = str(exc.value)
    assert "established_by" in msg
    # The refusal must say which values could still stand against THIS grade.
    # Naming all four every time would be wrong: at `exact-checked` only RAN
    # survives, at `certified` three do.
    survives = [b for b in K.ESTABLISHED_BY
                if (b, ladder) not in K.IMPOSSIBLE_EVIDENCE]
    assert "{%s}" % ", ".join(survives) in msg


def test_the_half_grade_rule_does_not_fire_on_a_grade_that_claims_no_run():
    """The positive control, and the reason the rule is narrow.

    A rule that demanded provenance for every grade would push people back to
    leaving the field blank, which is the state it was invented to fix.
    `claimed` means the author says so, and that IS its own provenance.
    """
    for ladder in ("open", "claimed"):
        g = _claim(ladder=ladder)
        assert g.claims["CL"]["ladder"] == ladder
        assert g.claims["CL"].get("established_by") is None


def test_migrate_downgrades_a_half_grade_rather_than_inventing_a_provenance(tmp_path):
    """There is NO ignorance value for `established_by`.

    Every other migration fills an absent field with the value meaning "nobody
    vouched" -- UNKNOWN for an identity's origin, ASSERTED for a witness.  Here
    that value does not exist: NOT_REACHED would be a lie about the author, and
    it is refused against these grades anyway.  So the ignorance goes on the
    OTHER axis, and `claimed` is exactly it: the author says so, and nothing
    recorded says a run happened.

    The downgrade can be wrong, and the direction is the point.  A claim that
    really was checked gets under-graded, costing its conclusions nothing.  The
    reverse -- an unsupported `exact-checked` left standing -- is the failure
    this project exists to avoid.
    """
    from grandportage import cli
    p = _stale(tmp_path, [
        {"ev": "model", "id": "M", "desc": "m"},
        {"ev": "claim", "id": "CL", "model": "M", "kind": "PREDICATE",
         "statement": "P", "ladder": "exact-checked", "caveat": "pre-existing"}])
    with pytest.raises(K.EvidenceError):
        S.load(p)
    assert cli.main(["--root", str(tmp_path), "migrate"]) == 0
    c = S.load(p).claims["CL"]
    assert c["ladder"] == "claimed"
    assert c.get("established_by") is None, (
        "migrate must not invent a provenance -- there is no honest value")
    # The caveat says where the strength went, and does not eat what was there.
    assert "pre-existing" in c["caveat"] and "exact-checked" in c["caveat"]


def test_migrate_leaves_every_line_it_did_not_change_byte_identical(tmp_path):
    """WRITTEN AFTER MIGRATE DESTROYED TWO SHIPPED FIXTURES.

    The first version rebuilt the file from parsed events, so every `#` comment
    and every blank line vanished -- `load_events` discards them, and anything
    a parser discards a round-trip destroys.  An append-only log is a FILE
    FORMAT with human content in it, not the serialized form of a data
    structure.

    Four migrate regressions were written the session before this one and none
    caught it, because all four asserted what migrate WRITES and none asserted
    what it PRESERVES.
    """
    from grandportage import cli
    p = S.graph_path(str(tmp_path))
    os.makedirs(os.path.dirname(p), exist_ok=True)
    raw = [
        "# a header comment someone wrote by hand\n",
        json.dumps({"ev": "model", "id": "M", "desc": "m"}) + "\n",
        "\n",
        "#   grouping comment, with trailing spaces   \n",
        json.dumps({"ev": "claim", "id": "CL", "model": "M",
                    "kind": "PREDICATE", "statement": "P",
                    "ladder": "exact-checked"}) + "\n",
        "\n",
        json.dumps({"ev": "note", "text": "unaffected"}) + "\n",
    ]
    with open(p, "w", encoding="utf-8") as fh:
        fh.writelines(raw)

    assert cli.main(["--root", str(tmp_path), "migrate"]) == 0
    after = open(p, encoding="utf-8").readlines()

    assert len(after) == len(raw), "migrate changed the line count"
    for i, (was, now) in enumerate(zip(raw, after)):
        if i == 4:
            assert was != now, "the claim line was supposed to change"
        else:
            assert was == now, "migrate rewrote line %d, which it never touched" % (i + 1)


# ===========================================================================
# OPEN PREMISE SLOTS.  A claim that should exist and does not.
# ===========================================================================
def test_an_argument_can_declare_a_premise_it_does_not_have():
    """T5's headline gap. The campaign's central finding was that a claim the
    published artifact REQUIRES is absent -- nowhere in 529 files is there an
    'every candidate is killed' statement, because five are not killed.

    Both escapes were bad: writing the missing claim enters a falsehood into
    the graph, and writing nothing loses the finding. So the slot is declared
    and left open -- the fold accepts it, and the checker refuses to license
    the inference while naming exactly what is missing.
    """
    g = _graph(TWO_MODELS + [
        {"ev": "edge", "id": "E", "src": "TIGHT", "dst": "LOOSE",
         "type": "NECESSARY_CONDITION", "why": "drops equations"},
        {"ev": "claim", "id": "HAVE", "model": "LOOSE", "kind": "PREDICATE",
         "statement": "what the artifact does supply"},
        {"ev": "inference", "id": "INF", "premises": [
            {"claim": "HAVE", "path": [["E", "AGAINST"]]},
            {"required_kind": "EMPTY", "at": "LOOSE",
             "missing_why": "the conclusion needs every case killed and the "
                            "graph has no such claim"}],
         "concludes_kind": "PREDICATE", "asserted": "the artifact establishes X"},
    ])
    ok, trace = C.audit_inference(g, "INF")
    assert not ok
    missing = [t for t in trace if t[0] == "(missing)"]
    assert len(missing) == 1
    assert "EMPTY claim at LOOSE" in missing[0][3]
    assert "every case killed" in missing[0][3], (
        "the reason the premise is absent must travel with the refusal")


def test_an_open_slot_must_say_where_and_why():
    """An unexplained hole is indistinguishable from an oversight."""
    for bad in ({"required_kind": "EMPTY"},
                {"required_kind": "EMPTY", "at": "LOOSE"}):
        with pytest.raises(S.GraphError):
            _graph(TWO_MODELS + [
                {"ev": "inference", "id": "INF", "premises": [bad],
                 "asserted": "x"}])


# ===========================================================================
# MERGE REPORTING.  T4's other half.
# ===========================================================================
def _branch(tmp_path, name, desc, extra=()):
    p = tmp_path / ("%s.jsonl" % name)
    evs = [{"ev": "model", "id": "SEED", "desc": "the shared starting point"},
           {"ev": "model", "id": "SAT", "desc": desc}] + list(extra)
    p.write_text("\n".join(json.dumps(e) for e in evs) + "\n", encoding="utf-8")
    return str(p)


def test_a_merge_reports_every_conflict_not_just_the_first(tmp_path):
    """T4 failed its pass condition partly on this. The fold raises on the
    FIRST conflicting redeclaration, so a real two-branch merge showed one
    collision, and the second only appeared after the first was resolved and
    the fold re-run.

    On the live T4 logs there were two -- both agents independently chose `SAT`
    for the saturated system AND `INF_ANSWER` for their answer -- and only one
    was visible.
    """
    a = _branch(tmp_path, "a", "the closure of the x != 0 locus",
                [{"ev": "model", "id": "OTHER", "desc": "A's version"}])
    b = _branch(tmp_path, "b", "the closure of the x*y != 0 locus",
                [{"ev": "model", "id": "OTHER", "desc": "B's version"}])
    graph, conflicts = S.merge_report([a, b])
    assert graph is None, "a conflicted merge must not yield a graph"
    assert {c["id"] for c in conflicts} == {"SAT", "OTHER"}, (
        "both conflicts must be reported at once, not one per run")
    sat = [c for c in conflicts if c["id"] == "SAT"][0]
    assert sat["fields"] == ["desc"], (
        "the report must name WHICH fields differ, not print two JSON blobs")
    assert sat["a"]["line"] and sat["b"]["line"]


def test_a_clean_merge_composes_and_yields_the_folded_graph(tmp_path):
    """The positive control: branches that agree must merge silently, which is
    the property the append-only shape exists to give."""
    a = _branch(tmp_path, "a", "same wording",
                [{"ev": "model", "id": "A_ONLY", "desc": "A's own work"}])
    b = _branch(tmp_path, "b", "same wording",
                [{"ev": "model", "id": "B_ONLY", "desc": "B's own work"}])
    graph, conflicts = S.merge_report([a, b])
    assert conflicts == []
    assert set(graph.models) == {"SEED", "SAT", "A_ONLY", "B_ONLY"}


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
             "kind": "NONEMPTY", "witness_kind": "EXHIBITED", "statement": "a point", "scope": "Q"},
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
        {"ev": "claim", "id": "C-BAD", "model": "SIDE", "kind": "NONEMPTY", "witness_kind": "EXHIBITED",
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
        {"ev": "claim", "id": "CL", "model": "TIGHT", "kind": "NONEMPTY", "witness_kind": "EXHIBITED",
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


# ===========================================================================
# SUPERSESSION FOR CLAIMS AND INFERENCES.  Edges have had it since v0.2.
# ===========================================================================
_SUP_BASE = TWO_MODELS + [
    {"ev": "edge", "id": "E", "src": "TIGHT", "dst": "LOOSE",
     "type": K.NECESSARY_CONDITION, "why": "equations are dropped"},
]
# A PREDICATE moving ALONG a NECESSARY_CONDITION is refused: what holds of
# every point of the tighter model need not hold of the looser one's extra
# points.  Used here because it gives a finding to watch.
_REFUSED = {"ev": "inference", "id": "I1", "claim": "C1",
            "path": [["E", K.ALONG]], "concludes_kind": K.PREDICATE,
            "asserted": "P holds on the looser model too"}
_C1 = {"ev": "claim", "id": "C1", "model": "TIGHT", "kind": K.PREDICATE,
       "statement": "P holds"}


def test_amend_is_computed_not_declared():
    """THE CENSUS'S OWN AMENDMENT, and it is the dangerous one.

    A live campaign had to remint a claim to add `coefficients_in_base`, and
    described the change -- accurately -- as "same claim, with
    coefficients_in_base declared".  But that field is exactly what licenses an
    IDENTITY to cross a BASE_EXTENSION.  "I only added an attribute" is the
    sentence through which a transport-determining field arrives unexamined,
    and five separate defects in this project reduce to a field whose value was
    taken on the author's word.

    So the tool holds both records and diffs them.  AMEND is a computation.
    """
    with pytest.raises(K.SupersessionError) as exc:
        _graph(_SUP_BASE + [
            {"ev": "claim", "id": "C1", "model": "TIGHT", "kind": K.IDENTITY,
             "statement": "x = y", "identity_origin": K.DERIVED},
            {"ev": "claim", "id": "C1R", "model": "TIGHT", "kind": K.IDENTITY,
             "statement": "x = y", "identity_origin": K.DERIVED,
             "coefficients_in_base": True,
             "supersedes": "C1", "discharge_kind": K.AMEND}])
    msg = str(exc.value)
    assert "coefficients_in_base changed" in msg and "RELICENSE" in msg


def test_over_declaring_a_supersession_is_allowed():
    """One direction only.  Calling a citation fix a RESTATE costs a second
    look; calling a certificate swap an AMEND costs the second look that was
    needed.  Only the second is refused."""
    g = _graph(_SUP_BASE + [
        _C1,
        {"ev": "claim", "id": "C1R", "model": "TIGHT", "kind": K.PREDICATE,
         "statement": "P holds", "cite": "a better citation",
         "supersedes": "C1", "discharge_kind": K.RESTATE}])
    assert g.claims["C1"]["superseded_by"] == "C1R"


def test_a_superseded_premise_is_graded_by_what_actually_changed():
    """SUPERSESSION DELIBERATELY DOES NOT REPOINT ANYTHING.

    Making an inference follow its premise to the replacement would credit an
    argument against a record it was never checked against.  So the old
    argument keeps pointing at the old claim and the checker says so -- at a
    severity that depends on whether anything it relied on moved.

    An author who could self-report that distinction would always report the
    cheap one, which is why the kind is computed.
    """
    def stale(newer):
        g = _graph(_SUP_BASE + [_C1, _REFUSED, newer])
        return [f for f in C.run(g) if f.rule == C.R_STALE_PREMISE]

    # Nothing that licenses a transport moved -> the argument stands.
    amended = stale({"ev": "claim", "id": "C1R", "model": "TIGHT",
                     "kind": K.PREDICATE, "statement": "P holds",
                     "cite": "where it came from",
                     "supersedes": "C1", "discharge_kind": K.AMEND})
    assert len(amended) == 1 and amended[0].severity == C.DEBT
    assert "stale is the pointer" in amended[0].detail

    # A licensing attribute moved -> the argument is UNEXAMINED, not withdrawn.
    relicensed = stale({"ev": "claim", "id": "C1R", "model": "TIGHT",
                        "kind": K.PREDICATE, "statement": "P holds",
                        "scope": "Q(sqrt 17)",
                        "supersedes": "C1", "discharge_kind": K.RELICENSE})
    assert len(relicensed) == 1
    assert relicensed[0].severity == C.UNSOUND_PREMISE
    assert "UNEXAMINED" in relicensed[0].detail


def test_a_superseded_inference_stops_reporting_as_live_debt():
    """THE BASELINE DILUTION, which is the cost a live campaign actually paid.

    With no supersession, a reminted inference stayed in the graph forever and
    its findings kept reporting, so the baseline grew an entry meaning
    "superseded, not carried on its merits".  One entry like that makes every
    other entry in the file weaker.

    Nothing is hidden: the superseding inference is audited in its own right.
    """
    live = _graph(_SUP_BASE + [_C1, _REFUSED])
    assert [f for f in C.run(live) if f.rule == C.R_TRANSPORT
            and f.subject == "I1"], "the control has to actually be flagged"

    withdrawn = _graph(_SUP_BASE + [_C1, _REFUSED,
        {"ev": "inference", "id": "I2", "claim": "C1",
         "path": [["E", K.ALONG]], "concludes_kind": K.PREDICATE,
         "asserted": "P holds on the looser model, restated",
         "supersedes": "I1", "discharge_kind": K.RESTATE}])
    flagged = {f.subject for f in C.run(withdrawn) if f.rule == C.R_TRANSPORT}
    assert "I1" not in flagged, "a withdrawn inference is not live debt"
    assert "I2" in flagged, (
        "supersession must not be a way to make a finding disappear -- the "
        "replacement has the same defect and must still be caught")


def test_supersession_must_name_a_record_that_exists():
    """Otherwise `supersedes` is a comment.  The failure mode is a typo that
    silently withdraws nothing while reading as though it withdrew something.
    """
    with pytest.raises(S.GraphError) as exc:
        _graph(_SUP_BASE + [
            _C1,
            {"ev": "claim", "id": "C1R", "model": "TIGHT", "kind": K.PREDICATE,
             "statement": "P holds", "supersedes": "C-TYPO",
             "discharge_kind": K.AMEND}])
    assert "not a claim in this graph" in str(exc.value)


def test_supersession_must_say_how():
    """Same discipline edges have had since v0.2: replacing a record without
    saying what kind of replacement it is transfers no information."""
    with pytest.raises(S.GraphError) as exc:
        _graph(_SUP_BASE + [
            _C1,
            {"ev": "claim", "id": "C1R", "model": "TIGHT", "kind": K.PREDICATE,
             "statement": "P holds", "supersedes": "C1"}])
    assert "without saying HOW" in str(exc.value)


# ===========================================================================
# RESTRICTION.  The sixth type, and the first one a LIVE RUN forced.
# ===========================================================================
def test_restriction_is_not_necessary_condition_wearing_a_new_name():
    """`signature` exists to assert exactly this, and a new type is where it
    finally gets used in anger.

    The six point-cells ARE identical to NECESSARY_CONDITION's -- they follow
    from containment and nothing else, which is why NECESSARY_CONDITION was the
    attractor for the positivity-cone edge that forced this type, and why
    mislabelling it would have licensed nothing false.  The IDENTITY row is
    where they diverge, and the divergence is real: a restriction adds no
    equations, so there is no larger
    ideal and no quotient, and the obstruction that stops a DERIVED identity
    crossing a NECESSARY_CONDITION is simply absent.
    """
    import itertools
    sigs = {t: K.signature(t) for t in K.ALL_TYPES}
    dupes = [(a, b) for a, b in itertools.combinations(sorted(sigs), 2)
             if sigs[a] == sigs[b]]
    assert not dupes, "two types are the same table under different names: %s" % dupes

    point_kinds = (K.EMPTY, K.NONEMPTY, K.PREDICATE)
    for d, k in itertools.product(K.DIRECTIONS, point_kinds):
        assert (K.transport(K.RESTRICTION, d, k).licensed
                is K.transport(K.NECESSARY_CONDITION, d, k).licensed), (
            "%s/%s should agree with NECESSARY_CONDITION -- both follow from "
            "containment alone" % (d, k))


def test_a_restriction_may_not_change_coordinates():
    """The licence and the argument for it must not drift apart.

    IDENTITY crosses a RESTRICTION AGAINST unconditionally, where a
    NECESSARY_CONDITION needs a denominator-free map, for exactly one reason:
    a restriction substitutes nothing, because the coordinates are the same
    ones.  A RESTRICTION declared over a coordinate change would keep the
    licence and lose the reason.
    """
    with pytest.raises(S.GraphError) as exc:
        _graph(TWO_MODELS + [
            {"ev": "edge", "id": "E", "src": "TIGHT", "dst": "LOOSE",
             "type": K.RESTRICTION, "why": "positivity", "map_kind": "RATIONAL"}])
    assert "SAME COORDINATES" in str(exc.value)


def test_the_generic_versus_global_cell_refuses_and_says_why():
    """THE CELL THE CENSUS EXISTS TO PROTECT.

    A predicate holding at every point of a positivity cone is silent about
    the ambient model, and stating it there anyway -- taking a theorem proved
    off an exceptional locus and using it on data that may sit in the bad
    locus -- is a recurring error in the applied literature.

    The discharge must NOT offer a certificate, because there isn't one.  A
    refusal that implies a fix exists sends someone looking for it.
    """
    g = _graph(TWO_MODELS + [
        {"ev": "edge", "id": "E", "src": "TIGHT", "dst": "LOOSE",
         "type": K.RESTRICTION, "why": "the positive-definite cone"},
        {"ev": "claim", "id": "C", "model": "TIGHT", "kind": K.PREDICATE,
         "statement": "the parameter is recoverable from the data"},
        {"ev": "inference", "id": "I", "claim": "C", "path": [["E", K.ALONG]],
         "concludes_kind": K.PREDICATE,
         "asserted": "the parameter is recoverable on the whole model"}])
    found = [f for f in C.run(g) if f.rule == C.R_TRANSPORT and f.subject == "I"]
    assert found, "a generic result stated globally must not pass"
    assert "GENERIC-VERSUS-GLOBAL" in found[0].discharge
    assert "no certificate to produce" in found[0].discharge


def test_the_identity_cell_does_not_send_you_after_denominators():
    """A WRONG DISCHARGE IS WORSE THAN A TERSE ONE, and this cell had one.

    Before RESTRICTION got its own move, the IDENTITY refusal fell through to
    the generic identity text -- "this needs a DENOMINATOR-FREE map" -- which
    is NECESSARY_CONDITION's remedy and is irrelevant here.  A restriction
    changes no coordinates, so there is no map to make polynomial, and anyone
    following that advice would spend the effort and still be refused.
    """
    from grandportage.discharge import discharge_for
    msg = discharge_for(K.RESTRICTION, K.ALONG, K.IDENTITY,
                        edge={"src": "PD", "dst": "REAL"})
    assert "zariski_dense" in msg
    assert "NOT THE DENOMINATOR QUESTION" in msg
    # And it names the counterexample rather than asserting the condition is
    # usually fine, because "usually fine" is how a gate stops being consulted.
    assert "x^2 + y^2" in msg


def test_the_density_condition_is_declared_not_assumed():
    """Over R the real points of a variety need not be Zariski-dense in it, so
    the strongest cell of the strongest new type is gated by default."""
    base = TWO_MODELS + [
        {"ev": "claim", "id": "C", "model": "TIGHT", "kind": K.IDENTITY,
         "statement": "x = y", "identity_origin": K.DERIVED},
        {"ev": "inference", "id": "I", "claim": "C", "path": [["E", K.ALONG]],
         "concludes_kind": K.IDENTITY, "asserted": "x = y on the whole model"}]
    edge = {"ev": "edge", "id": "E", "src": "TIGHT", "dst": "LOOSE",
            "type": K.RESTRICTION, "why": "cut by strict inequalities"}

    gated = _graph([edge] + base)
    assert [f for f in C.run(gated) if f.rule == C.R_TRANSPORT], (
        "undeclared, the density cell must refuse")

    declared = _graph([dict(edge, zariski_dense=True)] + base)
    assert not [f for f in C.run(declared) if f.rule == C.R_TRANSPORT], (
        "declared, the identity crosses -- otherwise the type buys nothing "
        "over NECESSARY_CONDITION")


def test_the_readme_transport_table_matches_the_kernel():
    """THE README SAID IT COULD NOT DRIFT, AND IT HAD.

    "Printed by the kernel itself with `gp table`, so a document quoting it and
    the code applying it cannot drift apart" -- except nothing checked, and by
    the time RESTRICTION landed the table in the README was wrong in FIVE
    cells.  Every conditional IDENTITY cell still showed the PRE-v0.2 rule:
    EQUIVALENCE unconditional rather than needing a ring isomorphism,
    NECESSARY_CONDITION gated on denominators rather than on origin,
    BASE_EXTENSION descending for free.  Those are the exact licences that were
    found unsound and fixed, still documented as sound in the file a reader
    meets first.

    A claim of non-drift with nothing enforcing it is worse than no claim: it
    tells a reader they need not check.
    """
    import os
    import re
    readme = os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))),
                          "README.md")
    with open(readme, encoding="utf-8") as fh:
        text = fh.read()

    words = {"zariski_dense": "if Zariski-dense",
             "ambient_identity": "if ambient",
             "ring_isomorphism": "if ring iso",
             "coefficients_in_base": "if defined over base",
             "integral_identity": "if p-integral",
             "map_polynomial": "if denominator-free",
             "scheme_scope": "only with a certificate",
             "closed_condition": "if Zariski-closed"}

    documented = {}
    for line in text.splitlines():
        m = re.match(r"^\|\s*`([A-Z_]+)`\s*\|\s*\**(ALONG|AGAINST)\**\s*\|(.*)$",
                     line.strip())
        if not m:
            continue
        cells = [c.strip().replace("**", "")
                 for c in m.group(3).rstrip("|").split("|")]
        documented[(m.group(1), m.group(2))] = cells

    missing = [t for t in K.ALL_TYPES
               if not any(k[0] == t for k in documented)]
    assert not missing, "types absent from the README table: %s" % missing

    for (etype, direction), cells in sorted(documented.items()):
        assert len(cells) == len(K.CLAIM_KINDS), (etype, direction, cells)
        for kind, shown in zip(K.CLAIM_KINDS, cells):
            rule = K.TRANSPORT[etype][direction][kind]
            want = ("yes" if rule is True else "NO" if rule is False
                    else words.get(rule, rule))
            assert shown == want, (
                "README documents %s/%s/%s as %r; the kernel says %r"
                % (etype, direction, kind, shown, want))


# ===========================================================================
# THE ACCEPT PATH.  Both defects here were found by a live campaign, and both
# are the same failure the baseline machinery exists to prevent, inside it.
# ===========================================================================
def _accept_fixture(tmp_path, events):
    p = S.graph_path(str(tmp_path))
    os.makedirs(os.path.dirname(p), exist_ok=True)
    with open(p, "w", encoding="utf-8") as fh:
        for e in events:
            fh.write(json.dumps(e) + "\n")
    return p


_TWO_FINDINGS = [
    {"ev": "model", "id": "T", "desc": "tight"},
    {"ev": "model", "id": "L", "desc": "loose"},
    {"ev": "edge", "id": "E1", "src": "T", "dst": "L",
     "type": K.NECESSARY_CONDITION, "why": "drops equations"},
    {"ev": "edge", "id": "E2", "src": "T", "dst": "L",
     "type": K.NECESSARY_CONDITION, "why": "drops equations again"},
    {"ev": "claim", "id": "C", "model": "T", "kind": K.PREDICATE,
     "statement": "P"},
    {"ev": "inference", "id": "I1", "claim": "C", "path": [["E1", K.ALONG]],
     "concludes_kind": K.PREDICATE, "asserted": "P on the looser model"},
]


def test_only_with_prune_does_not_delete_live_acceptances(tmp_path):
    """THE `--only` BASELINE WIPE, REINTRODUCED BY THE FLAG ADDED TO FIX IT.

    `prune` computed the surviving set from the list being ACCEPTED. `gp accept
    --only X` filters that list before calling, so `--only X --prune` deleted
    every other acceptance and reported each as "pruned: no longer in the
    graph" -- entries that were still live. The output did not merely get it
    wrong, it asserted the one fact that would have justified the deletion.

    One variable was carrying two questions: what am I accepting, and what
    still exists. They are equal only when nothing was filtered.
    """
    from grandportage import cli
    from grandportage import hook as H
    _accept_fixture(tmp_path, _TWO_FINDINGS)
    root = str(tmp_path)
    assert cli.main(["--root", root, "accept", "-m", "carrying both"]) == 0
    both = set(H.read_baseline(root)["accepted"])
    assert len(both) >= 2, "the fixture must produce at least two findings"

    keep = sorted(both)[0]
    assert cli.main(["--root", root, "accept", "--only", keep, "--prune",
                     "-m", "just this one"]) == 0
    after = set(H.read_baseline(root)["accepted"])
    assert after == both, (
        "--only narrows what is ACCEPTED and must never narrow what counts as "
        "still existing; lost %s" % sorted(both - after))
    # And the untouched entry keeps ITS OWN reason, not the new one.
    other = sorted(both - {keep})[0]
    assert H.read_baseline(root)["accepted"][other]["why"] == "carrying both"


def test_prune_still_drops_a_finding_that_really_left_the_graph(tmp_path):
    """The counter-test, and the one that stops the fix being 'disable prune'.

    A repair that makes a destructive operation safe by making it do nothing is
    not a repair. `prune` exists so a baseline does not accumulate acceptances
    for findings nobody can hit any more.
    """
    from grandportage import cli
    from grandportage import hook as H
    root = str(tmp_path)
    _accept_fixture(tmp_path, _TWO_FINDINGS)
    cli.main(["--root", root, "accept", "-m", "carrying both"])
    before = set(H.read_baseline(root)["accepted"])

    # Drop E2, so PARALLEL-EDGE genuinely no longer exists.
    _accept_fixture(tmp_path, [e for e in _TWO_FINDINGS if e.get("id") != "E2"])
    cli.main(["--root", root, "accept", "--prune", "-m", "sweep"])
    after = set(H.read_baseline(root)["accepted"])
    assert after < before, "prune must still drop what genuinely left"
    assert not any(f.startswith("PARALLEL-EDGE") for f in after)


def test_save_baseline_refuses_to_prune_without_being_told_what_is_live(tmp_path):
    """There is deliberately no default that reproduces the bug.

    A caller that cannot say what still exists has no business deleting
    anything, so `live` is mandatory under `prune` rather than defaulting back
    to the filtered list.
    """
    from grandportage import hook as H
    with pytest.raises(ValueError) as exc:
        H.save_baseline(str(tmp_path), [], prune=True)
    assert "not the same list" in str(exc.value)


def test_gp_accept_can_reach_a_supersession_finding(tmp_path):
    """THE ONE FINDING CLASS THE ACCEPT PATH COULD NOT SEE.

    `check_supersession` is the only rule that reads the baseline -- a
    SUPERSESSION finding exists BECAUSE a baseline entry pinned `admits` and a
    supersession offered a discharge outside it. `cmd_check` passed the
    baseline in; `cmd_accept` did not. So the one class that is definitionally
    baseline-derived was the one class `gp accept` reported as "no such
    finding" while `gp check` printed it two functions away.

    It fires at the hook's blocking floor and an append-only log cannot
    un-declare the record that caused it, so a live campaign reached a state
    where a finding could be neither discharged nor accepted and the hook
    refused EVERY tool call until the CLI was bypassed by hand.
    """
    from grandportage import cli
    from grandportage import hook as H
    root = str(tmp_path)
    _accept_fixture(tmp_path, [
        {"ev": "model", "id": "T", "desc": "tight"},
        {"ev": "model", "id": "L", "desc": "loose"},
        {"ev": "edge", "id": "E1", "src": "T", "dst": "L", "type": K.UNTYPED,
         "why": "unknown", "debt_why": "not yet worked out"},
        {"ev": "claim", "id": "C", "model": "L", "kind": K.PREDICATE,
         "statement": "P"},
        {"ev": "inference", "id": "I1", "claim": "C",
         "path": [["E1", K.AGAINST]], "concludes_kind": K.PREDICATE,
         "asserted": "P at the tighter model"},
    ])
    cli.main(["--root", root, "accept", "--admits", "DERIVE",
              "-m", "only a derivation closes this"])
    with open(S.graph_path(root), "a", encoding="utf-8") as fh:
        fh.write(json.dumps({
            "ev": "edge", "id": "E2", "src": "T", "dst": "L",
            "type": K.NECESSARY_CONDITION, "why": "drops equations",
            "supersedes": "E1", "discharge_kind": "RETYPE"}) + "\n")

    g = S.load(S.graph_path(root))
    accepted = H.read_baseline(root)["accepted"]
    fids = [f.fid for f in C.run(g, accepted) if f.rule == C.R_SUPERSEDE]
    assert fids, "the fixture must actually produce a SUPERSESSION finding"

    assert cli.main(["--root", root, "accept", "--only", fids[0],
                     "-m", "reviewed: retyping really is right here"]) == 0, (
        "gp accept must be able to reach the finding gp check prints")
    assert fids[0] in H.read_baseline(root)["accepted"]


@pytest.mark.parametrize("slot_first", [False, True])
def test_an_open_premise_slot_survives_the_whole_checker_not_just_the_audit(slot_first):
    """`gp check` CRASHED on the construct built for T5's headline finding.

    `audit_inference` emits the sentinel `(missing)` in the edge position for
    an open slot -- nothing was traversed. `_first_refusal` looked that up in
    `graph.edges` and raised KeyError, so any graph declaring a slot took down
    the checker, the hook and the MCP server. A crashing checker is
    indistinguishable from a checker nobody ran.

    IT SURVIVED THE TEST WRITTEN FOR IT. The existing open-slot regression
    calls `audit_inference` directly and never `run`, so the construct was
    correct in every respect except being reachable. That is the same shape as
    the defects a live campaign found in `gp accept` and `portage_show`: the
    unit was right and the path through it was not.

    Both premise orders, because when the slot comes FIRST the fold leaves the
    legacy `claim` field None and two further lines used it as a dict key.
    """
    premises = [{"claim": "HAVE", "path": [["E", K.AGAINST]]},
                {"required_kind": K.EMPTY, "at": "LOOSE",
                 "missing_why": "the conclusion needs every case killed and "
                                "the graph has no such claim"}]
    if slot_first:
        premises = premises[::-1]
    g = _graph(TWO_MODELS + [
        {"ev": "edge", "id": "E", "src": "TIGHT", "dst": "LOOSE",
         "type": K.NECESSARY_CONDITION, "why": "drops equations"},
        {"ev": "claim", "id": "HAVE", "model": "LOOSE", "kind": K.PREDICATE,
         "statement": "what the artifact does supply"},
        {"ev": "inference", "id": "INF", "premises": premises,
         "concludes_kind": K.PREDICATE,
         "asserted": "the artifact establishes X"}])

    findings = C.run(g)                       # <-- the path, not the function
    transport = [f for f in findings if f.rule == C.R_TRANSPORT]
    assert len(transport) == 1
    f = transport[0]
    assert f.severity == C.UNSOUND_PREMISE
    # It must name what is missing, not a transport cell that was never reached.
    assert "needs a EMPTY claim at LOOSE" in f.detail
    assert "SUPPLY THE MISSING CLAIM" in f.discharge
    assert "no edge to retype" in f.discharge
    # And it must not invite the one repair that would be a lie.
    assert "as though it held" in f.discharge

    # The whole surface, not just check.run: these all crashed too.
    C.render(findings, {}, False)
    assert C.exit_code(findings, C.UNSOUND_PREMISE) != 0


# ===========================================================================
# PARTITIONS AND RULE NAMES.  Both found by the chart-map campaign.
# ===========================================================================
_PART_BASE = [
    {"ev": "model", "id": "P", "desc": "parent"},
    {"ev": "model", "id": "B1", "desc": "branch one"},
    {"ev": "model", "id": "B2", "desc": "branch two"},
    {"ev": "edge", "id": "EB1", "src": "B1", "dst": "P",
     "type": K.NECESSARY_CONDITION, "why": "a branch"},
    {"ev": "edge", "id": "EB2", "src": "B2", "dst": "P",
     "type": K.NECESSARY_CONDITION, "why": "a branch"},
    {"ev": "claim", "id": "X", "model": "B1", "kind": K.EMPTY,
     "statement": "branch one is empty", "certificate": "UNIT_IDEAL_CERT"},
    {"ev": "claim", "id": "EXH", "model": "P", "kind": K.PREDICATE,
     "statement": "the branches are exhaustive"},
    {"ev": "partition", "id": "PG", "parent": "P", "branches": ["B1", "B2"],
     "exhaustive": "EXH", "why": "gamma is 2 or 3"},
]


def test_a_partition_reports_when_it_FAILS_not_only_when_it_succeeds():
    """THE MECHANISM WAS UNREACHABLE IN THE CASE IT WAS BUILT FOR.

    `audit_inference` returns the partition id in the trace's edge position,
    and `_first_refusal` looked that up in `graph.edges` -- KeyError. So a case
    split that COVERS its parent reported fine and one that did not took down
    the checker. The uncovered-branch case is the entire reason the construct
    exists; `transport_over_partition`'s own docstring names it.

    A campaign hit this trying to record that a published case analysis leaves
    one case open, and could not record the parent-level conclusion at all.
    """
    g = _graph(_PART_BASE + [
        {"ev": "inference", "id": "IP", "via_partition": "PG",
         "premises": [{"claim": "X", "path": []}, {"claim": "EXH", "path": []}],
         "concludes_kind": K.EMPTY, "asserted": "the parent is empty"}])
    found = [f for f in C.run(g) if f.rule == C.R_TRANSPORT]
    assert len(found) == 1
    assert "B2" in found[0].detail, "it must name the branch left open"
    # And the discharge must be about COVERAGE, not about a transport cell or
    # a missing premise -- neither of which is what went wrong.
    assert "COVER EVERY BRANCH" in found[0].discharge
    assert "no edge to retype" not in found[0].discharge


def test_an_open_slot_inside_a_partition_names_the_unsettled_branch():
    """`graph.claims[pr["claim"]]` with claim=None -- KeyError: None.

    So the most honest thing a case analysis can say -- "this branch is not
    settled, here is which and why" -- was the one thing that crashed. `store`
    handles the same field correctly two files away.

    A slot must contribute NOTHING to coverage: it is a declaration that the
    branch is open, so the partition stays refused.
    """
    g = _graph(_PART_BASE + [
        {"ev": "inference", "id": "IP", "via_partition": "PG",
         "premises": [{"claim": "X", "path": []}, {"claim": "EXH", "path": []},
                      {"required_kind": K.EMPTY, "at": "B2",
                       "missing_why": "the gamma=4 case is not settled"}],
         "concludes_kind": K.EMPTY, "asserted": "the parent is empty"}])
    found = [f for f in C.run(g) if f.rule == C.R_TRANSPORT]
    assert len(found) == 1, "a slot settles nothing, so this stays refused"
    assert "the gamma=4 case is not settled" in found[0].detail


@pytest.mark.parametrize("bad,real", [
    ("ring_isomorphism", "ring_iso"),
    ("map_polynomial", "map_kind"),
])
def test_a_rule_name_used_as_a_field_name_is_refused(bad, real):
    """SILENTLY STORED AND IGNORED, which is the worst available outcome.

    Refusals report the RULE that blocked them. For `ring_isomorphism` the
    field you must actually set is `ring_iso`, and `gp table` prints rule names
    in a column that reads like fields. A campaign declared
    `ring_isomorphism: true` on two EQUIVALENCE edges; it was accepted and did
    nothing. Nothing false was licensed there by luck -- but an EQUIVALENCE
    relied on to carry an IDENTITY would have been refused with no hint why.

    WHAT MAKES THE MISTAKE REASONABLE IS THAT IT IS SOMETIMES RIGHT: two of the
    seven rule names ARE the field. So the user's inference about the
    vocabulary is sound and wrong about this word, which is exactly the case
    that must not fail silently.
    """
    with pytest.raises(S.GraphError) as exc:
        _graph(TWO_MODELS + [
            {"ev": "edge", "id": "E", "src": "TIGHT", "dst": "LOOSE",
             "type": K.EQUIVALENCE, "why": "reversible",
             "converse_witness": "the inverse construction", bad: True}])
    msg = str(exc.value)
    assert real in msg, "the refusal must name the field they meant"
    assert "stored and ignored" in msg


def test_a_withdrawn_inference_is_not_counted_as_a_positive_control():
    """`clean_inferences` counted everything `check_transport` did not flag,
    and `check_transport` correctly skips superseded inferences -- so every
    withdrawn argument was promoted into the clean list.

    A campaign's `gp check` reported "clean inferences (5)" of which four were
    withdrawn. That number IS the credibility claim: it is what a reader uses
    to decide the checker is not simply refusing everything.
    """
    # A PREDICATE travelling AGAINST a NECESSARY_CONDITION is licensed, so both
    # of these would be clean -- which is the point: the bug promoted a
    # WITHDRAWN clean inference, not a refused one.
    g = _graph(_SUP_BASE + [
        {"ev": "claim", "id": "CL", "model": "LOOSE", "kind": K.PREDICATE,
         "statement": "P holds on the looser model"},
        {"ev": "inference", "id": "I1", "claim": "CL",
         "path": [["E", K.AGAINST]], "concludes_kind": K.PREDICATE,
         "asserted": "P holds at the tighter model"},
        {"ev": "inference", "id": "I2", "claim": "CL",
         "path": [["E", K.AGAINST]], "concludes_kind": K.PREDICATE,
         "asserted": "P holds at the tighter model, restated",
         "supersedes": "I1", "discharge_kind": K.RESTATE}])
    findings = C.run(g)
    assert not [f for f in findings if f.rule == C.R_TRANSPORT], (
        "the fixture must be clean, or this tests the wrong thing")
    clean = C.clean_inferences(g, findings)
    assert "I1" not in clean, "a withdrawn inference is not a positive control"
    assert "I2" in clean, "and the live replacement still is"


def test_migrate_renames_a_rule_name_used_as_a_field(tmp_path):
    """The store now REFUSES `ring_isomorphism`, which breaks every graph that
    already carries it -- and a live campaign's did, four times.

    Renaming is safe here and nowhere else in that table: `ring_isomorphism`
    and `ring_iso` are both booleans meaning the same thing, so the key is
    wrong and the value is not. `map_polynomial: true` would have to become
    `map_kind: POLYNOMIAL` -- a value change, and a choice among three -- so it
    is reported for a human instead, and migrate exits nonzero.
    """
    from grandportage import cli
    p = _stale(tmp_path, [
        {"ev": "model", "id": "T", "desc": "t"},
        {"ev": "model", "id": "L", "desc": "l"},
        {"ev": "edge", "id": "E", "src": "T", "dst": "L",
         "type": K.EQUIVALENCE, "why": "reversible",
         "converse_witness": "the inverse", "ring_isomorphism": True}])
    with pytest.raises(S.GraphError):
        S.load(p)
    assert cli.main(["--root", str(tmp_path), "migrate"]) == 0
    e = S.load(p).edges["E"]
    assert e.get("ring_iso") is True and "ring_isomorphism" not in e
    # And the renamed field now actually does something.
    assert K.transport(K.EQUIVALENCE, K.ALONG, K.IDENTITY,
                       ring_iso=e["ring_iso"]).licensed


def test_migrate_refuses_to_guess_a_rule_name_whose_VALUE_must_change(tmp_path):
    """`map_polynomial: true` -> `map_kind: ???`. Only the author knows which
    of the three, so it is reported and left alone."""
    from grandportage import cli
    p = _stale(tmp_path, [
        {"ev": "model", "id": "T", "desc": "t"},
        {"ev": "model", "id": "L", "desc": "l"},
        {"ev": "edge", "id": "E", "src": "T", "dst": "L",
         "type": K.NECESSARY_CONDITION, "why": "drops equations",
         "map_polynomial": True}])
    assert cli.main(["--root", str(tmp_path), "migrate"]) == 1
    raw = open(p, encoding="utf-8").read()
    assert "map_polynomial" in raw, "left untouched for a human"


@pytest.mark.parametrize("entity", ["claim", "edge", "inference"])
def test_supersession_does_not_make_the_fold_order_dependent(entity):
    """MERGING IS CONCATENATE-AND-FOLD, and supersession briefly broke that.

    Checking `supersedes` inside `_apply_claim` meant the superseded record had
    to have been folded already:

        merge [old_branch, new_branch]  -> folds
        merge [new_branch, old_branch]  -> "supersedes X, which is not a claim
                                            in this graph"

    `load`'s docstring says order does not matter, DESIGN.md sells merging as
    concatenating logs, and `apply_all`'s own comment says CERTIFICATES ARE THE
    ONLY event kind whose prior presence changes how a later event folds. That
    sentence was falsified in the same file that explains why it must not be.

    The failure is not cosmetic: an unfoldable graph makes `hook.evaluate` fail
    CLOSED, so the wrong concatenation order blocks every tool call in a
    session -- a merge order deciding whether you can work.

    Fixed by resolving supersession in `validate()`, with every other
    cross-reference. Parametrised over all three because edges got the check at
    the same time and could regress independently.
    """
    models = [{"ev": "model", "id": "M", "desc": "m"},
              {"ev": "model", "id": "N", "desc": "n"}]
    old, new = {
        "claim": ([{"ev": "claim", "id": "C", "model": "M",
                    "kind": K.PREDICATE, "statement": "P"}],
                  [{"ev": "claim", "id": "CR", "model": "M",
                    "kind": K.PREDICATE, "statement": "P",
                    "cite": "a better citation", "supersedes": "C",
                    "discharge_kind": K.AMEND}]),
        "edge": ([{"ev": "edge", "id": "E1", "src": "M", "dst": "N",
                   "type": K.UNTYPED, "why": "?", "debt_why": "unknown"}],
                 [{"ev": "edge", "id": "E2", "src": "M", "dst": "N",
                   "type": K.NECESSARY_CONDITION, "why": "drops equations",
                   "supersedes": "E1", "discharge_kind": "RETYPE"}]),
        "inference": ([{"ev": "edge", "id": "E", "src": "M", "dst": "N",
                        "type": K.NECESSARY_CONDITION, "why": "drops eqs"},
                       {"ev": "claim", "id": "C", "model": "N",
                        "kind": K.PREDICATE, "statement": "P"},
                       {"ev": "inference", "id": "I1", "claim": "C",
                        "path": [["E", K.AGAINST]],
                        "concludes_kind": K.PREDICATE, "asserted": "P at M"}],
                      [{"ev": "inference", "id": "I2", "claim": "C",
                        "path": [["E", K.AGAINST]],
                        "concludes_kind": K.PREDICATE,
                        "asserted": "P at M, restated", "supersedes": "I1",
                        "discharge_kind": K.RESTATE}]),
    }[entity]

    def fold(events):
        g = S.Graph()
        return g.apply_all(
            [(e, "<log>", i) for i, e in enumerate(events)]).validate()

    forward = fold(models + old + new)
    backward = fold(models + new + old)     # the merge that used to fail
    reg = {"claim": "claims", "edge": "edges", "inference": "inferences"}[entity]
    assert (sorted(getattr(forward, reg)) == sorted(getattr(backward, reg)))
    # And the back-pointer lands either way -- including on EDGES, which
    # carried `supersedes` with no existence check and no stamp at all.
    old_id = list(old)[-1]["id"]
    assert getattr(backward, reg)[old_id].get("superseded_by")


def test_an_edge_cannot_supersede_itself_or_a_record_that_is_not_there():
    """Edges had NEITHER check. `_apply_edge` required `discharge_kind` and
    stopped there, so `supersedes: <typo>` withdrew nothing while reading like
    a repair, and `supersedes: <own id>` was expressible."""
    for bad, msg in [("E1", "supersedes itself"),
                     ("E-TYPO", "not a edge in this graph")]:
        with pytest.raises(S.GraphError) as exc:
            _graph(TWO_MODELS + [
                {"ev": "edge", "id": "E1", "src": "TIGHT", "dst": "LOOSE",
                 "type": K.NECESSARY_CONDITION, "why": "drops equations",
                 "supersedes": bad, "discharge_kind": "RETYPE"}])
        assert msg in str(exc.value)


def test_the_two_discharge_vocabularies_are_not_interchangeable():
    """An EDGE supersession says what happened to the OBLIGATION the old edge
    carried; a CLAIM's says what CHANGED about the record. Borrowing across
    them was silently accepted on edges, whose `discharge_kind` was validated
    against nothing at all."""
    with pytest.raises(S.GraphError) as exc:
        _graph(TWO_MODELS + [
            {"ev": "edge", "id": "E1", "src": "TIGHT", "dst": "LOOSE",
             "type": K.UNTYPED, "why": "?", "debt_why": "unknown"},
            {"ev": "edge", "id": "E2", "src": "TIGHT", "dst": "LOOSE",
             "type": K.NECESSARY_CONDITION, "why": "drops equations",
             "supersedes": "E1", "discharge_kind": K.AMEND}])
    assert "for a edge the kinds are" in str(exc.value)
    assert "OBLIGATION" in str(exc.value)


# ===========================================================================
# THE DOCUMENTS.  A read surface that lies is the defect this project is about.
# ===========================================================================
def _repo_root():
    return os.path.dirname(os.path.dirname(os.path.abspath(__file__)))


def test_every_marked_check_count_in_the_docs_is_the_real_one():
    """SIX DIFFERENT COUNTS WERE LIVE AT ONCE -- 160, 171, 251, 273, 307, 338 --
    against an actual 384. `HANDOFF.md`, the file labelled READ THIS FIRST IF
    YOU HAVE NO CONTEXT, disagreed with the README, which disagreed with
    REVIEW.md, which disagreed with TESTPLAN.md.

    That is not housekeeping. This project's thesis is that prose read surfaces
    rot first, and these are exactly the surfaces a cold session reads. A
    campaign whose headline measurement is COLD RESUMPTION cannot have its
    resumption documents lying about how much evidence exists. It is REVIEW.md
    section 7 occurring inside the documents that argue for section 7.

    A NAIVE `\d+ checks` SWEEP WOULD BE A FALSE-POSITIVE GENERATOR, which is
    the one thing this tool must not ship. Several of those numbers are TRUE
    HISTORY -- "the suite went 171 -> 251 checks", "171 checks agreed with an
    unsound cell" -- and a rule that could not tell a current-state claim from
    a narrative one would demand the history be falsified to go green. So only
    MARKED spans are checked, and marking one is the author saying "this is a
    claim about now".
    """
    import re
    import subprocess
    root = _repo_root()
    out = subprocess.run(
        [sys.executable, "-m", "pytest", "-q", "--collect-only",
         os.path.join(root, "tests")],
        capture_output=True, text=True, cwd=root).stdout
    m = re.search(r"(\d+) tests? collected", out)
    assert m, "could not collect the suite to compare against"
    real = int(m.group(1))

    span = re.compile(r"<!--checks-->(\d+)<!--/checks-->")
    wrong, seen = [], 0
    for name in sorted(os.listdir(root)):
        if not name.endswith(".md"):
            continue
        with open(os.path.join(root, name), encoding="utf-8") as fh:
            for n, line in enumerate(fh, 1):
                for hit in span.finditer(line):
                    seen += 1
                    if int(hit.group(1)) != real:
                        wrong.append("%s:%d says %s" % (name, n, hit.group(1)))
    assert seen, (
        "no document states the check count as a marked span, so this test "
        "guards nothing -- the counts have gone back to being retyped")
    assert not wrong, (
        "the suite has %d checks and these documents say otherwise:\n  %s\n"
        "Run `gp docs` to resync them." % (real, "\n  ".join(wrong)))


def test_the_docs_do_not_disagree_about_how_much_evidence_exists():
    """A version number drifting between mirrors is normal. A CLAIM ABOUT HOW
    MUCH EVIDENCE EXISTS drifting is the one kind that must not.

    The public README said "three live user sessions" while the private one
    said one, and `TESTPLAN.md` listed T1 as STAGED AND READY while
    `HANDOFF.md` recorded T1 as run and failed. A reader deciding how far to
    trust this tool is reading exactly those sentences.
    """
    import re
    root = _repo_root()
    counts = {}
    for name in ("README.md", "REVIEW.md", "HANDOFF.md"):
        path = os.path.join(root, name)
        if not os.path.exists(path):
            continue
        with open(path, encoding="utf-8") as fh:
            text = fh.read()
        for m in re.finditer(r"(\w+) live user sessions?", text):
            counts.setdefault(m.group(1).lower(), []).append(name)
    assert len(counts) <= 1, (
        "these documents disagree about how many live sessions have happened, "
        "which is a claim about how much evidence exists: %s"
        % {k: v for k, v in counts.items()})


# ===========================================================================
# THE REFUSAL SURFACE.  The one place with evidence of working.
# ===========================================================================
def test_a_hint_on_a_claim_or_a_model_reaches_the_refusal():
    """ONLY EDGES COULD CARRY ONE, and it was the single artifact that survived
    a context boundary.

    A campaign returning cold reported the edge hint "came back verbatim in
    every refusal, and it named the remedy precisely enough to execute" -- "the
    only artifact in the campaign that did real cross-session handoff work.
    Nothing in the prose files did that." The same report found every prose
    claim about the tool's vocabulary had rotted within one session.

    In Cognitive Dimensions terms it is SECONDARY NOTATION outperforming every
    piece of primary notation, which has a known implication: support it
    deliberately instead of treating it as decoration.
    """
    g = _graph(TWO_MODELS + [
        {"ev": "edge", "id": "E", "src": "TIGHT", "dst": "LOOSE",
         "type": K.NECESSARY_CONDITION, "why": "drops equations"},
        {"ev": "claim", "id": "C", "model": "TIGHT", "kind": K.PREDICATE,
         "statement": "P holds",
         "discharge_hint": "P was only ever checked on the smooth locus"},
        {"ev": "inference", "id": "I", "claim": "C", "path": [["E", K.ALONG]],
         "concludes_kind": K.PREDICATE, "asserted": "P on the looser model"}])
    f = [x for x in C.run(g) if x.rule == C.R_TRANSPORT][0]
    assert "FOR THIS CLAIM" in f.discharge
    assert "smooth locus" in f.discharge
    # And the cell's own requirement is still there -- a hint is APPENDED to
    # what the mathematics demands, never a replacement for it.
    assert "re-derive it in the target model" in f.discharge


def test_gp_why_prints_the_conservatism_register_with_the_cell(capsys):
    """A REFUSAL THAT IS A DELIBERATE CONSERVATISM READS EXACTLY LIKE A THEOREM,
    and a user who cannot tell them apart learns to route around both. Routing
    around a refusal is the T1 failure mode.

    IMAGE_CLOSURE/AGAINST/NONEMPTY is the case: sound under the existential
    reading of NONEMPTY, unsound under the witness reading, and the table can
    encode only one. A user hitting it should be told the mathematics may well
    be on their side and the tool is being careful.
    """
    from grandportage import cli
    assert cli.main(["why", "IMAGE_CLOSURE", "AGAINST", "NONEMPTY"]) == 0
    out = capsys.readouterr().out
    assert "DELIBERATE CONSERVATISM" in out
    assert "not a theorem against you" in out
    assert "Chevalley" in out, "the cell's own discharge must still print"


def test_gp_why_reads_the_kernel_rather_than_restating_it(capsys):
    """A second copy of an explanation is a second thing to rot, and this repo
    has already watched five README cells document licences withdrawn two
    versions earlier. `gp why` must render TYPE_MEANS and the transport table,
    not a paraphrase kept beside them."""
    from grandportage import cli
    for etype in K.ALL_TYPES:
        assert cli.main(["why", etype]) == 0
        out = capsys.readouterr().out
        assert K.TYPE_MEANS[etype].split(".")[0][:40] in out, (
            "%s's printed meaning must come from TYPE_MEANS" % etype)
        for d in K.DIRECTIONS:
            for kd in K.CLAIM_KINDS:
                rule = K.TRANSPORT[etype][d][kd]
                if rule is True:
                    assert "%-8s %-9s  licensed" % (d, kd) in out


def test_history_shows_the_struggle_the_fold_hides(tmp_path, capsys):
    """`gp show` prints the FOLD, and repair makes a fold tidier over time --
    so it under-represents difficulty exactly where the most work happened.

    This session made that worse deliberately: withdrawn edges, inferences and
    their findings all stopped reporting, which removed real baseline dilution
    and took the scar tissue with it. The append-only log kept everything and
    nothing surfaced it.

    A finished proof erases its own search. On a live campaign this shows an
    inference restated THREE times -- the hardest object there -- of which the
    fold displays only the survivor.
    """
    from grandportage import cli
    _accept_fixture(tmp_path, TWO_MODELS + [
        {"ev": "edge", "id": "E", "src": "TIGHT", "dst": "LOOSE",
         "type": K.NECESSARY_CONDITION, "why": "drops equations"},
        {"ev": "claim", "id": "C", "model": "LOOSE", "kind": K.PREDICATE,
         "statement": "P"},
        {"ev": "inference", "id": "I1", "claim": "C",
         "path": [["E", K.AGAINST]], "concludes_kind": K.PREDICATE,
         "asserted": "P at the tighter model"},
        {"ev": "inference", "id": "I2", "claim": "C",
         "path": [["E", K.AGAINST]], "concludes_kind": K.PREDICATE,
         "asserted": "P at the tighter model, restated once",
         "supersedes": "I1", "discharge_kind": K.RESTATE},
        {"ev": "inference", "id": "I3", "claim": "C",
         "path": [["E", K.AGAINST]], "concludes_kind": K.PREDICATE,
         "asserted": "P at the tighter model, restated twice",
         "supersedes": "I2", "discharge_kind": K.RESTATE},
    ])
    assert cli.main(["--root", str(tmp_path), "history"]) == 0
    out = capsys.readouterr().out
    assert "I1 --RESTATE--> I2 --RESTATE--> I3" in out, (
        "the whole chain, not only the survivor")

    # And the fold shows only the survivor -- which is correct for `show` and
    # is exactly why `history` has to exist.
    g = S.load(S.graph_path(str(tmp_path)))
    assert C.clean_inferences(g, C.run(g)) == ["I3"]


def test_history_is_honest_that_it_records_repairs_and_not_attempts(tmp_path,
                                                                    capsys):
    """The limit stated first, because overstating it would be the same error
    the tool exists to catch.

    The log records what was DECLARED, never what was REFUSED. A refusal that
    made an author think again and write something different leaves no direct
    trace -- only the something-different. So this is a floor on difficulty,
    not a measure of it, and a campaign with no supersessions is not thereby a
    campaign that found everything easy.
    """
    from grandportage import cli
    _accept_fixture(tmp_path, TWO_MODELS)
    assert cli.main(["--root", str(tmp_path), "history"]) == 0
    out = capsys.readouterr().out
    assert "No supersessions recorded" in out
    assert "which the log cannot distinguish and should not pretend to" in out
