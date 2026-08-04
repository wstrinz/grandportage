"""The CAS boundary and the enforcement hook.

The layers that make this a gate rather than a linter.  Everything above them
can be ignored by not looking; these two cannot.
"""

import io as _io
import json
import os
import shutil
import subprocess

import pytest

from grandportage import artifacts as A
from grandportage import cas
from grandportage import check as C
from grandportage import hook as HK
from grandportage import kernel as K
from grandportage import migration as MIG
from grandportage import store as S

import helpers as H


GOOD = dict(dialect=cas.SINGULAR, ring="GP_R", ring_vars=["x", "y"],
            decls=[("GP_I", "ideal", "x*y-1,x+y-2")],
            body=[], outputs=["GP_I"])

EDGE = {"src": "SRC", "type": "IMAGE_CLOSURE",
        "why": "elimination returns the Zariski closure of the image",
        "map_kind": "POLYNOMIAL"}


def program(**kw):
    d = dict(GOOD)
    d.update(kw)
    return cas.CASProgram(**d)


def fake_runner(stdout="", stderr="", rc=0):
    def run(prog, timeout):
        separator = "" if stdout.endswith("\n") else "\n"
        completed = stdout + separator + prog.completion_marker + "\n"
        return {"returncode": rc, "stdout": completed, "stderr": stderr,
                "aborted": rc in cas.ABORT_CODES,
                "abort_reason": cas.ABORT_CODES.get(rc), "argv": ["fake"]}
    return run


@pytest.fixture
def project(tmp_path):
    root = str(tmp_path)
    S.append([{"ev": "model", "id": "SRC", "desc": "the source system",
               "field": "Q"}], root=root)
    return root


def _install_epoch1_fixture(domain, root):
    """Migrate a legacy fixture before extending it with native events."""
    path = S.graph_path(root)
    os.unlink(path)
    MIG.migrate_epoch1([H.graph_file(domain)], output=path)


# ===========================================================================
# Guard 1 -- the forcing function
# ===========================================================================

def test_omitting_the_transport_is_a_TypeError_from_argument_binding():
    """Not a check inside the body -- a missing required keyword-only argument.

    The distinction is the point.  A check can be reordered or short-circuited
    by a later edit; Python's own argument binding cannot, so no code path
    reaches a subprocess without the declaration.
    """
    with pytest.raises(TypeError) as exc:
        cas.run_cas(program(), produces="M", describes="d")
    assert "edge" in str(exc.value)


def test_no_subprocess_is_spawned_when_the_declaration_is_missing():
    """The claim is 'no CAS process spawned', so assert it rather than assume."""
    calls = []

    def spy(prog, timeout):
        calls.append(prog)
        return fake_runner("@@GP_I:\n1\n")(prog, timeout)

    with pytest.raises(TypeError):
        cas.run_cas(program(), produces="M", describes="d", _runner=spy)
    assert calls == []


def test_untyped_is_a_legal_declaration_but_silence_is_not(project):
    """A recorded debt is allowed; an unrecorded one is not."""
    with pytest.raises(cas.TransportNotDeclared):
        cas.Transport.from_dict(None)
    with pytest.raises(cas.TransportNotDeclared):
        cas.Transport.from_dict({"src": "SRC", "type": "UNTYPED",
                                 "why": "exploratory"})
    t = cas.Transport.from_dict({"src": "SRC", "type": "UNTYPED",
                                 "why": "exploratory sweep",
                                 "debt_why": "relation to the germ unknown"})
    assert t.type == K.UNTYPED


def test_an_unknown_type_names_the_five_options():
    """The error message has to teach the distinction, because the person
    hitting it is being asked to make a modelling decision they were trying to
    skip."""
    with pytest.raises(cas.TransportNotDeclared) as exc:
        cas.Transport(src="A", type="PROBABLY_FINE", why="w")
    msg = str(exc.value)
    for t in (K.EQUIVALENCE, K.NECESSARY_CONDITION, K.BASE_EXTENSION,
              K.IMAGE_CLOSURE, K.SPECIALIZATION):
        assert t in msg


def test_a_transport_with_no_why_is_refused():
    with pytest.raises(cas.TransportNotDeclared):
        cas.Transport(src="A", type=K.NECESSARY_CONDITION, why="")


# ===========================================================================
# Guard 2 -- the non-bypassable identifier assert
# ===========================================================================

def test_the_historical_shadowing_defect_is_caught():
    """`poly g0 = ...` against ring variables (a0..a4, g0, g1, gamma).

    The emitted program redefined the ring variable, so `sat(I, nz)` saturated
    the ideal by an element of itself and collapsed it to (1) -- a confident
    false EMPTY in 0.3 s at every prime.
    """
    with pytest.raises(cas.IdentifierCollision) as exc:
        program(ring_vars=["a0", "a1", "a2", "a3", "a4", "g0", "g1", "gamma"],
                decls=[("g0", "poly", "7447*a4^5*gamma^23")], outputs=["g0"])
    assert "SHADOWS" in str(exc.value)


def test_the_illegal_identifier_defect_is_caught():
    """Singular identifiers must begin with a letter.  An `_ASSAY_` prefix
    produced `? error`, markers printed with no values, and EXIT 0."""
    with pytest.raises(cas.IdentifierCollision):
        program(decls=[("_GP_I", "ideal", "x*y-1")], outputs=["_GP_I"])


def test_reserved_words_and_duplicates_are_caught():
    with pytest.raises(cas.IdentifierCollision):
        program(decls=[("ideal", "ideal", "x")], outputs=["ideal"])
    with pytest.raises(cas.IdentifierCollision):
        program(decls=[("GP_I", "ideal", "x"), ("GP_I", "ideal", "y")])


def test_the_assert_DISCRIMINATES_rather_than_refusing_everything():
    """A check that rejects everything is worse than none.  A legal program
    with a variable deliberately named `g0` -- the exact name the historical
    defect shadowed -- must pass, because the collision is about the
    DECLARATION shadowing it, not about the name."""
    p = program(ring_vars=["x", "y", "g0"],
                decls=[("GP_I", "ideal", "x*y-1,g0-x")], outputs=["GP_I"])
    assert "g0" in p.text


def test_there_is_no_string_path_to_a_solver():
    with pytest.raises(TypeError) as exc:
        cas.run_cas("ideal I = 1;", edge=EDGE, produces="M", describes="d")
    assert "CASProgram" in str(exc.value)


def test_the_check_and_the_text_derive_from_the_same_pairs():
    """They cannot drift apart, because they read the same triples."""
    p = program()
    names = [n for n, _, _ in p.decls]
    for n in names:
        assert ("ideal %s =" % n) in p.text


# ===========================================================================
# Guard 3 -- an errored CAS is not a CAS that answered
# ===========================================================================

def test_an_error_line_refuses_a_verdict_even_at_exit_zero(project):
    """The recorded symptom exactly: `? error`, markers with nothing behind
    them, exit 0.  Exit status is not evidence."""
    out = "? error occurred in or before STDIN line 2: `ring ...`\n@@GP_I:\n\n"
    with pytest.raises(cas.CASError) as exc:
        cas.run_cas(program(), edge=EDGE, produces="M", describes="d",
                    root=project, _runner=fake_runner(out, rc=0))
    assert "exits 0" in str(exc.value)


def test_a_missing_or_doubled_marker_refuses_a_verdict(project):
    for out in ("no markers at all\n",
                "@@GP_I:\n1\n@@GP_I:\n2\n"):
        with pytest.raises(cas.CASError):
            cas.run_cas(program(), edge=EDGE, produces="M", describes="d",
                        root=project, _runner=fake_runner(out))


@pytest.mark.parametrize("rc", sorted(cas.ABORT_CODES))
def test_abort_codes_are_never_a_verdict(project, rc):
    r = cas.run_cas(program(), edge=EDGE, produces="M", describes="d",
                    root=project, record=False,
                    _runner=fake_runner("@@GP_I:\n1\n", rc=rc))
    assert r["verdict"] == "ABORTED" and r["values"] is None


# ===========================================================================
# Recording
# ===========================================================================

def test_a_successful_run_records_a_typed_edge(project):
    r = cas.run_cas(program(), edge=EDGE, produces="ELIM",
                    describes="the eliminated ideal", root=project,
                    _runner=fake_runner("@@GP_I:\n1\n"))
    assert r["values"] == {"GP_I": "1"}
    g = S.load(S.graph_path(project))
    assert "ELIM" in g.models
    assert g.edges["E-ELIM"]["type"] == K.IMAGE_CLOSURE
    assert g.edges["E-ELIM"]["src"] == "SRC"
    assert g.models["ELIM"]["characteristic"] == 0
    reference = A.note_reference(g.notes[-1]["source"])
    assert reference["artifact_fingerprint"] == r["artifact_fingerprint"]
    assert A.load(project, reference["artifact_fingerprint"])["stdout"]
    assert A.audit_graph(project, g) == []


def test_a_cas_record_preserves_nonzero_characteristic(project):
    cas.run_cas(
        program(characteristic=7), edge=EDGE, produces="ELIM7",
        describes="the characteristic-seven output", root=project,
        _runner=fake_runner("@@GP_I:\n1\n"))
    graph = S.load(S.graph_path(project))
    assert graph.models["ELIM7"]["characteristic"] == 7


def test_recording_a_step_whose_source_does_not_exist_is_refused(project):
    """The write is transactional against the fold, so a bad edge cannot land."""
    bad = dict(EDGE, src="NO_SUCH_MODEL")
    with pytest.raises(S.GraphError):
        cas.run_cas(program(), edge=bad, produces="ELIM", describes="d",
                    root=project, _runner=fake_runner("@@GP_I:\n1\n"))
    assert "NO_SUCH_MODEL" not in open(S.graph_path(project),
                                       encoding="utf-8").read()


def test_ideal_is_unit_returns_evidence_not_a_verdict(project):
    """The convenience wrapper deliberately does NOT turn std(I)==1 into a kill.

    A Groebner basis reducing to 1 is EVIDENCE of emptiness; what makes it a
    kill is the certificate attached and the scope that certificate derives.
    Collapsing those is the shape of the error that shipped.
    """
    r = cas.ideal_is_unit(["x", "y"], ["x", "x-1"], edge=EDGE, produces="E",
                          describes="d", root=project,
                          _runner=fake_runner("@@GP_G:\nGP_G[1]=1\n"))
    assert "verdict" not in str(r["values"]).lower()
    assert r["verdict"] == "OK"          # the RUN succeeded
    assert "EMPTY" not in json.dumps(r["values"])


# ===========================================================================
# The hook
# ===========================================================================

def _conclude(root, from_claim, edge_id, direction, asserted):
    S.append([{"ev": "inference", "id": "I-CONCLUDE", "claim": from_claim,
               "path": [[edge_id, direction]], "asserted": asserted,
               "era": "live"}], root=root)


def test_the_full_loop_compute_record_conclude_refuse(project):
    """The shape of the error that shipped, replayed through the whole stack.

    An emptiness is established over a small field with a field-relative
    certificate; the agent then reads it across a base extension as if it were
    geometric.  Nothing in the graph is malformed and the CAS ran clean -- the
    step is simply not licensed, and the hook is what stops it.
    """
    S.append([
        {"ev": "model", "id": "RES_L", "desc": "the residue equation over L",
         "field": "Q(sqrt 17)"},
        {"ev": "model", "id": "RES_K", "desc": "the same over arbitrary char-0 K",
         "field": "K"},
        {"ev": "edge", "id": "E-EXT", "src": "RES_L", "dst": "RES_K",
         "type": K.BASE_EXTENSION, "map_kind": K.IDENTITY_MAP,
         "why": "the coefficient field changes from Q(sqrt 17) to arbitrary K",
         "drops": ["every field-relative arithmetic fact, in particular "
                   "square classes"]},
        {"ev": "claim", "id": "CL-KILL", "model": "RES_L", "kind": K.EMPTY,
         "statement": "no solution with all leading coefficients nonzero",
         "scope": "Q(sqrt 17)", "certificate": "NONSQUARE_CLASS",
         "established_by": K.RAN, "ladder": "exact-checked"},
    ], root=project)

    block, _ = HK.evaluate(project)
    assert not block, "nothing has been concluded yet"

    _conclude(project, "CL-KILL", "E-EXT", K.ALONG,
              "the branch does not exist over the theorem's arbitrary char-0 K")

    block, message = HK.evaluate(project)
    assert block
    assert "REFUSED" in message
    assert "does not base-change" in message
    assert "DISCHARGE" in message


def test_the_same_step_is_ALLOWED_with_a_base_changing_certificate(project):
    """The contrast, and it is what makes the refusal a discrimination rather
    than a blanket ban on ever crossing a base extension."""
    S.append([
        {"ev": "model", "id": "RES_L", "desc": "over L", "field": "Q"},
        {"ev": "model", "id": "RES_K", "desc": "over K", "field": "K"},
        {"ev": "edge", "id": "E-EXT", "src": "RES_L", "dst": "RES_K",
         "type": K.BASE_EXTENSION, "map_kind": K.IDENTITY_MAP,
         "why": "the coefficient field changes"},
        {"ev": "claim", "id": "CL-KILL", "model": "RES_L", "kind": K.EMPTY,
         "statement": "1 lies in the ideal, exhibited over Q",
         "certificate": "UNIT_IDEAL_CERT", "established_by": K.RAN,
         "ladder": "exact-checked"},
    ], root=project)
    _conclude(project, "CL-KILL", "E-EXT", K.ALONG,
              "hence empty over every char-0 K")
    block, message = HK.evaluate(project)
    assert not block, message


def test_a_missing_graph_does_not_block(tmp_path):
    """Most tool calls in most repos have nothing to do with a proof campaign.
    A hook that blocks every session without a .portage/ gets disabled, and a
    disabled hook enforces nothing."""
    block, _ = HK.evaluate(str(tmp_path))
    assert not block


def test_a_malformed_graph_DOES_block(project):
    """Fail closed on the things we own.  The agent just caused this."""
    with open(S.graph_path(project), "a", encoding="utf-8") as fh:
        fh.write('{"ev":"claim","id":"X","model":"GHOST","kind":"EMPTY",'
                 '"statement":"x","certificate":"UNIT_IDEAL_CERT"}\n')
    block, message = HK.evaluate(project)
    assert block and "does not fold" in message


def test_the_baseline_suppresses_known_findings_but_not_new_ones(project):
    """A campaign mid-flight carries unrepaired historical inferences by
    construction.  Blocking on those forever trains the operator to disable the
    hook, so the baseline records what is knowingly carried -- in a file a
    reviewer can read, not in someone's memory of the normal warnings."""
    findings = C.run(H.load("jc2"))
    _install_epoch1_fixture("jc2", project)
    block, _ = HK.evaluate(project)
    assert block, "the four historical errors are present"

    HK.save_baseline(project, findings, note="the recorded errata")
    block, _ = HK.evaluate(project)
    assert not block, "accepted findings no longer block"

    S.append([{"ev": "inference", "id": "I-NEW", "claim": "CL-C20",
               "path": [["E9", K.ALONG]], "asserted": "a fresh bad step",
               "era": "live"}], root=project)
    block, message = HK.evaluate(project)
    assert block and "I-NEW" in message


def test_the_hook_reads_cwd_from_its_stdin_payload(project, monkeypatch):
    payload = json.dumps({"tool_name": "Bash", "cwd": project})
    monkeypatch.setattr("sys.stdin", _Stdin(payload))
    assert HK.main([]) == 0


class _Stdin(object):
    def __init__(self, text):
        self._text = text

    def read(self):
        return self._text


# ===========================================================================
# Live CAS -- skipped where Singular is unreachable
# ===========================================================================

_UNREACHABLE = [None]   # the reason, once we know it


_PROBED = []


def _singular_available():
    """Is the solver there?  And SAY WHICH WAY IT IS ABSENT when it is not.

    THIS PROBE PRODUCED A FALSE GREEN.  The timeout was 30s and a cold WSL
    takes about 47s to answer, so on any run where the VM had gone to sleep the
    three live-CAS tests skipped with "Singular not reachable" -- while
    Singular sat installed and working one directory away.  The suite went
    green having quietly not run the only tests that touch a real solver.

    That is this project's own recurring shape wearing test-harness clothes: a
    load-bearing fact ("the CAS is absent") asserted by something that had not
    established it, and no way to tell from the output that it was guessing.
    So the probe now allows for a cold start, and DISTINGUISHES the two
    absences -- a missing binary and a slow one need different reactions, and
    reporting them identically is how the slow one hid for weeks.
    """
    if _PROBED:
        return _PROBED[0]
    try:
        p = subprocess.run(cas._argv() + ["--version"], capture_output=True,
                           timeout=180)
    except subprocess.TimeoutExpired:
        _UNREACHABLE[0] = ("Singular did not answer within 180s. That is a "
                           "SLOW solver, not an absent one -- do not read this "
                           "skip as 'no CAS installed'.")
        return False
    except Exception as exc:
        _UNREACHABLE[0] = "Singular could not be started: %r" % (exc,)
        return False
    if p.returncode == 0 or b"Singular" in (p.stdout + p.stderr):
        _PROBED.append(True)
        return True
    _UNREACHABLE[0] = ("Singular answered but did not identify itself "
                       "(rc=%s)" % p.returncode)
    return False


# THE PROBE IS LAZY, and that is what makes a fast loop possible at all.
#
# It used to run at MODULE IMPORT, so every invocation paid for it -- including
# `-m "not live"`, which deselects the only tests that need it.  With the
# timeout raised to 180s to stop a cold WSL being misread as an absent solver,
# that fixed cost dominated the suite: 706 deselected-live tests still took 83
# seconds, essentially all of it waiting for a probe nobody was going to use.
#
# So the marker is plain, and the skip happens inside the test via a fixture in
# `conftest.py`, which runs the probe at most once and only if a live test is
# actually about to execute.
live = pytest.mark.live


@live
def test_live_singular_both_directions(project):
    """Two targets with known answers, on the real solver.

    Reviewing the emitter would never have caught the identifier defect; only
    running it did.  So the emitter gets run.
    """
    empty = cas.ideal_is_unit(["x", "y", "g0"], ["x", "x-1", "y-g0"],
                              edge=EDGE, produces="ELIM1", describes="d",
                              root=project)
    assert empty["values"]["GP_G"] == "GP_G[1]=1"

    nonempty = cas.ideal_is_unit(["x", "y", "g0"], ["x*y-1", "x+y-2", "g0-x"],
                                 edge=dict(EDGE, why="a second target"),
                                 produces="ELIM2", describes="d", root=project)
    # THE WHOLE basis, not its first line.  Reporting only `GP_G[1]=...` let a
    # three-generator basis read as "the ideal is (that one thing)".
    gb = nonempty["values"]["GP_G"]
    assert isinstance(gb, list) and len(gb) == 3, gb
    assert not any(g.replace(" ", "").endswith("=1") for g in gb)


@live
def test_the_health_probe_reaches_the_cas_and_writes_nothing(project):
    """Every other CAS path requires `produces` and `edge`, so the cheapest
    plumbing probe used to permanently add a model and an edge to a campaign.
    That pushed the first user toward composing the real call first and finding
    out about plumbing failures inside it."""
    from grandportage import mcp
    before = open(S.graph_path(project), encoding="utf-8").read()
    body = mcp.h_cas_health({}, project)["content"][0]["text"]
    assert "CAS reachable" in body and "answer is correct" in body
    assert "2 generator(s)" in body
    assert open(S.graph_path(project), encoding="utf-8").read() == before


@live
def test_live_run_emits_a_program_using_the_defects_own_variable_name(project):
    """The target deliberately names a variable `g0`, the exact name the
    historical defect shadowed, and the emitted program must be clean."""
    r = cas.ideal_is_unit(["x", "g0"], ["x*g0-1"], edge=EDGE, produces="E",
                          describes="d", root=project)
    assert r["verdict"] == "OK"


def test_the_first_run_hint_appears_only_when_no_baseline_exists(project):
    """The operational trap, caught as a test.

    On a graph with existing history and no baseline, EVERY tool call blocks.
    That is correct behaviour and a terrible first experience: it looks like a
    broken install, and the rational response to a broken install is to delete
    the hook.  So the first block has to name the one-command fix.
    """
    shutil.copy(H.graph_file("gamma_window"), S.graph_path(project))
    block, message = HK.evaluate(project)
    assert block and "--- FIRST RUN?" in message
    assert "gp accept" in message

    HK.save_baseline(project, C.run(S.load(S.graph_path(project))),
                     note="knowingly carried")
    block, _ = HK.evaluate(project)
    assert not block


def test_a_baseline_that_exists_suppresses_the_hint(project):
    """Once a baseline exists, a NEW finding must read as a new finding -- not
    as a setup problem the operator already solved."""
    _install_epoch1_fixture("gamma_window", project)
    HK.save_baseline(project, C.run(S.load(S.graph_path(project))), note="x")
    S.append([{"ev": "inference", "id": "I-FRESH", "claim": "GC-A2-KILL",
               "path": [["GE4", K.ALONG]],
               "asserted": "and therefore (75,125) is dead too",
               "era": "live"}], root=project)
    block, message = HK.evaluate(project)
    assert block and "I-FRESH" in message
    assert "--- FIRST RUN?" not in message


def test_gp_accept_records_a_reason_PER_FINDING(project):
    """The reason travels with the finding, not with the file.

    A single campaign-level note cannot say why one particular obligation is
    carried.  The first real user hit this immediately: they wrote a paragraph
    about one finding into the shared note because there was nowhere else for
    it to go.
    """
    from grandportage import cli
    shutil.copy(H.graph_file("gamma_window"), S.graph_path(project))
    assert cli.main(["--root", project, "accept", "-m",
                     "the standing four"]) == 0
    doc = HK.read_baseline(project)
    assert doc["accepted"]["TRANSPORT:GI-BRIDGE"]["why"] == "the standing four"


def test_gp_accept_can_take_one_finding_at_a_time(project):
    """Accepting everything is the blunt instrument.  Accepting one finding is
    the honest one, and it keeps the rest blocking."""
    from grandportage import cli
    shutil.copy(H.graph_file("gamma_window"), S.graph_path(project))
    cli.main(["--root", project, "accept", "-m", "just the bridge",
              "--only", "TRANSPORT:GI-BRIDGE"])
    block, message = HK.evaluate(project)
    assert block
    assert "GI-BRIDGE" not in message
    assert "GI-GAMMA-IMPORT" in message


def test_accept_only_ADDS_and_never_destroys_the_existing_baseline(project):
    """REGRESSION for the worst bug this tool has had.

    `gp accept --only <id>` replaced the whole file.  Accepting one finding
    therefore deleted every previously accepted entry -- silently, on a
    version-controlled file that humans read as the authoritative record of
    what a campaign knows it is carrying.

    It was caught by luck: the hook went red again with untouched findings.
    Had it been the last accept of a session it would have destroyed the record
    with no trace.  That is the failure this project exists to prevent,
    occurring inside the tool.
    """
    from grandportage import cli
    shutil.copy(H.graph_file("gamma_window"), S.graph_path(project))
    cli.main(["--root", project, "accept", "-m", "the standing four"])
    first = HK.load_baseline(project)
    assert len(first) == 8

    cli.main(["--root", project, "accept", "-m", "one more, deliberately",
              "--only", "TRANSPORT:GI-U35" if False else "UNTYPED-EDGE:GE4"])
    after = HK.load_baseline(project)
    assert first <= after, "accepting one finding dropped previously accepted ones"
    assert len(after) == 8


def test_accepting_one_finding_keeps_the_other_reasons_intact(project):
    """Merging the ids is not enough -- the REASONS have to survive too, or the
    record degrades to a list of ids nobody can audit."""
    from grandportage import cli
    shutil.copy(H.graph_file("gamma_window"), S.graph_path(project))
    cli.main(["--root", project, "accept", "-m", "documented in the handoff"])
    cli.main(["--root", project, "accept", "--only", "UNTYPED-EDGE:GE4",
              "-m", "a different, more specific reason"])
    doc = HK.read_baseline(project)
    assert doc["accepted"]["UNTYPED-EDGE:GE4"]["why"] ==         "a different, more specific reason"
    assert doc["accepted"]["TRANSPORT:GI-BRIDGE"]["why"] ==         "documented in the handoff"


def test_removing_an_acceptance_must_be_an_EXPLICIT_act(project):
    """`--prune` is the only way to drop an entry, and it only drops findings
    that no longer appear in the graph.  Silence must never delete."""
    from grandportage import cli
    shutil.copy(H.graph_file("gamma_window"), S.graph_path(project))
    cli.main(["--root", project, "accept", "-m", "all of them"])
    HK.save_baseline(project, [], note="")            # a no-op accept
    assert len(HK.load_baseline(project)) == 8

    stale = HK.read_baseline(project)
    stale["accepted"]["TRANSPORT:GONE"] = {"why": "fixed last week"}
    with open(HK.baseline_path(project), "w", encoding="utf-8") as fh:
        json.dump(stale, fh)
    assert "TRANSPORT:GONE" in HK.load_baseline(project)

    cli.main(["--root", project, "accept", "--prune", "-m", "tidy"])
    assert "TRANSPORT:GONE" not in HK.load_baseline(project)
    assert len(HK.load_baseline(project)) == 8


def test_a_legacy_list_baseline_still_loads(project):
    """An existing baseline written by the old code must keep working, or the
    fix for a data-loss bug becomes a second data-loss bug."""
    shutil.copy(H.graph_file("gamma_window"), S.graph_path(project))
    with open(HK.baseline_path(project), "w", encoding="utf-8") as fh:
        json.dump({"accepted": ["TRANSPORT:GI-BRIDGE"], "note": "old form"}, fh)
    assert HK.load_baseline(project) == {"TRANSPORT:GI-BRIDGE"}
    block, message = HK.evaluate(project)
    assert block
    assert "TRANSPORT:GI-BRIDGE" in message
    assert "ACCEPTANCE IS STALE" in message


def test_accept_rejects_an_unknown_finding_id(project):
    """A typo'd id used to be a silent no-op that also wiped the file."""
    from grandportage import cli
    shutil.copy(H.graph_file("gamma_window"), S.graph_path(project))
    cli.main(["--root", project, "accept", "-m", "all"])
    assert cli.main(["--root", project, "accept", "--only", "NOPE:1"]) == 2
    assert len(HK.load_baseline(project)) == 8


def test_the_hook_does_not_block_read_only_tools(project):
    """A gate that stops you reading the thing it complains about forces you to
    disable it to investigate -- which is the same as not having it.  The first
    real user could not write down what the hook had blocked until they had
    un-blocked it."""
    shutil.copy(H.graph_file("gamma_window"), S.graph_path(project))

    class _S:
        def __init__(self, t):
            self._t = json.dumps({"tool_name": t, "cwd": project})

        def read(self):
            return self._t

    import sys as _sys
    old = _sys.stdin
    try:
        for tool in ("Read", "Grep", "Glob", "WebSearch"):
            _sys.stdin = _S(tool)
            assert HK.main(["--root", project]) == 0, tool
        _sys.stdin = _S("Write")
        assert HK.main(["--root", project]) == 2
    finally:
        _sys.stdin = old


def test_an_identical_block_is_not_reprinted_in_full(project):
    """The same 40-line wall five times is one piece of information, not five,
    and the repetition buries the discharge move under its own restatement."""
    import sys as _sys
    shutil.copy(H.graph_file("gamma_window"), S.graph_path(project))

    class _S:
        def __init__(self, t="Write"):
            self._t = json.dumps({"tool_name": t, "cwd": project})

        def read(self):
            return self._t

    old_in, old_err = _sys.stdin, _sys.stderr
    try:
        _sys.stdin, _sys.stderr = _S(), _io.StringIO()
        assert HK.main(["--root", project]) == 2
        first = _sys.stderr.getvalue()
        _sys.stdin, _sys.stderr = _S(), _io.StringIO()
        assert HK.main(["--root", project]) == 2
        second = _sys.stderr.getvalue()
    finally:
        _sys.stdin, _sys.stderr = old_in, old_err
    assert "DISCHARGE" in first and len(first) > len(second)
    assert "still refused, unchanged" in second


def test_the_untyped_discharge_offers_BOTH_moves(project):
    """The first version named only 'name the relaxation', which is the one
    exit closed by construction: if you could name it there would be no
    obligation to record.  Recording a residual obligation AS a type error is
    an intended use and the message has to say so."""
    shutil.copy(H.graph_file("gamma_window"), S.graph_path(project))
    found = {f.fid: f for f in C.run(S.load(S.graph_path(project)))}
    d = found["TRANSPORT:GI-REPLAY-TRANSFER"].discharge
    assert "TYPE THE EDGE" in d
    assert "gp accept --only TRANSPORT:GI-REPLAY-TRANSFER" in d
    assert "carrying a debt in the open" in d
    assert "no transcription to copy" in d       # the edge's own debt_why


@live
def test_a_unit_ideal_certificate_is_checkable_by_expansion():
    """THE LAST HONOUR-SYSTEM FIELD THAT CARRIES SCOPE.

    `derive_scope` reads the certificate KIND to decide whether an emptiness
    survives a base change. That was the fix for a declared `scope`, and it
    moved the free choice one field along rather than removing it: nothing
    relates the label `UNIT_IDEAL_CERT` to any computation, so a caller who
    ran something and saw `1` gets the same scope as one who typed the name.

    A representation `1 = sum a_i f_i` closes it, because confirming it is one
    EXPANSION -- no Buchberger, no monomial order, no trust in the search that
    found the cofactors. The checker shares no code path with the thing it
    checks, which is the certifying-algorithms shape, and it is the clean
    bridge to a proof assistant: Lean checks a polynomial identity and never
    has to run a Groebner engine.
    """
    from grandportage import verify as V

    g = S.Graph().apply_all([(e, "t", i) for i, e in enumerate([
        {"ev": "model", "id": "M", "what": "an empty model",
         "characteristic": 0, "ring_vars": ["x", "y"],
         "generators": ["x", "1-x"]},
        {"ev": "claim", "id": "C", "model": "M", "kind": K.EMPTY,
         "statement": "no points", "certificate": "UNIT_IDEAL_CERT",
         "established_by": "RAN", "ladder": "exact-checked"},
    ])])
    g.validate()
    verdict, why, capability = V.unit_ideal(g, "C")
    assert verdict == V.CERT_VERIFIED, why
    assert capability["cofactors"] == ["1", "1"]
    assert "WITHOUT recomputing a basis" in why


@live
def test_a_declared_certificate_that_is_false_is_caught():
    """A claim may NAME `UNIT_IDEAL_CERT` over an ideal that is not the unit
    ideal, and until the certificate was checkable nothing said so.

    The verdict is deliberately about the CERTIFICATE and not about the
    emptiness -- a model can be empty for other reasons, established by other
    means, and this rules out one route rather than the conclusion.
    """
    from grandportage import verify as V

    g = S.Graph().apply_all([(e, "t", i) for i, e in enumerate([
        {"ev": "model", "id": "N", "what": "a model with points",
         "characteristic": 0, "ring_vars": ["x", "y"],
         "generators": ["x", "y"]},
        {"ev": "claim", "id": "D", "model": "N", "kind": K.EMPTY,
         "statement": "no points", "certificate": "UNIT_IDEAL_CERT",
         "established_by": "RAN", "ladder": "exact-checked"},
    ])])
    g.validate()
    verdict, why, capability = V.unit_ideal(g, "D")
    assert verdict == V.CERT_NOT_UNIT
    assert capability is None
    assert "not the unit ideal" in why
    assert "statement about the CERTIFICATE" in why


@live
def test_the_expansion_catches_cofactors_that_do_not_expand():
    """The half a reader can check, exercised on a representation that is
    wrong. A shorter cofactor list is refused rather than padded, because it
    would verify an identity about a DIFFERENT ideal and report it as this
    one."""
    from grandportage import cas as C2

    ok, got = C2.check_unit_ideal_representation(
        ["x", "y"], ["x", "1-x"], ["1", "0"])
    assert not ok and got == "x", (
        "expanding 1*x + 0*(1-x) gives x, and the checker must say so rather "
        "than agreeing with the search")

    with pytest.raises(C2.CASError) as exc:
        C2.check_unit_ideal_representation(["x", "y"], ["x", "1-x"], ["1"])
    assert "different ideal" in str(exc.value)


@live
def test_ring_iso_is_checkable_and_radicalisation_is_caught():
    """THE MOST POWERFUL UNAUDITED BOOLEAN LEFT, and the formalisation is what
    said how to check it.

    `Reflects` -- the awkward half of an isomorphism -- quantifies over
    preimages, which no CAS can search for. But it is not primitive: given an
    inverse map, `PullsBack psi I J` plus `psi . phi = id` gives it. So a
    verified iso is three reductions, not a search.

    The case it must catch is the kernel's own warning: V(x^2) and V(x) have
    the same single point and any converse you like, and `x = 0` holds in one
    coordinate ring and is false in the other. Points do not give `ring_iso`.
    """
    from grandportage import verify as V

    def mk(fwd, inv, sg, dg):
        g = S.Graph().apply_all([(e, "t", i) for i, e in enumerate([
            {"ev": "model", "id": "A", "what": "a", "ring_vars": ["x", "y"],
             "characteristic": 0, "generators": sg},
            {"ev": "model", "id": "B", "what": "b", "ring_vars": ["x", "y"],
             "characteristic": 0, "generators": dg},
            {"ev": "edge", "id": "E", "src": "A", "dst": "B",
             "type": K.EQUIVALENCE, "why": "a change of variables",
             "map_kind": K.POLYNOMIAL, "ring_iso": True,
             "converse_witness": "the inverse substitution",
             "forward": fwd, "inverse": inv}])])
        g.validate()
        return g

    swap = {"x": "y", "y": "x"}
    verdict, why = V.ring_iso(mk(swap, swap, ["x*y-1"], ["x*y-1"]), "E")
    assert verdict == V.ISO_VERIFIED, why
    assert "COORDINATE RINGS" in why

    ident = {"x": "x", "y": "y"}
    verdict, why = V.ring_iso(mk(ident, ident, ["x^2"], ["x"]), "E")
    assert verdict == V.ISO_NOT_ISO
    assert "does not pull back" in why, (
        "radicalisation carries the ideal forward and does not reflect -- it "
        "is the half that fails, and the message must say which")


def test_ring_iso_checks_both_inverse_compositions(monkeypatch):
    """The executable contract matches both inverse laws in Lean."""
    from grandportage import verify as V

    graph = S.Graph().apply_all([(event, "t", i) for i, event in enumerate([
        {"ev": "model", "id": "A", "what": "a",
         "characteristic": 0, "ring_vars": ["x"], "generators": []},
        {"ev": "model", "id": "B", "what": "b",
         "characteristic": 0, "ring_vars": ["x"], "generators": []},
        {"ev": "edge", "id": "E", "src": "A", "dst": "B",
         "type": K.EQUIVALENCE, "why": "proposed maps",
         "map_kind": K.POLYNOMIAL,
         "forward": {"x": "f"}, "inverse": {"x": "i"}},
    ])])

    def fake(_ring, polynomial, substitution, _generators, **_kwargs):
        table = {
            ("x", "f"): "u",
            ("u", "i"): "not_x",
            ("x", "i"): "v",
            ("v", "f"): "x",
        }
        marker = substitution["x"]
        return table[(polynomial, marker)], True

    monkeypatch.setattr(V.cas, "substitute_and_reduce", fake)
    verdict, why = V.ring_iso(graph, "E")
    assert verdict == V.ISO_NOT_ISO
    assert "right inverse" in why


@live
def test_w10_involution_is_verified_as_a_mapped_equivalence():
    """Lock the exact live shape that exposed mapped/literal conflation."""
    from grandportage import verify as V

    f = "a^3+a^2*b-a^2*b^2-a*b^3-a^2-a*b+a*b^2+b^3"
    fp = "a^3-a^2*b-a^2*b^2+a*b^3-a^2+a*b+a*b^2-b^3"
    graph = S.Graph().apply_all([(event, "t", i) for i, event in enumerate([
        {"ev": "model", "id": "Z", "what": "W10 curve",
         "characteristic": 0, "ring_vars": ["t", "a", "b"],
         "generators": ["t", f]},
        {"ev": "model", "id": "ZP", "what": "its involutive image",
         "characteristic": 0, "ring_vars": ["t", "a", "b"],
         "generators": ["t", fp]},
        {"ev": "edge", "id": "E-SIGMA", "src": "Z", "dst": "ZP",
         "type": K.EQUIVALENCE, "why": "b maps to -b",
         "map_kind": K.POLYNOMIAL,
         "forward": {"t": "t", "a": "a", "b": "-b"},
         "inverse": {"t": "t", "a": "a", "b": "-b"}},
    ])])

    verdict, why = V.ring_iso(graph, "E-SIGMA")
    assert verdict == V.ISO_VERIFIED, why
    assert "both compositions" in why

@live
def test_ring_iso_forward_is_the_point_forward_map_not_its_pullback():
    """A non-involution fixes the orientation hidden by every swap test."""
    from grandportage import verify as V

    def graph(forward, inverse):
        return S.Graph().apply_all([
            (event, "t", i) for i, event in enumerate([
                {"ev": "model", "id": "A", "what": "the point zero",
                 "characteristic": 0, "ring_vars": ["x"],
                 "generators": ["x"]},
                {"ev": "model", "id": "B", "what": "the point one",
                 "characteristic": 0, "ring_vars": ["x"],
                 "generators": ["x-1"]},
                {"ev": "edge", "id": "E", "src": "A", "dst": "B",
                 "type": K.EQUIVALENCE, "why": "translation by one",
                 "map_kind": K.POLYNOMIAL,
                 "forward": {"x": forward}, "inverse": {"x": inverse}},
            ])])

    verdict, why = V.ring_iso(graph("x+1", "x-1"), "E")
    assert verdict == V.ISO_VERIFIED, why

    verdict, why = V.ring_iso(graph("x-1", "x+1"), "E")
    assert verdict == V.ISO_NOT_ISO
    assert "point-forward" in why




@live
def test_a_substitution_is_simultaneous():
    """NESTED `subst` IS NOT SIMULTANEOUS, and getting it wrong is silent.

    Swapping two variables one at a time sends `x*y - 1` to `x*x - 1`: the
    first substitution puts `y` everywhere and the second rewrites the lot. The
    bug reported a map as failing to carry an ideal it carries perfectly well,
    and it was caught only by testing a case that was supposed to PASS.
    """
    from grandportage import cas as C2
    got, ok = C2.substitute_and_reduce(
        ["x", "y"], "x*y-1", {"x": "y", "y": "x"}, ["x*y-1"])
    assert ok, "the swap is an automorphism of this ideal; got %r" % got

    got, _ = C2.substitute_and_reduce(["x", "y"], "x^2+y",
                                      {"x": "y", "y": "x"}, [])
    assert got.replace(" ", "") == "y^2+x", (
        "a genuinely asymmetric case, so the test is not passing by symmetry")

    with pytest.raises(C2.CASError) as exc:
        C2.substitute_and_reduce(["x", "y"], "x", {"x": "y"}, [])
    assert "every ring variable" in str(exc.value)


@live
def test_the_verifier_reads_the_model_characteristic():
    """A FALSE LICENCE, in the code written to prevent false licences.

    A live campaign declared `characteristic: 23` on eight models, and nothing
    read it. Every reduction the verifier ran was in characteristic 0. So
    `verify.unit_ideal` returned VERIFIED for a claim the campaign KNEW was
    false -- over F_23 the ideal is (y, x+10) and it had exhibited the singular
    point -- and handed back a certificate whose every cofactor had 23 in the
    denominator. Undefined at the very prime the model declares.

    `gp check` reported zero findings on that graph, and `UNIT_IDEAL_CERT`
    base-changes, so the emptiness was SCHEME-scoped and would have travelled
    to every field.
    """
    from grandportage import verify as V

    g = S.Graph().apply_all([(e, "t", i) for i, e in enumerate([
        {"ev": "model", "id": "SING", "what": "the singular locus over F23",
         "ring_vars": ["x", "y"],
         "generators": ["y^2-x^3+x-1", "3*x^2-1", "2*y"],
         "characteristic": 23},
        {"ev": "claim", "id": "C", "model": "SING", "kind": K.EMPTY,
         "statement": "no singular point", "certificate": "UNIT_IDEAL_CERT",
         "established_by": "RAN", "ladder": "exact-checked"}])])
    g.validate()
    verdict, why, cap = V.unit_ideal(g, "C")
    assert verdict == V.CERT_NOT_UNIT, (
        "this ideal is (y, x+10) over F_23; a VERIFIED here is a false licence")
    assert cap is None


@live
def test_a_true_containment_in_characteristic_two_is_not_refused():
    """The same root cause, refusing something TRUE.

    In characteristic 2, `y^2 + 1 = (y+1)^2`, so V(x+1,y+1) really is inside
    V(y^2+1, x^2+1). Reducing in characteristic 0 the verifier reported that
    `y^2+1` "reduces to 2" -- the number 2, which is ZERO in the ring both
    models declare -- and escalated that to UNSOUND_PREMISE.
    """
    from grandportage import verify as V

    g = S.Graph().apply_all([(e, "t", i) for i, e in enumerate([
        {"ev": "model", "id": "PT", "what": "the point",
         "ring_vars": ["x", "y"], "generators": ["x+1", "y+1"],
         "characteristic": 2},
        {"ev": "model", "id": "SING", "what": "the singular locus",
         "ring_vars": ["x", "y"], "generators": ["y^2+1", "x^2+1"],
         "characteristic": 2},
        {"ev": "edge", "id": "E", "src": "PT", "dst": "SING",
         "type": K.NECESSARY_CONDITION, "why": "drops equations",
         "map_kind": K.POLYNOMIAL}])])
    g.validate()
    verdict, why = V.containment(g, "E")
    assert verdict == V.VERIFIED, why


@live
def test_the_saturation_constructor_can_actually_run():
    """IT COULD NEVER HAVE RUN.  `sat` lives in `elim.lib`, and `LIB` is in the
    dialect's FORBIDDEN set -- deliberately, so no emitted program can pull in
    arbitrary code. So the constructor emitted `sat(GP_I,GP_F)[1]` and Singular
    answered "`int` expected while building `sat(`".

    I tested `eliminate` against a real solver and did not test this one. A
    live campaign found it by trying to use it.

    Saturation by elimination needs no library:  I : f^oo = (I + (1-t*f)) ∩ R.
    """
    from grandportage import cas as C2
    from grandportage import operations as O

    op = O.saturate_closure("M", "x", "M_SAT", ["x", "y"], ["x*y"])
    res = C2._run_subprocess(op.program, 120)
    assert "? error" not in res["stdout"] + res["stderr"], res["stdout"][-400:]
    assert "y" in res["stdout"], "sat((xy), x) is (y); got %r" % res["stdout"]

    # AND AN EMPTY IDEAL IS NOT EXOTIC -- it is the ambient space, which is the
    # motivating use of `localize`: the smooth locus of a plane is the plane
    # with an inequality. `",".join([])` emitted `ideal GP_I = ;`.
    for op in (O.localize("M", "f", "L", ["a", "b"], []),
               O.saturate_closure("M", "a", "SS", ["a", "b"], []),
               O.eliminate("M", ["b"], "E", ["a", "b"], [])):
        res = C2._run_subprocess(op.program, 120)
        assert "? error" not in res["stdout"] + res["stderr"], (
            "%s on a zero ideal: %s" % (op.kind, res["stdout"][-200:]))


def test_the_cli_and_the_hook_agree_where_the_campaign_is(tmp_path, capsys):
    """W7 D10 -- THE WALK-UP WAS ADDED TO ONE OF THEM.

    From a subdirectory of a campaign the hook resolved the root correctly,
    refused the step, and printed its standard line: "run `gp check`". And
    `gp check` from that same directory reported there was no graph at all.

    Two components disagreeing about where the campaign is, surfacing as
    REMEDIATION THAT FAILS EXACTLY WHERE THE REFUSAL FIRES -- found on the
    first live use of the feature, one day after it was added.
    """
    import os
    from grandportage import cli, store as S, hook as HK
    cli.main(["--root", str(tmp_path), "init"])
    S.append([{"ev": "model", "id": "M", "what": "a model"}], str(tmp_path))
    deep = tmp_path / "a" / "b" / "c"
    deep.mkdir(parents=True)
    here = os.getcwd()
    try:
        os.chdir(str(deep))
        assert S.find_root(".") == os.path.abspath(str(tmp_path))
        assert cli.main(["check"]) == 0
        assert "1 models" in capsys.readouterr().out
    finally:
        os.chdir(here)


def test_init_does_not_walk_up(tmp_path):
    """`gp init` CREATES a graph, so walking up would silently initialise a
    parent campaign instead of here -- the one outcome worse than not finding
    one."""
    import os
    from grandportage import cli, store as S
    cli.main(["--root", str(tmp_path), "init"])
    child = tmp_path / "sub"
    child.mkdir()
    here = os.getcwd()
    try:
        os.chdir(str(child))
        cli.main(["init"])
        assert os.path.isdir(str(child / ".portage")), (
            "init walked up and wrote to the parent campaign")
    finally:
        os.chdir(here)
