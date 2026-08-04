"""GATE 2 -- every construct, driven through every surface a user touches.

THREE CRASHES IN ONE DAY, all the same shape:

    construct            built for                              how it failed
    ------------------   ------------------------------------   -------------
    open premise slot    "the artifact requires a claim that     gp check
                          does not exist"                        crashed
    partition            "this case analysis leaves one case     gp check
                          open"                                  crashed
    family               "4 of 1567 classes are 2-to-1"          gp check
                                                                 crashed

Each was built for the hardest thing a campaign has to say.  Each was CORRECT
IN ITSELF -- the kernel cell was right, the fold was right, the rule was right.
Each broke on the path a user takes, and each was found by a live run rather
than by a suite that was over 300 checks at the time.

THE REASON IS SPECIFIC AND THIS FILE IS THE REPAIR.  Nothing exercised a
construct END TO END.  `test_cell_ledger` tests the kernel.  `test_adversarial`
tests functions -- its open-slot regression called `audit_inference` and never
`run`, so the construct was correct in every respect except being reachable.
`contradicting_claims` subscripted `c["model"]` on a claim that had a `family`
instead.  `_first_refusal` looked up a sentinel in `graph.edges`.

So: one fixture per construct, every surface driven over every fixture, and a
completeness gate that fails when an event kind has no fixture.  A new
construct cannot be added without being walked through the whole surface, and a
new surface cannot be added without being walked over every construct.

The assertion is deliberately weak -- DOES IT COMPLETE.  Not what it says; the
other files own that.  All three crashes would have been caught by "does it
return at all", and that is the whole point: the bar was never height, it was
existence.
"""

import io
import json
import os
import subprocess
import sys

import pytest

from grandportage import check as C
from grandportage import cli
from grandportage import hook as HK
from grandportage import kernel as K
from grandportage import mcp
from grandportage import store as S


# ===========================================================================
# ONE FIXTURE PER CONSTRUCT.  Each is a COMPLETE graph, not a fragment: it
# carries whatever else the surfaces need to actually do work on it.  A family
# fixture with no inference would never have reached `contradicting_claims`,
# which is exactly how that crash survived.
# ===========================================================================
_MODELS = [
    {"ev": "model", "id": "TIGHT", "desc": "with equations"},
    {"ev": "model", "id": "LOOSE", "desc": "equations dropped"},
]
_NC = {"ev": "edge", "id": "E", "src": "TIGHT", "dst": "LOOSE",
       "type": K.NECESSARY_CONDITION, "why": "drops equations"}


def _claim(cid, model="TIGHT", kind=K.PREDICATE, **kw):
    c = {"ev": "claim", "id": cid, "model": model, "kind": kind,
         "statement": "a statement for %s" % cid}
    c.update(kw)
    return c


def _inf(iid, claim, path, kind=K.PREDICATE, **kw):
    i = {"ev": "inference", "id": iid, "claim": claim, "path": path,
         "concludes_kind": kind, "asserted": "an assertion for %s" % iid}
    i.update(kw)
    return i


FIXTURES = {}


def construct(name, event_kinds):
    """Register a fixture and the event kinds it is the coverage for."""
    def deco(fn):
        FIXTURES[name] = (fn(), set(event_kinds))
        return fn
    return deco


@construct("plain_transport", ["model", "edge", "claim", "inference"])
def _plain():
    return _MODELS + [_NC, _claim("C"),
                      _inf("I", "C", [["E", K.ALONG]])]


@construct("computation_and_doubt", ["evidence", "doubt"])
def _evidence_and_doubt():
    """A claim established by sweeping a bounded space, and a doubt about it.

    Both drawn from live sessions. The evidence record exists because
    certificates are algebraic and EMPTY-only, so a PREDICATE established by
    exhaustive enumeration could record only THAT something was run, never
    WHAT -- the script name went into a note. The doubt exists because an
    agent found a cited result did not supply the premise it was meant to and
    had nowhere to put that.
    """
    return [{"ev": "model", "id": "M", "what": "a bounded lattice of corners"},
            {"ev": "claim", "id": "C", "model": "M", "kind": K.PREDICATE,
             "statement": "every surviving pair lies in the published list",
             "established_by": "RAN", "ladder": "exact-checked"},
            {"ev": "evidence", "id": "EV1", "for": "C",
             "method": "ENUMERATION", "ran": "r714_enum.py",
             "what": "swept every (u,v) with u+v <= 50 applying the six "
                     "necessary conditions the source proves"},
            {"ev": "evidence", "id": "EV2", "for": "C",
             "method": "REPLICATION", "ran": "gamma_from_corner.py",
             "what": "an independent implementation of the same filter",
             "agrees_with": "EV1, on all 40 survivors"},
            {"ev": "doubt", "id": "D1", "about": "C",
             "kind": "SCOPE_MISMATCH", "severity": "TRIAGE",
             "why": "two of the six conditions are my reconstruction of a "
                    "proof stated only for a special case, not the source's "
                    "own general statement"}]


@construct("ambiguous_citation", ["citation"])
def _citation():
    """A citation whose naive resolution succeeds on the WRONG object.

    Drawn from the live case: a paper cites "GGV1 Remark 7.10", which denotes
    what the arXiv source numbers 7.14 because the citing work used a
    pre-publication draft -- and arXiv 7.10 is a different statement about the
    same subject, so a reader looking it up lands somewhere plausible and
    wrong with no signal at all.
    """
    return [{"ev": "model", "id": "M", "what": "the object under study"},
            {"ev": "citation", "id": "CIT_R714",
             "cites": "GGV1 Remark 7.10",
             "source": "GGV3 (1406.0886) L1721",
             "resolves_to": "GGV1 Remark 7.14 (arXiv:1401.1784 L4959-L4999)",
             "why": "GGV3 cites a pre-publication draft; section 7 gained "
                    "four numbered items before publication",
             "hazard": "arXiv GGV1's actual 7.10 is a DIFFERENT corner "
                       "statement, so the naive lookup succeeds on the wrong "
                       "object rather than failing"},
            {"ev": "claim", "id": "C", "model": "M", "kind": K.PREDICATE,
             "statement": "the corner is fixed, by GGV1 Remark 7.10",
             "established_by": "CITED", "ladder": "claimed"}]


@construct("voided_record", ["erratum"])
def _erratum():
    """A record the graph cannot read, and the erratum that repairs it.

    The malformed claim writes `supersession_kind`, which is not a field --
    the real one is `discharge_kind` -- so it folds to "supersedes X without
    saying HOW" and poisons the graph permanently.  A live session made
    exactly this typo twice and had to rewrite the append-only log to escape.

    Every surface has to render a graph containing a record that is present in
    the log and absent from the fold, which is a state none of them had seen.
    """
    return [{"ev": "model", "id": "M", "what": "a model"},
            {"ev": "claim", "id": "C", "model": "M", "kind": K.PREDICATE,
             "statement": "the first version", "established_by": "CITED",
             "ladder": "claimed"},
            {"ev": "claim", "id": "C2", "model": "M", "kind": K.PREDICATE,
             "statement": "corrected", "established_by": "CITED",
             "ladder": "claimed", "supersedes": "C",
             "supersession_kind": "AMEND"},
            {"ev": "erratum", "voids": "C2",
             "why": "wrote `supersession_kind`; the field is `discharge_kind`"}]


@construct("verified_identity", ["verdict"])
def _verdict():
    """A structured IDENTITY and the verifier's answer about it.

    The `verdict` event exists because the fields it writes were readable by
    the checker and writable by nobody -- so the only way to populate them was
    to type them into a declare event, which let a caller assert the checker's
    most severe finding with no computation behind it.  It gets a fixture
    because every surface now has to render a claim that has been EXAMINED,
    which is a state none of them had ever been shown.
    """
    return [{"ev": "model", "id": "X", "what": "a plane curve",
             "ring_vars": ["x", "y"], "generators": ["y^2-x^3"]},
            {"ev": "claim", "id": "C", "model": "X", "kind": K.IDENTITY,
             "statement": "y^2 = x^3 at X", "lhs": "y^2", "rhs": "x^3",
             "ring_vars": ["x", "y"], "identity_origin": K.DERIVED,
             "established_by": "RAN", "ladder": "exact-checked"},
            {"ev": "verdict", "id": "v.C.1", "subject": "claim", "of": "C",
             "verdict": "VERIFIED_DERIVED",
             "why": "y^2 - x^3 reduces to 0 modulo X's ideal"}]


@construct("open_premise_slot", [])
def _slot():
    """The construct that crashed `_first_refusal` on its sentinel."""
    return _MODELS + [_NC, _claim("HAVE", model="LOOSE"),
                      {"ev": "inference", "id": "I", "premises": [
                          {"claim": "HAVE", "path": [["E", K.AGAINST]]},
                          {"required_kind": K.EMPTY, "at": "LOOSE",
                           "missing_why": "nothing kills every case"}],
                       "concludes_kind": K.PREDICATE,
                       "asserted": "the artifact establishes X"}]


@construct("open_slot_leading", [])
def _slot_first():
    """Slot FIRST, so the fold leaves the legacy `claim` field None -- which
    broke two further lines that used it as a dict key."""
    return _MODELS + [_NC, _claim("HAVE", model="LOOSE"),
                      {"ev": "inference", "id": "I", "premises": [
                          {"required_kind": K.EMPTY, "at": "LOOSE",
                           "missing_why": "unsettled"},
                          {"claim": "HAVE", "path": [["E", K.AGAINST]]}],
                       "concludes_kind": K.PREDICATE,
                       "asserted": "the artifact establishes X"}]


@construct("partition_covered", ["partition"])
def _part_ok():
    return [{"ev": "model", "id": "P", "desc": "parent"},
            {"ev": "model", "id": "B1", "desc": "branch one"},
            {"ev": "model", "id": "B2", "desc": "branch two"},
            {"ev": "edge", "id": "EB1", "src": "B1", "dst": "P",
             "type": K.NECESSARY_CONDITION, "why": "a branch"},
            {"ev": "edge", "id": "EB2", "src": "B2", "dst": "P",
             "type": K.NECESSARY_CONDITION, "why": "a branch"},
            _claim("X", model="B1", kind=K.EMPTY,
                   certificate="UNIT_IDEAL_CERT"),
            _claim("Y", model="B2", kind=K.EMPTY,
                   certificate="UNIT_IDEAL_CERT"),
            _claim("EXH", model="P"),
            {"ev": "partition", "id": "PG", "parent": "P",
             "branches": ["B1", "B2"], "exhaustive": "EXH",
             "why": "the split is by gamma"},
            {"ev": "inference", "id": "IP", "via_partition": "PG",
             "premises": [{"claim": "X", "path": []},
                          {"claim": "Y", "path": []},
                          {"claim": "EXH", "path": []}],
             "concludes_kind": K.EMPTY, "asserted": "the parent is empty"}]


@construct("partition_uncovered", [])
def _part_bad():
    """The case the mechanism EXISTS for, and the one that crashed: a split
    that does not cover its parent."""
    evs = [e for e in _part_ok() if e.get("id") != "Y"]
    for e in evs:
        if e.get("id") == "IP":
            e["premises"] = [p for p in e["premises"]
                             if p.get("claim") != "Y"]
    return evs


@construct("partition_with_open_slot", [])
def _part_slot():
    """Both at once -- `graph.claims[pr["claim"]]` with claim=None."""
    evs = _part_bad()
    for e in evs:
        if e.get("id") == "IP":
            e["premises"] = e["premises"] + [
                {"required_kind": K.EMPTY, "at": "B2",
                 "missing_why": "the second branch is not settled"}]
    return evs


@construct("family_and_dispositions", ["family"])
def _family():
    """A family claim has no `model`, and five rules subscripted it. The
    inference is not decoration: without one, `contradicting_claims` never runs
    and the crash stays hidden."""
    return _MODELS + [_NC, _claim("C", model="LOOSE", kind=K.EMPTY,
                                  certificate="UNIT_IDEAL_CERT"),
                      _inf("I", "C", [["E", K.AGAINST]], kind=K.EMPTY),
                      {"ev": "family", "id": "F", "count": 4,
                       "desc": "the four cases",
                       "members": ["m1", "m2", "m3", "m4"],
                       "enumeration": "CF-ENUM"},
                      {"ev": "claim", "id": "CF-ENUM", "family": "F",
                       "kind": K.PREDICATE,
                       "statement": "there are exactly four",
                       "established_by": "RAN", "ladder": "exact-checked"},
                      {"ev": "claim", "id": "D", "family": "F", "kind": K.COUNT,
                       "statement": "three of four are settled",
                       "splits": "F",
                       "groups": [{"id": "G-OK", "settles": 3,
                                   "verdict": "settled",
                                   "exhibited": ["m1", "m2", "m3"]},
                                  {"id": "G-NO", "settles": 1,
                                   "verdict": "open", "exhibited": ["m4"]}],
                       "method": "a cheap screen",
                       "proves": ["G-OK"],
                       "why": "the screen proves the kill and not the survival",
                       "established_by": "RAN", "ladder": "exact-checked"}]


@construct("family_crosscut", [])
def _crosscut():
    evs = _family()
    return evs + [
        {"ev": "claim", "id": "D2", "family": "F", "kind": K.COUNT,
         "statement": "a second decomposition", "splits": "F",
         "groups": [{"id": "H-A", "settles": 2, "verdict": "type A",
                     "exhibited": ["m1", "m4"]},
                    {"id": "H-B", "settles": 2, "verdict": "type B",
                     "exhibited": ["m2", "m3"]}],
         "method": "an invariant", "proves": ["H-A", "H-B"],
         "why": "computed, not inferred",
         "established_by": "RAN", "ladder": "exact-checked"},
        {"ev": "claim", "id": "X", "family": "F", "kind": K.COUNT,
         "statement": "the result buys two", "rests_on": "H-A",
         "counts_against": "G-OK", "asserts_count": 2,
         "established_by": "RAN", "ladder": "exact-checked"}]


@construct("supersession_all_three", [])
def _supersede():
    return _MODELS + [
        {"ev": "edge", "id": "E1", "src": "TIGHT", "dst": "LOOSE",
         "type": K.UNTYPED, "why": "?", "debt_why": "not worked out"},
        {"ev": "edge", "id": "E2", "src": "TIGHT", "dst": "LOOSE",
         "type": K.NECESSARY_CONDITION, "why": "drops equations",
         "supersedes": "E1", "discharge_kind": "RETYPE"},
        _claim("C", model="LOOSE"),
        {"ev": "claim", "id": "C2", "model": "LOOSE",
         "kind": K.PREDICATE, "statement": "a statement for C",
         "cite": "a better citation", "supersedes": "C",
         "discharge_kind": K.AMEND},
        _inf("I1", "C2", [["E2", K.AGAINST]]),
        _inf("I2", "C2", [["E2", K.AGAINST]], supersedes="I1",
             discharge_kind=K.RESTATE),
    ]


@construct("certificates_and_scope", ["certificate"])
def _certs():
    return _MODELS + [
        {"ev": "certificate", "id": "MY_CERT", "base_changes": False,
         "why": "field-relative by construction"},
        {"ev": "edge", "id": "EB", "src": "TIGHT", "dst": "LOOSE",
         "type": K.BASE_EXTENSION, "why": "the coefficient field grows"},
        _claim("C", kind=K.EMPTY, certificate="MY_CERT",
               scope="Q(sqrt 17)"),
        _inf("I", "C", [["EB", K.ALONG]], kind=K.EMPTY)]


@construct("aliases_and_provenance", ["same_as", "built_by", "note"])
def _misc():
    return _MODELS + [_NC, _claim("C"),
                      _inf("I", "C", [["E", K.ALONG]]),
                      {"ev": "same_as", "id": "A", "models": ["TIGHT", "LOOSE"],
                       "why": "two names for one object, recorded to be checked"},
                      {"ev": "built_by", "model": "LOOSE", "inference": "I"},
                      {"ev": "note", "text": "carried and never typed"}]


@construct("every_edge_type", [])
def _all_types():
    evs = list(_MODELS)
    for i, t in enumerate(K.ALL_TYPES):
        e = {"ev": "edge", "id": "E%d" % i, "src": "TIGHT", "dst": "LOOSE",
             "type": t, "why": "a step of type %s" % t}
        if t == K.EQUIVALENCE:
            e["converse_witness"] = "the inverse construction"
            e["ring_iso"] = True
        if t == K.RESTRICTION:
            e["zariski_dense"] = True
        evs.append(e)
    evs.append(_claim("C"))
    evs.append(_inf("I", "C", [["E0", K.ALONG]]))
    return evs


# ===========================================================================
# EVERY SURFACE A USER TOUCHES.  Each takes (root, graph) and must COMPLETE.
# ===========================================================================
def _s_fold(root, g):
    S.load(S.graph_path(root))


def _s_check(root, g):
    C.run(g)


def _s_render(root, g):
    C.render(C.run(g), {}, full=False)
    C.render(C.run(g), {}, full=True)


def _s_clean(root, g):
    C.clean_inferences(g, C.run(g))


def _s_cli_check(root, g):
    cli.main(["--root", root, "check"])


def _s_cli_check_json(root, g):
    cli.main(["--root", root, "check", "--json"])


def _s_cli_check_quiet(root, g):
    cli.main(["--root", root, "check", "--quiet"])


def _s_cli_show(root, g):
    cli.main(["--root", root, "show"])


def _s_cli_history(root, g):
    cli.main(["--root", root, "history"])


def _s_cli_accept(root, g):
    cli.main(["--root", root, "accept", "-m", "smoke"])


def _s_cli_migrate(root, g):
    cli.main(["--root", root, "migrate", "--dry-run"])


def _s_hook(root, g):
    HK.evaluate(root)


def _s_mcp_declare(root, g):
    """THE WRITE PATH, which is the one that has actually failed.

    Both MCP READ paths were in this list from the start and neither write path
    was -- and `portage_declare` is the primary interface for a campaign, the
    thing an agent calls to record anything at all. It went down in two
    consecutive live sessions and the gate built to catch that class did not
    cover it.
    """
    mcp.h_portage_declare(
        {"events": [{"ev": "note", "text": "a smoke write"}]}, root)


def _s_mcp_declare_rejects_cleanly(root, g):
    """A REJECTED write must be a message, not a traceback, and must leave the
    log untouched. Transactionality is the property the append-only shape is
    for; a half-written batch is unrecoverable."""
    before = io.open(S.graph_path(root), encoding="utf-8").read()
    out = mcp.h_portage_declare(
        {"events": [{"ev": "claim", "id": "SMOKE-BAD", "model": "NOPE",
                     "kind": "PREDICATE", "statement": "cites no model"}]},
        root)
    assert out.get("isError"), "a claim at an undeclared model must be refused"
    after = io.open(S.graph_path(root), encoding="utf-8").read()
    assert after == before, "a refused write must leave the log byte-identical"


def _s_mcp_check(root, g):
    mcp.h_portage_check({"full": True}, root)


def _s_mcp_show(root, g):
    mcp.h_portage_show({}, root)


def _s_fingerprints(root, g):
    for f in C.run(g):
        f.fingerprint
        f.as_dict()
        repr(f)


SURFACES = {
    "fold": _s_fold,
    "check.run": _s_check,
    "check.render": _s_render,
    "check.clean_inferences": _s_clean,
    "finding.fingerprint": _s_fingerprints,
    "gp check": _s_cli_check,
    "gp check --json": _s_cli_check_json,
    "gp check --quiet": _s_cli_check_quiet,
    "gp show": _s_cli_show,
    "gp history": _s_cli_history,
    "gp accept": _s_cli_accept,
    "gp migrate --dry-run": _s_cli_migrate,
    "hook.evaluate": _s_hook,
    "mcp portage_declare": _s_mcp_declare,
    "mcp portage_declare rejects": _s_mcp_declare_rejects_cleanly,
    "mcp portage_check": _s_mcp_check,
    "mcp portage_show": _s_mcp_show,
}


def _write(root, events):
    p = S.graph_path(root)
    os.makedirs(os.path.dirname(p), exist_ok=True)
    with io.open(p, "w", encoding="utf-8") as fh:
        for e in events:
            fh.write(json.dumps(e) + "\n")
    return S.load(p)


@pytest.mark.parametrize("surface", sorted(SURFACES))
@pytest.mark.parametrize("fixture", sorted(FIXTURES))
def test_every_construct_survives_every_surface(fixture, surface, tmp_path,
                                                capsys):
    """DOES IT COMPLETE.  Deliberately not what it says.

    All three of this week's crashes would have been caught by exactly this
    question, which is the point: the bar was never height, it was existence.
    A checker that raises is indistinguishable from a checker nobody ran, and
    it takes the hook and `gp accept` down with it -- so a campaign that hits
    one cannot even record what it knowingly carries.
    """
    events, _kinds = FIXTURES[fixture]
    root = str(tmp_path)
    graph = _write(root, events)
    SURFACES[surface](root, graph)
    capsys.readouterr()


def test_every_event_kind_has_a_fixture():
    """The gate on the gate, same discipline as the cell ledger's.

    A new event kind cannot be added without being walked through every
    surface. `family` was added yesterday, was exercised by the kernel and by
    its own rules, and crashed on first contact with a real graph because no
    fixture drove it through the CLI.
    """
    # `meta` is synthesized by every epoch-1 writer rather than authored as a
    # mathematical construct, and the native init/events tests exercise it.
    covered = {S.EV_META}
    for _events, kinds in FIXTURES.values():
        covered |= kinds
    missing = sorted(set(S.EVENT_KINDS) - covered)
    assert not missing, (
        "these event kinds have no smoke fixture, so nothing walks them "
        "through the user-facing surfaces: %s" % ", ".join(missing))


def test_the_surface_list_covers_what_a_campaign_actually_calls():
    """A surface absent from this list is a surface no construct is driven
    through. The three crashes were all in `gp check`; `gp accept` shares its
    path and went down with it, which is why the affected campaign could not
    record its own deliberate findings."""
    for required in ("gp check", "gp accept", "hook.evaluate",
                     "mcp portage_check", "mcp portage_declare",
                     "mcp portage_declare rejects", "gp show"):
        assert required in SURFACES


# ===========================================================================
# A FILE CALLED .jsonl HAD BETTER BE JSONL.
#
# `gp init` wrote `# Grand Portage graph. ...` as line 1. `load_events` skips
# `#` lines so the tool never noticed, and the trap was DOCUMENTED rather than
# removed -- `gp declare`'s epilog warned that "a naive json.loads per line
# will not" work. That warning is in `gp declare --help`; a person opening the
# graph file is not reading `gp declare --help`.
#
# A live session wrote a parser, choked on line 1, and diagnosed it in seconds.
# That is the GOOD case. The bad one is a parser that skips the line silently
# and reports a graph one record short.
# ===========================================================================
def test_a_new_graph_is_parseable_as_jsonl(tmp_path):
    """The naive parser, which is the whole point."""
    import json
    from grandportage import cli, store as S
    cli.main(["--root", str(tmp_path), "init"])
    with open(S.graph_path(str(tmp_path)), encoding="utf-8") as fh:
        for line in fh:
            if line.strip():
                json.loads(line)   # must not raise


def test_the_old_comment_header_still_loads(tmp_path):
    """Backward compatibility is not optional: every existing campaign graph
    opens with the `#` line, and `load_events` must keep skipping it."""
    from grandportage import store as S
    p = tmp_path / ".portage"
    p.mkdir()
    f = p / "graph.jsonl"
    f.write_text('# Grand Portage graph.  Append-only.\n'
                 '{"ev": "model", "id": "M", "what": "m"}\n',
                 encoding="utf-8")
    g = S.load(str(f))
    assert "M" in g.models


def test_gp_events_dumps_the_log_without_hand_parsing(tmp_path, capsys):
    """THE REASON THE HEADER BUG WAS FOUND AT ALL.

    A session wanted to read a graph, found that `gp check --json` was the only
    JSON any command emitted -- and it returns findings, not the graph -- so it
    wrote its own parser. The file was the only interface to its own contents.
    """
    import json
    from grandportage import cli, store as S
    cli.main(["--root", str(tmp_path), "init"])
    S.append([{"ev": "model", "id": "M", "what": "a model",
               "ring_vars": ["x"], "generators": ["x"]}], str(tmp_path))
    capsys.readouterr()

    cli.main(["--root", str(tmp_path), "events"])
    raw = json.loads(capsys.readouterr().out)
    assert [e["ev"] for e in raw] == ["meta", "note", "model"]

    cli.main(["--root", str(tmp_path), "events", "--folded"])
    folded = json.loads(capsys.readouterr().out)
    assert set(folded) == {"models", "edges", "claims", "inferences",
                           "partitions", "tombstones"}
    assert folded["models"]["M"]["generators"] == ["x"]


# ===========================================================================
# W6 FINDINGS. A live session, 2026-07-28, on a quartic-discriminant campaign.
# ===========================================================================
def test_operations_has_a_user_facing_surface():
    """D2 — THE SECOND CONFIRMED INSTANCE of a class HANDOFF §4 named as
    unguarded: "Neither asks whether a capability has a surface at all."

    `operations.py` had four constructors and ZERO production callers -- no
    subcommand, no MCP tool, no import outside the tests. `verify.py` was
    instance one and got `gp verify`; this was instance two, found the day
    after a fourth constructor was added to a module nobody could call.
    """
    from grandportage import cli
    p = cli.build_parser()
    sub = [a for a in p._actions if hasattr(a, "choices") and a.choices
           and "construct" in (a.choices or {})]
    assert sub, "operations.py is still unreachable from the CLI"


def test_construct_reads_the_algebra_from_the_graph(tmp_path, capsys, monkeypatch):
    """The argument FOR constructors is that the caller stops writing the same
    thing twice. If `gp construct` asked for ring_vars and generators again it
    would buy nothing."""
    import json
    from grandportage import cli, operations as O, store as S
    real_decompose = O.decompose

    def fake_decompose(src, ring_vars, generators, **kwargs):
        def runner(program, timeout):
            return {
                "aborted": False, "returncode": 0, "stderr": "",
                "stdout": ("@@GP_L:\n[1]:\n_[1]=q\n"
                           "[2]:\n_[1]=p2-4aq\n"
                           + program.completion_marker + "\n")}
        kwargs["_runner"] = runner
        return real_decompose(src, ring_vars, generators, **kwargs)

    monkeypatch.setattr(O, "decompose", fake_decompose)
    cli.main(["--root", str(tmp_path), "init"])
    S.append([{"ev": "model", "id": "D", "what": "a reducible locus",
               "characteristic": 0, "ring_vars": ["a", "p", "q"],
               "generators": ["p^2*q-4*a*q^2"]}], str(tmp_path))
    capsys.readouterr()

    cli.main(["--root", str(tmp_path), "construct", "decompose", "--src", "D",
              "--produces", "CASE-%s-%d"])
    events = json.loads(capsys.readouterr().out)
    gens = sorted(e["generators"][0] for e in events if e["ev"] == "model")
    assert gens == ["p2-4aq", "q"], gens
    assert any(e["ev"] == "partition" for e in events)
    ids = sorted(e["id"] for e in events if e["ev"] == "model")
    assert ids == ["CASE-D-0", "CASE-D-1"], ids

    # NOT written unless asked: a constructor must not be a second, weaker
    # door into the graph.
    assert "D_C0" not in S.load(S.graph_path(str(tmp_path))).models

def test_construct_run_materializes_before_emitting(tmp_path, capsys,
                                                     monkeypatch):
    import json
    from grandportage import cli, operations as O, store as S

    cli.main(["--root", str(tmp_path), "init"])
    S.append([{"ev": "model", "id": "D", "what": "a reducible locus",
               "characteristic": 0, "ring_vars": ["x", "y"],
               "generators": ["x*y"]}],
             str(tmp_path))
    capsys.readouterr()
    real_execute = O.execute

    def fake_execute(op, timeout=300):
        def runner(program, _timeout):
            return {"aborted": False, "returncode": 0, "stderr": "",
                    "stdout": ("@@GP_OUT:\nGP_OUT[1]=y\n"
                               + program.completion_marker + "\n")}
        return real_execute(op, timeout=timeout, _runner=runner)

    monkeypatch.setattr(O, "execute", fake_execute)
    rc = cli.main(["--root", str(tmp_path), "construct", "saturate",
                   "--src", "D", "--at", "x", "--produces", "D-SAT",
                   "--run"])
    assert rc == 0
    events = json.loads(capsys.readouterr().out)
    model = [e for e in events if e["ev"] == "model"][0]
    assert model["generators"] == ["y"]
    assert "ideal_pending" not in model
    assert "D-SAT" not in S.load(S.graph_path(str(tmp_path))).models

def test_construct_refuses_to_guess_characteristic_zero(tmp_path, capsys):
    from grandportage import cli, store as S
    cli.main(["--root", str(tmp_path), "init"])
    S.append([{
        "ev": "model", "id": "M", "what": "unknown coefficient field",
        "ring_vars": ["x"], "generators": ["x"],
    }], str(tmp_path))
    capsys.readouterr()
    rc = cli.main(["--root", str(tmp_path), "construct", "localize",
                   "--src", "M", "--at", "x", "--produces", "M-OPEN"])
    assert rc == 2
    assert "cannot silently choose characteristic 0" in capsys.readouterr().err


def test_a_model_without_algebra_is_refused_with_the_reason(tmp_path, capsys):
    from grandportage import cli, store as S
    cli.main(["--root", str(tmp_path), "init"])
    S.append([{"ev": "model", "id": "M", "what": "no algebra"}], str(tmp_path))
    capsys.readouterr()
    rc = cli.main(["--root", str(tmp_path), "construct", "decompose",
                   "--src", "M"])
    assert rc == 2
    assert "records no" in capsys.readouterr().err


def test_ring_iso_runs_on_the_maps_alone(tmp_path):
    """D4 — it required the `ring_iso` FLAG in addition to `forward` and
    `inverse`, so an author who did the natural thing got SILENCE: no verdict,
    and nothing saying the maps had been ignored. W6 reached the verifier only
    by reading the dispatcher.

    A VERIFIED verdict must still not MINT the flag -- an author who never
    declared it is not granted it by a check they did not ask for.
    """
    from grandportage import cli, store as S, verify as V
    S.append([
        {"ev": "model", "id": "A", "what": "a curve",
         "characteristic": 0, "ring_vars": ["x", "y"],
         "generators": ["y^2-x^4-1"]},
        {"ev": "model", "id": "B", "what": "the same curve",
         "characteristic": 0, "ring_vars": ["x", "y"],
         "generators": ["y^2-x^4-1"]},

        {"ev": "edge", "id": "E", "src": "A", "dst": "B",
         "type": "EQUIVALENCE", "map_kind": "POLYNOMIAL",
         "why": "the involution", "converse_witness": "the same map back",
         "forward": {"x": "-x", "y": "-y"},
         "inverse": {"x": "-x", "y": "-y"}},
    ], str(tmp_path))
    def fake(program, timeout):
        del timeout
        decls = {name: expr for name, _kind, expr in program.decls}
        values = {}
        for output in program.outputs:
            if output == "GP_E" and "GP_R2" not in program.outputs:
                expr = decls["GP_P"].replace(" ", "")
                values[output] = {
                    "x": "-x",
                    "-x": "x",
                    "y": "-y",
                    "-y": "y",
                }[expr]
            else:
                values[output] = "0"
        stdout = "".join(
            "@@%s:\n%s=%s\n" % (output, output, values[output])
            for output in program.outputs
        ) + program.completion_marker + "\n"
        return {
            "aborted": False,
            "returncode": 0,
            "stderr": "",
            "stdout": stdout,
        }

    results = V.verify_all(root=str(tmp_path), _runner=fake, record=False)
    assert [(subject, oid, verdict)
            for subject, oid, verdict, _ in results] == [
        ("ring_iso", "E", "VERIFIED")
    ]
    e = S.load(S.graph_path(str(tmp_path))).edges["E"]
    assert e.get("ring_iso_verdict") is None
    assert e.get("ring_iso") is None, "a verdict minted a licence"


def test_mapped_equivalence_is_not_verified_as_literal_containment(tmp_path):
    """W10: a coordinate change relates points through its declared maps.

    It does not assert that the two solution sets, in the coordinates as
    written, literally contain one another.  The involution x |-> -x sends
    V(x-1) to V(x+1), although neither singleton contains the other.
    """
    from grandportage import check as C, store as S, verify as V
    S.append([
        {"ev": "model", "id": "A", "what": "the point x = 1",
         "characteristic": 0, "ring_vars": ["x"],
         "generators": ["x-1"]},
        {"ev": "model", "id": "B", "what": "the point x = -1",
         "characteristic": 0, "ring_vars": ["x"],
         "generators": ["x+1"]},
        {"ev": "edge", "id": "E", "src": "A", "dst": "B",
         "type": "EQUIVALENCE", "map_kind": "POLYNOMIAL",
         "why": "the involution x |-> -x",
         "converse_witness": "apply the same involution",
         "ring_iso": True,
         "forward": {"x": "-x"}, "inverse": {"x": "-x"}},
    ], str(tmp_path))

    def fake(program, timeout):
        del timeout
        decls = {name: expr for name, _kind, expr in program.decls}
        values = {}
        for output in program.outputs:
            if output == "GP_E" and "GP_R2" not in program.outputs:
                values[output] = {"x": "-x", "-x": "x"}[
                    decls["GP_P"].replace(" ", "")]
            else:
                values[output] = "0"
        return {
            "aborted": False, "returncode": 0, "stderr": "",
            "stdout": ("".join(
                "@@%s:\n%s=%s\n" % (o, o, values[o])
                for o in program.outputs)
                + program.completion_marker + "\n"),
        }

    results = V.verify_all(root=str(tmp_path), _runner=fake, record=False)
    assert [(subject, oid) for subject, oid, _verdict, _why in results] == [
        ("ring_iso", "E")]
    graph = S.load(S.graph_path(str(tmp_path)))
    edge = graph.edges["E"]
    assert edge.get("ring_iso_verdict") is None
    assert "containment" not in edge, (
        "a mapped equivalence was also tested as literal containment")
    assert not [f for f in C.run(graph) if f.rule == C.R_CONTAINMENT]


def test_direct_containment_declines_a_mapped_equivalence_without_a_solver():
    from grandportage import store as S, verify as V
    graph = S.Graph().apply_all([(event, "t", i) for i, event in enumerate([
        {"ev": "model", "id": "A", "what": "a",
         "ring_vars": ["x"], "generators": ["x-1"]},
        {"ev": "model", "id": "B", "what": "b",
         "ring_vars": ["x"], "generators": ["x+1"]},
        {"ev": "edge", "id": "E", "src": "A", "dst": "B",
         "type": "EQUIVALENCE", "why": "x |-> -x",
         "forward": {"x": "-x"}, "inverse": {"x": "-x"}},
    ])])

    def never(*args, **kwargs):
        raise AssertionError("literal containment spawned a solver")

    verdict, why = V.containment(graph, "E", _runner=never)
    assert verdict == V.UNVERIFIED
    assert "mapped EQUIVALENCE" in why


def test_unjustified_equivalence_names_the_field_it_tests():
    """D6 — the rule tested `converse_witness` and reported the absence of
    `witness`. On an EQUIVALENCE those have OPPOSITE POLARITY, so a session
    wrote the field the message named and got two findings contradicting each
    other on the same edge in the same run."""
    from grandportage import check as C, store as S, kernel as K
    g = S.Graph().apply_all([(e, "t", i) for i, e in enumerate([
        {"ev": "model", "id": "A", "desc": "a"},
        {"ev": "model", "id": "B", "desc": "b"},
        {"ev": "edge", "id": "E", "src": "A", "dst": "B",
         "type": K.EQUIVALENCE, "why": "w", "map_kind": K.POLYNOMIAL},
    ])])
    f = [x for x in C.run(g) if x.rule == "UNJUSTIFIED-EQUIVALENCE"][0]
    assert "`converse_witness`" in f.detail
    assert "neither a `witness`" not in f.detail


def _malformed_hook_graph(root):
    """A fold failure makes protocol tests independent of checker policy."""
    graph = root / S.GRAPH_DIR / S.GRAPH_FILE
    graph.parent.mkdir(parents=True)
    graph.write_text('{"ev":"model"}\n', encoding="utf-8")


def test_codex_hook_process_returns_a_structured_post_tool_block(tmp_path):
    """W8: exit 2 ran the Codex hook but hid its refusal from the author."""
    _malformed_hook_graph(tmp_path)
    payload = {"cwd": str(tmp_path), "tool_name": "Bash",
               "hook_event_name": "PostToolUse", "model": "gpt-5"}
    result = subprocess.run(
        [sys.executable, "-m", "grandportage.hook"],
        input=json.dumps(payload), text=True, capture_output=True,
        cwd=str(tmp_path))

    assert result.returncode == 0
    decision = json.loads(result.stdout)
    assert decision["decision"] == "block"
    assert "does not fold" in decision["reason"]
    assert result.stderr == ""


def test_claude_hook_process_keeps_exit_two_and_stderr(tmp_path):
    """The Codex repair must not weaken the existing Claude protocol."""
    _malformed_hook_graph(tmp_path)
    payload = {"cwd": str(tmp_path), "tool_name": "Bash",
               "hook_event_name": "PostToolUse"}
    result = subprocess.run(
        [sys.executable, "-m", "grandportage.hook"],
        input=json.dumps(payload), text=True, capture_output=True,
        cwd=str(tmp_path))

    assert result.returncode == 2
    assert result.stdout == ""
    assert "does not fold" in result.stderr


def test_codex_project_hook_definition_is_found(tmp_path):
    hooks = tmp_path / ".codex" / "hooks.json"
    hooks.parent.mkdir()
    hooks.write_text(json.dumps({"hooks": {"PostToolUse": [{
        "matcher": "*", "hooks": [{"type": "command",
                                      "command":
                                      "python -m grandportage.hook"}]}]}}),
                     encoding="utf-8")
    assert cli._hook_definition_found(str(tmp_path))


def test_wrong_event_and_commented_hook_are_not_definitions(tmp_path):
    hooks = tmp_path / ".codex" / "hooks.json"
    hooks.parent.mkdir()
    hooks.write_text(json.dumps({"hooks": {"Stop": [{
        "hooks": [{"type": "command",
                   "command": "python -m grandportage.hook"}]}]}}),
                     encoding="utf-8")
    assert not cli._hook_definition_found(str(tmp_path))

    hooks.unlink()
    config = hooks.with_name("config.toml")
    config.write_text(
        "# [[hooks.PostToolUse.hooks]]\n"
        "# command = 'python -m grandportage.hook'\n",
        encoding="utf-8")
    assert not cli._hook_definition_found(str(tmp_path))


def test_inline_codex_toml_hook_definition_is_found(tmp_path):
    config = tmp_path / ".codex" / "config.toml"
    config.parent.mkdir()
    config.write_text(
        "[[hooks.PostToolUse]]\nmatcher = '^Bash$'\n\n"
        "[[hooks.PostToolUse.hooks]]\n"
        "type = 'command'\n"
        "command = 'python -m grandportage.hook'\n",
        encoding="utf-8")
    assert cli._hook_definition_found(str(tmp_path))


def test_declare_help_names_sparse_tombstones_and_required_why():
    help_text = cli._declare_epilog()
    assert "RETRACT or WITHDRAW tombstone also requires `why`" in help_text
    assert "sparse lifecycle history" in help_text
