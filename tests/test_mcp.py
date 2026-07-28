"""The MCP server: protocol, and the forcing function stated three ways.

`edge` is required in the JSON Schema, validated by the handler, and a
keyword-only argument with no default on `run_cas`.  Each layer protects
against a different failure, so each is tested separately -- a client that
ignores its own schema must still not reach the solver.
"""

import io
import json
import os
import re

import pytest

from grandportage import cas
from grandportage import discharge as D
from grandportage import kernel as K
from grandportage import mcp
from grandportage import store as S


def rpc(method, params=None, rid=1):
    r = {"jsonrpc": "2.0", "method": method}
    if rid is not None:
        r["id"] = rid
    if params is not None:
        r["params"] = params
    return r


def call(name, arguments, root):
    return mcp.dispatch(rpc("tools/call", {"name": name,
                                           "arguments": arguments}),
                        root=root)["result"]


def text(result):
    return result["content"][0]["text"]


@pytest.fixture
def project(tmp_path):
    root = str(tmp_path)
    S.append([{"ev": "model", "id": "SRC", "desc": "the source", "field": "Q"}],
             root=root)
    return root


# ===========================================================================
# Protocol
# ===========================================================================

def test_initialize_echoes_a_supported_protocol_version():
    for v in mcp.SUPPORTED_PROTOCOLS:
        r = mcp.dispatch(rpc("initialize", {"protocolVersion": v}))
        assert r["result"]["protocolVersion"] == v


def test_initialize_falls_back_for_an_unknown_version():
    r = mcp.dispatch(rpc("initialize", {"protocolVersion": "1999-01-01"}))
    assert r["result"]["protocolVersion"] == mcp.PROTOCOL_VERSION


def test_notifications_get_no_response():
    """A response to a notification is a protocol violation."""
    assert mcp.dispatch(rpc("notifications/initialized", rid=None)) is None


def test_unknown_method_fails_but_unknown_notification_is_silent():
    assert "error" in mcp.dispatch(rpc("no/such/method"))
    assert mcp.dispatch(rpc("no/such/method", rid=None)) is None


def test_tools_list_is_well_formed():
    tools = mcp.dispatch(rpc("tools/list"))["result"]["tools"]
    names = {t["name"] for t in tools}
    assert names == set(mcp.HANDLERS)
    for t in tools:
        assert t["description"]
        schema = t["inputSchema"]
        for req in schema["required"]:
            assert req in schema["properties"], (t["name"], req)


def test_serve_round_trips_over_a_stream(project):
    out = io.StringIO()
    mcp.serve(stdin=io.StringIO(json.dumps(rpc("tools/list")) + "\n"),
              stdout=out, root=project)
    assert "cas_ideal_is_unit" in out.getvalue()


def test_a_malformed_line_gets_a_parse_error_not_a_crash(project):
    out = io.StringIO()
    mcp.serve(stdin=io.StringIO("{not json\n"), stdout=out, root=project)
    assert json.loads(out.getvalue())["error"]["code"] == -32700


# ===========================================================================
# The forcing function
# ===========================================================================

def test_edge_is_required_in_the_schema_of_every_producing_tool():
    for t in mcp.dispatch(rpc("tools/list"))["result"]["tools"]:
        if "produces" in t["inputSchema"]["properties"]:
            assert "edge" in t["inputSchema"]["required"], t["name"]


def test_the_edge_schema_teaches_the_decision_not_just_the_enum():
    """The caller is being asked to make a modelling judgement, and an enum
    alone does not tell it how to choose.  Every declarable type must appear in
    the guidance, phrased around what the step LOSES."""
    desc = mcp.EDGE_SCHEMA["properties"]["type"]["description"]
    for t in K.DECLARABLE_TYPES:
        assert t in desc
    assert "LOSES" in desc
    assert set(mcp.EDGE_SCHEMA["required"]) == {"src", "type", "why"}


def test_a_client_ignoring_its_own_schema_still_cannot_reach_the_solver(project):
    r = call("cas_ideal_is_unit",
             {"ring_vars": ["x"], "generators": ["x"], "produces": "M",
              "describes": "d"}, project)
    assert r.get("isError")
    assert "no transport declared" in text(r)


def test_a_malformed_edge_is_refused_with_the_five_options(project):
    r = call("cas_ideal_is_unit",
             {"ring_vars": ["x"], "generators": ["x"], "produces": "M",
              "describes": "d",
              "edge": {"src": "SRC", "type": "SEEMS_FINE", "why": "w"}},
             project)
    assert r.get("isError")
    for t in (K.NECESSARY_CONDITION, K.BASE_EXTENSION, K.IMAGE_CLOSURE,
              K.SPECIALIZATION):
        assert t in text(r)


def test_refusals_come_back_as_tool_errors_not_protocol_errors(project):
    """A refusal is the PRODUCT, not a crash.  It has to reach the model as
    content it can read and act on, so it must not be a JSON-RPC error."""
    r = mcp.dispatch(rpc("tools/call", {
        "name": "cas_ideal_is_unit",
        "arguments": {"ring_vars": ["x"], "generators": ["x"],
                      "produces": "M", "describes": "d"}}), root=project)
    assert "error" not in r
    assert r["result"]["isError"] is True


# ===========================================================================
# Recording and checking
# ===========================================================================

def test_declare_writes_and_immediately_reports_findings(project):
    r = call("portage_declare", {"events": [
        {"ev": "model", "id": "DST", "desc": "the target", "field": "K"},
        {"ev": "edge", "id": "E1", "src": "SRC", "dst": "DST",
         "type": K.BASE_EXTENSION, "why": "the field grows"},
        {"ev": "claim", "id": "CL", "model": "SRC", "kind": K.EMPTY,
         "statement": "no solution", "scope": "Q",
         "certificate": "NONSQUARE_CLASS"},
        {"ev": "inference", "id": "INF", "claim": "CL",
         "path": [["E1", K.ALONG]], "asserted": "hence empty over K"},
    ]}, project)
    body = text(r)
    assert "recorded" in body
    assert "UNSOUND_PREMISE" in body
    assert "does not base-change" in body
    assert "DISCHARGE" in body


def test_a_declaration_that_would_not_fold_writes_nothing(project):
    r = call("portage_declare", {"events": [
        {"ev": "claim", "id": "CL", "model": "GHOST", "kind": K.EMPTY,
         "statement": "x", "certificate": "UNIT_IDEAL_CERT"}]}, project)
    assert r.get("isError")
    with open(S.graph_path(project), encoding="utf-8") as fh:
        assert "GHOST" not in fh.read()


def test_a_field_relative_certificate_at_scheme_scope_is_refused(project):
    """The scope error surfaces through the protocol as a readable refusal."""
    r = call("portage_declare", {"events": [
        {"ev": "claim", "id": "CL", "model": "SRC", "kind": K.EMPTY,
         "statement": "x", "certificate": "NONSQUARE_CLASS",
         "scope": "SCHEME"}]}, project)
    assert r.get("isError")
    assert "ScopeError" in text(r)


def test_check_and_show_on_an_empty_project(tmp_path):
    root = str(tmp_path)
    assert "no graph yet" in text(call("portage_check", {}, root))
    assert "no graph yet" in text(call("portage_show", {}, root))


def test_transport_table_names_every_type_and_certificate(project):
    body = text(call("portage_transport_table", {}, project))
    for t in K.DECLARABLE_TYPES:
        assert t in body
    for c in K.BUILTIN_CERTIFICATES:
        assert c in body
    assert "FIELD-RELATIVE" in body


def test_show_renders_the_graph_as_a_handoff(project):
    call("portage_declare", {"events": [
        {"ev": "model", "id": "DST", "desc": "the target"},
        {"ev": "edge", "id": "E1", "src": "SRC", "dst": "DST",
         "type": K.NECESSARY_CONDITION, "why": "drops equations"},
        {"ev": "claim", "id": "CL", "model": "DST", "kind": K.NONEMPTY,
         "statement": "a witness", "witness_kind": K.EXHIBITED},
        {"ev": "inference", "id": "INF", "claim": "CL",
         "path": [["E1", K.AGAINST]], "asserted": "a germ exists"},
    ]}, project)
    body = text(call("portage_show", {}, project))
    for tag in ("MODEL SRC", "MODEL DST", "EDGE  E1", "CLAIM CL", "INFER INF"):
        assert tag in body


def test_show_prints_every_premise_of_a_multi_premise_inference(project):
    """The handoff view has to show the JOIN, not the first leg of it.

    The fold keeps the singular `claim` and `path` populated from the FIRST
    premise so that older readers keep working, so a printer reading those
    fields renders a two-premise argument as a one-premise chain -- and renders
    it plausibly, which is what makes it expensive.  A campaign built its model
    of the graph from this output, concluded a claim was consumed by nothing,
    superseded it, and learned otherwise from a stale-premise finding.
    """
    r = call("portage_declare", {"events": [
        {"ev": "model", "id": "DST", "desc": "the target"},
        {"ev": "edge", "id": "E1", "src": "SRC", "dst": "DST",
         "type": K.NECESSARY_CONDITION, "why": "drops equations"},
        {"ev": "claim", "id": "CL-FAR", "model": "DST", "kind": K.NONEMPTY,
         "statement": "a witness in the relaxation",
         "witness_kind": K.EXHIBITED},
        {"ev": "claim", "id": "CL-NEAR", "model": "SRC", "kind": K.NONEMPTY,
         "statement": "the side condition, which used to end up in a note",
         "witness_kind": K.EXHIBITED},
        {"ev": "inference", "id": "INF", "asserted": "hence a germ at SRC",
         "premises": [{"claim": "CL-FAR", "path": [["E1", K.AGAINST]]},
                      {"claim": "CL-NEAR", "path": []}]},
    ]}, project)
    assert not r.get("isError"), text(r)
    body = text(call("portage_show", {}, project))
    assert "CL-FAR" in body
    # The premise the singular-field printer dropped on the floor.
    assert "CL-NEAR" in body
    # And each premise's own route, since a premise that arrives by a different
    # path is a different argument.
    assert "E1/%s" % K.AGAINST in body
    assert "2 premises" in body


def test_show_prints_an_open_slot_premise_as_a_visible_absence(project):
    """A premise the argument NEEDS and does not have licenses nothing, so it
    must print as a hole.  Omitting it makes an argument with a declared gap
    indistinguishable from one that never needed the premise -- which is the
    single thing the open slot was added to make impossible.

    Written through `S.append` rather than `portage_declare` deliberately.
    Declaring this graph currently raises out of `check._first_refusal`, which
    looks the trace's `(missing)` marker up in `graph.edges`; that is a defect
    in a file this change does not own, and routing around it keeps this test
    about the printer.
    """
    S.append([
        {"ev": "claim", "id": "CL", "model": "SRC", "kind": K.NONEMPTY,
         "statement": "a witness", "witness_kind": K.EXHIBITED},
        {"ev": "inference", "id": "INF", "asserted": "hence a germ",
         "premises": [
             {"claim": "CL", "path": []},
             {"required_kind": K.EMPTY, "at": "SRC",
              "missing_why": "no such claim exists: five candidates survive"}]},
    ], root=project)
    body = text(call("portage_show", {}, project))
    assert "MISSING" in body
    # The full phrase, because EMPTY is a substring of NONEMPTY and the claim
    # line above already prints one of those.
    assert "needs a claim of kind %s at SRC" % K.EMPTY in body
    assert "five candidates survive" in body


def test_show_marks_a_superseded_record_and_names_its_replacement(project):
    """A dead record that prints like a live one is the reason supersession
    exists, and the handoff view is where it does the most damage."""
    r = call("portage_declare", {"events": [
        {"ev": "claim", "id": "CL", "model": "SRC", "kind": K.NONEMPTY,
         "statement": "a witness", "witness_kind": K.EXHIBITED},
        {"ev": "inference", "id": "INF", "asserted": "hence a germ",
         "premises": [{"claim": "CL", "path": []}]},
        {"ev": "claim", "id": "CL2", "model": "SRC", "kind": K.NONEMPTY,
         "statement": "a witness", "witness_kind": K.EXHIBITED,
         "cite": "arXiv:0000.0000", "supersedes": "CL",
         "discharge_kind": K.AMEND},
        {"ev": "inference", "id": "INF2", "asserted": "hence a germ, cited",
         "premises": [{"claim": "CL2", "path": []}],
         "supersedes": "INF", "discharge_kind": K.RESTATE},
    ]}, project)
    assert not r.get("isError"), text(r)
    body = text(call("portage_show", {}, project))
    assert "[SUPERSEDED by CL2]" in body
    assert "supersedes CL (%s)" % K.AMEND in body
    assert "[SUPERSEDED by INF2]" in body
    assert "supersedes INF (%s)" % K.RESTATE in body


# ===========================================================================
# The two discharge vocabularies
# ===========================================================================

def _declare_events_description():
    tools = {t["name"]: t
             for t in mcp.dispatch(rpc("tools/list"))["result"]["tools"]}
    return tools["portage_declare"]["inputSchema"]["properties"]["events"][
        "description"]


def test_both_discharge_vocabularies_are_documented_on_the_tool_surface():
    """A refusal that is correct but whose correct answer cannot be looked up
    from the tool is a design cost charged to the caller.  A campaign hit a
    refusal demanding a DERIVE or RETYPE discharge and had to read
    discharge.py's source to find the words, because only the claim vocabulary
    was documented here.

    Word BOUNDARIES, not `in`: DERIVE is a substring of DERIVED, an unrelated
    identity_origin value this same description documents, so a substring test
    passes against a file where the edge vocabulary is entirely absent.
    """
    desc = _declare_events_description()
    for kind in tuple(D.DISCHARGE_KINDS) + tuple(K.SUPERSESSION_KINDS):
        assert re.search(r"\b%s\b" % kind, desc), kind


def test_the_two_discharge_vocabularies_are_never_offered_as_one_list():
    """Documenting both invites the failure documenting neither did not: a
    reader merging seven words into one menu and picking AMEND for an edge.

    So each vocabulary must sit under the kind of record it applies to, and
    neither list's words may appear in the other's section.
    """
    desc = _declare_events_description()
    before, sep, claim_part = desc.partition("REPLACING A CLAIM OR AN INFERENCE")
    assert sep, "the claim/inference vocabulary has no heading of its own"
    edge_part = before.partition("REPLACING AN EDGE")[2]
    assert edge_part, "the edge vocabulary has no heading of its own"
    for kind in D.DISCHARGE_KINDS:
        assert re.search(r"\b%s\b" % kind, edge_part), kind
        assert not re.search(r"\b%s\b" % kind, claim_part), kind
    for kind in K.SUPERSESSION_KINDS:
        assert re.search(r"\b%s\b" % kind, claim_part), kind
        assert not re.search(r"\b%s\b" % kind, edge_part), kind


def test_the_edge_vocabulary_says_what_it_discharges_and_the_other_does_not():
    """The lists differ because the QUESTIONS differ, and a reader who cannot
    see that will pick by feel.  An edge supersession discharges an OBLIGATION
    the old edge was carrying; a claim supersession describes WHAT CHANGED
    about the record."""
    desc = _declare_events_description()
    edge_part = desc.partition("REPLACING AN EDGE")[2].partition(
        "REPLACING A CLAIM OR AN INFERENCE")[0]
    assert "OBLIGATION" in edge_part
    claim_part = desc.partition("REPLACING A CLAIM OR AN INFERENCE")[2]
    assert "WHAT CHANGED" in claim_part
    # And the collision is called out where a reader would otherwise trip on
    # it: the discharge kind DERIVE is not the identity_origin value DERIVED.
    assert K.DERIVED in edge_part


def test_a_successful_cas_call_records_the_typed_edge(project, monkeypatch):
    monkeypatch.setattr(cas, "_run_subprocess",
                        lambda prog, timeout: {
                            "returncode": 0, "stdout": "@@GP_G:\nGP_G[1]=1\n",
                            "stderr": "", "aborted": False,
                            "abort_reason": None, "argv": ["fake"]})
    r = call("cas_ideal_is_unit", {
        "ring_vars": ["x"], "generators": ["x", "x-1"],
        "produces": "ELIM", "describes": "the eliminated ideal",
        "edge": {"src": "SRC", "type": K.IMAGE_CLOSURE,
                 "why": "elimination returns the Zariski closure",
                 "map_kind": K.POLYNOMIAL}}, project)
    body = text(r)
    assert "recorded: model ELIM" in body
    g = S.load(S.graph_path(project))
    assert g.edges["E-ELIM"]["type"] == K.IMAGE_CLOSURE


def test_a_unit_ideal_result_is_reported_as_evidence_not_a_kill(project,
                                                                monkeypatch):
    """The single most important sentence the server emits.

    An ideal reducing to (1) is where the shipped error STARTED, so the tool
    that reports it must say what it is and is not.
    """
    monkeypatch.setattr(cas, "_run_subprocess",
                        lambda prog, timeout: {
                            "returncode": 0, "stdout": "@@GP_G:\nGP_G[1]=1\n",
                            "stderr": "", "aborted": False,
                            "abort_reason": None, "argv": ["fake"]})
    body = text(call("cas_ideal_is_unit", {
        "ring_vars": ["x"], "generators": ["x", "x-1"], "produces": "E",
        "describes": "d",
        "edge": {"src": "SRC", "type": K.BASE_EXTENSION,
                 "why": "the field grows"}}, project))
    assert "EVIDENCE of emptiness and not yet a kill" in body
    assert "certificate" in body
    assert "will NOT base-change" in body


def test_the_server_holds_no_state_between_calls(project, monkeypatch):
    """Restart mid-campaign and the next call folds the same graph.

    Asserted because the protocol is moving toward statelessness at the
    transport layer, and a transport graph is stateful -- so the state must
    live in .portage/, never in a session.
    """
    call("portage_declare", {"events": [
        {"ev": "model", "id": "DST", "desc": "the target"}]}, project)
    # a completely fresh dispatch, as if the process had been restarted
    body = text(call("portage_show", {}, project))
    assert "MODEL DST" in body


def test_a_call_may_name_its_own_root(tmp_path):
    """THE FIX FOR THE HAZARD THE TEST BELOW ONLY NARRATES.

    That one says "the server cannot know where its config lives, so it cannot
    resolve the root differently. It can say which graph it wrote." True, and
    incomplete: the SERVER cannot resolve it, and the CALLER can. Naming the
    campaign per call turns an environment guess into an argument.

    This matters because sessions run from a directory that is not the
    campaign. Three consecutive live sessions reported the MCP server
    unreachable and fell back to hand-appending JSONL -- which is how one of
    them poisoned a graph past the transactional guard. The server was fine;
    it was declared in a repo the sessions were not rooted in, and even when
    reached would have written to the session root.
    """
    from grandportage import mcp as M
    campaign = tmp_path / "campaign"
    (campaign / ".portage").mkdir(parents=True)
    session_root = str(tmp_path / "elsewhere")
    os.makedirs(session_root)

    req = {"jsonrpc": "2.0", "id": 1, "method": "tools/call",
           "params": {"name": "portage_declare",
                      "arguments": {
                          "events": [{"ev": "model", "id": "M",
                                      "desc": "a model"}],
                          "root": str(campaign)}}}
    M.dispatch(req, root=session_root)

    assert os.path.exists(S.graph_path(str(campaign))), (
        "the call named its campaign and the write must land there")
    assert not os.path.exists(S.graph_path(session_root)), (
        "and must NOT land in the server's own working directory, which is "
        "the whole failure this argument exists to prevent")


def test_declare_names_the_graph_it_writes(tmp_path):
    """`GP_ROOT` defaults to "." and "." is the SERVER's cwd, not the directory
    its `.mcp.json` sits in. So a campaign whose config says `GP_ROOT: "."`
    writes to a different graph than `gp check` inside that campaign reads.

    A live lane hit this in the worst available way. The root graph was in a
    refused state from an unrelated session, `declare` is transactional against
    the fold, and the author's FIRST declaration came back citing a claim id
    they had never seen in a campaign they had just created. They diagnosed it
    by diffing four copies of a fixture.

    The server cannot know where its config lives, so it cannot resolve the
    root differently. It can say which graph it wrote, which turns a mystery
    into a fact on the first call.
    """
    from grandportage import mcp as M
    root = str(tmp_path)
    out = M.h_portage_declare(
        {"events": [{"ev": "model", "id": "M", "desc": "a model"}]}, root)
    text = out["content"][0]["text"]
    assert os.path.abspath(S.graph_path(root)) in text, (
        "a write must name the file it wrote")


def test_a_refused_graph_says_which_graph_refused(tmp_path):
    """The failure path matters more than the success path here, because that
    is the one that cost a session an hour."""
    from grandportage import mcp as M
    root = str(tmp_path)
    p = S.graph_path(root)
    os.makedirs(os.path.dirname(p), exist_ok=True)
    with open(p, "w", encoding="utf-8") as fh:
        fh.write(json.dumps({"ev": "model", "id": "M", "desc": "m"}) + "\n")
        fh.write(json.dumps({"ev": "claim", "id": "C", "model": "M",
                             "kind": "PREDICATE", "statement": "P",
                             "ladder": "exact-checked"}) + "\n")
    out = M.h_portage_declare(
        {"events": [{"ev": "model", "id": "N", "desc": "another"}]}, root)
    text = out["content"][0]["text"]
    assert "THE GRAPH BEING WRITTEN IS" in text
    assert os.path.abspath(p) in text
    assert "may be about your campaign at all" in text
