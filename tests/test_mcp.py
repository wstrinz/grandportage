"""The MCP server: protocol, and the forcing function stated three ways.

`edge` is required in the JSON Schema, validated by the handler, and a
keyword-only argument with no default on `run_cas`.  Each layer protects
against a different failure, so each is tested separately -- a client that
ignores its own schema must still not reach the solver.
"""

import io
import json

import pytest

from grandportage import cas
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
         "statement": "a witness"},
        {"ev": "inference", "id": "INF", "claim": "CL",
         "path": [["E1", K.AGAINST]], "asserted": "a germ exists"},
    ]}, project)
    body = text(call("portage_show", {}, project))
    for tag in ("MODEL SRC", "MODEL DST", "EDGE  E1", "CLAIM CL", "INFER INF"):
        assert tag in body


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
