"""ARR15 identity, diagnostics, schema, and isolated MCP acceptance tests."""

import json
import os
import sys

import pytest

from grandportage import __version__
from grandportage import cas
from grandportage import cli
from grandportage import format as F
from grandportage import identity as I
from grandportage import mcp as MCP
from grandportage import store as S


def test_version_reports_exact_shared_identity(capsys):
    with pytest.raises(SystemExit) as stopped:
        cli.main(["--version"])
    assert stopped.value.code == 0
    output = capsys.readouterr().out
    expected = I.implementation_identity(
        __version__, F.GRAPH_FORMAT, F.KERNEL_EPOCH)
    assert output == I.version_text(expected) + "\n"
    assert "source " in output
    assert "MCP protocol " in output
    assert "backend " in output


def test_mcp_initialize_exposes_the_same_closed_identity():
    response = MCP.dispatch({
        "jsonrpc": "2.0", "id": 1, "method": "initialize",
        "params": {"protocolVersion": MCP.PROTOCOL_VERSION},
    })
    server = response["result"]["serverInfo"]
    assert server["version"] == __version__
    assert server["grandPortage"] == I.implementation_identity(
        __version__, F.GRAPH_FORMAT, F.KERNEL_EPOCH)


def test_native_schema_is_generated_from_the_runtime_contract(capsys):
    assert cli.main(["schema"]) == 0
    document = json.loads(capsys.readouterr().out)
    assert document["graph_format"] == F.GRAPH_FORMAT
    assert document["kernel_epoch"] == F.KERNEL_EPOCH
    assert set(document["events"]) == set(F.EVENT_FIELDS)
    for kind, entry in document["events"].items():
        schema = entry["schema"]
        assert set(schema["properties"]) == F.EVENT_FIELDS[kind]
        assert set(schema["required"]) == F.AUTHOR_REQUIRED_FIELDS.get(
            kind, F.REQUIRED_FIELDS.get(kind, {"ev"}))
        assert schema["additionalProperties"] is False
    assert document["events"]["meta"]["authorable"] is False
    assert document["events"]["verdict"]["authorable"] is False


def test_doctor_names_root_graph_identity_and_read_only_health(
        tmp_path, monkeypatch, capsys):
    assert cli.main(["--root", str(tmp_path), "init"]) == 0
    capsys.readouterr()
    monkeypatch.setattr(cas, "_singular_binary_version", lambda: "Singular 4.test")
    monkeypatch.setattr(
        MCP, "h_cas_health",
        lambda _args, _root: MCP._text(
            "CAS reachable; answer is correct. NOTHING was written."))
    before = open(S.graph_path(str(tmp_path)), "rb").read()
    assert cli.main(["--root", str(tmp_path), "doctor", "--json"]) == 0
    report = json.loads(capsys.readouterr().out)
    assert report["root"] == os.path.abspath(str(tmp_path))
    assert report["graph"]["path"] == os.path.abspath(
        S.graph_path(str(tmp_path)))
    assert report["graph"]["header"]["implementation"] == (
        report["implementation"])
    assert report["cas"]["binary_version"] == "Singular 4.test"
    assert report["cas"]["healthy"] is True
    assert open(S.graph_path(str(tmp_path)), "rb").read() == before


def test_init_mcp_pins_two_campaigns_to_different_absolute_roots(tmp_path):
    roots = [tmp_path / "alpha", tmp_path / "beta"]
    for root in roots:
        root.mkdir()
        assert cli.main(["--root", str(root), "init", "--mcp"]) == 0

    configs = [
        json.loads((root / ".mcp.json").read_text(encoding="utf-8"))
        for root in roots
    ]
    configured_roots = []
    for root, config in zip(roots, configs):
        server = config["mcpServers"]["grand-portage"]
        assert server["command"] == sys.executable
        assert server["args"][:3] == ["-m", "grandportage.mcp", "--root"]
        configured_roots.append(server["args"][3])
        result = MCP.h_portage_declare({
            "events": [{"ev": "model", "id": root.name,
                        "what": "isolated campaign"}],
        }, server["args"][3])
        assert not result.get("isError")

    assert configured_roots == [os.path.abspath(str(root)) for root in roots]
    assert set(S.load(S.graph_path(str(roots[0]))).models) == {"alpha"}
    assert set(S.load(S.graph_path(str(roots[1]))).models) == {"beta"}


def test_init_mcp_refuses_to_overwrite_existing_config(tmp_path):
    config = tmp_path / ".mcp.json"
    config.write_text('{"owned":"elsewhere"}\n', encoding="utf-8")
    assert cli.main(["--root", str(tmp_path), "init", "--mcp"]) == 1
    assert json.loads(config.read_text(encoding="utf-8")) == {
        "owned": "elsewhere"}
    assert not os.path.exists(S.graph_path(str(tmp_path)))
