"""Durable raw executions are complete, immutable, and independently audited."""

import json
import os
from dataclasses import replace

import pytest

from grandportage import artifacts as A
from grandportage import backend as B
from grandportage import cas
from grandportage import cli
from grandportage import kernel as K
from grandportage import provenance as P
from grandportage import store as S
from grandportage import verify as V


def _artifact(stdout="answer\n"):
    backend = B.BackendIdentity(
        B.SINGULAR_CONTRACT,
        B.SINGULAR_IMPLEMENTATION,
        B.SINGULAR_IMPLEMENTATION_VERSION,
        "Singular 4.4.1",
    )
    program = 'print("@@GP-END:0123456789abcdef0123456789abcdef");\n'
    return B.ExecutionArtifact(
        backend=backend,
        semantic_input_fingerprint=B.semantic_fingerprint(
            "test_request", {"x": 1}),
        program_fingerprint=B.text_fingerprint(program),
        program_text=program,
        completion_nonce="0123456789abcdef0123456789abcdef",
        argv=("Singular", "-q"),
        returncode=0,
        aborted=False,
        abort_reason=None,
        stdout=stdout,
        stderr="",
        stdout_fingerprint=B.text_fingerprint(stdout),
        stderr_fingerprint=B.text_fingerprint(""),
        parsed_output='{"answer":1}',
        certificate='{"cofactors":["1"]}',
    )


def _manifest(artifact):
    trace = [B.execution_trace_entry(artifact)]
    return {
        "schema": 2,
        "contract": artifact.backend.contract,
        "implementation": artifact.backend.implementation,
        "implementation_version": artifact.backend.implementation_version,
        "protocol_version": B.BACKEND_PROTOCOL_VERSION,
        "binary_version": artifact.backend.binary_version,
        "executions": trace,
        "trace_fingerprint": B.semantic_fingerprint(
            "backend_execution_trace", trace),
    }


def test_complete_execution_round_trips_and_deduplicates(tmp_path):
    artifact = _artifact()
    first = A.persist(str(tmp_path), artifact)
    second = A.persist(str(tmp_path), artifact)

    assert first == second == B.execution_artifact_fingerprint(artifact)
    stored = A.load(str(tmp_path), first)
    assert stored == artifact.payload()
    assert stored["program_text"] == artifact.program_text
    assert stored["completion_nonce"] == artifact.completion_nonce
    assert stored["stdout"] == artifact.stdout
    assert stored["parsed_output"] == artifact.parsed_output
    assert stored["certificate"] == artifact.certificate
    assert A.audit_manifest(str(tmp_path), _manifest(artifact)) == []


def test_corrupt_existing_object_is_refused_and_not_healed(tmp_path):
    artifact = _artifact()
    ref = A.persist(str(tmp_path), artifact)
    path = A.artifact_path(str(tmp_path), ref)
    corrupt = b'{"corrupt":true}'
    with open(path, "wb") as fh:
        fh.write(corrupt)

    with pytest.raises(A.ArtifactError, match="other bytes"):
        A.persist(str(tmp_path), artifact)
    with open(path, "rb") as fh:
        assert fh.read() == corrupt


def test_publication_fails_closed_without_atomic_immutable_link(
        tmp_path, monkeypatch):
    artifact = _artifact()

    def no_link(_source, _target):
        raise OSError("hard links unavailable")

    monkeypatch.setattr(A.os, "link", no_link)
    with pytest.raises(A.ArtifactError, match="cannot atomically publish"):
        A.persist(str(tmp_path), artifact)
    assert not os.path.exists(A.artifact_path(
        str(tmp_path), B.execution_artifact_fingerprint(artifact)))


def test_inner_hash_and_content_address_are_both_checked(tmp_path):
    artifact = _artifact()
    ref = A.persist(str(tmp_path), artifact)
    path = A.artifact_path(str(tmp_path), ref)
    value = artifact.payload()
    value["stdout"] = "tampered\n"
    with open(path, "w", encoding="utf-8") as fh:
        json.dump(value, fh, sort_keys=True, separators=(",", ":"))

    with pytest.raises(A.ArtifactError, match="stdout hash"):
        A.load(str(tmp_path), ref)


def test_manifest_audit_reports_missing_and_swapped_artifacts(tmp_path):
    one = _artifact("one\n")
    two = _artifact("two\n")
    A.persist(str(tmp_path), two)

    missing = A.audit_manifest(str(tmp_path), _manifest(one))
    assert len(missing) == 1
    assert "missing artifact" in missing[0]

    manifest = _manifest(one)
    manifest["executions"][0]["artifact_fingerprint"] = (
        B.execution_artifact_fingerprint(two))
    swapped = A.audit_manifest(str(tmp_path), manifest)
    assert any("projection does not match trace" in problem
               for problem in swapped)

    wrong_protocol = _manifest(two)
    wrong_protocol["protocol_version"] -= 1
    assert any("backend does not match manifest" in problem
               for problem in A.audit_manifest(str(tmp_path), wrong_protocol))


def test_malformed_fingerprint_cannot_escape_artifact_store(tmp_path):
    with pytest.raises(A.ArtifactError, match="malformed"):
        A.artifact_path(str(tmp_path), "../../graph.jsonl")


def test_persist_all_uses_content_addresses_in_execution_order(tmp_path):
    artifacts = [_artifact("one\n"), _artifact("two\n")]
    refs = A.persist_all(str(tmp_path), artifacts)
    assert refs == [B.execution_artifact_fingerprint(a) for a in artifacts]
    assert all(os.path.isfile(A.artifact_path(str(tmp_path), ref))
               for ref in refs)


def test_cli_audits_referenced_objects_without_changing_graph_fold(
        tmp_path, capsys, monkeypatch):
    root = str(tmp_path)
    S.append([
        {"ev": "model", "id": "M", "what": "origin",
         "characteristic": 0, "ring_vars": ["x"], "generators": ["x"]},
        {"ev": "claim", "id": "C", "model": "M", "kind": K.IDENTITY,
         "statement": "x vanishes", "lhs": "x", "rhs": "0",
         "ring_vars": ["x"], "identity_origin": K.DERIVED},
    ], root)
    graph = S.load(S.graph_path(root))
    artifact = _artifact()
    monkeypatch.setitem(
        cas._BINARY_VERSION_CACHE, tuple(cas._argv()),
        artifact.backend.binary_version)
    A.persist(root, artifact)
    verdict = V._verdict_event(
        graph, "claim", "C", "VERIFIED_DERIVED", "test reduction",
        execution=_manifest(artifact))
    S.append([verdict], root)

    assert cli.main(["--root", root, "artifacts", "check"]) == 0
    assert "1 execution reference checked" in capsys.readouterr().out
    assert S.load(S.graph_path(root)).claims["C"]["identity_verdict"] == (
        "VERIFIED_DERIVED")

    os.remove(A.artifact_path(root, B.execution_artifact_fingerprint(artifact)))
    # Filesystem loss is an explicit audit failure, not ambient graph semantics.
    assert cli.main(["--root", root, "artifacts", "check"]) == 1
    assert "missing artifact" in capsys.readouterr().err
    assert S.load(S.graph_path(root)).claims["C"]["identity_verdict"] == (
        "VERIFIED_DERIVED")


@pytest.mark.parametrize("current_binary", [
    "unavailable: exit 1",
    "Singular for test-fixture version 99.0",
])
def test_exact_identity_receipt_survives_local_backend_state(
        tmp_path, monkeypatch, current_binary):
    """Reading exact authority must not depend on whether WSL is reachable.

    CFG23's final identities carried complete cofactor derivations. The same
    graph folded VERIFIED with Singular available and UNVERIFIED when the WSL
    service was denied, producing TRIAGE findings that disappeared when the
    reader changed execution context. The retained arithmetic certificate is
    the stable boundary.
    """
    root = str(tmp_path)
    S.append([
        {"ev": "model", "id": "M", "what": "double point",
         "characteristic": 0, "ring_vars": ["x"], "generators": ["x"]},
        {"ev": "claim", "id": "C", "model": "M", "kind": K.IDENTITY,
         "statement": "x squared vanishes", "lhs": "x^2", "rhs": "0",
         "ring_vars": ["x"], "identity_origin": K.DERIVED},
    ], root)
    graph = S.load(S.graph_path(root))
    artifact = _artifact()
    A.persist(root, artifact)
    representation = {
        "cofactors": ["x"], "generators": ["x"],
        "ring_vars": ["x"], "target": "(x^2) - (0)",
    }
    verdict = V._verdict_event(
        graph, "claim", "C", "VERIFIED_DERIVED", "exact derivation",
        representation, execution=_manifest(artifact))
    S.append([verdict], root)

    monkeypatch.setattr(
        cas, "_singular_binary_version", lambda **_kw: current_binary)
    cas._BINARY_VERSION_CACHE.clear()
    reloaded = S.load(S.graph_path(root))
    assert reloaded.claims["C"]["identity_verdict"] == "VERIFIED_DERIVED"
    assert reloaded.verdicts[verdict["id"]]["current"] is True
    assert V.verify_all(root=root, record=False) == []


def test_malformed_v2_manifest_is_an_explicit_audit_failure(tmp_path):
    root = str(tmp_path)
    S.append([
        {"ev": "model", "id": "M", "what": "origin",
         "characteristic": 0, "ring_vars": ["x"], "generators": ["x"]},
        {"ev": "claim", "id": "C", "model": "M", "kind": K.IDENTITY,
         "statement": "x vanishes", "lhs": "x", "rhs": "0",
         "ring_vars": ["x"], "identity_origin": K.DERIVED},
    ], root)
    graph = S.load(S.graph_path(root))
    artifact = _artifact()
    manifest = _manifest(artifact)
    del manifest["protocol_version"]
    verdict = V._verdict_event(
        graph, "claim", "C", "VERIFIED_DERIVED", "malformed manifest",
        execution=manifest)
    S.append([verdict], root)

    problems = A.audit_graph(root, S.load(S.graph_path(root)))
    assert any("backend v2 manifest is malformed" in problem
               for problem in problems)


def test_unavailable_historical_backend_is_readable_but_not_authority(
        tmp_path, capsys):
    root = str(tmp_path)
    S.append([
        {"ev": "model", "id": "M", "what": "origin",
         "characteristic": 0, "ring_vars": ["x"], "generators": ["x"]},
        {"ev": "claim", "id": "C", "model": "M", "kind": K.IDENTITY,
         "statement": "x vanishes", "lhs": "x", "rhs": "0",
         "ring_vars": ["x"], "identity_origin": K.DERIVED},
    ], root)
    graph = S.load(S.graph_path(root))
    artifact = _artifact()
    unavailable = replace(
        artifact,
        backend=replace(
            artifact.backend,
            binary_version="unavailable: TimeoutExpired"))
    A.persist(root, unavailable)
    manifest = _manifest(unavailable)
    verdict = V._verdict_event(
        graph, "claim", "C", "VERIFIED_DERIVED", "historical reduction",
        execution=manifest)
    S.append([verdict], root)

    encoded = verdict["backend"]
    assert P.decode_backend_provenance(encoded, current_only=False) is not None
    assert P.backend_provenance(encoded, current_only=False) is None
    report = A.audit_graph_report(root, S.load(S.graph_path(root)))
    assert report["problems"] == []
    assert len(report["legacy_unverifiable"]) == 1
    assert cli.main(["--root", root, "artifacts", "check"]) == 0
    output = capsys.readouterr().out
    assert "1 execution reference checked" in output
    assert "legacy-readable / legacy-unverifiable: 1 verdict" in output


def test_cli_reports_artifact_publication_failure_without_traceback(
        tmp_path, capsys, monkeypatch):
    def fail(**_kwargs):
        raise A.ArtifactError("disk refuses immutable publication")

    monkeypatch.setattr(V, "verify_all", fail)
    assert cli.main(["--root", str(tmp_path), "verify"]) == 2
    error = capsys.readouterr().err
    assert "ARTIFACT PERSISTENCE FAILED" in error
    assert "graph is unchanged" in error
