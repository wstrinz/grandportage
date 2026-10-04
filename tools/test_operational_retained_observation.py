"""Local integrity tests for the retained operational diagnostic adapter.

All copied fixtures and mutations stay under this workspace's F: tmp directory.
"""

import contextlib
import hashlib
import importlib.util
import json
import shutil
import tempfile
from pathlib import Path

import pytest

WORKSPACE = Path(__file__).resolve().parents[1]
ADAPTER = WORKSPACE / "tools" / "operational-retained-observation.py"
MANIFEST = "reports/PHASE-0A-OPERATIONAL-EVIDENCE-BINDINGS.json"
spec = importlib.util.spec_from_file_location("operational_retained_observation", ADAPTER)
adapter = importlib.util.module_from_spec(spec)
spec.loader.exec_module(adapter)


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


@contextlib.contextmanager
def scratch_bindings():
    manifest = json.loads((WORKSPACE / MANIFEST).read_text(encoding="utf-8"))
    paths = {MANIFEST}
    for entry in manifest["candidates"]:
        paths.add(entry["candidate_path"])
        paths.add("oracle/checkout/" + entry["primary_source"]["path"])
        paths.update(item["ref"].split("#", 1)[0]
                     for item in entry["evidence"])
    tmp_root = WORKSPACE / "tmp"
    tmp_root.mkdir(exist_ok=True)
    with tempfile.TemporaryDirectory(prefix="retained-adapter-", dir=tmp_root) as name:
        root = Path(name).resolve(strict=True)
        assert root.is_relative_to(tmp_root.resolve(strict=True))
        for relative in paths:
            target = root / relative
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(WORKSPACE / relative, target)
        yield root, manifest


def verified(root, candidate_id="GP-X370"):
    return adapter.verify(candidate_id, workspace=root, manifest=MANIFEST,
                          manifest_sha256=digest(root / MANIFEST))


def test_all_current_bindings_return_only_a_retained_null_verdict():
    with scratch_bindings() as (root, manifest):
        assert len(manifest["candidates"]) == 29
        assert sum(len(entry["evidence"]) for entry in manifest["candidates"]) == 50
        for entry in manifest["candidates"]:
            result = verified(root, entry["id"])
            assert result["diagnostic_status"] == "RETAINED_DIAGNOSTIC_BINDINGS_VERIFIED"
            assert result["observed_verdict"] is None
            assert result["oracle_called"] is False
            assert result["agreement"] is None
            assert result["evidence_refs_verified"] == len(entry["evidence"])


def test_changed_candidate_evidence_and_source_fail_closed():
    with scratch_bindings() as (root, manifest):
        entry = next(e for e in manifest["candidates"] if e["id"] == "GP-X370")
        candidate = root / entry["candidate_path"]
        evidence = root / entry["evidence"][0]["ref"].split("#", 1)[0]
        source = root / "oracle/checkout" / entry["primary_source"]["path"]
        for path, mutate in (
            (candidate, lambda raw: raw.replace(b'"GP-X370"', b'"GP-X370-tampered"', 1)),
            (evidence, lambda raw: raw + b" "),
            (source, lambda raw: raw + b"\n# changed scratch source\n"),
        ):
            original = path.read_bytes()
            changed = mutate(original)
            assert changed != original
            path.write_bytes(changed)
            try:
                with pytest.raises(adapter.BindingError):
                    verified(root)
            finally:
                path.write_bytes(original)
            assert verified(root)["observed_verdict"] is None


def test_altered_or_missing_manifest_bindings_fail_closed():
    with scratch_bindings() as (root, _manifest):
        path = root / MANIFEST
        original = path.read_bytes()
        pinned = digest(path)
        path.write_bytes(original + b" ")
        with pytest.raises(adapter.BindingError, match="manifest SHA-256 mismatch"):
            adapter.verify("GP-X370", workspace=root, manifest=MANIFEST,
                           manifest_sha256=pinned)
        path.write_bytes(original)

        changed = json.loads(original)
        entry = next(e for e in changed["candidates"] if e["id"] == "GP-X370")
        entry["evidence"].pop()
        path.write_text(json.dumps(changed), encoding="utf-8")
        with pytest.raises(adapter.BindingError, match="evidence binding list mismatch"):
            verified(root)

        changed = json.loads(original)
        entry = next(e for e in changed["candidates"] if e["id"] == "GP-X370")
        entry["evidence"][0].pop("pointer_canonical_sha256")
        path.write_text(json.dumps(changed), encoding="utf-8")
        with pytest.raises(adapter.BindingError, match="missing binding field"):
            verified(root)


def test_cli_failure_stays_null_and_never_claims_oracle_execution():
    import subprocess
    import sys

    with scratch_bindings() as (root, manifest):
        entry = next(e for e in manifest["candidates"] if e["id"] == "GP-X394")
        evidence = root / entry["evidence"][0]["ref"].split("#", 1)[0]
        evidence.write_bytes(evidence.read_bytes() + b" ")
        result = subprocess.run(
            [sys.executable, "-B", str(ADAPTER), "--workspace", str(root),
             "--candidate", "GP-X394", "--manifest-sha256",
             digest(root / MANIFEST)],
            capture_output=True, text=True, check=False)
        assert result.returncode == 2
        payload = json.loads(result.stdout)
        assert payload["diagnostic_status"] == "RETAINED_DIAGNOSTIC_BINDING_FAILED"
        assert payload["observed_verdict"] is None
        assert payload["oracle_called"] is False
        assert payload["agreement"] is None
