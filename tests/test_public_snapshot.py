import importlib.util
import json
from pathlib import Path
import subprocess

import pytest


ROOT = Path(__file__).resolve().parents[1]
SCRIPT = ROOT / "scripts" / "public_snapshot.py"
MANIFEST = ROOT / "public-snapshot-v1.json"


def _load():
    spec = importlib.util.spec_from_file_location(
        "public_snapshot_test", SCRIPT)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def _candidate_paths():
    top = subprocess.run(
        ["git", "rev-parse", "--show-toplevel"], cwd=ROOT,
        capture_output=True, text=True, check=False)
    if top.returncode != 0 or Path(top.stdout.strip()).resolve() != ROOT:
        receipt_path = ROOT / "PUBLIC-SNAPSHOT-RECEIPT.json"
        if not receipt_path.is_file():
            raise AssertionError("snapshot has neither a local Git root nor a receipt")
        receipt = json.loads(receipt_path.read_text(encoding="utf-8"))
        return ([item["path"] for item in receipt["files"]] +
                ["PUBLIC-SNAPSHOT-RECEIPT.json"])
    completed = subprocess.run(
        ["git", "ls-files", "--cached", "--others", "--exclude-standard"],
        cwd=ROOT, capture_output=True, text=True, check=True)
    return [line for line in completed.stdout.splitlines() if line]


def test_every_current_path_has_exactly_one_public_boundary_classification():
    module = _load()
    manifest = module.load_manifest(MANIFEST)
    result = module.classify_paths(manifest, _candidate_paths())

    assert "README.md" in result["public"]
    receipt_path = ROOT / module.RECEIPT_PATH
    if receipt_path.is_file():
        receipt = json.loads(receipt_path.read_text(encoding="utf-8"))
        assert "HANDOFF.md" in receipt["private_paths"]
        assert "uv.lock" in manifest["private_paths"]
        assert not (ROOT / "uv.lock").exists()
        assert result["generated"] == [module.RECEIPT_PATH]
    else:
        assert "HANDOFF.md" in result["private"]
        assert "uv.lock" in manifest["private_paths"]
        if (ROOT / "uv.lock").exists():
            assert "uv.lock" in result["private"]
        assert not result["generated"]


def test_new_unclassified_path_fails_closed():
    module = _load()
    manifest = module.load_manifest(MANIFEST)

    with pytest.raises(module.PublicSnapshotError, match="CLS2"):
        module.classify_paths(manifest, _candidate_paths() + ["SECRETS.md"])


def test_public_and_private_overlap_is_refused():
    module = _load()
    manifest = module.load_manifest(MANIFEST)
    manifest["private_paths"].append("README.md")

    with pytest.raises(module.PublicSnapshotError, match="CLS1"):
        module.classify_paths(manifest, _candidate_paths())


def test_required_public_path_cannot_silently_disappear():
    module = _load()
    manifest = module.load_manifest(MANIFEST)
    paths = [path for path in _candidate_paths() if path != "LICENSE"]

    with pytest.raises(module.PublicSnapshotError, match="CLS3"):
        module.classify_paths(manifest, paths)


def test_receipt_is_deterministic_and_binds_every_public_byte():
    module = _load()
    manifest_payload = MANIFEST.read_bytes()
    classifications = {"public": ["a", "b"], "private": ["secret"],
                       "generated": []}
    blobs = {"b": b"second", "a": b"first"}
    first = module.build_receipt(
        "a" * 40, MANIFEST.name, manifest_payload, blobs, classifications)
    second = module.build_receipt(
        "a" * 40, MANIFEST.name, manifest_payload,
        dict(reversed(list(blobs.items()))), classifications)

    assert first == second
    assert first["counts"] == {
        "public_files": 2, "private_files": 1, "generated_files": 1}
    assert first["files"] == [
        {"path": "a", "sha256": module.digest_bytes(b"first")},
        {"path": "b", "sha256": module.digest_bytes(b"second")},
    ]


def test_materialization_requires_a_new_exact_target(tmp_path):
    module = _load()
    output = tmp_path / "snapshot"
    receipt = {"schema": module.RECEIPT_SCHEMA}
    module.materialize(output, {"nested/file.txt": b"payload"}, receipt)

    assert (output / "nested" / "file.txt").read_bytes() == b"payload"
    assert json.loads((output / module.RECEIPT_PATH).read_text(
        encoding="utf-8")) == receipt
    with pytest.raises(module.PublicSnapshotError, match="OUT1"):
        module.materialize(output, {}, receipt)
