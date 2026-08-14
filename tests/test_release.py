import copy
import json
from pathlib import Path
import subprocess
import sys

import pytest

from grandportage import cli
from grandportage import dossier as D
from grandportage import release as R


ROOT = Path(__file__).resolve().parents[1]
SYNTHETIC = ROOT / "fixtures" / "release" / "synthetic" / "release.json"
SYNTHETIC_SOURCE = ROOT / "fixtures" / "dossier" / "synthetic"
JC = ROOT / "fixtures" / "release" / "jc_publication" / "release.json"


def _load(path=SYNTHETIC):
    return json.loads(path.read_text(encoding="utf-8"))


def _clean_git(_root, *args):
    if args[0] == "rev-parse":
        return "0000000123456789", None
    return "", None


def test_synthetic_release_compiles_deterministically_and_fails_closed_unchecked():
    first = R.build_path(SYNTHETIC)
    second = R.build_path(SYNTHETIC)

    assert R.canonical_json(first) == R.canonical_json(second)
    assert first["authority"] == "DERIVED_READ_MODEL_ONLY"
    assert first["graph_effect"] == "NONE"
    assert first["profile"]["status"] == "READY"
    assert first["coverage"]["required_ids"] == [
        "SYNTHETIC.AUTHORITY", "SYNTHETIC.PROOF"]
    assert first["coverage"]["missing_ids"] == []
    assert first["source_audit"]["status"] == "UNCHECKED"
    assert not first["materializable"]
    assert {item["code"] for item in first["blockers"]} == {
        "ITEM_NOT_AUDITED", "REPLAY_RESOURCE_NOT_AUDITED",
        "SOURCE_NOT_CLEAN"}
    assert not first["replay_materializable"]


def test_clean_synthetic_release_materializes_atomically(monkeypatch, tmp_path):
    monkeypatch.setattr(D, "_git", _clean_git)
    release = R.build_path(SYNTHETIC, source_root=SYNTHETIC_SOURCE)
    assert release["source_audit"]["status"] == "CURRENT_CLEAN"
    assert release["materializable"]

    output = tmp_path / "archive"
    report = R.materialize(release, SYNTHETIC_SOURCE, output)
    assert report["files"] == 7
    assert report["mode"] == "FULL_RELEASE"
    assert (output / "authority" / "authority.md").is_file()
    assert (output / "receipts" / "proof.txt").is_file()
    assert (output / "replay" / "verify_synthetic.py").is_file()
    assert (output / "replay" / "synthetic-receipt.json").is_file()
    assert (output / "REPLAY.md").read_text(encoding="utf-8").count(
        "python verify_synthetic.py") == 1
    materialized = json.loads((output / "manifest.json").read_text(
        encoding="utf-8"))
    assert materialized["history"] == release["history"]
    sums = (output / "SHA256SUMS").read_text(encoding="utf-8")
    assert "authority/authority.md" in sums
    assert "receipts/proof.txt" in sums
    assert "replay/verify_synthetic.py" in sums
    assert "replay/synthetic-receipt.json" in sums
    assert "REPLAY.md" in sums
    replay = subprocess.run(
        [sys.executable, "verify_synthetic.py"], cwd=output / "replay",
        text=True, capture_output=True, check=False)
    assert replay.returncode == 0, replay.stderr
    assert "passed" in replay.stdout

    with pytest.raises(R.ReleaseError, match="already exists"):
        R.materialize(release, SYNTHETIC_SOURCE, output)


def test_clean_plan_fingerprint_is_independent_of_checkout_path(monkeypatch,
                                                                tmp_path):
    monkeypatch.setattr(D, "_git", _clean_git)
    copy_root = tmp_path / "another-checkout"
    copy_root.mkdir()
    for name in ("authority.md", "proof.txt", "verify_synthetic.py",
                 "synthetic-receipt.json"):
        (copy_root / name).write_bytes((SYNTHETIC_SOURCE / name).read_bytes())

    first = R.build_path(SYNTHETIC, source_root=SYNTHETIC_SOURCE)
    second = R.build_path(SYNTHETIC, source_root=copy_root)
    assert first["history"]["plan_fingerprint"] == second["history"][
        "plan_fingerprint"]
    assert first == second


def test_materializer_rechecks_payload_after_planning(monkeypatch, tmp_path):
    monkeypatch.setattr(D, "_git", _clean_git)
    source = tmp_path / "source"
    source.mkdir()
    for name in ("authority.md", "proof.txt", "verify_synthetic.py",
                 "synthetic-receipt.json"):
        (source / name).write_bytes((SYNTHETIC_SOURCE / name).read_bytes())
    release = R.build_path(SYNTHETIC, source_root=source)
    (source / "proof.txt").write_text("changed\n", encoding="utf-8")

    output = tmp_path / "archive"
    with pytest.raises(R.ReleaseError, match="changed after planning"):
        R.materialize(release, source, output)
    assert not output.exists()
    assert not list(tmp_path.glob(".gp-release-*"))


def test_jc_draft_generates_audit_and_manifest_but_exposes_remaining_debt():
    release = R.build_path(JC)
    blockers = release["blockers"]
    profile_blockers = [item["detail"] for item in blockers
                        if item["code"] == "PROFILE_BLOCKED"]

    assert release["provides_artifact_ids"] == [
        "JC.ARTIFACT.PORTRAIT_AUDIT", "JC.ARTIFACT.RELEASE_MANIFEST"]
    assert release["coverage"]["missing_ids"] == [
        "JC.ARTIFACT.MANUSCRIPT"]
    assert release["counts"]["required"] == 17
    assert release["counts"]["selected"] == 16
    assert release["counts"]["replay_debt"] == 0
    assert release["counts"]["replay_resources"] == 152
    assert not any("RELEASE_MANIFEST is missing" in item
                   for item in profile_blockers)
    assert not any("PORTRAIT_AUDIT is missing" in item
                   for item in profile_blockers)
    release_criterion = next(
        item for item in release["profile"]["criteria"]
        if item["id"] == "JC.PUBLICATION.RELEASE_BUNDLE")
    assert release_criterion["passed"]
    audit_criterion = next(
        item for item in release["profile"]["criteria"]
        if item["id"] == "JC.PUBLICATION.PORTRAIT_AUDIT")
    assert audit_criterion["passed"]
    generated = {item["generator"]: item
                 for item in release["generated_artifacts"]}
    assert generated["PORTRAIT_AUDIT"]["sha256"].startswith("sha256:")
    assert generated["RELEASE_MANIFEST"]["sha256"] is None
    assert not release["materializable"]


def test_release_binding_paths_and_portable_archive_paths_fail_closed():
    value = _load()
    value["dossier"]["sha256"] = "0" * 64
    with pytest.raises(R.ReleaseError, match="digest changed"):
        R.build(value, manifest_path=SYNTHETIC)

    value = _load()
    value["items"][1]["release_path"] = "authority/AUTHORITY.md"
    with pytest.raises(R.ReleaseError, match="portably unique"):
        R.build(value, manifest_path=SYNTHETIC)

    value = _load()
    value["items"][0]["release_path"] = "../authority.md"
    with pytest.raises(R.ReleaseError, match="must not escape"):
        R.build(value, manifest_path=SYNTHETIC)

    value = _load()
    value["items"][0]["release_path"] = "manifest.json"
    with pytest.raises(R.ReleaseError, match="reserved"):
        R.build(value, manifest_path=SYNTHETIC)


def test_license_and_replay_lane_debt_are_explicit(monkeypatch):
    monkeypatch.setattr(D, "_git", _clean_git)
    value = _load()
    value["items"][1]["license_status"] = "REVIEW"
    value["replay_lanes"] = []
    value["replay_resources"] = []
    release = R.build(value, manifest_path=SYNTHETIC,
                      source_root=SYNTHETIC_SOURCE)
    assert {item["code"] for item in release["blockers"]} == {
        "LICENSE_DEBT", "REPLAY_DEBT"}
    assert not release["materializable"]


def test_replay_lane_cannot_name_an_unselected_payload():
    value = _load()
    value["items"] = value["items"][:1]
    with pytest.raises(R.ReleaseError, match="unselected artifact payloads"):
        R.build(value, manifest_path=SYNTHETIC)


def test_replay_resources_fail_closed_on_digest_role_path_and_usage():
    value = _load()
    value["replay_resources"][0]["sha256"] = "0" * 64
    with pytest.raises(R.ReleaseError, match="embedded_text digest changed|digest"):
        # A source resource reaches its digest check during source audit; make
        # this one embedded so the manifest itself must prove the bytes.
        value["replay_resources"][0].pop("source_path")
        value["replay_resources"][0]["embedded_text"] = "checker\n"
        R.build(value, manifest_path=SYNTHETIC)

    value = _load()
    value["replay_resources"][1]["role"] = "CHECKER"
    with pytest.raises(R.ReleaseError, match="receipt_ids name non-receipts"):
        R.build(value, manifest_path=SYNTHETIC)

    value = _load()
    value["replay_resources"][0]["release_path"] = "other/checker.py"
    with pytest.raises(R.ReleaseError, match="resources must live under"):
        R.build(value, manifest_path=SYNTHETIC)

    value = _load()
    value["replay_resources"][0]["release_path"] = "authority/authority.md"
    with pytest.raises(R.ReleaseError, match="collide"):
        R.build(value, manifest_path=SYNTHETIC)

    value = _load()
    value["replay_lanes"][0]["resource_ids"] = [
        "SYNTHETIC.REPLAY.RECEIPT"]
    with pytest.raises(R.ReleaseError, match="replay resources are unused"):
        R.build(value, manifest_path=SYNTHETIC)


def test_replay_kit_can_close_before_publication_profile(monkeypatch, tmp_path):
    monkeypatch.setattr(D, "_git", _clean_git)
    dossier_value = json.loads(
        (SYNTHETIC_SOURCE / "dossier.json").read_text(encoding="utf-8"))
    dossier_value["artifacts"].append({
        "id": "SYNTHETIC.MANUSCRIPT",
        "availability": "MISSING",
        "role": "PUBLICATION",
        "grade": "ADVISORY",
        "description": "Publication manuscript not yet written.",
        "public_disposition": "INCLUDE",
        "replay": {"status": "NOT_APPLICABLE", "command": None,
                   "receipt": None},
    })
    dossier_value["profiles"][0]["criteria"].append({
        "id": "SYNTHETIC.CRITERION.MANUSCRIPT",
        "kind": "ARTIFACTS_PRESENT",
        "description": "The manuscript exists.",
        "artifact_ids": ["SYNTHETIC.MANUSCRIPT"],
    })
    dossier_path = tmp_path / "dossier.json"
    dossier_path.write_text(json.dumps(dossier_value), encoding="utf-8")

    release_value = _load()
    release_value["root"] = "."
    release_value["dossier"]["path"] = "dossier.json"
    release_value["dossier"]["sha256"] = R._digest(dossier_path)
    release_path = tmp_path / "release.json"
    release_path.write_text(json.dumps(release_value), encoding="utf-8")

    release = R.build_path(release_path, source_root=SYNTHETIC_SOURCE)
    assert not release["materializable"]
    assert release["replay_materializable"]
    assert {item["code"] for item in release["blockers"]} >= {
        "COVERAGE_MISSING", "PROFILE_BLOCKED"}
    assert release["replay_blockers"] == []

    output = tmp_path / "replay-kit"
    report = R.materialize_replay_kit(
        release, SYNTHETIC_SOURCE, output)
    assert report["mode"] == "REPLAY_KIT"
    replay = subprocess.run(
        [sys.executable, "verify_synthetic.py"], cwd=output / "replay",
        text=True, capture_output=True, check=False)
    assert replay.returncode == 0, replay.stderr


def test_replay_kit_rechecks_resource_after_planning(monkeypatch, tmp_path):
    monkeypatch.setattr(D, "_git", _clean_git)
    source = tmp_path / "source"
    source.mkdir()
    for name in ("authority.md", "proof.txt", "verify_synthetic.py",
                 "synthetic-receipt.json"):
        (source / name).write_bytes((SYNTHETIC_SOURCE / name).read_bytes())
    release = R.build_path(SYNTHETIC, source_root=source)
    (source / "verify_synthetic.py").write_text(
        "raise SystemExit('tampered')\n", encoding="utf-8")

    output = tmp_path / "replay-kit"
    with pytest.raises(R.ReleaseError, match="changed after planning"):
        R.materialize_replay_kit(release, source, output)
    assert not output.exists()


def test_generated_artifact_must_match_the_dossier_contract():
    value = json.loads(JC.read_text(encoding="utf-8"))
    value["generated_artifacts"][0]["generator"] = "MANUSCRIPT_TABLES"
    with pytest.raises(R.ReleaseError, match="does not permit"):
        R.build(value, manifest_path=JC)

    value = _load()
    value["provides_artifact_ids"] = []
    with pytest.raises(R.ReleaseError, match="replaced by bound"):
        R.build(value, manifest_path=SYNTHETIC)


def test_generated_artifact_license_debt_blocks_materialization():
    value = json.loads(JC.read_text(encoding="utf-8"))
    value["generated_artifacts"][0]["license_status"] = "REVIEW"
    release = R.build(value, manifest_path=JC)
    assert any(item["code"] == "LICENSE_DEBT" and
               item.get("record_id") == "JC.ARTIFACT.PORTRAIT_AUDIT"
               for item in release["blockers"])
    assert not release["materializable"]


def test_generated_portrait_audit_is_checksumned_in_a_ready_archive(
        monkeypatch, tmp_path):
    monkeypatch.setattr(D, "_git", _clean_git)
    dossier_value = json.loads(
        (SYNTHETIC_SOURCE / "dossier.json").read_text(encoding="utf-8"))
    dossier_value["artifacts"].append({
        "id": "SYNTHETIC.PORTRAIT_AUDIT",
        "availability": "MISSING",
        "role": "PUBLICATION",
        "grade": "ADVISORY",
        "description": "Generated portrait dependency audit.",
        "public_disposition": "INCLUDE",
        "generated_by": "PORTRAIT_AUDIT",
        "replay": {"status": "NOT_APPLICABLE", "command": None,
                   "receipt": None},
    })
    dossier_value["profiles"][0]["criteria"].append({
        "id": "SYNTHETIC.CRITERION.AUDIT",
        "kind": "ARTIFACTS_PRESENT",
        "description": "The portrait audit is generated.",
        "artifact_ids": ["SYNTHETIC.PORTRAIT_AUDIT"],
    })
    dossier_path = tmp_path / "dossier.json"
    dossier_path.write_text(json.dumps(dossier_value), encoding="utf-8")

    release_value = _load()
    release_value["root"] = "."
    release_value["dossier"]["path"] = "dossier.json"
    release_value["dossier"]["sha256"] = R._digest(dossier_path)
    release_value["generated_artifacts"] = [{
        "id": "SYNTHETIC.PORTRAIT_AUDIT",
        "generator": "PORTRAIT_AUDIT",
        "release_path": "reports/PORTRAIT-AUDIT.md",
        "license_status": "CLEAR",
        "provenance": "Generated from the synthetic dossier.",
    }]
    release_path = tmp_path / "release.json"
    release_path.write_text(json.dumps(release_value), encoding="utf-8")
    release = R.build_path(release_path, source_root=SYNTHETIC_SOURCE)
    assert release["materializable"]

    output = tmp_path / "archive"
    R.materialize(release, SYNTHETIC_SOURCE, output)
    audit = output / "reports" / "PORTRAIT-AUDIT.md"
    assert "SYNTHETIC.CLAIM.A" in audit.read_text(encoding="utf-8")
    assert "reports/PORTRAIT-AUDIT.md" in (
        output / "SHA256SUMS").read_text(encoding="utf-8")


def test_cli_readiness_exit_and_materialization(monkeypatch, tmp_path, capsys):
    code = cli.main(["campaign-release", str(SYNTHETIC),
                     "--format", "human", "--require-ready"])
    captured = capsys.readouterr()
    assert code == 1
    assert "materializable: `NO`" in captured.out

    monkeypatch.setattr(D, "_git", _clean_git)
    output = tmp_path / "release"
    code = cli.main(["campaign-release", str(SYNTHETIC),
                     "--source-root", str(SYNTHETIC_SOURCE),
                     "--output-dir", str(output), "--require-ready"])
    captured = capsys.readouterr()
    assert code == 0
    assert json.loads(captured.out)["output_dir"] == str(output.resolve())
    assert (output / "manifest.json").is_file()


def test_cli_materialization_requires_source_root(tmp_path, capsys):
    code = cli.main(["campaign-release", str(SYNTHETIC),
                     "--output-dir", str(tmp_path / "release")])
    captured = capsys.readouterr()
    assert code == 2
    assert "materialization requires --source-root" in captured.err


def test_cli_replay_kit_materializes_and_uses_replay_readiness(
        monkeypatch, tmp_path, capsys):
    monkeypatch.setattr(D, "_git", _clean_git)
    output = tmp_path / "replay-kit"
    code = cli.main([
        "campaign-release", str(SYNTHETIC),
        "--source-root", str(SYNTHETIC_SOURCE),
        "--replay-kit-dir", str(output), "--require-ready",
    ])
    captured = capsys.readouterr()
    assert code == 0
    report = json.loads(captured.out)
    assert report["mode"] == "REPLAY_KIT"
    assert report["files"] == 7
    assert (output / "replay" / "verify_synthetic.py").is_file()
