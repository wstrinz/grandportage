import copy
import hashlib
import json
from pathlib import Path

import pytest

from grandportage import cli
from grandportage import dossier as D


ROOT = Path(__file__).resolve().parents[1]
SYNTHETIC = ROOT / "fixtures" / "dossier" / "synthetic" / "dossier.json"
SYNTHETIC_ROOT = SYNTHETIC.parent


def _load(path=SYNTHETIC):
    return json.loads(path.read_text(encoding="utf-8"))


def _profiles(dossier):
    return {item["id"]: item for item in dossier["profiles"]}


def _digest(path):
    return hashlib.sha256(path.read_bytes().replace(b"\r\n", b"\n")).hexdigest()


def test_synthetic_dossier_compiles_deterministically_and_prices_open_work():
    first = D.build_path(SYNTHETIC)
    second = D.build_path(SYNTHETIC)
    profiles = _profiles(first)

    assert D.canonical_json(first) == D.canonical_json(second)
    assert first["authority"] == "DERIVED_READ_MODEL_ONLY"
    assert first["graph_effect"] == "NONE"
    assert first["source"]["audit"]["status"] == "UNCHECKED"
    assert first["counts"] == {
        "claims": 1,
        "open_leaves": 1,
        "closed_leaves": 1,
        "priced_open_leaves": 1,
        "artifacts_present": 1,
        "artifacts_missing": 0,
        "profiles_ready": 1,
    }
    assert profiles["SYNTHETIC.PUBLICATION_FLAG"]["status"] == "READY"
    assert profiles["SYNTHETIC.GOLD_FLAG"]["status"] == "NOT_READY"
    assert profiles["SYNTHETIC.GOLD_FLAG"]["criteria"][0]["blockers"] == [
        "SYNTHETIC.LEAF.B remains OPEN"
    ]


def test_source_audit_distinguishes_clean_dirty_and_stale(monkeypatch, tmp_path):
    value = _load()
    value["source"]["expected_commit"] = "abcdef0"
    (tmp_path / "authority.md").write_bytes(
        (SYNTHETIC_ROOT / "authority.md").read_bytes())
    (tmp_path / "proof.txt").write_bytes(
        (SYNTHETIC_ROOT / "proof.txt").read_bytes())

    def clean_git(_root, *args):
        if args[0] == "rev-parse":
            return "abcdef0123456789", None
        return "", None

    monkeypatch.setattr(D, "_git", clean_git)
    clean = D.build(value, source_root=tmp_path)
    assert clean["source"]["audit"]["status"] == "CURRENT_CLEAN"

    def dirty_git(_root, *args):
        if args[0] == "rev-parse":
            return "abcdef0123456789", None
        return " M authority.md", None

    monkeypatch.setattr(D, "_git", dirty_git)
    dirty = D.build(value, source_root=tmp_path)
    assert dirty["source"]["audit"]["status"] == "CURRENT_DIRTY"
    assert dirty["source"]["audit"]["dirty_paths"] == [" M authority.md"]

    (tmp_path / "authority.md").write_text("drift\n", encoding="utf-8")
    stale = D.build(value, source_root=tmp_path)
    assert stale["source"]["audit"]["status"] == "STALE"
    assert "SYNTHETIC.AUTHORITY digest changed" in stale["source"]["audit"][
        "problems"]


def test_source_freshness_is_a_fail_closed_profile_criterion(monkeypatch):
    value = _load()
    value["profiles"][0]["criteria"].append({
        "id": "SYNTHETIC.CRITERION.FRESH",
        "kind": "SOURCE_FRESH",
        "description": "The source is clean and current.",
        "allowed_statuses": ["CURRENT_CLEAN"],
    })
    dossier = D.build(value)
    profile = _profiles(dossier)["SYNTHETIC.PUBLICATION_FLAG"]
    assert profile["status"] == "NOT_READY"
    fresh = next(item for item in profile["criteria"]
                 if item["id"] == "SYNTHETIC.CRITERION.FRESH")
    assert fresh["blockers"] == [
        "source is UNCHECKED; accepted: CURRENT_CLEAN"
    ]


def test_reconnaissance_cannot_support_a_theorem_claim():
    value = _load()
    artifact = value["artifacts"][0]
    artifact["grade"] = "RECONNAISSANCE"
    artifact["role"] = "RECONNAISSANCE"
    with pytest.raises(D.DossierError, match="launders reconnaissance"):
        D.build(value)


def test_missing_artifact_cannot_support_a_portrait_or_leaf():
    value = _load()
    artifact = value["artifacts"][0]
    artifact["availability"] = "MISSING"
    artifact.pop("path")
    artifact.pop("digest_algo")
    artifact.pop("sha256")
    artifact["replay"] = {"status": "NOT_RUN", "command": None,
                          "receipt": None}
    with pytest.raises(D.DossierError, match="names missing evidence"):
        D.build(value)


@pytest.mark.parametrize("field", ["next_accepted_object", "resume_condition"])
def test_open_leaf_requires_next_object_and_resume_condition(field):
    value = _load()
    value["leaves"][1][field] = None
    with pytest.raises(D.DossierError, match="open leaf needs"):
        D.build(value)


def test_retired_representation_requires_an_exact_reason():
    value = _load()
    value["leaves"][1]["retired_representations"][0]["reason"] = ""
    with pytest.raises(D.DossierError, match="retired reason"):
        D.build(value)

    value = _load()
    value["leaves"][1]["retired_representations"][0]["evidence_ids"] = []
    with pytest.raises(D.DossierError, match="must not be empty"):
        D.build(value)


def test_duplicate_ids_and_absent_profile_records_fail_closed():
    value = _load()
    value["leaves"].append(copy.deepcopy(value["leaves"][0]))
    with pytest.raises(D.DossierError, match="leaf ids must be unique"):
        D.build(value)

    value = _load()
    value["profiles"][0]["criteria"][0]["claim_ids"] = ["ABSENT.CLAIM"]
    with pytest.raises(D.DossierError, match="names absent records"):
        D.build(value)


def test_missing_artifact_cannot_be_self_declared_as_replayed():
    value = _load()
    artifact = value["artifacts"][0]
    artifact["availability"] = "MISSING"
    artifact.pop("path")
    artifact.pop("digest_algo")
    artifact.pop("sha256")
    with pytest.raises(D.DossierError, match="missing and cannot have"):
        D.build(value)


def test_generator_contract_is_only_for_missing_publication_artifacts():
    value = _load()
    value["artifacts"][0]["generated_by"] = "PORTRAIT_AUDIT"
    with pytest.raises(D.DossierError, match="present and cannot declare"):
        D.build(value)

    value = _load()
    artifact = value["artifacts"][0]
    artifact["availability"] = "MISSING"
    artifact["generated_by"] = "PORTRAIT_AUDIT"
    artifact["replay"] = {"status": "NOT_RUN", "command": None,
                          "receipt": None}
    artifact.pop("path")
    artifact.pop("digest_algo")
    artifact.pop("sha256")
    with pytest.raises(D.DossierError, match="requires a publication artifact"):
        D.build(value)


def test_authority_digest_algorithm_and_paths_fail_closed():
    value = _load()
    value["authority"] = "MATHEMATICAL_AUTHORITY"
    with pytest.raises(D.DossierError, match="widened authority"):
        D.build(value)

    value = _load()
    value["source"]["canonical_sources"][0]["digest_algo"] = "sha256-raw"
    with pytest.raises(D.DossierError, match="must use sha256-lf-normalized"):
        D.build(value)

    value = _load()
    value["artifacts"][0]["path"] = "../proof.txt"
    with pytest.raises(D.DossierError, match="must not escape"):
        D.build(value)

    value = _load()
    value["artifacts"][0]["path"] = "authority.md"
    with pytest.raises(D.DossierError, match="conflicting expected digests"):
        D.build(value)


def test_cli_human_and_json_surfaces_share_the_same_fingerprint(capsys):
    code = cli.main(["campaign-dossier", str(SYNTHETIC), "--format", "human"])
    captured = capsys.readouterr()
    assert code == 0
    expected = D.build_path(SYNTHETIC)
    assert expected["history"]["observation_fingerprint"] in captured.out
    assert "Synthetic publication flag" in captured.out
    assert "DERIVED_READ_MODEL_ONLY" in captured.out

    code = cli.main(["campaign-dossier", str(SYNTHETIC)])
    captured = capsys.readouterr()
    assert code == 0
    assert json.loads(captured.out) == expected


def test_cli_refusal_is_nonzero_and_explanatory(tmp_path, capsys):
    value = _load()
    value["graph_effect"] = "WRITE"
    path = tmp_path / "bad.json"
    path.write_text(json.dumps(value), encoding="utf-8")
    code = cli.main(["campaign-dossier", str(path)])
    captured = capsys.readouterr()
    assert code == 2
    assert "campaign-dossier refused" in captured.err
    assert "widened authority" in captured.err


def test_fixture_digests_are_lf_normalized():
    value = _load()
    assert value["source"]["canonical_sources"][0]["sha256"] == _digest(
        SYNTHETIC_ROOT / "authority.md")
    assert value["artifacts"][0]["sha256"] == _digest(
        SYNTHETIC_ROOT / "proof.txt")
