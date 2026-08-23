import json
from pathlib import Path

from grandportage import cli
from grandportage import publication as P
from grandportage import release as R


ROOT = Path(__file__).resolve().parents[1]
SYNTHETIC = ROOT / "fixtures" / "release" / "synthetic" / "release.json"


def test_neutral_publication_keeps_grades_scopes_and_release_coverage():
    publication = R.build_path(SYNTHETIC)["publication"]
    claim = publication["claims"][0]
    assert publication["schema"] == "campaign-publication/v0"
    assert publication["authority"] == "DERIVED_READ_MODEL_ONLY"
    assert publication["graph_effect"] == "NONE"
    assert publication["counts"]["claims"] == 1
    assert publication["counts"]["proved_claims"] == 1
    assert publication["counts"]["conditional_claims"] == 0
    assert claim["id"] == "SYNTHETIC.CLAIM.A"
    assert claim["grade"] == "PROVED"
    assert claim["scope_id"] == "SYNTHETIC.SCOPE.A"
    assert claim["release_covered"] is True


def test_neutral_portrait_audit_is_dependency_complete_and_not_authority():
    publication = R.build_path(SYNTHETIC)["publication"]
    audit = P.render(publication, "PORTRAIT_AUDIT")
    assert "portrait dependency audit" in audit
    assert "does not upgrade any claim" in audit
    assert "SYNTHETIC.CLAIM.A" in audit
    assert "SYNTHETIC.PROOF" in audit
    assert "PASS" in audit
    assert audit.count("DERIVED_READ_MODEL_ONLY") == 1


def test_neutral_manuscript_tables_keep_residuals_and_blockers_distinct():
    publication = R.build_path(SYNTHETIC)["publication"]
    tables = P.render(publication, "MANUSCRIPT_TABLES")
    assert "generated editorial material, not a manuscript" in tables
    assert "SYNTHETIC.LEAF.B" in tables and "OPEN / PRICED" in tables
    assert "SYNTHETIC.LEAF.B.DENSE_MATRIX" in tables
    assert "REPLAY_RESOURCE_NOT_AUDITED" in tables
    assert "## Replay and archival matrix" in tables


def test_publication_fingerprint_and_rendering_are_deterministic():
    first = R.build_path(SYNTHETIC)["publication"]
    second = R.build_path(SYNTHETIC)["publication"]
    assert first == second
    assert P.canonical_json(first) == P.canonical_json(second)
    assert P.render(first) == P.render(second)


def test_campaign_publication_cli_json_markdown_and_safe_output(tmp_path, capsys):
    assert cli.main(["campaign-publication", str(SYNTHETIC),
                     "--format", "json"]) == 0
    assert json.loads(capsys.readouterr().out)["schema"] == (
        "campaign-publication/v0")

    output = tmp_path / "portrait.md"
    assert cli.main(["campaign-publication", str(SYNTHETIC),
                     "--document", "portrait-audit",
                     "--output", str(output)]) == 0
    assert capsys.readouterr().out.strip() == str(output.resolve())
    assert "SYNTHETIC.CLAIM.A" in output.read_text(encoding="utf-8")

    assert cli.main(["campaign-publication", str(SYNTHETIC),
                     "--output", str(output)]) == 2
    assert "derived output already exists" in capsys.readouterr().err
