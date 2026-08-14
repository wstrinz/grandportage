import json
from pathlib import Path

from grandportage import cli
from grandportage import publication as P
from grandportage import release as R


ROOT = Path(__file__).resolve().parents[1]
SYNTHETIC = ROOT / "fixtures" / "release" / "synthetic" / "release.json"
JC = ROOT / "fixtures" / "release" / "jc_publication" / "release.json"


def test_jc_publication_projection_keeps_grades_scopes_and_qualifications():
    publication = R.build_path(JC)["publication"]
    claims = {item["id"]: item for item in publication["claims"]}

    assert publication["schema"] == "campaign-publication/v0"
    assert publication["authority"] == "DERIVED_READ_MODEL_ONLY"
    assert publication["graph_effect"] == "NONE"
    assert publication["counts"]["claims"] == 6
    assert publication["counts"]["proved_claims"] == 3
    assert publication["counts"]["conditional_claims"] == 3
    assert publication["counts"]["claims_release_covered"] == 6
    conditional = claims["JC.PORTRAIT.CONDITIONAL_COMPOSITION"]
    assert conditional["grade"] == "CONDITIONAL"
    assert conditional["scope_id"] == "JC.75_125.ACTUAL_PAIR"
    assert "JC.S2" in conditional["assumptions"]
    assert all(item["selected"] for item in conditional["evidence"])


def test_portrait_audit_is_dependency_complete_and_not_authority():
    publication = R.build_path(JC)["publication"]
    audit = P.render(publication, "PORTRAIT_AUDIT")

    assert "portrait dependency audit" in audit
    assert "does not upgrade any claim" in audit
    assert "JC.PORTRAIT.LOCAL_CONSUMER" in audit
    assert "JC.LOCAL.FINITE_ALGEBRA" in audit
    assert "matching finite-algebra bounds" in audit
    assert "JC.ARTIFACT.LOCAL_RECURRENCE" in audit
    assert "PASS" in audit
    assert audit.count("DERIVED_READ_MODEL_ONLY") == 1


def test_manuscript_tables_keep_residuals_retirements_and_blockers_distinct():
    publication = R.build_path(JC)["publication"]
    tables = P.render(publication, "MANUSCRIPT_TABLES")

    assert "generated editorial material, not a manuscript" in tables
    assert "JC.S2.DIRECT_CRT_PML" in tables
    assert "SIEGE" in tables
    assert "JC.S1_PRIME" in tables and "UNPRICED" in tables
    assert "JC.ARTIFACT.MANUSCRIPT" in tables
    assert "REPLAY_RESOURCE_NOT_AUDITED" in tables
    assert "REPLAY_DEBT" not in tables
    assert "## Replay and archival matrix" in tables


def test_publication_fingerprint_and_rendering_are_deterministic():
    first = R.build_path(SYNTHETIC)["publication"]
    second = R.build_path(SYNTHETIC)["publication"]
    assert first == second
    assert P.canonical_json(first) == P.canonical_json(second)
    assert P.render(first) == P.render(second)


def test_campaign_publication_cli_json_markdown_and_safe_output(tmp_path, capsys):
    code = cli.main(["campaign-publication", str(JC),
                     "--format", "json"])
    captured = capsys.readouterr()
    assert code == 0
    assert json.loads(captured.out)["schema"] == "campaign-publication/v0"

    output = tmp_path / "portrait.md"
    code = cli.main(["campaign-publication", str(JC),
                     "--document", "portrait-audit",
                     "--output", str(output)])
    captured = capsys.readouterr()
    assert code == 0
    assert captured.out.strip() == str(output.resolve())
    assert "JC.PORTRAIT.ORDER6_VERTEX" in output.read_text(encoding="utf-8")

    code = cli.main(["campaign-publication", str(JC),
                     "--output", str(output)])
    captured = capsys.readouterr()
    assert code == 2
    assert "derived output already exists" in captured.err
