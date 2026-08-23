from pathlib import Path

from grandportage import dossier as D


ROOT = Path(__file__).resolve().parents[1]
DOSSIER = (ROOT / "fixtures" / "dossier" /
           "f2_75_125_publication" / "dossier.json")


def _profiles(dossier):
    return {item["id"]: item for item in dossier["profiles"]}


def test_final_f2_publication_state_fits_the_existing_dossier_schema():
    dossier = D.build_path(DOSSIER)
    profiles = _profiles(dossier)

    assert dossier["authority"] == "DERIVED_READ_MODEL_ONLY"
    assert dossier["graph_effect"] == "NONE"
    assert dossier["counts"] == {
        "claims": 6,
        "open_leaves": 8,
        "closed_leaves": 0,
        "priced_open_leaves": 8,
        "artifacts_present": 12,
        "artifacts_missing": 1,
        "profiles_ready": 0,
    }

    publication = profiles["F2_PUBLICATION"]
    exclusion = profiles["75125_EXCLUSION"]
    assert publication["status"] == "NOT_READY"
    assert exclusion["status"] == "NOT_READY"

    publication_blockers = [
        blocker
        for criterion in publication["criteria"]
        for blocker in criterion["blockers"]
    ]
    assert not any("JC.F2.ARTIFACT.QUICK_REPLAY replay" in item
                   for item in publication_blockers)
    assert not any("JC.F2.ARTIFACT.K5_FORMALIZATION replay" in item
                   for item in publication_blockers)
    assert "JC.F2.ARTIFACT.MANUSCRIPT is missing" not in publication_blockers
    assert "JC.F2.ARTIFACT.EXTERNAL_REVIEW is missing" in publication_blockers
    assert not any("price is" in blocker for blocker in publication_blockers)

    exclusion_blockers = [
        blocker
        for criterion in exclusion["criteria"]
        for blocker in criterion["blockers"]
    ]
    assert "JC.F2.LEAF.SOURCE_ATTACHMENT remains OPEN" in exclusion_blockers
    assert "JC.F2.LEAF.CARRIER_SURVIVORS remains OPEN" in exclusion_blockers
    assert "JC.F2.LEAF.GB31 remains OPEN" in exclusion_blockers


def test_final_f2_profile_names_match_the_publication_policy_split():
    dossier = D.build_path(DOSSIER)
    profiles = _profiles(dossier)

    assert profiles["F2_PUBLICATION"]["kind"] == "SHORT_OF_SUMMIT"
    assert profiles["75125_EXCLUSION"]["kind"] == "GOLD"
    assert dossier["campaign"]["summit_status"].startswith("OPEN")
