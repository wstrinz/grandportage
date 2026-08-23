from pathlib import Path
import hashlib
import os
import subprocess

from grandportage import dossier as D
from experiments.f2_75_125_publication import adapter as A


ROOT = Path(__file__).resolve().parents[1]
DOSSIER = (ROOT / "fixtures" / "dossier" /
           "f2_75_125_publication" / "dossier.json")


def _rows():
    supports = [
        "a*P5*b*P4", "a*P5*b*u7", "a*P5*P4*u7",
        "a*b*P4*u7", "P5*b*P4*u7", "a*P5*b*P4*u7",
    ]
    rows = [{"support": "closed-%02d" % index,
             "verdict": "closed-exact", "custody_class": "portable-exact",
             "artifact": "", "checker": ""}
            for index in range(24)]
    rows.extend([
        {"support": "a*P5", "verdict": "closed-exact",
         "custody_class": "digest-backed-historical",
         "artifact": "d2_plane_72_108/pair.json",
         "checker": "d2_plane_72_108/check_pair.py"},
        {"support": "a*P4", "verdict": "closed-exact",
         "custody_class": "digest-backed-historical",
         "artifact": "d2_plane_72_108/pair.json",
         "checker": "d2_plane_72_108/check_pair.py"},
    ])
    rows.extend({"support": support, "verdict": "open",
                 "custody_class": "open", "artifact": "", "checker": ""}
                for support in supports)
    return rows


def _manifest(gates=True):
    return {
        "overall_theorem": "OPEN",
        "gate_b": "26/32",
        "release_gates": {"review": gates},
    }


def _findings(report):
    return {item["id"]: item for item in report["findings"]}


def test_audit_distinguishes_math_consistency_from_release_debt():
    dossier = D.build_path(DOSSIER)
    report = A.analyze(
        dossier=dossier, manifest=_manifest(False), gate_b_rows=_rows(),
        export_paths=set(),
        canonical_paths=set(A.CANONICAL_CHECKER_CANDIDATES.values()))
    findings = _findings(report)

    assert findings["PORTRAIT.PROFILE_SPLIT"]["status"] == "PASS"
    assert findings["THEOREM.OPEN_CONSISTENCY"]["status"] == "PASS"
    assert findings["GATE_B.CENSUS"]["status"] == "PASS"
    assert findings["GATE_B.OPEN_TOPOLOGY"]["status"] == "PASS"
    assert findings["DOSSIER.PUBLICATION_PROFILE"]["status"] == "BLOCKER"
    assert findings["REPLAY.ADVERTISED_PAYLOADS"]["status"] == "BLOCKER"
    packaging = findings["REPLAY.CANONICAL_PACKAGING"]
    assert packaging["status"] == "OPPORTUNITY"
    assert len(packaging["candidates"]) == 10
    assert packaging["unresolved"] == ["proofs/A_reduction_to_F2/check.py"]
    assert findings["RELEASE.CHECKSUMS"]["status"] == "BLOCKER"
    assert findings["PUBLICATION.RELEASE_GATES"]["status"] == "BLOCKER"
    assert report["authority"] == "DERIVED_READ_MODEL_ONLY"
    assert report["graph_effect"] == "NONE"


def test_audit_can_report_positive_custody_evidence_without_promoting_it():
    dossier = D.build_path(DOSSIER)
    paths = (set(A.ADVERTISED_CHECKERS) | {"SHA256SUMS"} |
             A.FORMALIZATION_REQUIRED)
    canonical = ({"d2_plane_72_108/pair.json",
                  "d2_plane_72_108/check_pair.py"} |
                 set(A.CANONICAL_CHECKER_CANDIDATES.values()))
    report = A.analyze(dossier=dossier, manifest=_manifest(True),
                       gate_b_rows=_rows(), export_paths=paths,
                       canonical_paths=canonical)
    findings = _findings(report)

    assert findings["REPLAY.ADVERTISED_PAYLOADS"]["status"] == "PASS"
    assert findings["RELEASE.CHECKSUMS"]["status"] == "PASS"
    opportunity = findings["GATE_B.PORTABILITY_REVIEW"]
    assert opportunity["status"] == "OPPORTUNITY"
    assert opportunity["candidates"] == ["a*P5", "a*P4"]
    assert findings["DOSSIER.PUBLICATION_PROFILE"]["status"] == "BLOCKER"
    assert report["counts"]["opportunity"] == 1
    assert findings["FORMALIZATION.STANDALONE"]["status"] == "PASS"


def test_partial_formalization_package_fails_closed():
    dossier = D.build_path(DOSSIER)
    report = A.analyze(
        dossier=dossier, manifest=_manifest(True), gate_b_rows=_rows(),
        export_paths={"formalization/Challenge.lean"})
    formal = _findings(report)["FORMALIZATION.STANDALONE"]

    assert formal["status"] == "BLOCKER"
    assert formal["missing"] == sorted(
        A.FORMALIZATION_REQUIRED - {"formalization/Challenge.lean"})


def test_formalization_declaration_and_scope_drift_fails_closed():
    dossier = D.build_path(DOSSIER)
    formalization = {
        "comparator": {
            "theorem_names": ["N.expected_theorem"],
            "definition_names": ["N.expected_definition"],
            "permitted_axioms": ["Classical.choice"],
        },
        "challenge": "def expected_definition := 0\n"
                     "theorem expected_theorem : True := by sorry\n",
        "solution": "def expected_definition := 0\n"
                    "theorem renamed_theorem : True := by trivial\n",
        "metadata": "Classical.choice; no global scope boundary",
    }
    report = A.analyze(
        dossier=dossier, manifest=_manifest(True), gate_b_rows=_rows(),
        export_paths=A.FORMALIZATION_REQUIRED, formalization=formalization)
    binding = _findings(report)["FORMALIZATION.DECLARATION_BINDING"]

    assert binding["status"] == "BLOCKER"
    assert not binding["declarations_match"]
    assert binding["deliberate_challenge_hole"]
    assert binding["solution_has_no_sorry"]
    assert not binding["scope_nonclaims_present"]


def test_formalization_flags_broad_tactic_import_as_replay_debt():
    dossier = D.build_path(DOSSIER)
    formalization = {
        "comparator": {
            "theorem_names": ["N.expected_theorem"],
            "definition_names": ["N.expected_definition"],
            "permitted_axioms": ["Classical.choice"],
        },
        "challenge": "def expected_definition := 0\n"
                     "theorem expected_theorem : True := by sorry\n",
        "solution": "import Mathlib.Tactic\n"
                    "def expected_definition := 0\n"
                    "theorem expected_theorem : True := by trivial\n",
        "metadata": ("Classical.choice; substantive actual-source/carrier attachment; "
                     "six open Gate-B; does not exclude or construct"),
    }
    report = A.analyze(
        dossier=dossier, manifest=_manifest(True), gate_b_rows=_rows(),
        export_paths=A.FORMALIZATION_REQUIRED, formalization=formalization)
    finding = _findings(report)["FORMALIZATION.IMPORT_CLOSURE"]

    assert finding["status"] == "OPPORTUNITY"
    assert finding["broad_tactic_import"]


def test_manifest_formal_replay_layers_are_audited_together():
    dossier = D.build_path(DOSSIER)
    manifest = _manifest(True)
    manifest["palomar_candidate"] = {
        "lean_kernel_replay": "PASS",
        "comparator_replay": "PASS",
        "nanoda_replay": "PASS",
    }
    report = A.analyze(
        dossier=dossier, manifest=manifest, gate_b_rows=_rows(),
        export_paths=set())
    finding = _findings(report)["FORMALIZATION.REPLAY_LAYERS"]

    assert finding["status"] == "PASS"
    assert set(finding["replay_layers"].values()) == {"PASS"}

    manifest["palomar_candidate"]["nanoda_replay"] = "FAIL"
    report = A.analyze(
        dossier=dossier, manifest=manifest, gate_b_rows=_rows(),
        export_paths=set())
    assert (_findings(report)["FORMALIZATION.REPLAY_LAYERS"]["status"] ==
            "BLOCKER")


def test_export_scan_prunes_build_and_vcs_trees(tmp_path, monkeypatch):
    export = tmp_path / "export"
    (export / "artifacts").mkdir(parents=True)
    (export / "gate_b").mkdir()
    (export / "kept").mkdir()
    for hidden in A.EXPORT_SCAN_EXCLUDES:
        (export / hidden).mkdir()
        (export / hidden / "noise").write_text("noise", encoding="utf-8")
    (export / "artifacts" / "release-manifest.json").write_text(
        '{"overall_theorem":"OPEN","gate_b":"26/32",'
        '"release_gates":{"review":false}}', encoding="utf-8")
    (export / "gate_b" / "CUSTODY_MATRIX.csv").write_text(
        "support,verdict,custody_class,artifact,checker\n",
        encoding="utf-8")
    (export / "kept" / "payload.txt").write_text("kept", encoding="utf-8")
    seen = []
    real_walk = os.walk

    def recording_walk(root):
        for directory, names, files in real_walk(root):
            seen.append(Path(directory).relative_to(export).as_posix())
            yield directory, names, files

    monkeypatch.setattr(A.os, "walk", recording_walk)
    dossier = D.build_path(DOSSIER)
    monkeypatch.setattr(D, "build_path", lambda *args, **kwargs: dossier)
    A.audit_paths(DOSSIER, ROOT, export)

    assert "kept" in seen
    assert not any(part in A.EXPORT_SCAN_EXCLUDES
                   for directory in seen for part in Path(directory).parts)


def test_git_object_source_audit_ignores_live_worktree_drift(tmp_path):
    repo = tmp_path / "source"
    repo.mkdir()

    def git(*args):
        subprocess.run(["git", "-C", str(repo), *args], check=True,
                       capture_output=True, text=True)

    git("init")
    git("config", "user.email", "audit@example.test")
    git("config", "user.name", "Audit Fixture")
    tracked = repo / "claim.txt"
    tracked.write_text("frozen\n", encoding="utf-8")
    git("add", "claim.txt")
    git("commit", "-m", "freeze")
    commit = subprocess.run(
        ["git", "-C", str(repo), "rev-parse", "HEAD"], check=True,
        capture_output=True, text=True).stdout.strip()

    tracked.write_text("dirty-live-value\n", encoding="utf-8")
    (repo / "untracked.txt").write_text("not in release\n", encoding="utf-8")

    source = {
        "expected_commit": commit[:12],
        "canonical_sources": [{
            "id": "SOURCE.CLAIM",
            "path": "claim.txt",
            "sha256": "sha256:" + hashlib.sha256(b"frozen\n").hexdigest(),
        }],
    }
    frozen = D._audit_source(source, [], repo, source_ref=commit)
    live = D._audit_source(source, [], repo)

    assert frozen["status"] == "CURRENT_CLEAN"
    assert frozen["source_ref"] == commit
    assert frozen["dirty"] is False
    assert frozen["files"][0]["status"] == "MATCH"
    assert live["status"] == "STALE"
    assert live["dirty"] is True
    assert tracked.read_text(encoding="utf-8") == "dirty-live-value\n"


def test_source_observation_finding_distinguishes_ref_from_worktree():
    dossier = D.build_path(DOSSIER)
    common = dict(dossier=dossier, manifest=_manifest(True),
                  gate_b_rows=_rows(), export_paths=set())
    live = A.analyze(**common)
    frozen = A.analyze(
        **common, source_observation={"requested_ref": "freeze", "commit": "a" * 40})

    assert _findings(live)["SOURCE.IMMUTABLE_REF"]["status"] == "NOTE"
    finding = _findings(frozen)["SOURCE.IMMUTABLE_REF"]
    assert finding["status"] == "PASS"
    assert finding["commit"] == "a" * 40
