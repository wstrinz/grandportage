"""Cross-surface audit for the final Family-F2 ``(75,125)`` public export.

This is deliberately an experiment rather than a core schema.  It compares
the campaign dossier with the export manifest, Gate-B custody matrix, and
advertised replay payloads.  It grants no mathematical or graph authority.
"""

from __future__ import annotations

import argparse
import csv
import json
import os
from pathlib import Path
import re
import subprocess
from typing import Iterable

from grandportage import dossier as D


SCHEMA = "f2-75-125-publication-audit/v0"
AUTHORITY = "DERIVED_READ_MODEL_ONLY"
GRAPH_EFFECT = "NONE"
EXPORT_SCAN_EXCLUDES = {".git", ".lake", ".cache", "__pycache__"}

OPEN_SUPPORTS = {
    "a*P5*b*P4",
    "a*P5*b*u7",
    "a*P5*P4*u7",
    "a*b*P4*u7",
    "P5*b*P4*u7",
    "a*P5*b*P4*u7",
}

# These are the Python payloads invoked by verify_quick.py and the additional
# payloads invoked directly by verify_release.py.  The runners themselves are
# intentionally excluded: this inventory asks whether their declared work is
# actually in the public tree.
ADVERTISED_CHECKERS = {
    "proofs/A_reduction_to_F2/check.py",
    "proofs/B_K3_K4_rootjets/calculations/carrier_k4_universal_rootjet/check_carrier_k4_universal_rootjet.py",
    "proofs/B_K3_K4_rootjets/calculations/carrier_valuation_k3_k4/check_carrier_valuation_k3_k4.py",
    "proofs/B_K3_K4_rootjets/calculations/k4_poisson_cokernel_crosscheck/check_k4_poisson_cokernel.py",
    "proofs/B_K3_K4_rootjets/calculations/k4_poisson_repeatroot_crosscheck/check_pk4rr.py",
    "proofs/C_K5_deeper_contact/calculations/k5_mge3_k1_p12_valuation/check_k5_mge3_k1_p12_valuation.py",
    "proofs/C_K5_deeper_contact/calculations/k5_depth5_support_shift_repair/check_repair.py",
    "proofs/C_K5_deeper_contact/calculations/k5_k4_stratum_collapse/check_k5_k4_stratum_collapse.py",
    "proofs/C_K5_deeper_contact/calculations/k5_degenerate_k7_survivors/check_k5_degenerate_k7_survivors.py",
    "proofs/C_K5_deeper_contact/calculations/k5_tuned_order20/check_k5_tuned_order20.py",
    "proofs/D_carrier_limits/calculations/k6_k8_corrected_audit/corrected_audit.py",
}

CANONICAL_CHECKER_CANDIDATES = {
    path: "d2_plane_72_108/_smoosh_v0/%s" % path.split("calculations/", 1)[-1]
    for path in ADVERTISED_CHECKERS
    if "calculations/" in path
}

FORMALIZATION_REQUIRED = {
    "formalization/Challenge.lean",
    "formalization/Solution.lean",
    "formalization/comparator.json",
    "formalization/formalization.yaml",
    "formalization/lakefile.toml",
    "formalization/lean-toolchain",
}


def _finding(item_id: str, status: str, title: str, detail: str, **data):
    result = {"id": item_id, "status": status, "title": title,
              "detail": detail}
    result.update(data)
    return result


def analyze(*, dossier, manifest, gate_b_rows,
            export_paths: Iterable[str], canonical_paths: Iterable[str] = (),
            formalization=None, source_observation=None):
    """Analyze already-loaded observations without reading or executing files."""
    export_paths = {Path(item).as_posix() for item in export_paths}
    canonical_paths = {Path(item).as_posix() for item in canonical_paths}
    findings = []

    if source_observation:
        findings.append(_finding(
            "SOURCE.IMMUTABLE_REF", "PASS",
            "Canonical source is observed at an immutable Git commit",
            "The audit reads declared paths from Git objects, not the live worktree.",
            **source_observation))
    else:
        findings.append(_finding(
            "SOURCE.IMMUTABLE_REF", "NOTE",
            "Canonical source observation is worktree-relative",
            "Pass --source-ref to audit the immutable source commit named by "
            "the publication instead of the live checkout."))

    profiles = {item["id"]: item for item in dossier["profiles"]}
    claims = {item["id"] for item in dossier["claims"]}
    leaves = {item["id"]: item for item in dossier["leaves"]}
    required_profiles = {"F2_PUBLICATION", "75125_EXCLUSION"}
    portrait_ok = (required_profiles <= set(profiles) and len(claims) == 6 and
                   len(leaves) == 8 and
                   all(item["price"]["status"] == "PRICED"
                       for item in leaves.values()))
    findings.append(_finding(
        "PORTRAIT.PROFILE_SPLIT", "PASS" if portrait_ok else "BLOCKER",
        "Publication and exclusion are distinct profiles",
        ("Six portrait claims and eight priced residuals are represented."
         if portrait_ok else
         "The dossier no longer has the expected two-profile, six-claim, "
         "eight-priced-residual shape.")))

    publication = profiles.get("F2_PUBLICATION", {})
    publication_blockers = [
        blocker
        for criterion in publication.get("criteria", [])
        for blocker in criterion.get("blockers", [])
    ]
    publication_ready = publication.get("status") == "READY"
    findings.append(_finding(
        "DOSSIER.PUBLICATION_PROFILE",
        "PASS" if publication_ready else "BLOCKER",
        "The selected short-of-summit profile is ready",
        ("The dossier publication profile is READY."
         if publication_ready else
         "The dossier publication profile has %d blocker(s)." %
         len(publication_blockers)),
        blockers=publication_blockers))

    theorem_open = (manifest.get("overall_theorem") == "OPEN" and
                    dossier["campaign"]["summit_status"].startswith("OPEN") and
                    "JC.F2.CLAIM.NON_COMPOSITION" in claims)
    findings.append(_finding(
        "THEOREM.OPEN_CONSISTENCY", "PASS" if theorem_open else "BLOCKER",
        "The open theorem and non-composition boundary agree",
        ("Manifest, dossier summit, and portrait all keep (75,125) open."
         if theorem_open else
         "At least one public surface widens or loses the open-theorem boundary.")))

    rows = list(gate_b_rows)
    closed = [row for row in rows if row.get("verdict") == "closed-exact"]
    opened = [row for row in rows if row.get("verdict") == "open"]
    census_ok = (len(rows) == 32 and len(closed) == 26 and len(opened) == 6 and
                 manifest.get("gate_b") == "26/32")
    findings.append(_finding(
        "GATE_B.CENSUS", "PASS" if census_ok else "BLOCKER",
        "Gate-B manifest and custody census agree",
        ("The matrix has 32 rows, 26 exact closures, and six opens."
         if census_ok else
         "The manifest's 26/32 claim does not match the literal custody rows."),
        rows=len(rows), closed=len(closed), open=len(opened)))

    observed_supports = {row.get("support") for row in opened}
    topology_ok = observed_supports == OPEN_SUPPORTS
    findings.append(_finding(
        "GATE_B.OPEN_TOPOLOGY", "PASS" if topology_ok else "BLOCKER",
        "The six named Gate-B residuals match the matrix",
        ("The five size-four supports and the size-five support match exactly."
         if topology_ok else
         "The open-cell identities drifted from the dossier."),
        expected=sorted(OPEN_SUPPORTS), observed=sorted(observed_supports)))

    missing = sorted(ADVERTISED_CHECKERS - export_paths)
    findings.append(_finding(
        "REPLAY.ADVERTISED_PAYLOADS", "PASS" if not missing else "BLOCKER",
        "Advertised public replay payloads resolve",
        ("All eleven headline/release checker paths exist."
         if not missing else
         "%d of 11 advertised checker payloads are absent." % len(missing)),
        missing=missing))

    packageable = {
        public: canonical
        for public, canonical in CANONICAL_CHECKER_CANDIDATES.items()
        if public in missing and canonical in canonical_paths
    }
    missing_producers = sorted(set(missing) - set(packageable))
    findings.append(_finding(
        "REPLAY.CANONICAL_PACKAGING",
        "OPPORTUNITY" if packageable else "NOTE",
        "Missing replay entry points already exist in canonical custody",
        ("%d missing public entry point(s) have canonical campaign candidates; "
         "compute and bind each directory's dependency closure before export."
         % len(packageable) if packageable else
         "No missing public replay entry point has a known canonical candidate."),
        candidates=packageable, unresolved=missing_producers))

    checksums_present = "SHA256SUMS" in export_paths
    findings.append(_finding(
        "RELEASE.CHECKSUMS", "PASS" if checksums_present else "BLOCKER",
        "The content checksum index is present",
        ("SHA256SUMS is present for independent archive verification."
         if checksums_present else
         "SHA256SUMS is absent, so build_sha256s.py --check fails closed.")))

    gates = manifest.get("release_gates", {})
    open_gates = sorted(key for key, value in gates.items() if value is not True)
    findings.append(_finding(
        "PUBLICATION.RELEASE_GATES", "PASS" if not open_gates else "BLOCKER",
        "Publication release gates are explicit",
        ("Every declared publication gate is closed."
         if not open_gates else
         "%d declared publication gates remain false." % len(open_gates)),
        open_gates=open_gates))

    replay_candidate = manifest.get("palomar_candidate")
    if replay_candidate:
        replay_layers = {
            key: replay_candidate.get(key)
            for key in ("lean_kernel_replay", "comparator_replay",
                        "nanoda_replay")
        }
        replay_layers_pass = all(value == "PASS"
                                 for value in replay_layers.values())
        replay_layers_status = "PASS" if replay_layers_pass else "BLOCKER"
        replay_layers_detail = (
            "The release manifest records PASS for the Lean kernel, comparator, "
            "and nanoda replay layers."
            if replay_layers_pass else
            "The release manifest advertises a formal candidate but at least "
            "one of its three replay layers is not PASS.")
    else:
        replay_layers = {}
        replay_layers_status = "NOTE"
        replay_layers_detail = (
            "The release manifest does not advertise a multi-layer formal "
            "replay candidate.")
    findings.append(_finding(
        "FORMALIZATION.REPLAY_LAYERS", replay_layers_status,
        "Independent formal replay layers are explicit",
        replay_layers_detail, replay_layers=replay_layers))

    historical = [row for row in rows
                  if row.get("custody_class") == "digest-backed-historical"]
    portable_candidates = []
    for row in historical:
        candidates = []
        for field in ("artifact", "checker"):
            for token in row.get(field, "").split(";"):
                token = token.strip()
                if token.startswith("d2_plane_72_108/"):
                    candidates.append(token)
        if candidates and all(item in canonical_paths for item in candidates):
            portable_candidates.append(row.get("support"))
    findings.append(_finding(
        "GATE_B.PORTABILITY_REVIEW",
        "OPPORTUNITY" if portable_candidates else "NOTE",
        "Conservative Gate-B custody may be upgradeable",
        ("Canonical payload and checker paths exist for: %s. Recheck the "
         "cofactors before changing custody." % ", ".join(portable_candidates)
         if portable_candidates else
         "No digest-backed row has a complete canonical path set in this observation."),
        candidates=portable_candidates))

    standalone_formalization = any(
        item.startswith("formalization/") and item.endswith(".lean")
        for item in export_paths)
    missing_formalization = sorted(FORMALIZATION_REQUIRED - export_paths)
    if not standalone_formalization:
        formal_status = "NOTE"
        formal_detail = (
            "The preview contains no standalone Lean source; GP cannot yet "
            "audit the memo's proposed declaration-level transport boundary.")
    elif missing_formalization:
        formal_status = "BLOCKER"
        formal_detail = (
            "The standalone Lean package is partial; %d required package "
            "file(s) are absent." % len(missing_formalization))
    else:
        formal_status = "PASS"
        formal_detail = "The standalone Lean package surface is complete."
    findings.append(_finding(
        "FORMALIZATION.STANDALONE", formal_status,
        "Standalone formalization boundary",
        formal_detail, missing=missing_formalization))

    if formal_status == "PASS" and formalization:
        comparator = formalization.get("comparator", {})
        challenge = formalization.get("challenge", "")
        solution = formalization.get("solution", "")
        metadata = formalization.get("metadata", "")
        names = (comparator.get("theorem_names", []) +
                 comparator.get("definition_names", []))
        short_names = [item.rsplit(".", 1)[-1] for item in names]
        declarations_match = all(
            re.search(r"\b(?:theorem|def)\s+%s\b" % re.escape(name), challenge)
            and re.search(r"\b(?:theorem|def)\s+%s\b" % re.escape(name), solution)
            for name in short_names)
        deliberate_hole = re.search(r"\bby\s+sorry\b", challenge) is not None
        proved_solution = re.search(r"\bsorry\b", solution) is None
        metadata_lower = metadata.lower()
        metadata_words = " ".join(metadata_lower.split())
        attachment_boundary = (
            "attachment" in metadata_words
            and ("source/coordinate" in metadata_words
                 or "actual-source" in metadata_words
                 or "source/carrier" in metadata_words)
        )
        scope_closed = (
            attachment_boundary
            and "six open gate-b" in metadata_words
            and "does not exclude or construct" in metadata_words
        )
        axioms_bound = all(
            axiom in metadata
            for axiom in comparator.get("permitted_axioms", []))
        binding_ok = (bool(short_names) and declarations_match and
                      deliberate_hole and proved_solution and scope_closed and
                      axioms_bound)
        findings.append(_finding(
            "FORMALIZATION.DECLARATION_BINDING",
            "PASS" if binding_ok else "BLOCKER",
            "Challenge, solution, comparator, and scope metadata agree",
            ("Named definitions/theorems occur in both modules, only the "
             "challenge has the deliberate proof hole, permitted axioms are "
             "bound, and global nonclaims are explicit."
             if binding_ok else
             "The standalone formalization surfaces disagree on declarations, "
             "proof holes, axioms, or global nonclaims."),
            declaration_names=names,
            declarations_match=declarations_match,
            deliberate_challenge_hole=deliberate_hole,
            solution_has_no_sorry=proved_solution,
            scope_nonclaims_present=scope_closed,
            attachment_boundary_present=attachment_boundary,
            permitted_axioms_bound=axioms_bound))

        broad_tactic_import = bool(re.search(
            r"^\s*import\s+Mathlib\.Tactic\s*$", solution,
            flags=re.MULTILINE))
        findings.append(_finding(
            "FORMALIZATION.IMPORT_CLOSURE",
            "OPPORTUNITY" if broad_tactic_import else "PASS",
            "Formal replay imports are narrowly scoped",
            ("Solution.lean imports the Mathlib.Tactic umbrella; the observed "
             "cold replay completed 3,000 build jobs, including unrelated "
             "topology, analysis, and category-theory surfaces. Replace it with "
             "the smallest tactic imports that preserve the proof."
             if broad_tactic_import else
             "Solution.lean does not import the Mathlib.Tactic umbrella."),
            broad_tactic_import=broad_tactic_import))
    elif standalone_formalization:
        findings.append(_finding(
            "FORMALIZATION.DECLARATION_BINDING", "BLOCKER",
            "Challenge, solution, comparator, and scope metadata agree",
            "The formalization package exists but its declaration surfaces "
            "could not be loaded for comparison."))

    return {
        "schema": SCHEMA,
        "authority": AUTHORITY,
        "graph_effect": GRAPH_EFFECT,
        "campaign": dossier["campaign"],
        "dossier_fingerprint": dossier["history"]["observation_fingerprint"],
        "findings": findings,
        "counts": {
            "pass": sum(item["status"] == "PASS" for item in findings),
            "blocker": sum(item["status"] == "BLOCKER" for item in findings),
            "opportunity": sum(item["status"] == "OPPORTUNITY" for item in findings),
            "note": sum(item["status"] == "NOTE" for item in findings),
        },
    }


def _git(repo: Path, *args: str) -> str:
    result = subprocess.run(
        ["git", "-c", "safe.directory=%s" % repo, "-C", str(repo), *args],
        text=True, capture_output=True)
    if result.returncode:
        raise RuntimeError(
            "git %s failed in %s: %s" %
            (" ".join(args), repo, result.stderr.strip()))
    return result.stdout.strip()


def audit_paths(dossier_path, source_root, export_root=None, source_ref=None):
    """Load one live source observation and produce the derived audit.

    ``source_root`` remains the canonical campaign checkout used by the
    dossier and by optional custody-upgrade archaeology.  ``export_root`` may
    point at the separately published repository.  When omitted, retain the
    historical in-tree ``_public_export_75_125`` default, while also accepting
    a source root that is itself the public repository.
    """
    source_root = Path(source_root).resolve()
    resolved_commit = (_git(source_root, "rev-parse", "--verify",
                            source_ref + "^{commit}")
                       if source_ref is not None else None)
    if export_root is None:
        direct_manifest = source_root / "artifacts" / "release-manifest.json"
        export_root = (source_root if direct_manifest.is_file() else
                       source_root / "_public_export_75_125")
    else:
        export_root = Path(export_root).resolve()
    dossier = D.build_path(
        dossier_path, source_root=source_root, source_ref=source_ref)
    manifest = json.loads(
        (export_root / "artifacts" / "release-manifest.json").read_text(
            encoding="utf-8"))
    with (export_root / "gate_b" / "CUSTODY_MATRIX.csv").open(
            encoding="utf-8", newline="") as stream:
        rows = list(csv.DictReader(stream))
    export_paths = set()
    for directory, names, files in os.walk(export_root):
        names[:] = [name for name in names if name not in EXPORT_SCAN_EXCLUDES]
        root = Path(directory)
        export_paths.update(
            (root / name).relative_to(export_root).as_posix()
            for name in files)

    def canonical_exists(relative):
        if resolved_commit is None:
            return (source_root / relative).is_file()
        result = subprocess.run(
            ["git", "-c", "safe.directory=%s" % source_root,
             "-C", str(source_root), "cat-file", "-e",
             "%s:%s" % (resolved_commit, Path(relative).as_posix())],
            capture_output=True)
        return result.returncode == 0

    canonical_candidates = set()
    for row in rows:
        for field in ("artifact", "checker"):
            for token in row.get(field, "").split(";"):
                token = token.strip()
                if (token.startswith("d2_plane_72_108/") and
                        canonical_exists(token)):
                    canonical_candidates.add(Path(token).as_posix())
    for candidate in CANONICAL_CHECKER_CANDIDATES.values():
        if canonical_exists(candidate):
            canonical_candidates.add(Path(candidate).as_posix())
    formalization = None
    if FORMALIZATION_REQUIRED <= export_paths:
        formalization = {
            "comparator": json.loads(
                (export_root / "formalization/comparator.json").read_text(
                    encoding="utf-8")),
            "challenge": (export_root / "formalization/Challenge.lean").read_text(
                encoding="utf-8"),
            "solution": (export_root / "formalization/Solution.lean").read_text(
                encoding="utf-8"),
            "metadata": (export_root / "formalization/formalization.yaml").read_text(
                encoding="utf-8"),
        }
    source_observation = (
        {"requested_ref": source_ref, "commit": resolved_commit}
        if source_ref is not None else None)
    return analyze(
        dossier=dossier, manifest=manifest, gate_b_rows=rows,
        export_paths=export_paths, canonical_paths=canonical_candidates,
        formalization=formalization, source_observation=source_observation)


def render_human(report):
    lines = ["# Family-F2 (75,125) publication audit", "",
             "Authority: `%s`; graph effect: `%s`." %
             (report["authority"], report["graph_effect"]), ""]
    for finding in report["findings"]:
        lines.append("- `%s` **%s** — %s" %
                     (finding["status"], finding["id"], finding["title"]))
        lines.append("  %s" % finding["detail"])
        if finding.get("missing"):
            lines.extend("  - `%s`" % item for item in finding["missing"])
        if finding.get("open_gates"):
            lines.extend("  - `%s`" % item for item in finding["open_gates"])
        if finding.get("blockers"):
            lines.extend("  - %s" % item for item in finding["blockers"])
        if finding.get("candidates") and isinstance(finding["candidates"], dict):
            lines.extend("  - `%s` <- `%s`" % item
                         for item in sorted(finding["candidates"].items()))
    return "\n".join(lines) + "\n"


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("dossier")
    parser.add_argument("--source-root", required=True)
    parser.add_argument(
        "--source-ref",
        help=("immutable Git ref/commit to export from --source-root; when "
              "omitted the live worktree is observed for backward compatibility"))
    parser.add_argument(
        "--export-root",
        help=("published export checkout; defaults to SOURCE_ROOT itself when "
              "it contains artifacts/release-manifest.json, otherwise to "
              "SOURCE_ROOT/_public_export_75_125"))
    parser.add_argument("--format", choices=("human", "json"), default="human")
    parser.add_argument("--require-clear", action="store_true")
    args = parser.parse_args(argv)
    report = audit_paths(
        args.dossier, args.source_root, args.export_root, args.source_ref)
    if args.format == "json":
        print(json.dumps(report, indent=2, sort_keys=True))
    else:
        print(render_human(report), end="")
    if args.require_clear and report["counts"]["blocker"]:
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
