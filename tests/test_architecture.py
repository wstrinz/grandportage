"""Executable trust-zone and cold-start boundaries."""

import ast
import os
from pathlib import Path
import re

import pytest

from grandportage import __version__
from grandportage import format as F

import conftest


ROOT = Path(__file__).parents[1]
PACKAGE = ROOT / "grandportage"

PACKAGE_ROOT = {"__version__"}

SEMANTIC_CORE = {
    "kernel", "format", "contracts", "discharge", "backend", "identity",
    "reference_oracle",
}
AFFINE_EVIDENCE = {
    "evidence",
    "groebner", "coefficient_expansion", "localization", "factor_power",
    "factor_power_contradiction", "product_split", "laurent_lowering",
    "laurent_coefficient_pipeline", "triangular", "number_field", "ordered",
    "ordered_receipt",
}
AUTHORITY_DECLARATIONS = {"authority_registry"}
AUTHORITY_BINDING = {"authority", "provenance"}
DERIVED_READ_SURFACES = {
    "campaign", "dossier", "frontier", "frontier_bundle", "projection",
    "publication", "release", "visualization",
}


def _local_imports(module):
    tree = ast.parse((PACKAGE / (module + ".py")).read_text(encoding="utf-8"))
    imported = set()
    for node in ast.walk(tree):
        if isinstance(node, ast.ImportFrom) and node.level:
            if node.module:
                imported.add(node.module.split(".", 1)[0])
            else:
                imported.update(alias.name.split(".", 1)[0]
                                for alias in node.names)
    return imported


def test_semantic_core_never_imports_lower_trust_zones():
    for module in SEMANTIC_CORE:
        assert _local_imports(module) <= SEMANTIC_CORE | PACKAGE_ROOT, (
            module, _local_imports(module) - SEMANTIC_CORE)


def test_reference_oracle_shares_no_fast_checker_helpers():
    assert not _local_imports("reference_oracle")


def test_standalone_affine_evidence_never_imports_graph_or_adapters():
    allowed = SEMANTIC_CORE | AFFINE_EVIDENCE | AUTHORITY_DECLARATIONS
    for module in AFFINE_EVIDENCE:
        assert _local_imports(module) <= allowed, (
            module, _local_imports(module) - allowed)


def test_authority_binding_imports_only_trusted_lower_layers():
    allowed = (SEMANTIC_CORE | AFFINE_EVIDENCE | AUTHORITY_BINDING |
               PACKAGE_ROOT)
    for module in AUTHORITY_BINDING:
        # Provenance lazily asks the production adapter for its binary identity
        # while reloading persisted backend verdicts. ARCHITECTURE.md records
        # this existing downward call; the new binder must not add another.
        module_allowed = allowed | ({"cas"} if module == "provenance" else set())
        assert _local_imports(module) <= module_allowed, (
            module, _local_imports(module) - module_allowed)


def test_store_projects_verdict_authority_only_through_the_binder():
    source = (PACKAGE / "store.py").read_text(encoding="utf-8")
    assert "P.current_verdict(" not in source
    assert "A.check(" in source
    assert "A.bind(" in source
    assert "A.project(receipt, target[of])" in source
    assert "target[of][field] =" not in source


def test_derived_read_surfaces_do_not_enter_trusted_modules():
    trusted = SEMANTIC_CORE | AFFINE_EVIDENCE | {
        "store", "check", "verify", "operations", "provenance",
    }
    for module in trusted:
        assert not (_local_imports(module) & DERIVED_READ_SURFACES), module


def test_every_named_zone_module_exists():
    named = (SEMANTIC_CORE | AFFINE_EVIDENCE | AUTHORITY_DECLARATIONS |
             AUTHORITY_BINDING | DERIVED_READ_SURFACES)
    missing = [module for module in sorted(named)
               if not (PACKAGE / (module + ".py")).is_file()]
    assert not missing


def test_every_marked_release_boundary_in_root_docs_is_current():
    expected = {
        "version": __version__,
        "graph-format": str(F.GRAPH_FORMAT),
        "kernel-epoch": str(F.KERNEL_EPOCH),
    }
    seen = dict((key, 0) for key in expected)
    wrong = []
    for name in sorted(os.listdir(ROOT)):
        if not name.endswith(".md"):
            continue
        text = (ROOT / name).read_text(encoding="utf-8")
        for key, value in expected.items():
            pattern = r"<!--%s-->([^<]+)<!--/%s-->" % (key, key)
            for match in re.finditer(pattern, text):
                seen[key] += 1
                if match.group(1) != value:
                    wrong.append("%s says %s=%s" % (
                        name, key, match.group(1)))
    assert all(seen.values()), seen
    assert not wrong, "Run `gp docs` to resync: %s" % "; ".join(wrong)


def test_lean_shadow_epoch_cannot_drift_silently():
    source = (ROOT / "lean" / "GrandPortage" /
              "SelectedEmbedding.lean").read_text(encoding="utf-8")
    match = re.search(
        r"^def modeledKernelEpoch\s*:\s*Nat\s*:=\s*(\d+)\s*$",
        source, re.MULTILINE)
    assert match, "Lean shadow must publish modeledKernelEpoch"
    assert int(match.group(1)) == F.KERNEL_EPOCH, (
        "runtime kernel epoch %d has advanced past Lean shadow epoch %s"
        % (F.KERNEL_EPOCH, match.group(1)))
    aggregate = (ROOT / "lean" / "GrandPortage.lean").read_text(
        encoding="utf-8")
    assert "import GrandPortage.SelectedEmbedding" in aggregate


def test_readme_remains_a_bounded_introduction():
    lines = (ROOT / "README.md").read_text(encoding="utf-8").splitlines()
    assert len(lines) <= 160, "README is %d lines; move detail to SPEC.md" % len(lines)


def test_intro_and_quickstart_answer_the_five_cold_reader_questions():
    intro = (ROOT / "README.md").read_text(encoding="utf-8")
    quickstart = (ROOT / "QUICKSTART.md").read_text(encoding="utf-8")
    combined = intro + "\n" + quickstart
    for concept in ("Established", "Carried", "Stale", "Licensed",
                    "First unresolved seam"):
        assert concept.lower() in combined.lower(), concept
    assert "SPEC.md" in intro


def test_operational_spec_retains_historical_confessions_and_verifiers():
    spec = (ROOT / "SPEC.md").read_text(encoding="utf-8")
    for anchor in ("Five of those cells were", "gp verify", "gp evidence",
                   "Scope is derived", "The six relaxation types"):
        assert anchor.lower() in spec.lower(), anchor


class _CollectedItem:
    def __init__(self, live):
        self.live = live
        self.markers = []

    def get_closest_marker(self, name):
        return object() if self.live and name == "live" else None

    def add_marker(self, marker):
        self.markers.append(marker)


def test_cas_less_collection_skips_only_live_tests(monkeypatch):
    monkeypatch.delenv("GP_REQUIRE_LIVE", raising=False)
    live = _CollectedItem(True)
    deterministic = _CollectedItem(False)
    conftest._mark_unreachable_live_tests(
        [live, deterministic], "unavailable: FileNotFoundError")
    assert len(live.markers) == 1
    assert live.markers[0].mark.name == "skip"
    assert live.markers[0].mark.kwargs["reason"] == (
        conftest.LIVE_CAS_SKIP_REASON)
    assert deterministic.markers == []


@pytest.mark.parametrize("version", ["Singular 4.4.1", "unreported"])
def test_reachable_live_collection_is_not_made_skippable(monkeypatch, version):
    monkeypatch.delenv("GP_REQUIRE_LIVE", raising=False)
    live = _CollectedItem(True)
    conftest._mark_unreachable_live_tests([live], version)
    assert live.markers == []


def test_authorized_live_collection_refuses_environmental_skip(monkeypatch):
    monkeypatch.setenv("GP_REQUIRE_LIVE", "1")
    live = _CollectedItem(True)
    conftest._mark_unreachable_live_tests(
        [live], "unavailable: FileNotFoundError")
    assert live.markers == []
