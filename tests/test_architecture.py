"""Executable trust-zone and cold-start boundaries."""

import ast
import os
from pathlib import Path
import re

from grandportage import __version__
from grandportage import format as F


ROOT = Path(__file__).parents[1]
PACKAGE = ROOT / "grandportage"

PACKAGE_ROOT = {"__version__"}

SEMANTIC_CORE = {
    "kernel", "format", "contracts", "discharge",
}
AFFINE_EVIDENCE = {
    "evidence",
    "groebner", "coefficient_expansion", "localization", "factor_power",
    "factor_power_contradiction", "product_split", "laurent_lowering",
    "laurent_coefficient_pipeline", "triangular",
}
DERIVED_READ_SURFACES = {
    "frontier", "frontier_bundle", "projection", "visualization",
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


def test_standalone_affine_evidence_never_imports_graph_or_adapters():
    allowed = SEMANTIC_CORE | AFFINE_EVIDENCE
    for module in AFFINE_EVIDENCE:
        assert _local_imports(module) <= allowed, (
            module, _local_imports(module) - allowed)


def test_derived_read_surfaces_do_not_enter_trusted_modules():
    trusted = SEMANTIC_CORE | AFFINE_EVIDENCE | {
        "store", "check", "verify", "operations", "provenance",
    }
    for module in trusted:
        assert not (_local_imports(module) & DERIVED_READ_SURFACES), module


def test_every_named_zone_module_exists():
    named = SEMANTIC_CORE | AFFINE_EVIDENCE | DERIVED_READ_SURFACES
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
