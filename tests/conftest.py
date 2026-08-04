"""Repository-level test environment boundaries.

The public Grand Portage release includes the frozen JC pressure adapters and
their tests, but not the sibling ``math-stuff`` research checkout.  Keep those
tests visible in collection while skipping the integration group when its
native source tree is genuinely absent.  Workspace runs beside math-stuff are
unchanged and still exercise every JC binding.
"""

from pathlib import Path

import pytest


REPOSITORY_ROOT = Path(__file__).resolve().parents[1]
JC_NATIVE_ROOT = REPOSITORY_ROOT.parent / "math-stuff"


def pytest_collection_modifyitems(items):
    if JC_NATIVE_ROOT.exists():
        return
    missing = pytest.mark.skip(
        reason="JC integration tests require the sibling math-stuff checkout")
    for item in items:
        if Path(str(item.fspath)).name.startswith("test_jc_"):
            item.add_marker(missing)
