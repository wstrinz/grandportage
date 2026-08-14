"""Repository-level test environment boundaries.

The public Grand Portage release includes the frozen JC pressure adapters and
their tests, but not the sibling ``math-stuff`` research checkout.  Keep those
tests visible in collection while skipping the integration group when its
native source tree is genuinely absent.  Workspace runs beside math-stuff are
unchanged and still exercise every JC binding.
"""

import os
from pathlib import Path

import pytest


REPOSITORY_ROOT = Path(__file__).resolve().parents[1]
JC_NATIVE_ROOT = REPOSITORY_ROOT.parent / "math-stuff"


@pytest.fixture
def explicit_jc_native_binding_check():
    """Moving-head integration is opt-in; frozen JC replay stays unconditional.

    The sibling campaign is intentionally allowed to advance beyond GP's
    historical adapters.  A current-head digest comparison is useful when
    coordinating a new handback, but it is not a deterministic release test.
    The dossier source audit is the ordinary way to report that drift.
    """
    if os.environ.get("GP_CHECK_JC_NATIVE_BINDINGS") != "1":
        pytest.skip(
            "set GP_CHECK_JC_NATIVE_BINDINGS=1 for moving-head JC integration")
    if not JC_NATIVE_ROOT.exists():
        pytest.skip("the sibling JC research checkout is not present")


def pytest_collection_modifyitems(items):
    if JC_NATIVE_ROOT.exists():
        return
    missing = pytest.mark.skip(
        reason="JC integration tests require the sibling math-stuff checkout")
    for item in items:
        if Path(str(item.fspath)).name.startswith("test_jc_"):
            item.add_marker(missing)
