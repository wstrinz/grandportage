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

from grandportage import cas


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


LIVE_CAS_SKIP_REASON = (
    "Singular not found; live tier requires a CAS — see QUICKSTART")


def _mark_unreachable_live_tests(items, binary_version=None):
    """Skip only a CAS-less collection, never a failure after a run starts."""
    live_items = [item for item in items if item.get_closest_marker("live")]
    if not live_items or os.environ.get("GP_REQUIRE_LIVE") == "1":
        return
    if binary_version is None:
        binary_version = cas._singular_binary_version(timeout=10)
    if not binary_version.startswith("unavailable:"):
        return
    missing = pytest.mark.skip(reason=LIVE_CAS_SKIP_REASON)
    for item in live_items:
        item.add_marker(missing)


def pytest_collection_modifyitems(items):
    _mark_unreachable_live_tests(items)
    if not JC_NATIVE_ROOT.exists():
        missing = pytest.mark.skip(
            reason="JC integration tests require the sibling math-stuff checkout")
        for item in items:
            if Path(str(item.fspath)).name.startswith("test_jc_"):
                item.add_marker(missing)
