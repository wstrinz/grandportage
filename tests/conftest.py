import os
import sys

import pytest

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)

for p in (ROOT, HERE):
    if p not in sys.path:
        sys.path.insert(0, p)


@pytest.fixture(autouse=True)
def _skip_when_the_cas_is_absent(request):
    """Skip `live` tests when there is no reachable CAS -- and only then run
    the probe that decides.

    The probe costs up to 180 seconds against a cold WSL, and it used to run at
    module import, so `-m "not live"` paid for a solver it had just deselected.
    Doing it here means the cost is paid at most once, and only by a run that
    actually reaches a live test.
    """
    if request.node.get_closest_marker("live") is None:
        return
    import test_boundary as TB
    if not TB._singular_available():
        pytest.skip(TB._UNREACHABLE[0] or "Singular not reachable")
