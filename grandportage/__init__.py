"""Grand Portage -- transport typing and obstruction tracking for computational
algebra.

A deliberate, effortful carry between two bodies of water, where you are
acutely aware of what you can bring.

The claim is small and should stay small: computations produce artifacts, and
an artifact does not carry its own license to conclude.  This records what each
step LOSES, and refuses the conclusions that loss does not support.
"""

__version__ = "0.1.0"

from . import kernel, store, check, discharge  # noqa: F401

__all__ = ["kernel", "store", "check", "discharge", "__version__"]
