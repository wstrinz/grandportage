"""The Kernel tier matches KERNEL-PIN.json and imports nothing outside Kernel."""
import importlib.util
from pathlib import Path
import re
import unittest

ROOT = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location("kernel_pin", ROOT / "tools/kernel-pin.py")
pin = importlib.util.module_from_spec(spec)
spec.loader.exec_module(pin)


class KernelPinTests(unittest.TestCase):
    def test_kernel_matches_pin(self):
        result = pin.verify()
        self.assertTrue(result["unchanged"], "Kernel changed since KERNEL-PIN.json; log each change in PROMOTIONS.md: %s"
                        % result["changed"])

    def test_kernel_imports_only_kernel(self):
        kernel = set(pin.kernel_modules())
        for module in sorted(kernel):
            source = (pin.PACKAGE / (module.replace(".", "/") + ".lean")).read_text(encoding="utf-8")
            with self.subTest(module=module):
                for imported in re.findall(r"^import (GP50\.\w+)", source, re.M):
                    self.assertIn(imported, kernel, "%s imports non-kernel %s" % (module, imported))

    def test_kernel_has_no_mathlib(self):
        for module in pin.kernel_modules():
            source = (pin.PACKAGE / (module.replace(".", "/") + ".lean")).read_text(encoding="utf-8")
            with self.subTest(module=module):
                self.assertNotRegex(source, r"^import Mathlib", )


if __name__ == "__main__":
    unittest.main()
