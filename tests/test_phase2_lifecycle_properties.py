"""Lifecycle, retraction and totality proofs compile, kernel-check and use only standard axioms."""
import importlib.util
from pathlib import Path
import unittest

ROOT=Path(__file__).resolve().parents[1]
spec=importlib.util.spec_from_file_location("lifecycle_properties",ROOT/"tools/check-phase2-lifecycle-properties.py")
m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)

class LifecyclePropertyTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.report=m.run(m.SCRATCH/"tests.report.json")

    def test_every_property_is_kernel_checked(self):
        build=self.report["build"]
        self.assertTrue(build["kernel_checked"])
        self.assertEqual(set(build["axiom_declarations"]),set(m.DECLARATIONS))
        self.assertLessEqual(set(build["axioms"]),{"propext","Quot.sound","Classical.choice"})
        self.assertEqual(build["harness_sha256"],m.sha(m.HARNESS.read_bytes()))

    def test_kernel_sources_are_total(self):
        audit=self.report["totality_audit"]
        self.assertEqual(audit["violations"],[])
        self.assertGreater(audit["kernel_sources"],10)

    def test_audit_catches_nontotal_declarations(self):
        for line in ("partial def loop : Nat := loop","unsafe def x : Nat := 0","@[extern \"f\"] def g : Nat := 0",
                     "@[implemented_by h] def k : Nat := 0","theorem t : True := sorry","example : 1 = 1 := by native_decide"):
            with self.subTest(line=line):
                self.assertTrue(m.NONTOTAL.search(line))
        self.assertIsNone(m.NONTOTAL.search("-- a partial def mentioned in a comment".split("--")[0]))

    def test_four_handoff_properties_are_named(self):
        self.assertEqual(set(self.report["properties"]),{"retraction_invalidates_exactly_dependents",
            "failed_retries_never_revoke","circular_support_never_bootstraps","determinism_and_totality"})

if __name__=="__main__":
    unittest.main()
