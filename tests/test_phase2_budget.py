"""Guard proof/runtime accounting against hiding executable helpers."""
import importlib.util
from pathlib import Path
import unittest

ROOT = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location("phase2_budget", ROOT / "tools/check-phase2-budget.py")
budget = importlib.util.module_from_spec(spec)
spec.loader.exec_module(budget)

class Phase2BudgetTests(unittest.TestCase):
    def test_theorems_and_erased_predicates_are_proof_only(self):
        self.assertFalse(budget.has_executable_declaration(
            "def Closed (n : Nat) : Prop := n = 0\n"
            "theorem zero_closed : Closed 0 := rfl\n"))

    def test_runtime_helper_makes_a_proof_module_chargeable(self):
        self.assertTrue(budget.has_executable_declaration(
            "def Closed (n : Nat) : Prop := n = 0\n"
            "private def closes (n : Nat) : Bool := n == 0\n"
            "theorem zero_closed : Closed 0 := rfl\n"))

    def test_multiline_predicate_is_erased(self):
        self.assertFalse(budget.has_executable_declaration(
            "protected def Closed\n    (n : Nat)\n    : Prop := n = 0\n"))

    def test_erased_proof_record_is_proof_only(self):
        self.assertFalse(budget.has_executable_declaration(
            "structure Contract (n : Nat) : Prop where\n  sound : n = 0\n"))
        self.assertTrue(budget.has_executable_declaration(
            "structure Contract (n : Nat) : Prop where\n  sound : n = 0\n"
            "def runtime : Nat := 0\n"))

    def test_runtime_abbreviations_and_types_are_charged(self):
        for source in ("abbrev Id := Nat", "structure Token where\n  value : Nat",
                       "inductive Token where | value", "opaque token : Nat",
                       "noncomputable def token : Nat := 0",
                       "instance : Inhabited Nat := ⟨0⟩"):
            with self.subTest(source=source):
                self.assertTrue(budget.has_executable_declaration(source))

if __name__ == "__main__":
    unittest.main()
