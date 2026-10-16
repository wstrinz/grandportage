"""Release plan (stable gate): the main soundness theorems GUARANTEES.md cites depend only on the
three standard axioms. Run on every CI build where the binding and census are built (CI's gp50 job
builds both); skipped, with a reason, where they are not."""
import os
from pathlib import Path
import re
import subprocess
import unittest

ROOT = Path(__file__).resolve().parents[1]
STANDARD = {"propext", "Quot.sound", "Classical.choice"}


def lake(package):
    toolchain = Path(os.environ.get("ELAN_HOME", Path.home() / ".elan")) / "toolchains" / (
        package / "lean-toolchain").read_text(encoding="utf-8").strip().replace("/", "--").replace(":", "---")
    return toolchain / "bin" / ("lake.exe" if os.name == "nt" else "lake")


def audit(package, imports, names, prelude=""):
    """#print axioms for each name in a temporary file under the package; returns {name: set(axioms)}."""
    path = package / "tmp" / "AxiomAudit.lean"
    path.parent.mkdir(exist_ok=True)
    path.write_bytes(("\n".join(f"import {m}" for m in imports) + "\n\n" + prelude +
                      "\n".join(f"#print axioms {n}" for n in names) + "\n").encode("utf-8"))
    try:
        run = subprocess.run([str(lake(package)), "env", "lean", "tmp/AxiomAudit.lean"], cwd=package,
                             capture_output=True, text=True, encoding="utf-8")
    finally:
        path.unlink(missing_ok=True)
    if run.returncode != 0:
        raise AssertionError(run.stdout + run.stderr)
    found = {}
    text = run.stdout.replace("\r\n", "\n")
    for m in re.finditer(r"'([^']+)' depends on axioms: \[([^\]]*)\]", text):
        found[m.group(1)] = {a.strip() for a in m.group(2).replace("\n", " ").split(",") if a.strip()}
    for m in re.finditer(r"'([^']+)' does not depend on any axioms", text):
        found[m.group(1)] = set()
    return found


class AxiomAudit(unittest.TestCase):
    def check(self, package, imports, names, built_marker):
        if not (package / built_marker).exists():
            self.skipTest(f"{package.name} is not built here")
        found = audit(package, imports, names)
        self.assertEqual(set(found), set(names), "every audited theorem must be reported")
        for name, axioms in found.items():
            self.assertTrue(axioms <= STANDARD, f"{name} depends on {sorted(axioms - STANDARD)}")

    def test_kernel_and_binding(self):
        binding = ROOT / "binding"
        self.check(binding,
                   ["GP50.NarrowingAdmissionProofs", "GPBinding.Admission.Profile", "GPBinding.Admission.RuleSound",
                    "GPBinding.Matroid.Theorem", "GPBinding.Real.AdmissionSound", "GPBinding.UDG.Frame",
                    "GPBinding.UDG.Spine"],
                   ["GP50.Semantic.fold_held_meaning", "GPBinding.Admission.fold_held_meaning",
                    "GPBinding.Admission.fold_held_meaning_rules", "GPBinding.Matroid.frame_iff",
                    "GPBinding.Real.fold_held_meaning3", "GPBinding.Real.fold_held_goal",
                    "GPBinding.Real.fold_held_not_Q", "GPBinding.UDG.udg_frame_iff", "GPBinding.UDG.spine_sound",
                    "GPBinding.UDG.realize_sound"],
                   ".lake/build/lib/lean/GPBinding/Real/AdmissionSound.olean")

    def test_control_detects_a_custom_axiom(self):
        census = ROOT / "census"  # the lightest package; the control needs no imports
        if not (census / "lean-toolchain").exists():
            self.skipTest("no census package")
        found = audit(census, [], ["auditControl"],
                      prelude="axiom auditCheat : False\ntheorem auditControl : 1 = 2 := auditCheat.elim\n\n")
        self.assertIn("auditCheat", found["auditControl"])
        self.assertFalse(found["auditControl"] <= STANDARD)

    def test_profile_withdrawal(self):
        # GP 0.51 claim withdrawal (docs/WITHDRAWAL-DESIGN.md §3): W1-W3 and W3 for every 3a and 3b run.
        profile = ROOT / "profile"
        self.check(profile, ["GPProfile.Withdraw"],
                   ["GPProfile.Withdraw.withdraw_antitone", "GPProfile.Withdraw.withdraw_resolves",
                    "GPProfile.Withdraw.withdraw_unholds", "GPProfile.Withdraw.runWith_withdrawn",
                    "GPProfile.Withdraw.run3_withdrawn"],
                   ".lake/build/lib/lean/GPProfile/Withdraw.olean")

    def test_census(self):
        census = ROOT / "census"
        self.check(census, ["GPCensus.Profile"], ["GPCensus.fold_held_meaning"],
                   ".lake/build/lib/lean/GPCensus/Profile.olean")

    def test_lane_p(self):
        # GP 0.52 Lane P, phase P1 (premises as scope): the fold soundness theorem, the discharge (cut) rule, the
        # meaning of a P scope, withdrawal W1P-W3P and W3P for every P run.
        profile = ROOT / "profile"
        self.check(profile, ["GPProfile.LaneP.Run"],
                   ["GPProfile.LaneP.fold_held_meaningP", "GPProfile.LaneP.dischargeOk_sound",
                    "GPProfile.LaneP.means_iff", "GPProfile.LaneP.acceptsProof_meaning",
                    "GPProfile.LaneP.acceptsRule_meaning", "GPProfile.LaneP.base_validator_soundP",
                    "GPProfile.LaneP.withdraw_antitoneP", "GPProfile.LaneP.withdraw_resolvesP",
                    "GPProfile.LaneP.withdraw_unholdsP", "GPProfile.LaneP.Run.run_withdrawn",
                    "GPProfile.LaneP.Run.events_ids", "GPProfile.LaneP.Run.events_noSupersede"],
                   ".lake/build/lib/lean/GPProfile/LaneP/Run.olean")


if __name__ == "__main__":
    unittest.main()
