"""HW61 G-4: rope R1a (`UDGRope`) imports Mathlib only; the u(22) lemma sources use no `sorry`,
`native_decide` or custom axiom; every constant they define depends only on the standard axioms;
and the Comparator emitter is deterministic and ships the repository's proofs."""
import importlib.util
import os
import re
import subprocess
import tempfile
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
BINDING = ROOT / "binding"
UDG = BINDING / "GPBinding/UDG"
ROPE = sorted((UDG / "Rope").rglob("*.lean"))
GP_SIDE = [UDG / "System.lean", UDG / "Spine.lean", UDG / "Frame.lean"]
PROFILE = ROOT / "profile/GPProfile/UDG.lean"
STANDARD = {"propext", "Quot.sound", "Classical.choice"}
MODULES = ["UDGRope.Defs", "UDGRope.Basic", "UDGRope.Rhombus", "UDGRope.Gadgets", "UDGRope.Schade",
           "GPBinding.UDG.System", "GPBinding.UDG.Spine", "GPBinding.UDG.Frame", "GPProfile.UDG"]

spec = importlib.util.spec_from_file_location("emit_udg", ROOT / "tools/emit-udg-comparator.py")
emit = importlib.util.module_from_spec(spec)
spec.loader.exec_module(emit)

AUDIT = """import Lean
{imports}
open Lean Elab Command in
#eval show CommandElabM Unit from do
  let env ← getEnv
  let mods : List Name := [{names}]
  let mut rows : Array String := #[]
  for (n, _) in env.constants.map₁.toList do
    if let some idx := env.getModuleIdxFor? n then
      if mods.contains env.header.moduleNames[idx.toNat]! then
        let axs ← Lean.collectAxioms n
        rows := rows.push (toString n ++ "\\t" ++ ",".intercalate (axs.toList.map toString))
  IO.println ("AUDIT-BEGIN\\n" ++ "\\n".intercalate rows.toList ++ "\\nAUDIT-END")
"""


def code(text):
    """Lean source without comments and docstrings."""
    text = re.sub(r"/-.*?-/", "", text, flags=re.S)
    return re.sub(r"--[^\n]*", "", text)


class UDGRopeTests(unittest.TestCase):
    def test_rope_imports_mathlib_only(self):
        self.assertEqual({p.name for p in ROPE},
                         {"UDGRope.lean", "Defs.lean", "Basic.lean", "Rhombus.lean", "Gadgets.lean", "Schade.lean"})
        for p in ROPE:
            for line in p.read_text(encoding="utf-8").splitlines():
                if line.startswith("import "):
                    self.assertRegex(line, r"^import (Mathlib|UDGRope)(\.|$)", p.name)

    def test_no_sorry_native_decide_or_axiom(self):
        for p in ROPE + GP_SIDE + [PROFILE]:
            src = code(p.read_text(encoding="utf-8"))
            for bad in (r"\bsorry\b", r"\bnative_decide\b", r"^\s*axiom\b", r"\bdecide\s*\+kernel\b"):
                self.assertIsNone(re.search(bad, src, re.M), f"{p.name}: {bad}")

    def test_lf_line_endings(self):
        for p in ROPE + GP_SIDE + [PROFILE, ROOT / "tools/encode-udg.py", ROOT / "tools/emit-udg-comparator.py"]:
            self.assertNotIn(b"\r\n", p.read_bytes(), p.name)

    def test_emitter_deterministic_and_faithful(self):
        with tempfile.TemporaryDirectory() as a, tempfile.TemporaryDirectory() as b:
            emit.main(["--out", a])
            emit.main(["--out", b])
            files = sorted(q.relative_to(a) for q in Path(a).rglob("*") if q.is_file())
            self.assertEqual(files, sorted(q.relative_to(b) for q in Path(b).rglob("*") if q.is_file()))
            committed = UDG / "Comparator"  # the pairs Comparator was run on (RESULTS.json) match the sources
            for f in files:
                self.assertEqual((Path(a) / f).read_bytes(), (Path(b) / f).read_bytes(), f)
                self.assertEqual((Path(a) / f).read_bytes(), (committed / f).read_bytes(), f)
            sol = (Path(a) / "GPUDGComparator/Solution.lean").read_text(encoding="utf-8")
            for p in emit.SOURCES:
                self.assertIn(emit.split_imports(p.read_text(encoding="utf-8"))[1], sol)
            self.assertNotIn("sorry", code(sol))
            self.assertEqual(len(list((Path(a) / "comparator").glob("ctl-*.json"))), len(emit.CHALLENGES))
            for name in emit.CHALLENGES:
                chal = (Path(a) / "GPUDGComparator" / name / "Challenge.lean").read_text(encoding="utf-8")
                self.assertEqual(code(chal).count("sorry"), 1, name)
                self.assertIn(emit.defs_body(), chal)

    def test_axioms(self):
        if not (BINDING / ".lake/build/lib/lean/GPBinding/UDG/Frame.olean").exists():
            self.skipTest("binding UDG modules not built")
        toolchain = Path(os.environ.get("ELAN_HOME", Path.home() / ".elan")) / "toolchains" / (
            BINDING / "lean-toolchain").read_text(encoding="utf-8").strip().replace("/", "--").replace(":", "---")
        lake = toolchain / "bin" / ("lake.exe" if os.name == "nt" else "lake")
        path = BINDING / "tmp" / "UDGAxioms.lean"
        path.parent.mkdir(exist_ok=True)
        path.write_bytes(AUDIT.format(imports="\n".join(f"import {m}" for m in MODULES),
                                      names=", ".join(f"`{m}" for m in MODULES)).encode("utf-8"))
        try:
            run = subprocess.run([str(lake), "env", "lean", "tmp/UDGAxioms.lean"], cwd=BINDING,
                                 capture_output=True, text=True, encoding="utf-8")
        finally:
            path.unlink(missing_ok=True)
        self.assertEqual(run.returncode, 0, run.stdout + run.stderr)
        body = run.stdout.split("AUDIT-BEGIN\n")[1].split("\nAUDIT-END")[0]
        rows = [r.split("\t") for r in body.splitlines() if r]
        names = {r[0] for r in rows}
        for thm in ("UDGRope.rhombus", "UDGRope.gadget0_tu", "UDGRope.gadget5_tu", "UDGRope.schade",
                    "GPBinding.UDG.tu_hereditary", "GPBinding.UDG.spine_sound", "GPBinding.UDG.udg_frame_iff",
                    "GPBinding.UDG.udg_system_iff", "GPBinding.UDG.candidate_isEmpty", "GPBinding.UDG.realize_sound",
                    "GPBinding.UDG.udg_realize", "GPBinding.UDG.coverComplete_of_all"):
            self.assertIn(thm, names)
        for name, axs in rows:
            used = set(axs.split(",")) - {""}
            self.assertTrue(used <= STANDARD, f"{name}: {used}")


if __name__ == "__main__":
    unittest.main()
