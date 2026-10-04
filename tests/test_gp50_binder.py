"""G1 decision 2 / Addendum A4: generated theorem warrants, the binder's records, and their use."""
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

EXE_SUFFIX = ".exe" if __import__("os").name == "nt" else ""
ELAN_HOME = Path(__import__("os").environ.get("ELAN_HOME") or Path.home() / ".elan")
ROOT = Path(__file__).resolve().parents[1]
PROFILE = ROOT / "profile"
RUNNER = PROFILE / (".lake/build/bin/gp_corpus_run" + EXE_SUFFIX)
RECORDS = ROOT / "reports/PHASE-3A-BINDER.json"
GENERATED = ROOT / "binding/GPBinding/Warrants/Generated.lean"
STANDARD = {"propext", "Quot.sound", "Classical.choice"}
BINDING = ROOT / "binding"
TOOLCHAIN = ELAN_HOME / "toolchains" / (PROFILE / "lean-toolchain").read_text(
    encoding="utf-8").strip().replace("/", "--").replace(":", "---")


def fnv1a(data: bytes) -> int:
    h = 0xcbf29ce484222325
    for b in data:
        h = ((h ^ b) * 0x100000001b3) & 0xFFFFFFFFFFFFFFFF
    return h


def run(*args):
    return json.loads(subprocess.run([str(RUNNER), str(ROOT), *map(str, args)], check=True,
                                     capture_output=True, text=True, encoding="utf-8").stdout)


class BinderTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        env = dict(os.environ, PATH=str(TOOLCHAIN / "bin") + os.pathsep + os.environ["PATH"])
        subprocess.run([str(TOOLCHAIN / ("bin/lake" + EXE_SUFFIX)), "build", "gp_corpus_run"], cwd=PROFILE,
                       env=env, check=True, capture_output=True)

    def test_generated_warrants_are_current(self):
        cands = run(PROFILE / "slice/manifest.json", "--candidates") + \
            run(PROFILE / "slice/corpus-3a.json", "--candidates")
        with tempfile.TemporaryDirectory() as d:
            src = Path(d) / "cands.json"
            src.write_text(json.dumps(cands, ensure_ascii=False), encoding="utf-8")
            out = Path(d) / "Generated.lean"
            subprocess.run([sys.executable, str(ROOT / "tools/gen-warrants.py"), str(src), "--out", str(out)],
                           check=True, capture_output=True)
            self.assertEqual(out.read_text(encoding="utf-8"), GENERATED.read_text(encoding="utf-8"))

    def test_records_are_bound_with_standard_axioms(self):
        records = json.loads(RECORDS.read_text(encoding="utf-8"))["records"]
        self.assertTrue(records)
        for r in records:
            with self.subTest(declaration=r["declaration"]):
                self.assertTrue(r["bound"])
                self.assertLessEqual(set(r["axioms"]), STANDARD)

    def test_receipt_is_schema_v2_with_registry_audit(self):
        receipt = json.loads(RECORDS.read_text(encoding="utf-8"))
        self.assertEqual(receipt["schema"], "gp-binder/v2")
        self.assertLessEqual(set(receipt["registryAxioms"]), STANDARD)
        for r in receipt["records"]:
            with self.subTest(declaration=r["declaration"]):
                self.assertTrue(r["proofIsNamedConstant"])
                self.assertTrue(r["wellFormed"])

    def test_receipt_environment_is_current(self):
        env = json.loads(RECORDS.read_text(encoding="utf-8"))["environment"]
        toolchain = (BINDING / "lean-toolchain").read_text(encoding="utf-8").strip()
        self.assertTrue(toolchain.endswith(env["toolchain"]))
        manifest = json.loads((BINDING / "lake-manifest.json").read_text(encoding="utf-8"))
        mathlib = next(p["rev"] for p in manifest["packages"] if p["name"] == "mathlib")
        self.assertEqual(env["mathlib"], mathlib)
        self.assertEqual(env["warrantModuleFnv1a"], str(fnv1a(GENERATED.read_bytes())))

    def test_canonical_identity_is_golden(self):
        # Binding identity is canonical JSON, not `repr` (G3a review, binder hole b).
        records = {r["declaration"]: r for r in json.loads(RECORDS.read_text(encoding="utf-8"))["records"]}
        c01 = records["GPBinding.Warrants.w_GP_C01_1"]
        self.assertEqual(c01["statementHash"], '[["x"],[[[[1],"1/1"]],[[[0],"1/1"],[[1],"-1/1"]]],[],["EMPTY"]]')
        self.assertEqual(c01["scopeHash"], '[true,"cofinite",[]]')

    def test_warrants_are_minted_at_computed_reach(self):
        # G3a review §5: warrants cover the receipt's reach, not only characteristic 0.
        records = {r["declaration"]: r for r in json.loads(RECORDS.read_text(encoding="utf-8"))["records"]}
        self.assertEqual(records["GPBinding.Warrants.w_GP_X125_1"]["scopeHash"], '[true,"cofinite",[2,23]]')

    def test_minted_theorem_warrants_support_their_claims(self):
        out = run(PROFILE / "slice/manifest.json", "--binder", RECORDS)
        minted = [t for c in out["cases"] for t in c.get("theorem_warrants", [])]
        self.assertTrue(minted)
        self.assertTrue(all(t["supported"] for t in minted))
        self.assertEqual(out["agree"], out["case_count"])

    def test_tampered_record_mints_nothing(self):
        records = json.loads(RECORDS.read_text(encoding="utf-8"))
        for r in records["records"]:
            r["scopeHash"] = r["scopeHash"].replace("true", "false")
        with tempfile.TemporaryDirectory() as d:
            path = Path(d) / "tampered.json"
            path.write_text(json.dumps(records), encoding="utf-8")
            out = run(PROFILE / "slice/manifest.json", "--binder", path)
        self.assertFalse([t for c in out["cases"] for t in c.get("theorem_warrants", [])])

    def test_foreign_environment_is_refused(self):
        for key, value in [("toolchain", "4.0.0"), ("mathlib", "0" * 40), ("warrantModuleFnv1a", "1")]:
            with self.subTest(key=key):
                records = json.loads(RECORDS.read_text(encoding="utf-8"))
                records["environment"][key] = value
                with tempfile.TemporaryDirectory() as d:
                    path = Path(d) / "foreign.json"
                    path.write_text(json.dumps(records), encoding="utf-8")
                    out = run(PROFILE / "slice/manifest.json", "--binder", path)
                self.assertEqual(out["binder_refused"], [key])
                self.assertFalse([t for c in out["cases"] for t in c.get("theorem_warrants", [])])


if __name__ == "__main__":
    unittest.main()
