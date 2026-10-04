"""G3a review §7 (ruling 6): instantiation fixtures are current, signed, and fail closed when stale."""
import json
import os
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest

EXE_SUFFIX = ".exe" if __import__("os").name == "nt" else ""
ELAN_HOME = Path(__import__("os").environ.get("ELAN_HOME") or Path.home() / ".elan")
ROOT = Path(__file__).resolve().parents[1]
PROFILE = ROOT / "profile"
RUNNER = PROFILE / (".lake/build/bin/gp_corpus_run" + EXE_SUFFIX)
FIXTURES = json.loads((ROOT / "corpus/INSTANTIATIONS.json").read_text(encoding="utf-8"))["fixtures"]
TOOLCHAIN = ELAN_HOME / "toolchains" / (PROFILE / "lean-toolchain").read_text(
    encoding="utf-8").strip().replace("/", "--").replace(":", "---")


def fnv1a(data: bytes) -> int:
    h = 0xcbf29ce484222325
    for b in data:
        h = ((h ^ b) * 0x100000001b3) & 0xFFFFFFFFFFFFFFFF
    return h


class FixtureTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        env = dict(os.environ, PATH=str(TOOLCHAIN / "bin") + os.pathsep + os.environ["PATH"])
        subprocess.run([str(TOOLCHAIN / ("bin/lake" + EXE_SUFFIX)), "build", "gp_corpus_run"], cwd=PROFILE,
                       env=env, check=True, capture_output=True)

    def test_fixtures_match_case_bytes(self):
        for f in FIXTURES:
            with self.subTest(case=f["id"]):
                self.assertEqual(f["case_fnv1a"], str(fnv1a((ROOT / f["case_path"]).read_bytes())))

    def test_fixtures_are_signed(self):
        changes = (ROOT / "corpus/CHANGES.md").read_text(encoding="utf-8")
        for f in FIXTURES:
            with self.subTest(case=f["id"]):
                self.assertIn(f["id"], changes)

    def test_fixtures_decide_their_cases(self):
        manifest = {"schema": "gp-3a-corpus-manifest/v1", "cases": [{"path": f["case_path"]} for f in FIXTURES]}
        with tempfile.TemporaryDirectory() as d:
            path = Path(d) / "fixtures.json"
            path.write_text(json.dumps(manifest), encoding="utf-8")
            out = json.loads(subprocess.run([str(RUNNER), str(ROOT), str(path)], check=True,
                                            capture_output=True, text=True, encoding="utf-8").stdout)
        for case in out["cases"]:
            with self.subTest(case=case["id"]):
                self.assertTrue(case["instantiated"])
                self.assertEqual(case["observed"], case["expected"])

    def test_stale_fixture_fails_closed(self):
        f = FIXTURES[0]
        with tempfile.TemporaryDirectory() as d:
            root = Path(d)
            (root / "corpus").mkdir()
            shutil.copy(ROOT / "corpus/INSTANTIATIONS.json", root / "corpus/INSTANTIATIONS.json")
            case = root / f["case_path"]
            case.parent.mkdir(parents=True, exist_ok=True)
            case.write_bytes((ROOT / f["case_path"]).read_bytes() + b"\n")
            manifest = root / "m.json"
            manifest.write_text(json.dumps({"schema": "gp-3a-corpus-manifest/v1",
                                            "cases": [{"path": f["case_path"]}]}), encoding="utf-8")
            run = subprocess.run([str(RUNNER), str(root), str(manifest)], capture_output=True, text=True)
        self.assertNotEqual(run.returncode, 0)
        self.assertIn("stale instantiation fixture", run.stderr)


if __name__ == "__main__":
    unittest.main()
