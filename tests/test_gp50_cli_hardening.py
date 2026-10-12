"""Release hardening of `gp` (v0.50.0): gaps a newcomer hit while writing docs/USING-GP.md.

- Build feedback: the first build says so on stderr; a failed build is a refusal naming the target with the last
  lines of lake's output; a missing toolchain is a refusal with the elan install hint.
- `explain` names the stored receipt (receipts/<sha256>.json) and the submitted file, each labelled.
- Excluded primes print one way everywhere: "except {2, 3}" (filing, reach, status).
- The init record's schema must be one this gp reads; an unknown or missing schema is refused, also on merge.
- `--matroid` on a statement with no family is a refusal, not a KeyError.
- A characteristic-scoped system may omit `nonzero`; sign conditions there are refused, not dropped.
"""
import hashlib
import importlib.util
import io
import json
import os
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest
from contextlib import redirect_stderr, redirect_stdout
from unittest import mock

ROOT = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location("gp_cli_hardening", ROOT / "tools/gp.py")
gp = importlib.util.module_from_spec(spec)
spec.loader.exec_module(gp)

TWO_POINTS = {"variables": ["x"], "equations": ["x - 1", "x + 1"]}  # no "nonzero": none
EMPTY_Q = {"certificate": {"type": "ideal", "cofactors": ["-1/2", "1/2"], "m": 0, "k": 0}}


class Hardening(unittest.TestCase):
    def setUp(self):
        self.tmp = Path(tempfile.mkdtemp())
        self.addCleanup(shutil.rmtree, self.tmp, ignore_errors=True)
        self.dir = self.tmp / "campaign"
        self.dir.mkdir()
        self.write("campaign.json", {"name": "hardening", "family": []}, where=self.dir)

    def write(self, name, body, where=None, indent=None):
        path = (where or self.tmp) / name
        path.write_bytes((json.dumps(body, indent=indent) + "\n").encode("utf-8"))
        return str(path)

    def gp(self, *args, where=None):
        out, err = io.StringIO(), io.StringIO()
        with redirect_stdout(out), redirect_stderr(err):
            code = gp.main(["--campaign", str(where or self.dir), *args])
        return code, out.getvalue(), err.getvalue()

    def ok(self, *args, where=None):
        code, out, err = self.gp(*args, where=where)
        self.assertEqual(code, 0, out + err)
        return out

    def no(self, *args, where=None):
        code, out, err = self.gp(*args, where=where)
        self.assertEqual(code, 1, out + err)
        self.assertTrue(err.startswith("refused: "), err)
        self.assertNotIn("Traceback", out + err)
        return err

    # --- build feedback ---

    def fake_toolchain(self):
        pin = (gp.PROFILE / "lean-toolchain").read_text(encoding="utf-8").strip()
        lake = self.tmp / "elan/toolchains" / pin.replace("/", "--").replace(":", "---") / (
            "bin/lake" + (".exe" if os.name == "nt" else ""))
        lake.parent.mkdir(parents=True)
        lake.write_bytes(b"")
        return lake

    def test_build_announced_and_stamped(self):
        lake = self.fake_toolchain()
        exe = self.tmp / "bin/gp_ledger.exe"  # missing: the first build
        calls = []

        def run(argv, **kw):
            calls.append(argv)
            return subprocess.CompletedProcess(argv, 0, b"Build completed successfully.\n", b"")
        err = io.StringIO()
        with mock.patch.object(gp, "ELAN_HOME", self.tmp / "elan"), mock.patch.object(gp, "_announced", False), \
                mock.patch.object(gp.subprocess, "run", run), redirect_stderr(err):
            exe.parent.mkdir()
            gp.lake_build("gp_ledger", exe)
            gp.lake_build("gp_ledger3", exe.with_name("gp_ledger3.exe"))
        self.assertEqual(err.getvalue(), "building the GP runners (one-time, several minutes)…\n")  # once
        self.assertEqual(calls, [[str(lake), "build", "gp_ledger"], [str(lake), "build", "gp_ledger3"]])
        self.assertTrue(gp.stamp_path(exe).exists())

    def test_build_failure_is_a_refusal(self):
        self.fake_toolchain()
        lines = b"".join(b"info: step %d\n" % i for i in range(30)) + \
            b"error: GPProfile/Ledger.lean:3:0: unknown identifier 'oops'\n"

        def run(argv, **kw):
            return subprocess.CompletedProcess(argv, 1, lines, b"error: build failed\n")
        self.ok("init")
        with mock.patch.object(gp, "ELAN_HOME", self.tmp / "elan"), mock.patch.object(gp, "_built", False), \
                mock.patch.object(gp, "_announced", True), mock.patch.object(gp, "stale", lambda exe=gp.EXE: True), \
                mock.patch.object(gp.subprocess, "run", run):
            err = self.no("status")  # (the announcement is test_build_announced_and_stamped's)
        self.assertIn("refused: building the runner gp_ledger failed (lake build exited 1) [rule: runner build", err)
        self.assertIn("smallest fix: run `lake build gp_ledger` in", err)
        tail = err.split("lake's last lines:\n", 1)[1].splitlines()
        self.assertEqual(len(tail), gp.BUILD_TAIL)
        self.assertEqual(tail[-2:], ["  error: GPProfile/Ledger.lean:3:0: unknown identifier 'oops'",
                                     "  error: build failed"])
        self.assertNotIn("CalledProcessError", err)

    def test_missing_toolchain_is_a_refusal(self):
        self.ok("init")
        with mock.patch.object(gp, "ELAN_HOME", self.tmp / "no-elan"), mock.patch.object(gp, "_built", False), \
                mock.patch.object(gp, "stale", lambda exe=gp.EXE: True):
            err = self.no("status")
        self.assertIn("refused: the GP runners need the Lean toolchain leanprover/lean4:", err)
        self.assertIn("which is not installed", err)
        self.assertIn("smallest fix: install elan (https://github.com/leanprover/elan), then run `lake build "
                      "gp_ledger gp_ledger3`", err)

    # --- explain, scope text ---

    def test_explain_names_stored_and_submitted_receipts(self):
        self.ok("init")
        self.ok("claim", "distinct-q", "--system", self.write("two.json", TWO_POINTS), "--kind", "EMPTY", "--char0")
        submitted = self.write("empty-q.json", EMPTY_Q, indent=2)  # not canonical bytes
        self.ok("submit", "distinct-q", submitted)
        stored = hashlib.sha256(gp.receipt_bytes(EMPTY_Q)).hexdigest()
        filed = hashlib.sha256(Path(submitted).read_bytes()).hexdigest()
        self.assertNotEqual(stored, filed)
        self.assertTrue((self.dir / "receipts" / f"{stored}.json").is_file())
        out = self.ok("explain", "distinct-q")
        self.assertIn(f"by ideal certificate (stored receipt {stored[:12]}, submitted file {filed[:12]}), reach 0 and "
                      "every prime except {2}", out)
        # A receipt gp files itself (a goal rule) is submitted as its canonical bytes: one hash, shown once.
        support = gp.Ledger(self.dir).supports()[gp.Ledger(self.dir).claim("distinct-q")["key"]]
        self.assertEqual(gp.receipt_ids(dict(support, receipt_sha256=stored)), f"stored receipt {stored[:12]}")

    def test_excluded_primes_print_one_way(self):
        self.ok("init")
        system = self.write("two.json", TWO_POINTS)
        out = self.ok("claim", "odd", "--system", system, "--kind", "EMPTY", "--outside", "3,2")
        self.assertIn("filed: EMPTY at characteristic 0 and every prime except {2, 3}; open", out)
        out = self.ok("submit", "odd", self.write("empty-q.json", EMPTY_Q))
        self.assertEqual(out.strip(), "held: odd at characteristic 0 and every prime except {2, 3}; "
                                      "earned, unclaimed: 0 and every prime except {2}")
        out = self.ok("status")
        self.assertIn("characteristic 0 and every prime except {2, 3}; earned, unclaimed: 0 and every prime except {2}",
                      out)
        self.assertEqual(gp.CharSet(True, True, [5, 3]).text(), "every characteristic except {3, 5}")
        self.assertNotIn("except [", out)

    # --- schema, family, system files ---

    def test_unknown_schema_refused(self):
        self.ok("init")
        path = self.dir / "ledger.jsonl"
        good = path.read_bytes()
        self.ok("status")
        for schema, why in (("gp-ledger/v2", "the ledger's schema is 'gp-ledger/v2'; gp "),
                            (None, "the ledger's init record names no schema; gp ")):
            init = json.loads(good)
            init.pop("schema")
            if schema:
                init["schema"] = schema
            path.write_bytes((json.dumps(init, sort_keys=True) + "\n").encode("utf-8"))
            for command in (("status",), ("frontier",), ("restate", "--reason", "x")):
                err = self.no(*command)
                self.assertIn(why, err)
                self.assertIn("[rule: ledger schema", err)
        # merge checks the other branch's schema too
        other = self.tmp / "other"
        shutil.copytree(self.dir, other)
        path.write_bytes(good)
        err = self.no("merge", str(other))
        self.assertIn("the ledger's init record names no schema", err)
        self.assertEqual(path.read_bytes(), good)

    def test_matroid_without_family_refused(self):
        self.write("campaign.json", {"name": "no family"}, where=self.dir)
        self.ok("init")
        err = self.no("claim", "m", "--matroid", "Fano", "--kind", "EMPTY", "--char0")
        self.assertIn("refused: --matroid Fano: the campaign statement has no family [rule: campaign statement", err)
        self.write("campaign.json", {"name": "bad family", "family": {"matroids": []}}, where=self.dir)
        self.ok("restate", "--reason", "family")
        err = self.no("claim", "m", "--matroid", "Fano", "--kind", "EMPTY", "--char0")
        self.assertIn("the campaign statement's family is not a list of stages", err)

    def test_system_files(self):
        self.ok("init")
        out = self.ok("claim", "two", "--system", self.write("two.json", TWO_POINTS), "--kind", "EMPTY", "--char0")
        self.assertIn("filed: EMPTY at characteristic 0; open", out)
        self.assertEqual(gp.Ledger(self.dir).claim("two")["system"]["nonzero"], [])
        signed = self.write("signed.json", dict(TWO_POINTS, signs=[["x", ">0"]]))
        err = self.no("claim", "signed", "--system", signed, "--kind", "EMPTY", "--char0")
        self.assertIn("sign conditions are read only over ℝ", err)
        err = self.no("claim", "nothing", "--system", str(self.tmp / "missing.json"), "--kind", "EMPTY", "--char0")
        self.assertIn("cannot read the system file", err)
        err = self.no("claim", "novars", "--system", self.write("nv.json", {"equations": ["x"]}), "--kind", "EMPTY",
                      "--char0")
        self.assertIn("the system file needs variables and equations", err)


if __name__ == "__main__":
    unittest.main()
