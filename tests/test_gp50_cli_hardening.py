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

    def test_matroid_path_refused(self):
        # 3P friction (F0-fano): a path where a family name belongs; the fix names the matroid, not a path.
        self.ok("init")
        err = self.no("claim", "m", "--matroid", "matroids/F7.json", "--kind", "EMPTY", "--char0")
        self.assertIn("--matroid takes a family name, not a path: 'matroids/F7.json'", err)
        self.assertIn("pass the name, for example --matroid F7", err)
        self.assertNotIn(".json.json", err)

    def test_matroid_record_read_in_full(self):
        # 0.50 Trials C3a: a rank-9 record (a rank and an F2 matrix) was filed as U(3,18), its extra keys
        # ignored. Keys the encoder would not read are refused; U(3, n) needs an explicit "lines": [].
        self.ok("init")
        (self.dir / "matroids").mkdir()
        self.write("larson.json", {"name": "larson", "source": "arXiv 2607.02208", "rank": 9,
                                   "matrix": ["111"], "elements": [str(i) for i in range(1, 19)]},
                   where=self.dir / "matroids")
        err = self.no("claim", "l", "--matroid", "larson", "--kind", "EMPTY", "--char", "2")
        self.assertIn("matrix, rank are not read: --matroid takes simple rank-3 matroids", err)
        self.assertIn("as a --system claim", err)
        self.write("u34.json", {"name": "u34", "source": "uniform", "elements": ["1", "2", "3", "4"]},
                   where=self.dir / "matroids")
        err = self.no("claim", "u", "--matroid", "u34", "--kind", "NONEMPTY", "--char0")
        self.assertIn("the record has no lines", err)
        self.write("u34.json", {"name": "u34", "source": "uniform", "elements": ["1", "2", "3", "4"], "lines": []},
                   where=self.dir / "matroids")
        self.ok("claim", "u", "--matroid", "u34", "--kind", "NONEMPTY", "--char0")
        # A record that stops being read in full (filed before v0.50.1, or edited since) does not take the
        # ledger down: that claim's ENCODING-FRAME stays OPEN, with a notice, and the rest stays usable.
        self.ok("claim", "two", "--system", self.write("two.json", TWO_POINTS), "--kind", "EMPTY", "--char0")
        self.write("u34.json", {"name": "u34", "source": "uniform", "elements": ["1", "2", "3", "4"], "lines": [],
                                "rank": 3}, where=self.dir / "matroids")
        out = self.ok("status")
        self.assertIn("two", out)
        self.assertIn("unread   u: matroids/u34.json: rank is not read", out)
        self.assertIn("its ENCODING-FRAME stays OPEN, so it is not a claim about matroid 'u34'", out)

    def test_unparsable_text_refused_at_filing_and_target_from_file(self):
        # 0.50 Trials C3b: `--target @file` was filed unparsed. Text that does not parse is refused at filing, and
        # --target @FILE reads a long target from a file.
        self.ok("init")
        system = self.write("x.json", {"variables": ["x"], "equations": ["x^2 - 1"]})
        err = self.no("claim", "t", "--system", system, "--kind", "IN_IDEAL", "--target", "x^4 @ 1", "--char0")
        self.assertIn("a polynomial text does not parse (target: unexpected character '@')", err)
        bad = self.write("y.json", {"variables": ["x"], "equations": ["x^2 - y"]})
        err = self.no("claim", "u", "--system", bad, "--kind", "EMPTY", "--char0")
        self.assertIn("(equations[0]: undeclared variable: y)", err)
        (self.tmp / "target.txt").write_bytes(b"x^4 - 1\n")
        self.ok("claim", "t", "--system", system, "--kind", "IN_IDEAL", "--target", "@" + str(self.tmp / "target.txt"),
                "--char0")
        self.assertEqual(gp.Ledger(self.dir).claim("t")["target"], "x^4 - 1")
        err = self.no("claim", "v", "--system", system, "--kind", "IN_IDEAL", "--target", "@" + str(self.tmp / "no.txt"),
                      "--char0")
        self.assertIn("no such file", err)

    def test_one_unparsable_claim_does_not_stop_the_ledger(self):
        # A claim filed before that check (its text does not parse) is set aside: not held, with a notice; the
        # rest folds, and a sound receipt for another claim is held (C3b: six sound receipts were refused).
        self.ok("init")
        self.ok("claim", "two", "--system", self.write("two.json", TWO_POINTS), "--kind", "EMPTY", "--char0")
        body = {"label": "old", "matroid": None, "system": {"variables": ["x"], "equations": ["x^2 - 1"],
                                                            "nonzero": []},
                "kind": "IN_IDEAL", "target": "@target.txt", "scope": {"char0": True}, "inputs": ["system:0"],
                "named_premises": []}
        with (self.dir / "ledger.jsonl").open("a", encoding="utf-8", newline="\n") as f:
            f.write(json.dumps(dict({"op": "claim", "key": 4242}, **body)) + "\n")
        out = self.ok("status")
        self.assertIn("unparsed old: target: unexpected character '@' does not parse; it is not held", out)
        self.ok("frontier")
        out = self.ok("submit", "two", self.write("q.json", EMPTY_Q))
        self.assertIn("held", out)

    def test_real_point_names_the_failing_condition(self):
        # A campaign's friction log: a refused real point names the system file's entry that fails.
        self.ok("init")
        system = self.write("neg.json", {"variables": ["x"], "equations": ["x^2 - 2"], "signs": [["x", "<0"]]})
        self.ok("claim", "neg-root", "--system", system, "--kind", "NONEMPTY", "--real")
        receipt = self.write("pos.json", {"certificate": {"type": "real_point", "symbol": "w", "polynomial": "w^2 - 2",
                                                          "interval": ["1", "2"], "point": {"x": "w"}}})
        code, out, err = self.gp("submit", "neg-root", receipt)
        self.assertEqual(code, 1, out + err)
        self.assertIn("signs[0] is positive at the point; it must be negative", out + err)

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
