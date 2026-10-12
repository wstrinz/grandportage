"""ud22 performance (DECISIONS 2026-10-10): receipts filed by reference, with their controls.

`gp submit` files a held receipt as receipts/<sha256>.json and the support record carries
{"receipt_ref": {"path", "sha256"}} instead of the inline body. Every command reads the file back
and checks its SHA-256 before anything folds. Controls:

- a tampered receipt file is refused, and so is a missing one or a malformed reference;
- an inline support record (every ledger before this change) still holds;
- the merge guard compares receipts by SHA-256 (an inline receipt and a reference to the same bytes
  agree), copies the other branch's receipt files after checking them, and refuses a tampered one.
"""
import hashlib
import importlib.util
import io
import json
from pathlib import Path
import shutil
import tempfile
import unittest
from contextlib import redirect_stderr, redirect_stdout

ROOT = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location("gp_cli_receipt_ref", ROOT / "tools/gp.py")
gp = importlib.util.module_from_spec(spec)
spec.loader.exec_module(gp)

SYSTEMS = {"sx": {"variables": ["x"], "equations": ["x - 1"], "nonzero": []},
           "sy": {"variables": ["y"], "equations": ["y - 2"], "nonzero": []}}


def point(**values):
    return {"certificate": {"type": "point", "point": {k: str(v) for k, v in values.items()}}}


class ReceiptRef(unittest.TestCase):
    def setUp(self):
        self.tmp = Path(tempfile.mkdtemp())
        self.files = self.tmp / "files"
        self.files.mkdir()
        for name, system in SYSTEMS.items():
            (self.files / f"{name}.json").write_text(json.dumps(system), encoding="utf-8")
        self.base = self.tmp / "base"
        self.base.mkdir()
        shutil.copy(ROOT / "campaigns/3p-matroids/campaign.json", self.base / "campaign.json")
        self.ok(self.base, "init")

    def tearDown(self):
        shutil.rmtree(self.tmp, ignore_errors=True)

    def gp(self, where, *args):
        out, err = io.StringIO(), io.StringIO()
        with redirect_stdout(out), redirect_stderr(err):
            code = gp.main(["--campaign", str(where), *args])
        return code, out.getvalue() + err.getvalue()

    def ok(self, where, *args):
        code, out = self.gp(where, *args)
        self.assertEqual(code, 0, out)
        return out

    def refused(self, where, reason, *args):
        before = (where / "ledger.jsonl").read_bytes()
        code, out = self.gp(where, *args)
        self.assertEqual(code, 1, out)
        self.assertIn(reason, out)
        self.assertEqual((where / "ledger.jsonl").read_bytes(), before, "a refusal never writes the ledger")

    def claim(self, where, label, system):
        return self.ok(where, "claim", label, "--system", str(self.files / f"{system}.json"),
                       "--kind", "NONEMPTY", "--char0")

    def submit(self, where, label, receipt):
        path = self.files / f"{where.name}-{label}.json"
        path.write_text(json.dumps(receipt), encoding="utf-8")
        return self.ok(where, "submit", label, str(path))

    def records(self, where, op):
        return [r for r in gp.Ledger(where).records if r["op"] == op]

    def status_line(self, where, label):
        return next(l for l in self.ok(where, "status").splitlines() if f" {label} " in l)

    def forge(self, where, record):
        with (where / "ledger.jsonl").open("ab") as f:
            f.write((json.dumps(dict(record, at="2026-10-10T00:00:00Z"), sort_keys=True) + "\n").encode("utf-8"))

    def test_new_support_is_filed_by_reference(self):
        self.claim(self.base, "a", "sx")
        self.submit(self.base, "a", point(x=1))
        (s,) = self.records(self.base, "support")
        self.assertNotIn("receipt", s)
        ref = s["receipt_ref"]
        data = (self.base / ref["path"]).read_bytes()
        self.assertEqual(ref["path"], f"receipts/{ref['sha256']}.json")
        self.assertEqual(hashlib.sha256(data).hexdigest(), ref["sha256"])
        self.assertEqual(json.loads(data), point(x=1))
        self.assertTrue(self.status_line(self.base, "a").startswith("held"))
        self.assertEqual(gp.Ledger(self.base).supports()[s["key"]]["receipt"], point(x=1))

    def test_tampered_file_is_refused(self):
        self.claim(self.base, "a", "sx")
        self.submit(self.base, "a", point(x=1))
        path = self.base / self.records(self.base, "support")[0]["receipt_ref"]["path"]
        path.write_bytes(json.dumps(point(x=2), sort_keys=True).encode("utf-8"))
        for command in (["status"], ["explain", "a"], ["frontier"]):
            self.refused(self.base, "does not match its recorded SHA-256", *command)
        path.write_bytes(path.read_bytes() + b" ")  # a byte of whitespace is tampering too
        self.refused(self.base, "does not match its recorded SHA-256", "status")

    def test_missing_file_is_refused(self):
        self.claim(self.base, "a", "sx")
        self.submit(self.base, "a", point(x=1))
        (self.base / self.records(self.base, "support")[0]["receipt_ref"]["path"]).unlink()
        self.refused(self.base, "is missing", "status")
        self.refused(self.base, "is missing", "explain", "a")

    def test_malformed_reference_is_refused(self):
        self.claim(self.base, "a", "sx")
        self.submit(self.base, "a", point(x=1))
        s = self.records(self.base, "support")[0]
        outside = self.tmp / "outside.json"
        outside.write_bytes(gp.receipt_bytes(point(x=1)))
        digest = s["receipt_ref"]["sha256"]
        for ref in ({"path": "../outside.json", "sha256": digest}, {"path": str(outside), "sha256": digest},
                    {"path": s["receipt_ref"]["path"], "sha256": digest.upper()}, {"path": s["receipt_ref"]["path"]}):
            where = self.tmp / f"m{len(list(self.tmp.iterdir()))}"
            shutil.copytree(self.base, where)
            self.forge(where, {k: v for k, v in s.items() if k != "at"} | {"receipt_ref": ref})
            self.refused(where, "malformed receipt reference", "status")

    def test_inline_support_still_holds(self):
        self.claim(self.base, "a", "sx")
        key = gp.Ledger(self.base).claim("a")["key"]
        digest = hashlib.sha256(json.dumps(point(x=1)).encode("utf-8")).hexdigest()
        self.forge(self.base, {"op": "support", "label": "a", "key": key, "receipt": point(x=1),
                               "receipt_sha256": digest, "reach": None})
        self.assertTrue(self.status_line(self.base, "a").startswith("held"))
        self.assertEqual(gp.Ledger(self.base).supports()[key]["receipt"], point(x=1))
        # An inline receipt that does not replay is still refused by the fold.
        self.forge(self.base, {"op": "support", "label": "a", "key": key, "receipt": point(x=2),
                               "receipt_sha256": digest, "reach": None})
        self.assertFalse(self.status_line(self.base, "a").startswith("held"))

    def test_merge_copies_checked_receipt_files(self):
        self.claim(self.base, "a", "sx")
        a, b = self.tmp / "a", self.tmp / "b"
        shutil.copytree(self.base, a)
        shutil.copytree(self.base, b)
        self.claim(b, "b", "sy")
        self.submit(b, "b", point(y=2))
        ref = self.records(b, "support")[0]["receipt_ref"]
        # A tampered file on the other branch is refused before anything lands.
        good = (b / ref["path"]).read_bytes()
        (b / ref["path"]).write_bytes(good.replace(b'"2"', b'"3"'))
        self.refused(a, "does not match its recorded SHA-256", "merge", str(b))
        self.assertFalse((a / ref["path"]).exists())
        (b / ref["path"]).write_bytes(good)
        self.assertIn("the merged log folds", self.ok(a, "merge", str(b)))
        self.assertEqual((a / ref["path"]).read_bytes(), good)
        self.assertTrue(self.status_line(a, "b").startswith("held"))

    def test_merge_compares_receipts_by_sha256(self):
        self.claim(self.base, "a", "sx")
        a, b = self.tmp / "a", self.tmp / "b"
        shutil.copytree(self.base, a)
        shutil.copytree(self.base, b)
        key = gp.Ledger(a).claim("a")["key"]
        # Branch a holds the receipt inline (as filed before references); b files the same bytes by
        # reference. Same SHA-256, so the same receipt: the merge lands.
        self.forge(a, {"op": "support", "label": "a", "key": key, "receipt": point(x=1),
                       "receipt_sha256": "0" * 64, "reach": None})
        self.submit(b, "a", point(x=1))
        self.assertIn("the merged log folds", self.ok(a, "merge", str(b)))
        # The other way round, ours by reference is restated last, as filed: no inline body.
        e, f = self.tmp / "e", self.tmp / "f"
        shutil.copytree(self.base, e)
        shutil.copytree(self.base, f)
        self.submit(e, "a", point(x=1))
        self.forge(f, {"op": "support", "label": "a", "key": key, "receipt": point(x=1),
                       "receipt_sha256": "0" * 64, "reach": None})
        self.assertIn("the merged log folds", self.ok(e, "merge", str(f)))
        last = [r for r in self.records(e, "support")][-1]
        self.assertIn("receipt_ref", last)
        self.assertNotIn("receipt", last)
        self.assertTrue(self.status_line(e, "a").startswith("held"))
        # Different receipts under one claim on two branches are still refused.
        c, d = self.tmp / "c", self.tmp / "d"
        shutil.copytree(self.base, c)
        shutil.copytree(self.base, d)
        self.submit(c, "a", point(x=1))
        self.forge(d, {"op": "support", "label": "a", "key": key, "receipt": point(x="2/2"),
                       "receipt_sha256": "1" * 64, "reach": None})
        self.refused(c, "conflicting warrant contents", "merge", str(d))


if __name__ == "__main__":
    unittest.main()
