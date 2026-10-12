"""Track E / R1b: comparator-emit reads supports filed by reference (`receipt_ref`), checked by SHA-256.

`gp submit` has filed receipts by reference since 2026-10-10 (tests/test_gp50_receipt_ref.py). The emitter
must read such a support's receipt from its campaign file, verify the recorded SHA-256, and emit exactly
what it emits for the same receipt inline. Controls: a tampered, missing or malformed reference refuses
the whole run (exit 2) and writes nothing. The committed 3P manifest is unchanged
(tests/test_gp50_comparator_emit.py).
"""
import contextlib
import hashlib
import importlib.util
import io
import json
import shutil
import tempfile
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
CAMPAIGN = ROOT / "campaigns/3p-matroids"
spec = importlib.util.spec_from_file_location("comparator_emit_refs", ROOT / "tools/comparator-emit.py")
E = importlib.util.module_from_spec(spec)
spec.loader.exec_module(E)


def canonical(receipt):
    """`gp`'s stored bytes for a receipt filed by reference (tools/gp.py `receipt_bytes`)."""
    return json.dumps(receipt, ensure_ascii=False, sort_keys=True).encode("utf-8")


def by_reference(src, dst, every=1):
    """Copy a campaign, turning every `every`-th support into a reference record, as `gp submit` files it."""
    shutil.copytree(src, dst, ignore=shutil.ignore_patterns("warrants"))
    lines, n = [], 0
    for line in (src / "ledger.jsonl").read_text(encoding="utf-8").splitlines():
        d = json.loads(line)
        if d["op"] == "support" and "receipt" in d:
            if n % every == 0:
                data = canonical(d.pop("receipt"))
                digest = hashlib.sha256(data).hexdigest()
                (dst / "receipts").mkdir(exist_ok=True)
                (dst / "receipts" / f"{digest}.json").write_bytes(data)
                d["receipt_ref"] = {"path": f"receipts/{digest}.json", "sha256": digest}
            n += 1
        lines.append(json.dumps(d, ensure_ascii=False, sort_keys=True))
    (dst / "ledger.jsonl").write_bytes(("\n".join(lines) + "\n").encode("utf-8"))
    return n


def emit(camp, out):
    err = io.StringIO()
    with contextlib.redirect_stdout(io.StringIO()), contextlib.redirect_stderr(err):
        code = E.main(["--campaign", str(camp), "--out", str(out)])
    files = {p.relative_to(out).as_posix(): p.read_bytes() for p in sorted(out.rglob("*")) if p.is_file()} \
        if out.exists() else {}
    return code, files, err.getvalue()


def refs(camp):
    return [json.loads(l) for l in (camp / "ledger.jsonl").read_text(encoding="utf-8").splitlines()
            if '"receipt_ref"' in l]


class ComparatorEmitReceiptRefs(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.tmp = Path(tempfile.mkdtemp())
        cls.camp = cls.tmp / "camp"
        cls.converted = by_reference(CAMPAIGN, cls.camp, every=2)
        code, cls.inline, _ = emit(CAMPAIGN, cls.tmp / "inline")
        assert code == 0
        code, cls.byref, _ = emit(cls.camp, cls.tmp / "byref")
        assert code == 0

    @classmethod
    def tearDownClass(cls):
        shutil.rmtree(cls.tmp, ignore_errors=True)

    def test_mixed_ledger_has_both_kinds(self):
        recs = [json.loads(l) for l in (self.camp / "ledger.jsonl").read_text(encoding="utf-8").splitlines()]
        sup = [r for r in recs if r["op"] == "support"]
        self.assertTrue(any("receipt_ref" in r for r in sup) and any("receipt" in r for r in sup))
        self.assertGreater(len(refs(self.camp)), 500)

    def test_same_emission_as_inline(self):
        self.assertEqual(sorted(self.byref), sorted(self.inline))
        for path, data in self.inline.items():
            if path != "MANIFEST.json":
                self.assertEqual(self.byref[path], data, path)
        a, b = json.loads(self.inline["MANIFEST.json"]), json.loads(self.byref["MANIFEST.json"])
        self.assertNotEqual(a["inputs"].pop("ledger_sha256"), b["inputs"].pop("ledger_sha256"))
        self.assertEqual(a, b)  # per-claim receipt_sha256 included

    def test_receipt_digest_falls_back_to_the_reference(self):
        raw, claims, sup = E.load_ledger(self.camp)

        def cls(k):
            try:
                return E.classify(k, claims, sup)
            except E.Refuse:
                return None
        k = next(k for k, s in sup.items() if "receipt_ref" in s and cls(k) == "point-s")
        s = dict(sup[k])
        del s["receipt_sha256"]
        x = E.build(k, "point-s", claims, {**sup, k: s}, self.camp,
                    E.load_encoder(ROOT / "tools/encode-matroid.py"))
        self.assertEqual(x["receipt_sha256"], s["receipt_ref"]["sha256"])

    def mutated(self, name, mutate):
        camp = self.tmp / name
        shutil.copytree(self.camp, camp)
        mutate(camp, refs(camp)[0])
        return camp

    def refused(self, camp, reason):
        with self.assertRaises(E.Custody) as cm:
            E.load_ledger(camp)
        self.assertIn(reason, str(cm.exception))
        out = self.tmp / f"{camp.name}-out"
        code, files, err = emit(camp, out)
        self.assertEqual(code, 2)
        self.assertIn(reason, err)
        self.assertEqual(files, {}, "a refused run writes nothing")

    def test_tampered_receipt_file_is_refused(self):
        def tamper(camp, r):
            p = camp / r["receipt_ref"]["path"]
            p.write_bytes(p.read_bytes() + b" ")  # still valid JSON, different bytes
        self.refused(self.mutated("tampered", tamper), "does not match its recorded SHA-256")

    def test_missing_receipt_file_is_refused(self):
        self.refused(self.mutated("missing", lambda camp, r: (camp / r["receipt_ref"]["path"]).unlink()),
                     "is missing")

    @staticmethod
    def rewrite(camp, r, new_ref, append=None):
        """Replace the first support record `r`'s reference with `new_ref`; optionally append a record."""
        lines = (camp / "ledger.jsonl").read_text(encoding="utf-8").splitlines()
        j = next(j for j, l in enumerate(lines) if json.loads(l) == r)
        lines[j] = json.dumps(dict(r, receipt_ref=new_ref), ensure_ascii=False, sort_keys=True)
        if append is not None:
            lines.append(json.dumps(append, ensure_ascii=False, sort_keys=True))
        (camp / "ledger.jsonl").write_bytes(("\n".join(lines) + "\n").encode("utf-8"))

    def test_malformed_references_are_refused(self):
        for i, bad in enumerate([{"path": "../x.json", "sha256": "0" * 64}, {"path": "receipts/a.json"},
                                 {"path": "C:/x.json", "sha256": "0" * 64},
                                 {"path": "receipts\\a.json", "sha256": "0" * 64},
                                 {"path": "receipts/a.json", "sha256": "A" * 64}, "receipts/a.json"]):
            camp = self.mutated(f"malformed{i}", lambda camp, r, bad=bad: self.rewrite(camp, r, bad))
            with self.assertRaises(E.Custody) as cm:
                E.load_ledger(camp)
            self.assertIn("malformed receipt reference", str(cm.exception))

    def test_superseded_reference_is_not_read(self):
        # A later support supersedes an earlier one, as in `gp`: only the accepted support's file is read.
        def supersede(camp, r):
            receipt = json.loads((camp / r["receipt_ref"]["path"]).read_bytes())
            later = {k: v for k, v in r.items() if k != "receipt_ref"} | {"receipt": receipt}
            self.rewrite(camp, r, {"path": "receipts/" + "0" * 64 + ".json", "sha256": "0" * 64}, later)
        camp = self.mutated("superseded", supersede)
        raw, claims, sup = E.load_ledger(camp)
        self.assertTrue(all("receipt" in s for s in sup.values()))
        self.assertEqual(sum("receipt_ref" in s for s in sup.values()), len(refs(self.camp)) - 1)


if __name__ == "__main__":
    unittest.main()
