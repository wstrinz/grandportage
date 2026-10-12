"""Release plan A1: every command runs against the campaign statement bound at `init`; a deliberate
change is an explicit, versioned `restate` event, and a merge needs both branches to bind the same one."""
import importlib.util
import io
import json
from pathlib import Path
import shutil
import tempfile
import unittest
from contextlib import redirect_stderr, redirect_stdout

ROOT = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location("gp_statement_binding", ROOT / "tools/gp.py")
gp = importlib.util.module_from_spec(spec)
spec.loader.exec_module(gp)


class StatementBinding(unittest.TestCase):
    def setUp(self):
        self.dir = Path(tempfile.mkdtemp(prefix="gp-binding-"))
        self.addCleanup(shutil.rmtree, self.dir, ignore_errors=True)
        self.write({"name": "binding controls", "family": []})
        self.assertEqual(self.gp("init")[0], 0)

    def write(self, statement, where=None):
        (where or self.dir).joinpath("campaign.json").write_bytes(
            (json.dumps(statement, sort_keys=True) + "\n").encode("utf-8"))

    def gp(self, *args, where=None):
        out, err = io.StringIO(), io.StringIO()
        with redirect_stdout(out), redirect_stderr(err):
            code = gp.main(["--campaign", str(where or self.dir), *args])
        return code, out.getvalue() + err.getvalue()

    def test_version_is_reported_and_recorded(self):
        out = io.StringIO()
        with redirect_stdout(out), self.assertRaises(SystemExit):
            gp.main(["--version"])
        self.assertEqual(out.getvalue().strip(), f"gp {gp.GP_VERSION}")
        init = json.loads((self.dir / "ledger.jsonl").read_text(encoding="utf-8").splitlines()[0])
        self.assertEqual(init["gp_version"], gp.GP_VERSION)

    def test_bound_statement_accepted(self):
        code, out = self.gp("status")
        self.assertEqual(code, 0, out)

    def test_edited_statement_refused_until_restated(self):
        self.write({"name": "binding controls, edited", "family": []})
        code, out = self.gp("status")
        self.assertEqual(code, 1, out)
        self.assertIn("the campaign statement changed since it was bound", out)
        code, out = self.gp("restate", "--reason", "renamed the campaign")
        self.assertEqual(code, 0, out)
        self.assertIn("statement restated (version 2)", out)
        code, out = self.gp("status")
        self.assertEqual(code, 0, out)
        records = [json.loads(l) for l in (self.dir / "ledger.jsonl").read_text(encoding="utf-8").splitlines()]
        restate = [r for r in records if r["op"] == "restate"]
        self.assertEqual(len(restate), 1)
        self.assertEqual(restate[0]["old_sha256"], records[0]["statement_sha256"])
        self.assertEqual(restate[0]["reason"], "renamed the campaign")

    def test_restating_an_unchanged_statement_is_refused(self):
        code, out = self.gp("restate", "--reason", "no change")
        self.assertEqual(code, 1, out)
        self.assertIn("unchanged", out)

    def test_missing_statement_refused(self):
        (self.dir / "campaign.json").unlink()
        code, out = self.gp("status")
        self.assertEqual(code, 1, out)
        self.assertIn("missing", out)

    def test_reverting_the_edit_restores_acceptance(self):
        self.write({"name": "binding controls, edited", "family": []})
        self.assertEqual(self.gp("status")[0], 1)
        self.write({"name": "binding controls", "family": []})
        self.assertEqual(self.gp("status")[0], 0)

    def test_merge_needs_the_same_bound_statement(self):
        other = Path(tempfile.mkdtemp(prefix="gp-binding-branch-"))
        self.addCleanup(shutil.rmtree, other, ignore_errors=True)
        shutil.copy(self.dir / "campaign.json", other / "campaign.json")
        shutil.copy(self.dir / "ledger.jsonl", other / "ledger.jsonl")
        self.write({"name": "binding controls, branch", "family": []}, where=other)
        self.assertEqual(self.gp("restate", "--reason", "branch change", where=other)[0], 0)
        code, out = self.gp("merge", str(other))
        self.assertEqual(code, 1, out)
        self.assertIn("bind different versions of the campaign statement", out)


if __name__ == "__main__":
    unittest.main()
