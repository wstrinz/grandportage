"""GP 0.55 Lane P: a recorded-only `citation` warrant kind and `gp claim --batch`, on the Mathlib-free fixture package of
tests/test_gp50_lanep.py (A, B, C; the prose "second review"; A-of-B, B-held, B-of-C, C-held).

1. `gp submit L --citation REF [--theorem-number N] [--locator TEXT] [--doi DOI] [--file P] [--condition H]...`: a
   published result, shown as "citation: REF, Thm N" at tier 5 (the rung of a complete hand proof), never holding a
   claim; [CITED] presentations are judged by OVERSTATED like every recorded tier; a local copy of the reference is
   re-hashed on every view (CHANGED SINCE RECORDED, MISSING) as other recorded files are.
2. `gp claim --batch FILE`: N claims with one bind, all or nothing; a refused spec is named with why and nothing is
   filed; the resulting ledger equals the one N single claims give (same records, same status).

Needs the pinned Lean toolchain (the package builds in seconds); skipped without it.
"""
import importlib.util
import json
from pathlib import Path
import shutil
import unittest

ROOT = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location("gp_lanep_p1_tests_055", ROOT / "tests/test_gp50_lanep.py")
p1 = importlib.util.module_from_spec(spec)
spec.loader.exec_module(p1)
gp = p1.gp

REF = "V. I. Levenshtein, Bounds for packings of metric spaces, Problems Inform. Transmission 1979"


def plain(records):
    return [{k: v for k, v in r.items() if k != "at"} for r in records]


@unittest.skipUnless(p1.have_toolchain(), "the pinned Lean toolchain is not installed")
class LaneP055(unittest.TestCase):
    setUpClass = classmethod(p1.LaneP.setUpClass.__func__)
    tearDownClass = classmethod(p1.LaneP.tearDownClass.__func__)
    make = staticmethod(p1.LaneP.make)
    gp_at = staticmethod(p1.LaneP.gp_at)
    ok_at = classmethod(p1.LaneP.ok_at.__func__)
    copy, ok, no, lines, held, append, key = (p1.LaneP.copy, p1.LaneP.ok, p1.LaneP.no, p1.LaneP.lines, p1.LaneP.held,
                                              p1.LaneP.append, p1.LaneP.key)

    def records(self, where, op=None):
        return [r for r in gp.Ledger(where).records if op is None or r["op"] == op]

    # --- 1. citations ----------------------------------------------------------------------------------------

    def test_citation_filed_shown_never_held(self):
        c = self.copy("cite")
        self.ok(c, "claim", "C-cited", "--lean", "C")
        out = self.ok(c, "submit", "C-cited", "--citation", REF, "--theorem-number", "3", "--locator", "p. 12, §2",
                      "--doi", "https://doi.org/10.1234/PIT.1979.7")
        self.assertIn(f"recorded only: citation: {REF}, Thm 3 for C-cited; it never holds a claim", out)
        rec = self.records(c, "pwarrant")[-1]
        self.assertEqual({k: rec[k] for k in ("kind", "ref", "theorem_number", "locator", "doi")},
                         {"kind": "citation", "ref": REF, "theorem_number": "3", "locator": "p. 12, §2",
                          "doi": "10.1234/PIT.1979.7"})
        self.assertNotIn("file", rec)
        line = self.lines(c)["C-cited"]
        self.assertTrue(line.startswith(f"C-cited: open; best: tier 5 (citation: {REF}, Thm 3, recorded only)"), line)
        self.assertFalse(self.held(c, "C-cited"))
        out = self.ok(c, "explain", "C-cited")
        self.assertIn(f"recorded only: citation: {REF}, Thm 3 (at p. 12, §2; doi 10.1234/PIT.1979.7)", out)
        # A number that is not a theorem's is shown as given; a citation beside a held theorem changes nothing.
        self.ok(c, "submit", "C-held", "--citation", "Folklore", "--theorem-number", "Lemma 4")
        line = self.lines(c)["C-held"]
        self.assertTrue(line.startswith("C-held: held; tier 2 (unreplayed)"), line)
        self.assertIn("recorded only: citation: Folklore, Lemma 4", self.ok(c, "explain", "C-held"))
        # A hand-appended citation never holds either: the Kernel gets every recorded-only warrant as a citation.
        k = self.key(c, "C-cited")
        self.append(c, {"op": "pwarrant", "key": k, "label": "C-cited", "kind": "citation", "ref": "x",
                        "locator": "not a file"})
        self.assertFalse(self.held(c, "C-cited"))
        self.assertNotIn("MISSING", self.lines(c)["C-cited"])  # a citation's locator is text, never a file

    def test_citation_refusals(self):
        c = self.copy("cite-no")
        self.ok(c, "claim", "C-cited", "--lean", "C")
        self.assertIn("a citation names its reference", self.no(c, "submit", "C-cited", "--citation", " "))
        self.assertIn("is not a DOI", self.no(c, "submit", "C-cited", "--citation", REF, "--doi", "pit-1979"))
        self.assertIn("--theorem-number, --doi describe a citation",
                      self.no(c, "submit", "C-cited", "--theorem-number", "3", "--doi", "10.1/x"))
        self.assertIn("--state is for hand proofs",
                      self.no(c, "submit", "C-cited", "--citation", REF, "--state", "complete"))
        self.assertIn("a P submission is one warrant",
                      self.no(c, "submit", "C-cited", "--citation", REF, "--numerical", str(c / "campaign.json")))
        self.assertIn("outside the campaign",
                      self.no(c, "submit", "C-cited", "--citation", REF, "--file", str(ROOT / "LIMITS.md")))
        self.assertIn("cannot read", self.no(c, "submit", "C-cited", "--citation", REF, "--file", str(c / "nope.pdf")))
        self.assertEqual(self.records(c, "pwarrant"), [])

    def test_citation_overstated(self):
        c = self.copy("cite-pres")
        self.ok(c, "claim", "C-cited", "--lean", "C")
        self.ok(c, "submit", "C-cited", "--citation", REF)
        self.assertNotIn("OVERSTATED", self.ok(c, "present", "C-cited", "--venue", "notes", "--tag", "CITED"))
        self.assertNotIn("OVERSTATED", self.ok(c, "present", "C-cited", "--venue", "draft", "--tag", "HAND"))
        self.assertIn("OVERSTATED", self.ok(c, "present", "C-cited", "--venue", "abstract", "--tag", "LEAN"))
        self.assertIn("OVERSTATED", self.ok(c, "present", "C-cited", "--venue", "talk", "--tag", "SCRIPT"))
        line = self.lines(c)["C-cited"]
        self.assertIn("presented [SCRIPT] in 1 venue: OVERSTATED", line)
        self.assertIn("presented [HAND] in 1 venue;", line)
        self.assertIn("presented [CITED] in 1 venue;", line)
        # A [CITED] tag on a claim whose only evidence is numerical is above what it earned.
        self.ok(c, "claim", "B-num", "--lean", "B")
        num = c / "b.csv"
        num.write_bytes(b"base,2<=base\n3,true\n")
        self.ok(c, "submit", "B-num", "--numerical", str(num))
        self.assertIn("OVERSTATED", self.ok(c, "present", "B-num", "--venue", "notes", "--tag", "CITED"))
        # The reference's own hypotheses (--condition) are open premises a presentation must state.
        self.ok(c, "claim", "A-cited", "--lean", "A")
        out = self.ok(c, "submit", "A-cited", "--citation", REF, "--condition", "second review")
        self.assertIn("open: second review", out)
        self.assertIn("OVERSTATED", self.ok(c, "present", "A-cited", "--venue", "notes", "--tag", "CITED"))
        self.assertNotIn("OVERSTATED", self.ok(c, "present", "A-cited", "--venue", "paper", "--tag", "CITED",
                                               "--premise", "second review"))
        self.assertFalse(self.held(c, "A-cited"))

    def test_citation_local_copy_rehashed(self):
        c = self.copy("cite-file")
        self.ok(c, "claim", "C-pdf", "--lean", "C")
        pdf = c / "refs/levenshtein-1979.pdf"
        pdf.parent.mkdir()
        pdf.write_bytes(b"%PDF-1.4\n% Theorem 3. ...\n%%EOF\n")
        out = self.ok(c, "submit", "C-pdf", "--citation", REF, "--theorem-number", "3", "--file", str(pdf))
        self.assertIn("(refs/levenshtein-1979.pdf, sha256 ", out)
        line = self.lines(c)["C-pdf"]
        self.assertTrue(line.startswith(f"C-pdf: open; best: tier 5 (citation: {REF}, Thm 3, recorded only)"), line)
        self.assertIn("local copy refs/levenshtein-1979.pdf sha256", self.ok(c, "explain", "C-pdf"))
        # The local copy changed after submission: the citation no longer counts until it is re-submitted.
        pdf.write_bytes(b"%PDF-1.4\n% another paper\n%%EOF\n")
        line = self.lines(c)["C-pdf"]
        self.assertFalse(line.startswith("C-pdf: open; best: tier"), line)
        self.assertIn(f"citation: {REF}, Thm 3 refs/levenshtein-1979.pdf CHANGED SINCE RECORDED: not counted "
                      "(re-submit it)", line)
        self.assertIn("CHANGED SINCE RECORDED: not counted until re-submitted", self.ok(c, "explain", "C-pdf"))
        self.assertIn("OVERSTATED", self.ok(c, "present", "C-pdf", "--venue", "notes", "--tag", "CITED"))
        pdf.unlink()
        self.assertIn("refs/levenshtein-1979.pdf MISSING: not counted (re-submit it)", self.lines(c)["C-pdf"])
        pdf.write_bytes(b"%PDF-1.4\n% Theorem 3, the right paper\n%%EOF\n")
        self.ok(c, "submit", "C-pdf", "--citation", REF, "--theorem-number", "3", "--file", str(pdf))
        line = self.lines(c)["C-pdf"]
        self.assertTrue(line.startswith(f"C-pdf: open; best: tier 5 (citation: {REF}, Thm 3, recorded only)"), line)

    # --- 2. claim --batch ------------------------------------------------------------------------------------

    SPECS = [{"label": "x-a-of-b", "lean": "A", "premises": ["B"], "theorem": "Tiny.a_of_b"},
             {"label": "x-c", "lean": "C", "theorem": "Tiny.c_holds"},
             {"label": "x-b-of-c", "lean": "B", "premises": ["C"], "theorem": "Tiny.b_of_c"},
             {"label": "x-c-weak", "lean": "C", "premises": ["B"], "from": "x-c"},
             {"label": "x-not-a", "lean": "¬A"},
             {"label": "x-prose", "prose": "second review"},
             {"label": "x-open", "lean": "A", "premises": ["C"]},
             {"label": "x-missing", "lean": "B", "theorem": "Tiny.nope"}]

    @staticmethod
    def single_args(s):
        args = ["claim", s["label"], "--lean" if "lean" in s else "--prose", s.get("lean") or s["prose"]]
        for h in s.get("premises", []):
            args += ["--premise", h]
        for k, flag in (("theorem", "--theorem"), ("from", "--from")):
            if k in s:
                args += [flag, s[k]]
        return args

    def counting_builds(self):
        built, orig = [], gp.lanep.run_capped

        def counted(cmd, *a, **k):
            if cmd[-1] == "build":
                built.append(cmd)
            return orig(cmd, *a, **k)
        gp.lanep.run_capped = counted
        self.addCleanup(setattr, gp.lanep, "run_capped", orig)
        return built

    def test_batch_equals_single_claims(self):
        one, many = self.copy("single"), self.copy("batch")
        for s in self.SPECS:
            self.ok(one, *self.single_args(s))
        path = many / "claims.json"
        path.write_bytes(json.dumps(self.SPECS, ensure_ascii=False).encode("utf-8"))
        binds = len(self.records(many, "bind"))
        built = self.counting_builds()
        out = self.ok(many, "claim", "--batch", str(path))
        self.assertEqual(len(built), 1, built)  # one `lake build`, one binder run, for every theorem of the batch
        self.assertEqual(len(self.records(many, "bind")), binds + 1)
        self.assertIn("8 claims filed with one bind (", out)
        self.assertIn("claim x-a-of-b (key ", out)
        self.assertIn("x-missing (key", out)
        # The same records (registers of new negation codes and claims, in order) and the same status.
        mine = [r for r in plain(self.records(many)) if r["op"] in ("register", "pclaim")]
        theirs = [r for r in plain(self.records(one)) if r["op"] in ("register", "pclaim")]
        self.assertEqual(mine, theirs)
        status = self.ok(many, "status")
        self.assertEqual(status, self.ok(one, "status"))
        lines = self.lines(many)
        self.assertTrue(lines["x-a-of-b"].startswith("x-a-of-b: held; tier 2 (unreplayed)"), lines["x-a-of-b"])
        self.assertTrue(lines["x-c-weak"].startswith("x-c-weak: held"), lines["x-c-weak"])
        self.assertTrue(lines["x-not-a"].startswith("x-not-a: open"), lines["x-not-a"])
        self.assertTrue(lines["x-prose"].startswith("x-prose: open"), lines["x-prose"])
        self.assertIn("the theorem is missing from the package", lines["x-missing"])
        # JSON lines, with comments, also work; the view after a batch rebinds nothing.
        jl = many / "more.jsonl"
        jl.write_bytes(b'# two more\n{"label": "y-b", "lean": "B", "theorem": "Tiny.b_holds"}\n\n'
                       b'{"label": "y-a", "lean": "A", "premises": ["B"], "from": "x-a-of-b"}\n')
        out = self.ok(many, "claim", "--batch", str(jl))
        self.assertIn("2 claims filed with one bind", out)
        del built[:]
        self.ok(many, "status")
        self.assertEqual(built, [])

    def test_batch_all_or_nothing(self):
        c = self.copy("batch-no")
        path = c / "claims.json"

        def run(specs):
            path.write_bytes(json.dumps(specs, ensure_ascii=False).encode("utf-8"))
            return self.no(c, "claim", "--batch", str(path))

        before = self.records(c)
        # Refused before anything binds: each refused spec is named, with why.
        out = run([{"label": "z-1", "lean": "¬C"},
                   {"label": "z-2", "lean": "A", "premise": ["B"]},
                   {"label": "B-held", "lean": "B"},
                   {"label": "z-1", "lean": "C"},
                   {"lean": "C"},
                   {"label": "z-3", "lean": "A", "comparator": "Tiny.a_of_b"},
                   {"label": "z-4", "lean": "A", "theorem": "Tiny.a_of_b", "from": "A-of-B", "premises": ["B"]},
                   {"label": "z-5", "lean": "Nope"},
                   {"label": "z-6", "prose": "second review", "theorem": "Tiny.c_holds"}])
        self.assertIn("the batch was not filed: 8 of 9 claims refused", out)
        for want in ("z-2: unknown field premise", "B-held: label 'B-held' is taken", "z-1: label 'z-1' is taken",
                     "item 5: a claim spec needs a label", "z-3: a Comparator claim is filed alone",
                     "z-4: a claim has one holding warrant", "z-5: no registered statement 'Nope'",
                     "z-6: second review is prose"):
            self.assertIn(want, out)
        self.assertNotIn("the bind is kept", out)
        self.assertEqual(self.records(c), before)  # nothing at all: not even the ¬C code z-1 registered
        # A wrong theorem is refused by the batch's one bind; the good specs are not filed either.
        built = self.counting_builds()
        out = run([{"label": "w-c", "lean": "C", "theorem": "Tiny.c_holds"},
                   {"label": "w-wrong", "lean": "A", "theorem": "Tiny.c_holds"},
                   {"label": "w-not", "lean": "¬B"}])
        self.assertIn("the batch was not filed: 1 of 3 claims refused", out)
        self.assertIn("w-wrong: theorem Tiny.c_holds refused for A: the kernel refused its type: Tiny.c_holds does not "
                      "prove the claim's statement; expected (the claim's type): Tiny.A; actual (Tiny.c_holds's type): "
                      "Tiny.C", out)
        self.assertIn("the bind is kept", out)
        self.assertEqual(len(built), 1)
        after = self.records(c)
        self.assertEqual([r["op"] for r in after[len(before):]], ["bind"])
        self.assertFalse(any(r.get("label", "").startswith("w-") for r in after))
        self.assertNotIn("¬B", [r["name"] for r in self.records(c, "register")])
        # The fixed batch files everything, and binds nothing new: its rows were bound by the refused batch.
        del built[:]
        path.write_bytes(json.dumps([{"label": "w-c", "lean": "C", "theorem": "Tiny.c_holds"},
                                     {"label": "w-not", "lean": "¬B"}], ensure_ascii=False).encode("utf-8"))
        self.assertIn("2 claims filed with one bind", self.ok(c, "claim", "--batch", str(path)))
        self.assertEqual(built, [])
        self.assertTrue(self.held(c, "w-c"))
        # The batch takes everything from its file.
        self.assertIn("--batch takes every claim from its file, not a label, --lean",
                      self.no(c, "claim", "v", "--lean", "A", "--batch", str(path)))
        path.write_bytes(b"{not json")
        self.assertIn("the batch file is not valid JSON or JSON lines", self.no(c, "claim", "--batch", str(path)))
        path.write_bytes(b"[]")
        self.assertIn("not a non-empty list of claim specs", self.no(c, "claim", "--batch", str(path)))


if __name__ == "__main__":
    unittest.main()
