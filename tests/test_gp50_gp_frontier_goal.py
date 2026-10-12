"""Goal frontier controls: real CLI/native replay, read-only views, no simulated admission.

P11-c0 data is copied from campaigns/ud22/graphs/p11-c0.g6 and receipts/p11/0.receipt.json
at 51fc660 (Git blobs ea46240d56936c27574637de203fc4003b11ed8a and
6e04c2422046705390217a20c996e35d6886205f). Kept inline so public snapshots
can run these controls without the private campaign directories.
"""
from contextlib import redirect_stderr, redirect_stdout
import hashlib
import importlib.util
import io
import json
from pathlib import Path
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location("gp_frontier_goal", ROOT / "tools/gp.py")
gp = importlib.util.module_from_spec(spec)
spec.loader.exec_module(gp)

P11_GRAPH = "U@?GOK_CG??@gaW`qHQaJ`DAGcIGoQPOKB{?~???"
P11_RECEIPT = {"certificate": {"type": "case_tree", "points": [[f"x{i+1}", f"y{i+1}"] for i in range(22)],
    "tree": {"collision": {"rhombi": [
        ["1/2", [0, 12, 2, 21]], ["-1/2", [0, 12, 10, 14]], ["1/2", [0, 14, 3, 21]],
        ["1/2", [0, 16, 5, 21]], ["-1/2", [0, 16, 11, 17]], ["1/2", [0, 17, 4, 21]],
        ["-1/2", [1, 13, 2, 21]], ["1/2", [1, 13, 11, 15]], ["-1/2", [1, 15, 3, 21]],
        ["-1/2", [1, 18, 5, 21]], ["1/2", [1, 18, 10, 19]], ["-1/2", [1, 19, 4, 21]]],
        "pair": [0, 1]}}}}
K4 = {"name": "K4", "n": 4, "edges": [[0, 1], [0, 2], [0, 3], [1, 2], [1, 3], [2, 3]]}
K4_RECEIPT = {"certificate": {"type": "case_tree", "points": [[f"x{i+1}", f"y{i+1}"] for i in range(4)],
    "tree": {"collision": {"rhombi": [["1/2", [0, 1, 2, 3]], ["1/2", [0, 1, 3, 2]]], "pair": [0, 1]}}}}
C4 = {"name": "C4", "n": 4, "edges": [[0, 1], [1, 2], [2, 3], [0, 3]]}
C4_POINT = {"certificate": {"type": "real_point", "point": {
    "x1": "0", "y1": "0", "x2": "1", "y2": "0", "x3": "1", "y3": "1", "x4": "0", "y4": "1"}}}


class GoalFrontier(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix="gp-frontier-goal-")
        self.addCleanup(self.temp.cleanup)
        self.directory = Path(self.temp.name)

    def file(self, name, body):
        path = self.directory / name
        path.write_bytes((json.dumps(body, sort_keys=True) + "\n").encode("utf-8"))
        return path

    def cli(self, *words):
        out, err = io.StringIO(), io.StringIO()
        with redirect_stdout(out), redirect_stderr(err):
            code = gp.main(["--campaign", str(self.directory), *map(str, words)])
        self.assertEqual(code, 0, out.getvalue() + err.getvalue())
        return out.getvalue() + err.getvalue()

    def campaign(self, n, m, *, parameters=True):
        goal = {"kind": "DECIDE", "name": "Q", "statement": f"{n} points with at least {m} unit distances"}
        if parameters:
            goal["udg"] = {"n": n, "m": m}
        self.file("campaign.json", {"name": "goal frontier controls", "family": [], "goal": goal})
        self.cli("init")

    def claim(self, label, graph, kind, *, receipt=None, premises=(), goal=False):
        graph_path = self.file(label + "-graph.json", graph) if isinstance(graph, dict) else graph
        words = ["claim", label, "--udg", graph_path, "--kind", kind, "--real"]
        for premise in premises:
            words += ["--premise", premise]
        if goal:
            words += ["--goal", "yes"]
        self.cli(*words)
        if receipt is not None:
            self.cli("submit", label, self.file(label + "-receipt.json", receipt))
        ledger = gp.Ledger(self.directory)
        out, items = gp.state(ledger)
        claim = ledger.claim(label)
        self.assertIs(items[claim["key"]]["held"], receipt is not None)
        self.assertEqual(gp.premise_state(out, claim), "discharged")

    def cover(self, label, candidates, n, m, *, premises=()):
        manifest = self.file(label + "-candidates.json", candidates)
        identity = hashlib.sha256(manifest.read_bytes()).hexdigest()
        words = ["cover", label, "--candidates", manifest, "--n", n, "--m", m]
        for premise in premises:
            words += ["--premise", premise + "=" + identity]
        self.cli(*words)
        return identity

    def frontier(self):
        ledger_before = (self.directory / "ledger.jsonl").read_bytes()
        campaign_before = (self.directory / "campaign.json").read_bytes()
        text = self.cli("frontier")
        self.assertEqual((self.directory / "ledger.jsonl").read_bytes(), ledger_before)
        self.assertEqual((self.directory / "campaign.json").read_bytes(), campaign_before)
        return text

    def test_held_p11_with_open_completeness_does_not_empty_frontier(self):
        self.campaign(22, 61)
        self.claim("P11-c0", P11_GRAPH, "EMPTY", receipt=P11_RECEIPT)
        identity = self.cover("one-p11", [P11_GRAPH], 22, 61, premises=["ENUM-COMPLETE"])
        ledger = gp.Ledger(self.directory)
        self.assertEqual(ledger.claim("one-p11")["premise_notes"], {"ENUM-COMPLETE": [identity]})
        out, items = gp.state(ledger)
        self.assertTrue(items[ledger.claim("one-p11:spine")["key"]]["held"])  # the Kernel checked the 22-vertex frame
        self.assertFalse(items[ledger.claim("one-p11")["key"]]["held"])
        status, explanation = self.cli("status"), self.cli("explain", "one-p11")
        text = self.frontier()
        self.assertIn("not Q: open; the Kernel holds spine one-p11:spine (if cover one-p11 is complete then not Q); "
                      "the cover is open", text)
        self.assertIn("cover one-p11: premise ENUM-COMPLETE: OPEN", text)
        self.assertIn("verdict: undecided", text)
        self.assertIn("goal frontier remains open", text)
        self.assertNotIn("frontier empty", text)
        self.assertNotIn("missing held exclusion", text)
        self.assertEqual(self.cli("status"), status)
        self.assertEqual(self.cli("explain", "one-p11"), explanation)

    def test_missing_candidate_exclusion_and_completeness_are_both_visible(self):
        self.campaign(22, 61)
        self.claim("P11-unproved", P11_GRAPH, "EMPTY")
        self.cover("missing-p11", [P11_GRAPH], 22, 61, premises=["ENUM-COMPLETE"])
        text = self.frontier()
        self.assertLess(text.index("P11-unproved: open"), text.index("Goal: DECIDE Q"))
        self.assertIn("missing held exclusion over R", text)
        self.assertIn("22 vertices, 61 edges", text)
        self.assertIn("ENUM-COMPLETE: OPEN", text)
        self.assertIn("verdict: undecided", text)
        self.assertNotIn("frontier empty", text)

    def test_cover_parameter_mismatch_cannot_count_held_exclusion(self):
        self.campaign(22, 61)
        self.claim("P11-c0", P11_GRAPH, "EMPTY", receipt=P11_RECEIPT)
        self.cover("wrong-m", [P11_GRAPH], 22, 60, premises=["ENUM-COMPLETE"])
        text = self.frontier()
        self.assertIn("cover wrong-m is for n = 22, m = 60; not the goal's n = 22, m = 61; it does not count", text)
        self.assertIn("no cover for n = 22, m = 61", text)
        self.assertIn("ENUM-COMPLETE: OPEN", text)
        self.assertIn("verdict: undecided", text)
        self.assertNotIn("frontier empty", text)

    def test_exhaustive_k4_cover_has_no_goal_obligations(self):
        self.campaign(4, 6)
        self.claim("K4-empty", K4, "EMPTY", receipt=K4_RECEIPT)
        self.cover("complete-k4", [K4], 4, 6)
        text = self.frontier()
        self.assertIn("not Q: held by cover complete-k4", text)
        self.assertIn("verdict: decided: not Q", text)
        self.assertIn("frontier empty", text)
        self.assertNotIn("OPEN", text)
        self.assertNotIn("goal frontier remains open", text)

    def test_two_vertices_two_pairs_empty_cover_uses_existing_contract(self):
        self.campaign(2, 2)
        self.cover("pair-bound", [], 2, 2)
        text = self.frontier()
        self.assertIn("not Q: held by cover pair-bound", text)
        self.assertIn("verdict: decided: not Q", text)
        self.assertIn("frontier empty", text)
        self.assertNotIn("OPEN", text)
        claims = gp.Ledger(self.directory).claims()
        self.assertEqual({c["family"] for c in claims}, {"goal", "cover", "spine"})

    def test_all_cover_and_inherited_premises_are_named(self):
        self.campaign(22, 61)
        self.claim("P11-c0", P11_GRAPH, "EMPTY", receipt=P11_RECEIPT, premises=["GP74-NON-UD"])
        self.cover("enum", [P11_GRAPH], 22, 61, premises=["ENUM-COMPLETE"])
        self.cover("amp", [P11_GRAPH], 22, 61, premises=["AMP-THM1"])
        text = self.frontier()
        for label, premise in [("enum", "ENUM-COMPLETE"), ("amp", "AMP-THM1"), ("enum", "GP74-NON-UD")]:
            self.assertIn(f"cover {label}: premise {premise}: OPEN", text)
        self.assertIn("verdict: undecided", text)
        self.assertNotIn("frontier empty", text)

    def test_held_point_with_too_few_edges_does_not_count_for_goal(self):
        self.campaign(4, 5)
        self.claim("square-lower-bound", C4, "NONEMPTY", receipt=C4_POINT)
        text = self.frontier()
        self.assertIn("held claim square-lower-bound does not count for Q: the graph has 4 edges; Q needs at least 5", text)
        self.assertIn("verdict: undecided", text)
        self.assertNotIn("frontier empty", text)

    def test_firm_yes_side_uses_existing_bridge(self):
        self.campaign(4, 4)
        self.claim("square", C4, "NONEMPTY", receipt=C4_POINT, goal=True)
        text = self.frontier()
        self.assertIn("Q: held by square", text)
        self.assertIn("verdict: decided: Q", text)
        self.assertIn("frontier empty", text)

    def test_conditional_yes_side_does_not_decide_goal(self):
        self.campaign(4, 4)
        self.claim("square", C4, "NONEMPTY", receipt=C4_POINT, goal=True, premises=["AMP-THM1"])
        text = self.frontier()
        self.assertIn("claim square: premise AMP-THM1: OPEN", text)
        self.assertIn("verdict: undecided", text)
        self.assertNotIn("frontier empty", text)

    def test_missing_goal_parameters_leave_obligation_open(self):
        self.campaign(2, 2, parameters=False)
        text = self.frontier()
        self.assertIn("the goal states no graph parameters", text)
        self.assertIn("verdict: undecided", text)
        self.assertNotIn("frontier empty", text)

    def test_resolved_goal_does_not_require_an_alternative_open_cover(self):
        self.campaign(4, 6)
        self.claim("K4-empty", K4, "EMPTY", receipt=K4_RECEIPT)
        self.cover("conditional-k4", [K4], 4, 6, premises=["ENUM-COMPLETE"])
        self.cover("complete-k4", [K4], 4, 6)
        text = self.frontier()
        self.assertIn("cover conditional-k4: premise ENUM-COMPLETE: OPEN", text)
        self.assertIn("verdict: decided: not Q", text)
        self.assertIn("frontier empty", text)
        self.assertNotIn("goal frontier remains open", text)


if __name__ == "__main__":
    unittest.main()
