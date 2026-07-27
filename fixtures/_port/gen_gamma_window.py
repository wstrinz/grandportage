"""Emit fixtures/gamma_window/graph.jsonl -- the LIVE research front.

Not a retrodiction.  The two other fixtures replay settled history against
pinned answer keys; this one models work that is open right now, so there is no
answer key and none is claimed.

WHAT THIS IS AND IS NOT.  Every obligation encoded below is ALREADY KNOWN and
already written down -- in SESSION_HANDOFF.md's prose, in F2_TOWER.md's "THE
BRIDGE IS UNVERIFIED" banner, and in one case in a `print` statement.  Grand
Portage discovers none of it.  What it changes is the FORM: a banner is prose a
reader has to find and believe, and it is the first thing lost at the next
compaction or handoff.  A typed edge is a fact about the graph that survives the
session, blocks the conclusion that depends on it, and names its own discharge.

Source: math-stuff/d2_plane_72_108/SESSION_HANDOFF.md (2026-07-26 evening),
F2_TOWER.md, ENDPOINT_CONTRACT.md.  Line-level citations throughout.
"""

import json
import os

OUT = os.path.abspath(os.path.join(
    os.path.dirname(os.path.abspath(__file__)), "..", "gamma_window",
    "graph.jsonl"))

EV = []


def model(mid, desc, field=None, chart=None, cite=""):
    e = {"ev": "model", "id": mid, "desc": desc, "cite": cite}
    if field:
        e["field"] = field
    if chart:
        e["chart"] = chart
    EV.append(e)


def edge(eid, src, dst, etype, why, map_kind="IDENTITY_MAP", drops=None,
         witness="", debt_why="", cite=""):
    e = {"ev": "edge", "id": eid, "src": src, "dst": dst, "type": etype,
         "why": why, "map_kind": map_kind, "cite": cite}
    if drops:
        e["drops"] = drops
    if witness:
        e["witness"] = witness
    if debt_why:
        e["debt_why"] = debt_why
    EV.append(e)


def claim(cid, model_id, kind, statement, scope=None, cert=None,
          zariski_closed=None, ladder="claimed", cite=""):
    e = {"ev": "claim", "id": cid, "model": model_id, "kind": kind,
         "statement": statement, "ladder": ladder, "cite": cite}
    if scope is not None:
        e["scope"] = scope
    if cert is not None:
        e["certificate"] = cert
    if zariski_closed is not None:
        e["zariski_closed"] = zariski_closed
    EV.append(e)


def inference(iid, claim_id, path, asserted, cite, note=""):
    e = {"ev": "inference", "id": iid, "claim": claim_id, "path": path,
         "asserted": asserted, "era": "live-2026-07", "cite": cite}
    if note:
        e["note"] = note
    EV.append(e)


def note(text, **kw):
    e = {"ev": "note", "text": text}
    e.update(kw)
    EV.append(e)


# ===========================================================================
note("The gamma-window compiler front, targeting (75,125) = GGV5's "
     "F_2(3,5)/125.  (72,108) is CLOSED and its enumerated f31 frontier is "
     "EMPTY; this is the successor object.  Every obligation here is already "
     "documented in prose -- what is new is that it is now mechanical.",
     domain="gamma_window", source="d2_plane_72_108/SESSION_HANDOFF.md "
     "(2026-07-26 evening)")

# ---------------------------------------------------------------------------
# (A) THE STANDING GAMMA OBLIGATION
# ---------------------------------------------------------------------------
model("CORNER_5_20",
      "The corner layer at (5,20): gamma derived from the corner A_0 by "
      "gamma_from_corner.py, calibrated on 28 published GGV1 data points.  "
      "Yields gamma in {2,3,4}.",
      chart="corner",
      cite="SESSION_HANDOFF.md 'Step 1 is DONE and it found an obstruction'; "
           "gamma_from_corner.py + _verify.py, 43 checks")
model("REDUCED_5_20",
      "The reduced chart (P_1,Q_1) and its degree/polygon bookkeeping -- the "
      "layer BELOW the corner, where GGV3's 'similar computations as in "
      "[GGV1, Prop 8.3]' must act.  Not mechanised here.",
      chart="reduced",
      cite="SESSION_HANDOFF.md: 'the corner layer CANNOT pin gamma.  Whatever "
           "GGV3's ... does, it acts BELOW the corner layer'")

edge("GE1", "REDUCED_5_20", "CORNER_5_20", "NECESSARY_CONDITION",
     "The corner layer retains only the corner A_0 and forgets the reduced "
     "chart's degree and polygon bookkeeping.  Strictly less information, so "
     "strictly more admissible gamma.",
     drops=["the reduced chart's degree/polygon bookkeeping",
            "whatever GGV1 machinery is not mechanised: Props 'case IIb', "
            "'impossibles', 'u(u-1)', 'encima de la diagonal', 'factores'"],
     witness="SESSION_HANDOFF.md: at (5,20) the corner admits gamma in "
             "{2,3,4} while GGV3 asserts {2,3}.  Condition (9) with "
             "d = gcd(f1-1,f2-1) = 3 != 1 gives only the BOUND gamma <= 4, "
             "never the equality that pins gamma at every Table 1 row.  Both "
             "halves of GGV1's corner machinery fail: 'case II' is "
             "INAPPLICABLE (needs gcd(a,b) > 1, which is 1 for gamma = 2,3,4 "
             "alike) and 'extremosfinales' is NON-EXCLUSIVE (an admissible k "
             "exists for all three).",
     cite="SESSION_HANDOFF.md, 'The obligation is CLASS-WIDE' section above")

claim("GC-GAMMA23", "REDUCED_5_20", "PREDICATE",
      "gamma is in {2,3}",
      ladder="claimed",
      cite="GGV3 sec.5, asserted WITHOUT PROOF -- tex:1716, verbatim: 'We do "
           "not provide proofs for this first part.'  Recorded at ladder "
           "'claimed' deliberately: the evidence grade and the transport are "
           "orthogonal, and this claim is weak on BOTH axes.")

inference("GI-GAMMA-IMPORT", "GC-GAMMA23", [["GE1", "ALONG"]],
          "gamma is in {2,3} at the corner layer too, so the compiler need "
          "only be built for gamma in {2,3}",
          cite="the step SESSION_HANDOFF.md warns against: 'Build it for "
               "gamma in {2,3,4}, not {2,3} -- step 1 requires this until the "
               "obligation closes.'",
          note="THE STANDING OBLIGATION, as a type error.  Exclude gamma = 4 "
               "at (5,20), or a third chart exists that GGV3 sec.5 does not "
               "analyse.  This is an obligation, NOT a refutation.")

# The class-wide consequence, recorded so the payoff is visible next to the cost
model("CLASS_T4_MONOMIAL",
      "The atlas's 'monomial corner, t=4' cluster: 9 rows on four corners "
      "(5,20), (8,32), (9,36), (10,40), all with b_0 = 4a_0.  Every branch in "
      "the class that yields a non-empty gamma has d = 3.",
      cite="SESSION_HANDOFF.md 'The obligation is CLASS-WIDE'; CORNER_ATLAS.md")
edge("GE2", "CLASS_T4_MONOMIAL", "CORNER_5_20", "NECESSARY_CONDITION",
     "(5,20) is one row of the class.  Reasoning about the single row forgets "
     "the other eight, so a result at (5,20) does not by itself close them.",
     drops=["the other eight rows of the cluster"],
     witness="(8,32) is the outlier: no branch survives at all, so the rows "
             "are not interchangeable.",
     cite="SESSION_HANDOFF.md: 'closing gamma at (5,20) plausibly reaches "
          "NINE rows, not three'")

# ---------------------------------------------------------------------------
# (B) THE RETRACTION THEOREM AND ITS NON-CONVERSE
# ---------------------------------------------------------------------------
model("RETRACT_B0_4A0",
      "The corners with b_0 = 4a_0 exactly.",
      cite="SESSION_HANDOFF.md: 'b_0 = 4a_0 => FAIL|PASS is a THEOREM "
           "(retraction needs 4u = 4(u-1), impossible; t = ceil(4u/u) = 4)'")
model("T4_CORNERS",
      "The corners with t = 4.",
      cite="SESSION_HANDOFF.md, same paragraph")
edge("GE3", "RETRACT_B0_4A0", "T4_CORNERS", "NECESSARY_CONDITION",
     "b_0 = 4a_0 implies t = 4.  The CONVERSE IS NOT TRUE and must not be "
     "typed as an equivalence.",
     drops=["the retraction property itself"],
     witness="SESSION_HANDOFF.md, verbatim: 'The converse is NOT -- t=4 "
             "without retraction only needs 3a_0 < b_0 <= 4a_0, "
             "b_0 != 4a_0-4, which at a_0=5 also admits 17, 18, 19.  It holds "
             "on GGV5's list empirically.  Do not state it as an "
             "equivalence.'",
     cite="SESSION_HANDOFF.md 'The obligation is CLASS-WIDE'")
claim("GC-T4-EMPIRICAL", "T4_CORNERS", "PREDICATE",
      "on GGV5's list, every t=4 corner has b_0 = 4a_0 or b_0 = 4a_0-4",
      ladder="exact-checked",
      cite="SESSION_HANDOFF.md: 'It holds on GGV5's list empirically.'")
inference("GI-T4-SOUND", "GC-T4-EMPIRICAL", [["GE3", "AGAINST"]],
          "the empirical property of the t=4 corners holds in particular of "
          "the b_0 = 4a_0 corners",
          cite="a PREDICATE read AGAINST the arrow, which is the licensed "
               "direction",
          note="POSITIVE CONTROL.  Must stay clean: a predicate valid on the "
               "looser class is valid on the tighter one, and refusing this "
               "would make the framework a false-positive generator.  The "
               "mutation that types GE3 EQUIVALENCE is what turns the "
               "recorded non-converse into a caught error.")

# ---------------------------------------------------------------------------
# (C) THE REPLAY TRAP
# ---------------------------------------------------------------------------
model("F2T_A2_CERT",
      "f2_tower.a2_certificate(): the (50,75) gamma=2 kill -- C_0, g_{-2}, "
      "g_{-5}, e_{-10}, c_{0,-10}.  A REPLAY of GGV3's published algebra: the "
      "13 gamma=2 equations and the forced C_0 are written down as LITERALS "
      "and a^3 = 2 is supplied as a GIVEN, not derived.",
      cite="F2_TOWER.md 'THE BRIDGE IS UNVERIFIED', mechanically checked: it "
           "references T, KAPPA, QC, C, ordPhi, Nof, build_gsystem ZERO times "
           "each")
model("TARGET_75_125",
      "The (75,125) target: GGV5's F_2(3,5)/125.  There is no published "
      "transcription to copy here -- which is why the compiler must exist.",
      cite="SESSION_HANDOFF.md 'THE REPLAY TRAP'")

edge("GE4", "F2T_A2_CERT", "TARGET_75_125", "UNTYPED",
     "Nothing established relates the (50,75) replay to (75,125).",
     debt_why="The (50,75) certificate is a replay of published algebra, not "
              "a derivation, and GGV3 itself declines to prove that part.  "
              "SESSION_HANDOFF.md: 'Sound as a check; useless as an oracle "
              "for (75,125), where there is no transcription to copy.'  Until "
              "the compiler derives the (75,125) system, no relation between "
              "these two models exists to type.",
     cite="SESSION_HANDOFF.md 'THE REPLAY TRAP'")

claim("GC-A2-KILL", "F2T_A2_CERT", "EMPTY",
      "the gamma=2 chart at (50,75) is killed",
      cert="UNIT_IDEAL_CERT", ladder="exact-checked",
      cite="f2_tower.a2_certificate(); a replay, but an internally exact one")
inference("GI-REPLAY-TRANSFER", "GC-A2-KILL", [["GE4", "ALONG"]],
          "the same kill applies at (75,125)",
          cite="the step the REPLAY TRAP banner exists to prevent",
          note="Recorded so the temptation is refused mechanically rather "
               "than by a reader remembering a banner.  Note the certificate "
               "BASE-CHANGES and the ladder is exact-checked: neither the "
               "evidence grade nor the field scope is what stops this.  The "
               "edge is.")

# ---------------------------------------------------------------------------
# (D) THE UNVERIFIED BRIDGE
# ---------------------------------------------------------------------------
model("F2T_PERIOD",
      "f2_tower.tower_step(): the period argument -- W_step, "
      "q_window = 12a-7, denominator sets, gcd(17,29).  References C_0, "
      "g_{-2}, g_{-5}, e_{-10}, aa, bb, lam ZERO times each.",
      cite="F2_TOWER.md 'THE BRIDGE IS UNVERIFIED', mechanically checked in "
           "both directions")

edge("GE5", "F2T_PERIOD", "F2T_A2_CERT", "UNTYPED",
     "The period computation and the kill share NOT ONE VARIABLE.",
     debt_why="F2_TOWER.md: the two functions are mechanically confirmed to "
              "share no variable in either direction, and the sentence "
              "joining them -- 'the a=2 kill lives entirely in this layer' -- "
              "is a PRINT STATEMENT.  The weak reading stands (the a=3 "
              "gamma-systems are not the a=2 ones); the STATED reason (period "
              "jump 17 -> 29) is an assertion.  Graded claimed.",
     cite="F2_TOWER.md 'THE BRIDGE IS UNVERIFIED', added 2026-07-26 second "
          "pass, which also WITHDRAWS a first-pass endorsement that the "
          "obstruction 'survives on coprimality alone'")

claim("GC-PERIOD", "F2T_PERIOD", "PREDICATE",
      "the period jumps 17 -> 29 between the a=2 and a=3 towers",
      ladder="claimed",
      cite="f2_tower.tower_step(); q_window = 12a-7, gcd(17,29)")
inference("GI-BRIDGE", "GC-PERIOD", [["GE5", "ALONG"]],
          "therefore the a=2 kill lives entirely in this layer, and the "
          "BLOCK-OBSTRUCTION verdict follows",
          cite="the `print` statement, promoted to a recorded inference so it "
               "can be refused",
          note="This is the single clearest case for the whole approach.  The "
               "defect is not a wrong computation -- both computations are "
               "fine.  It is a JOIN between two computations that share no "
               "variable, asserted in prose.  No evidence grade catches that, "
               "because both halves are individually well-evidenced.")

# ---------------------------------------------------------------------------
# (E) TWO DIFFERENT OBJECTS WEAR THE WORD "WINDOW"
# ---------------------------------------------------------------------------
model("CONE_75_125",
      "The u-weight / y-order CONE at (75,125), where q_window lives.  It "
      "DEGENERATES TO A RAY because C is a monomial, so lambda = 0: 'no "
      "window system, only a demonstration that the premise does not "
      "transfer.'",
      cite="window_functions_75_125.py (R3); SESSION_HANDOFF.md 'Two "
           "different objects wear the word window'")
model("DEPTH_LEDGER_75_125",
      "The gamma-chart DEPTH LEDGER at (75,125), where the kill lives.  "
      "Specified by ENDPOINT_CONTRACT.md, in GGV3's own reduced coordinates.",
      cite="ENDPOINT_CONTRACT.md; SESSION_HANDOFF.md, same section")

edge("GE6", "CONE_75_125", "DEPTH_LEDGER_75_125", "UNTYPED",
     "Two distinct layers that share a NAME and nothing else.",
     debt_why="SESSION_HANDOFF.md: 'A period fact about a collapsed cone is "
              "weak evidence about a depth ledger.'  The clean confirmation "
              "is that the repair moved t, kappa, C, N, Phi and q_window and "
              "left the gamma-chart kill numbers (caps, floor -6, c_{0,-10}) "
              "UNTOUCHED -- so the two layers are causally independent, and "
              "no transport between them has been established.",
     cite="SESSION_HANDOFF.md 'Two different objects wear the word window'")

claim("GC-CONE-PERIOD", "CONE_75_125", "PREDICATE",
      "the cone's period structure at (75,125)",
      ladder="claimed",
      cite="window_functions_75_125.py R3 -- but note the cone degenerates to "
           "a ray, so the premise does not transfer")
inference("GI-WINDOW-CONFLATION", "GC-CONE-PERIOD",
          [["GE6", "ALONG"]],
          "the same period structure governs the gamma-chart depth ledger, "
          "because both are 'the window'",
          cite="the conflation the handoff warns about, recorded so the "
               "warning is enforced rather than read",
          note="A NAME COLLISION promoted to a type error.  Nothing in an "
               "evidence ladder or a provenance graph distinguishes two "
               "objects that share an identifier; only declaring them as "
               "separate models does.")

with open(OUT, "w", encoding="utf-8") as fh:
    fh.write("# The gamma-window compiler front -- LIVE, open work.\n")
    fh.write("# Source: d2_plane_72_108/SESSION_HANDOFF.md (2026-07-26 eve).\n")
    fh.write("# Not a retrodiction: there is no answer key for open work.\n")
    for e in EV:
        fh.write(json.dumps(e, sort_keys=True) + "\n")
print("wrote %s (%d events)" % (OUT, len(EV)))
