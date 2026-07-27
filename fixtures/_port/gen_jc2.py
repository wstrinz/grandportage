"""Emit fixtures/jc2/graph.jsonl -- the JC(2) plane (72,108) typed DAG.

Ported from math-stuff/whetstone/whetstone_dag.py, where the same content lives
as Python literals inside the checker.  Nothing is retyped or regraded: every
model, edge, claim and inference keeps its identifier, its type and its
citation.  The only deliberate changes are structural:

  * `expected_flag` is DROPPED.  The answer key moves to expect.json so the
    checker cannot be told which inferences are supposed to fail.
  * severities are DROPPED except where the derived severity must be
    overridden, and the override carries a reason.
  * gauges/reads become axis-tagged rows, so the place rule generalises.
  * two counter-claims are ADDED (CL-C08-REAL already existed; CL-C20-REAL is
    lifted from E9's own witness text) so that "this is a true positive, not a
    conservative refusal" is DERIVED rather than asserted in prose.
"""

import json
import os

OUT = os.path.abspath(os.path.join(
    os.path.dirname(os.path.abspath(__file__)), "..", "jc2", "graph.jsonl"))

EV = []


def model(mid, desc, chart=None, declares=None, coverage_axes=None,
          touches=None, reads=None, universe=None, cite=""):
    e = {"ev": "model", "id": mid, "desc": desc, "cite": cite}
    if chart:
        e["chart"] = chart
    if declares:
        e["declares"] = declares
    if coverage_axes:
        e["coverage_axes"] = coverage_axes
    if touches:
        e["touches"] = touches
    if reads:
        e["reads"] = reads
    if universe:
        e["universe"] = universe
    EV.append(e)


def edge(eid, src, dst, etype, why, map_kind="IDENTITY_MAP", support=None,
         drops=None, refinement=False, cite="", witness="", ring_iso=None):
    e = {"ev": "edge", "id": eid, "src": src, "dst": dst, "type": etype,
         "why": why, "map_kind": map_kind, "cite": cite}
    if ring_iso is not None:
        e["ring_iso"] = ring_iso
    if support:
        e["support"] = support
    if drops:
        e["drops"] = drops
    if refinement:
        e["refinement"] = True
    if witness:
        e["witness"] = witness
    EV.append(e)


def claim(cid, model_id, kind, statement, scope=None, certificate=None,
          zariski_closed=None, ladder="claimed", cite="",
          identity_origin=None, witness_kind=None):
    e = {"ev": "claim", "id": cid, "model": model_id, "kind": kind,
         "statement": statement, "ladder": ladder, "cite": cite}
    if identity_origin is not None:
        e["identity_origin"] = identity_origin
    if witness_kind is not None:
        e["witness_kind"] = witness_kind
    if scope is not None:
        e["scope"] = scope
    if certificate is not None:
        e["certificate"] = certificate
    if zariski_closed is not None:
        e["zariski_closed"] = zariski_closed
    EV.append(e)


def inference(iid, claim_id, path, asserted, era, cite, note="",
              severity_override=None, severity_why=None):
    e = {"ev": "inference", "id": iid, "claim": claim_id, "path": path,
         "asserted": asserted, "era": era, "cite": cite}
    if note:
        e["note"] = note
    if severity_override:
        e["severity_override"] = severity_override
        e["severity_why"] = severity_why
    EV.append(e)


def built_by(model_id, inference_id):
    EV.append({"ev": "built_by", "model": model_id, "inference": inference_id})


def note(text, **kw):
    e = {"ev": "note", "text": text}
    e.update(kw)
    EV.append(e)


# ===========================================================================
note("JC(2) plane (72,108): the GGV-Horruitiner case (8,28), arXiv:2204.14178 "
     "Prop 4.3.  Ported from whetstone/whetstone_dag.py without retyping.",
     domain="jc2", source="math-stuff/whetstone/whetstone_dag.py")

# ---- models ---------------------------------------------------------------
model("GERM",
      "A counterexample germ: P = C^2, Q = C^3 + lam*C^-1 + F honest "
      "polynomials supported on the Newton polygons N(P), N(Q).",
      chart="unshifted", declares={"place": ["y", "t", "inf"]},
      cite="POSITIVE_SLICE.md sec.1; TRANSFORM_AUDIT.md A1/F3")

model("WINDOW",
      "The coefficient-window lattice: ord_y D_(4-K) >= 12K and "
      "deg_y D_(4-K) <= (12+c)K.  A collection of LOCAL lattices, one per "
      "place.",
      chart="unshifted", declares={"place": ["y", "inf"]},
      coverage_axes=["place"],
      touches=[
          {"name": "S2 c<->D gauge, D_j = c_j*C4^(7-2j), C4 = y^7*t",
           "axis": "place", "at": ["y", "t"],
           "cite": "GAUGE_LEAK.md sec.3 S2 (denominator divisor (7-2j)*(7,1))"},
          {"name": "S10 f1 gauge, f1 = C4^3*F_-5",
           "axis": "place", "at": ["y", "t"],
           "cite": "GAUGE_LEAK.md sec.3 S10 (divisor 21(y) + 3(t))"},
          {"name": "S1 d3-killing shift, x -> x - D_3/(4*C4^2)",
           "axis": "place", "at": ["y", "t"],
           "cite": "GAUGE_LEAK.md sec.3 S1 (x/c-coordinate divisor 14(y)+2(t))"},
      ],
      reads=[
          {"name": "a_t = v_t(e) = v_t(dm1), the cell coordinate",
           "axis": "place", "at": ["t"],
           "cite": "I3_AUDIT.md D5b; divisor_filter.py"},
          {"name": "the cascade t-place layer, v_t(h_k) >= 2k-1",
           "axis": "place", "at": ["t"], "cite": "SLICE_OBSTRUCTION.md sec.3"},
          {"name": "[Q6] t^a | dm2, dm3, dm4",
           "axis": "place", "at": ["t"],
           "cite": "SPINE.md sec.8 (flagged for second-party adjudication)"},
          {"name": "v_t(Phi) = 30 exactly",
           "axis": "place", "at": ["t"], "cite": "AT_LE9_AUDIT.md B6"},
          {"name": "the degree caps deg <= (12+c)K",
           "axis": "place", "at": ["inf"],
           "cite": "window_caps_verify.py W2 [Q3]"},
          {"name": "the order floor ord >= 12K",
           "axis": "place", "at": ["y"],
           "cite": "window_caps_verify.py W2 [Q3]"},
      ],
      cite="GAUGE_LEAK.md sec.1 table: the y row is ord >= 12K, the inf row is "
           "deg <= (12+c)K, and the t row reads 'none -- the full free module'.")

# The ORDER axis lives here.  GSYS is the model regenerate_system.py actually
# builds, so it is the model that decides which slices of the Q-side family are
# consumed -- and it consumes four of them.
#
# ANSWER-INDEPENDENCE.  MODELLING_GAPS.md sec.3.1 is right that the place rule's
# inputs were transcribed from GAUGE_LEAK.md, the document recording the answer,
# so the artifact showed the rule was CONSISTENT with the answer rather than
# that it FINDS it.  This axis is better on that count and it is worth being
# precise about why, because it is the only reason to run it:
#
#   declared  <- full_system_bridge.G_generators() asserts the consumed weight
#                set {156,168,180,204}, and regenerate_system.py:22 consumes
#                D3(j) for j in {1,2,3,5}.  Both are SOURCE, mechanically
#                parseable, and neither mentions a leak.
#   touched   <- the generator family is (D~^3)_-j, u-homogeneous of weight
#                144+12j, and the Q-slice formula Q_M is verified over a range.
#                Also source plus a verification range, not an audit finding.
#
# So both sides are harvestable without knowing there is a gap.  What is NOT
# answer-independent is the choice to run the rule on this model at all, and
# that is exactly the modelling cost the whole project keeps measuring.
model("GSYS",
      "V(G1,G2,G3,G5): the four consumed rows of the shifted, stripped "
      "G-system.  Built by regenerate_system.py, which selects which slices of "
      "the Q-side family to consume.",
      chart="shifted",
      declares={"place": ["y", "inf"],
                "order": ["M=-1", "M=-2", "M=-3", "M=-5"]},
      coverage_axes=["order"],
      touches=[
          {"name": "the Q-slice generator family (D~^3)_-j, u-homogeneous of "
                   "weight 144+12j: G1=156, G2=168, G3=180, G4=192, G5=204",
           "axis": "order", "at": ["M=-1", "M=-2", "M=-3", "M=-4", "M=-5"],
           "cite": "TRANSFORM_AUDIT.md F1 ladder 156,168,180,[192],204; "
                   "regenerate_system.py:22 consumes D3(j), j in {1,2,3,5}"},
          {"name": "the Q-slice strip formula Q_M = y^(2M-3)*tau_M/t^(21-2M), "
                   "verified against the direct convolution",
           "axis": "order",
           "at": ["M=8", "M=9", "M=10", "M=11", "M=12"],
           "cite": "GAUGE_LEAK.md sec.6.2, verified M = 8..12 on genuine "
                   "polygon-supported data, both regimes"},
      ],
      reads=[
          {"name": "the Q-side degree condition against N(Q), with equality",
           "axis": "order",
           "at": ["M=0", "M=1", "M=2", "M=3", "M=4", "M=5", "M=6", "M=7",
                  "M=8", "M=9", "M=10", "M=11", "M=12"],
           "cite": "GAUGE_LEAK.md sec.6 item 14: 'the Q-side degree side "
                   "matches N(Q) with equality at every M = 0..12'"},
          {"name": "tau_10 and tau_9, the quantities the non-implication "
                   "witness turns on",
           "axis": "order", "at": ["M=9", "M=10"],
           "cite": "GAUGE_LEAK.md sec.6 items 15-16: tau_10 = 3(d2 + h^2), "
                   "tau_9 = 3d1 + 6h*d2 + h^3; the witness is genuine data "
                   "satisfying all 58 P-side conditions with tau_10(-1) != 0"},
      ],
      universe=[1387, 63346],
      cite="generators.json; full_system_bridge.G_generators(); universe from "
           "FIELD_SCOPE_AUDIT.md sec.0(c) (C08/C20 OFF, the theorem-facing "
           "scope)")
model("GSYS_RL",
      "The same system with the C08/C20 residue kills applied: the Q-scoped "
      "universe that public v0.3.2 shipped.",
      chart="shifted", declares={"place": ["y", "inf"]},
      universe=[1365, 52005],
      cite="FIELD_SCOPE_AUDIT.md sec.0(c) (C08/C20 ON)")
model("GSYS_K", "V(G1,G2,G3,K) with K the four-term syzygy row.",
      chart="shifted", declares={"place": ["y", "inf"]},
      cite="DIVISOR_SYZYGY.md sec.1")
model("GSYS_G4",
      "GSYS + the lambda row G4_stripped = -lam*y^4*(y+1)^28 (u-weight 192).",
      chart="shifted", declares={"place": ["y", "inf"]},
      cite="TRANSFORM_AUDIT.md F1")
model("GSYS_POS",
      "GSYS + the three inverse-shift positive-slice conditions (A),(B),(C).",
      chart="shifted", declares={"place": ["y", "inf"]},
      cite="POSITIVE_SLICE.md sec.5")
model("GSYS_POS_G4",
      "GSYS_POS + the lambda row: the refinement whose non-reopening of sub2 "
      "is the monotonicity instance this project actually banked.",
      chart="shifted", declares={"place": ["y", "inf"]},
      cite="SESSION_HANDOFF.md G4 acceptance criteria; G4_ROW.md")
model("CASCADE",
      "The min-plus / max-plus valuation option tree over the q-places, t and "
      "infinity: a valuation abstraction of the G-system.",
      chart="valuation", declares={"place": ["y", "t", "inf"]},
      cite="cascade_engine.py")

model("RES08_L",
      "C08 support: level 5, {d1^2 d2^2, d1 d2 e, e^2}; the depth-1 residue "
      "equation 6X^2D^2 - 9XDE - E^2 = 0, over L = Q(sqrt 17).",
      chart="valuation", cite="cascade_engine.py:56-75; RESIDUE_LEMMAS.md:136")
model("RES08_K",
      "The same C08 support over an arbitrary characteristic-zero K.",
      chart="valuation", cite="FIELD_SCOPE_AUDIT.md sec.0")
model("RES20_L",
      "C20 support: level 4; 61X^2D^2 + 6XDE - 11E^2, over L = Q(sqrt 17).",
      chart="valuation", cite="cascade_engine.py:56-75; RESIDUE_LEMMAS.md:148")
model("RES20_K",
      "The same C20 support over an arbitrary characteristic-zero K.",
      chart="valuation", cite="FIELD_SCOPE_AUDIT.md sec.0")

model("ELIM_IMAGE",
      "The TRUE image of the a10_b0000_T1 specialization map -- constructible, "
      "by Chevalley, and never computed.",
      chart="shifted", cite="GAUGE_LEAK.md 'Why this exists'")
model("ELIM_CLOSURE",
      "What elimination actually returns: the Zariski closure of that image.",
      chart="shifted",
      cite="GAUGE_LEAK.md 'Why this exists'; POSITIVE_SLICE.md HEADLINE")
model("R9_RELAXED",
      "The R9 blowup systems as handed to the emptiness-triage solver.",
      chart="valuation",
      cite="EMPTINESS_TRIAGE.md; SESSION_HANDOFF.md acceptance criteria")

model("SLICEPHI",
      "slice_phi_yplace's model: the whole slice calculus run in the SHIFTED "
      "chart, with (P<)/(Q) and the cascade base imposed THERE.",
      chart="shifted", cite="SLICE_PHI_YPLACE.md sec.1, sec.3")
model("SYZCOLL",
      "syzygy_collision's model: the exact rows plus valuation arithmetic, "
      "entirely in the UNSHIFTED chart.",
      chart="unshifted",
      cite="AT_LE9_AUDIT.md sec.4 ('what does transfer')")

# ---- edges ----------------------------------------------------------------
edge("E1", "GERM", "WINDOW", "NECESSARY_CONDITION",
     "Retain only the window caps of the germ's coefficients; forget the "
     "polygon-support conditions the caps do not encode.",
     map_kind="RATIONAL", support=["y", "t"],
     drops=["t-adic integrality of every slice",
            "ord P_0 >= 0 (the window gives only >= -2)"],
     cite="GAUGE_LEAK.md sec.5 accounting theorem: 80-58 = 22 (sub2), "
          "116-58 = 58 (sub1), Jacobian rank exactly 58",
     witness="GAUGE_LEAK.md sec.6.4: genuine polygon-supported data satisfying "
             "all 58 P-side conditions has tau_10(-1) = 147/8 != 0, so the "
             "window does not imply the Q-side conditions.")

edge("E2", "WINDOW", "GSYS", "NECESSARY_CONDITION",
     "Apply the d3-killing shift and keep only four of the seven Q-slice rows. "
     "V(GSYS) is STRICTLY LARGER than the image of the germs.",
     map_kind="RATIONAL", support=["y", "t"],
     drops=["the j=4 lambda row G4 (u-weight 192)",
            "the bracket slices n <= 1",
            "N(Q) support and corner conditions",
            "unshifted-chart divisibility of the positive slices"],
     cite="I3_AUDIT.md sec.0 and E4b/E4d; TRANSFORM_AUDIT.md F1/F2/F3",
     witness="I3_AUDIT.md E4d: the shifted point d2=d1=d0=0, h=1 satisfies "
             "every G row (there is no d3 row) yet un-shifts to [u^2]H*^2 = "
             "7/4, so P_6 = y^10*[u^2]H*^2/t^2 is not a polynomial.  "
             "s = D_3/(4*C4^2) is polynomial only when D_3 = 0 (E4b).")

edge("E3", "GSYS_K", "GSYS", "EQUIVALENCE",
     "The K-syzygy: <G1,G2,G3,G5> == <G1,G2,G3,K>.  IDEAL EQUALITY, not a "
     "weakening -- K is an exact Q[d]-combination of the generators and G5 is "
     "recovered from K.",
     map_kind="POLYNOMIAL",
     # A RING ISOMORPHISM, and here in its strongest form: the two ideals are
     # EQUAL, so the coordinate rings are not merely isomorphic but identical
     # and the map is the identity.  This is what an EQUIVALENCE needs before
     # an IDENTITY may cross it -- a converse on POINTS would not be enough,
     # since V(x^2) and V(x) share their single point while `x = 0` holds in
     # one coordinate ring and fails in the other.  Established by C1 (residual
     # exactly 0) and C3 (G5 recovered), not by the type feeling reversible.
     ring_iso=True,
     cite="DIVISOR_SYZYGY.md sec.1: 2*(G5 + d2*G3 + d1*G2 + d0*G1) == "
          "2*Phi - e*(d2*e^2 + 3*e*S + 3*R^2), residual exactly 0 (check C1); "
          "G5 = K/2 - d2*G3 - d1*G2 - d0*G1 (check C3).")

edge("E4", "GSYS_G4", "GSYS", "NECESSARY_CONDITION",
     "Refinement, read in the safe direction: dropping the lambda row weakens "
     "the system.  V(GSYS_G4) subset V(GSYS).",
     refinement=True,
     drops=["the lambda row: G4_stripped = -lam*y^4*(y+1)^28, i.e. G4 has "
            "exactly the divisor 4*(0) + 28*(-1)"],
     cite="TRANSFORM_AUDIT.md sec.2 (+32 sub2 / +48 sub1 coefficient "
          "equations)",
     witness="TRANSFORM_AUDIT.md 2.3: the point (2Phi-3, -1/3, 1, 1, 0, 1, "
             "1/6) lies on G1=G2=G3=G5=0 with G4 = -3Phi + 37/24 != 0, so G4 "
             "is not in <G1,G2,G3,G5body+Phi>.")

edge("E5", "GSYS_POS", "GSYS", "NECESSARY_CONDITION",
     "Refinement: dropping the three positive-slice conditions weakens the "
     "system.",
     refinement=True,
     drops=["(A), (B), (C): the constant terms of the M = 6,5,4 slice "
            "conditions"],
     cite="POSITIVE_SLICE.md sec.5")

edge("E5b", "GSYS_POS_G4", "GSYS_POS", "NECESSARY_CONDITION",
     "Refinement of the refinement: this is the edge whose AGAINST direction "
     "let the project add the G4 row without recomputing sub2.",
     refinement=True, drops=["the lambda row"],
     cite="SESSION_HANDOFF.md 'WHAT LANDED' + the G4 acceptance criteria")

edge("E6", "GERM", "GSYS_POS", "NECESSARY_CONDITION",
     "The composite the positive-slice kill actually uses: germ data satisfies "
     "the four G rows AND the three re-imposed polynomiality conditions.",
     map_kind="RATIONAL", support=["y", "t"],
     drops=["55 of the 58 P-side conditions", "all 126 Q-side conditions"],
     cite="POSITIVE_SLICE.md sec.2-sec.5; GAUGE_LEAK.md sec.5b "
          "('positive_slice.py spends 3 of the 58')")

edge("E7", "GSYS", "CASCADE", "NECESSARY_CONDITION",
     "Valuation abstraction: replace polynomials by their valuations at each "
     "place and enumerate consistent tie/drop configurations.",
     drops=["everything except the min-plus / max-plus data"],
     cite="cascade_engine.py")

edge("E8", "RES08_L", "RES08_K", "BASE_EXTENSION",
     "The coefficient field changes from L = Q(sqrt 17) to an arbitrary "
     "characteristic-zero K.  C is a Q-algebra, so K = C is in scope.",
     drops=["every field-relative arithmetic fact, in particular square "
            "classes"],
     cite="FIELD_SCOPE_AUDIT.md sec.0, sec.1.2, sec.2",
     witness="RESIDUE_LEMMAS.md:162-166 / FIELD_SCOPE_REPAIR.md sec.1.1: the "
             "support has REAL torus points, hence is NONEMPTY over R and over "
             "C.  The flag is a true positive, not a conservative refusal.")

edge("E9", "RES20_L", "RES20_K", "BASE_EXTENSION",
     "Same, for C20 (square class 170).",
     drops=["every field-relative arithmetic fact"],
     cite="FIELD_SCOPE_AUDIT.md sec.0, sec.1.1",
     witness="RESIDUE_LEMMAS.md:162-166: real torus points on this support "
             "too.")

edge("E9b", "GSYS_RL", "GSYS", "BASE_EXTENSION",
     "The universe-level shadow of E8/E9: the Q-scoped Phase-D universe sits "
     "inside the char-0 one.  Recorded because it carries the measured radius.",
     drops=["11341 Phase-D states and 22 flag cases"],
     cite="FIELD_SCOPE_AUDIT.md sec.0(c): 1365 -> 1387 flag cases, "
          "52005 -> 63346 states, 11341 returning; 1685 genuinely return after "
          "the e|Phi divisor filter.")

edge("E10", "ELIM_IMAGE", "ELIM_CLOSURE", "IMAGE_CLOSURE",
     "Elimination returns the Zariski closure.  By Chevalley the true image is "
     "constructible, so the closure can contain boundary points with no lift.",
     drops=["the open conditions cutting the constructible image out of its "
            "closure"],
     cite="GAUGE_LEAK.md 'Why this exists'",
     witness="POSITIVE_SLICE.md HEADLINE: a10_b0000_T1's surviving family "
             "satisfies the four canonical G rows IDENTICALLY -- a genuine "
             "family on the closure with no polynomial P behind it.")

edge("E11", "GERM", "R9_RELAXED", "IMAGE_CLOSURE",
     "The R9 blowup systems as handed to a solver: a relaxed model of the same "
     "shape.  Recorded because the project got the typing RIGHT on this one.",
     drops=["liftability of a solution back to germ data"],
     cite="SESSION_HANDOFF.md acceptance criteria: 'A NON-EMPTY verdict is a "
          "POSITIVE result: it proves solver spending on that target is "
          "futile.'")

edge("E12", "GERM", "SLICEPHI", "NECESSARY_CONDITION",
     "Pass to the shifted chart and run the slice calculus there.  Same lossy "
     "edge as E2 -- the shifted model is a strict relaxation.",
     map_kind="RATIONAL", support=["y", "t"],
     drops=["unshifted-chart polynomiality, which is what produces "
            "t^(2n-2) | p_n in the first place"],
     cite="SLICE_PHI_YPLACE.md sec.1, sec.3; AT_LE9_AUDIT.md sec.4",
     witness="AT_LE9_AUDIT.md F11: on SLICE_OBSTRUCTION.md sec.4's own genuine "
             "joint control the shift gives p~_3 = (a^3 t^3 - 4ab t^4 + "
             "8c t^5)/4, so v_t(p~_3) = 3 while (P<) at n = 3 demands "
             "t^4 | p~_3.  F12: the assumed shifted profile (3,5,7,a,11,13,14) "
             "transfers only as (2,3,.,a,10,11,.).")

edge("E13", "GERM", "SYZCOLL", "NECESSARY_CONDITION",
     "syzygy_collision's abstraction: keep the exact rows and bound valuations "
     "IN THE UNSHIFTED CHART.  The only thing moved across the shift is the "
     "dictionary, which is denominator-free.",
     map_kind="POLYNOMIAL",
     drops=["everything except the four exact rows and the t-valuations"],
     cite="AT_LE9_AUDIT.md sec.4 F13: r~_13 = r_13, r~_14 = r_14 + a*r_13, "
          "r~_15 = r_15 + 2a*r_14 + a^2*r_13, r~_17 = r_17 + 4a*r_16 + "
          "6a^2*r_15 + 4a^3*r_14 + a^4*r_13, a = h_1/4 -- polynomial, no "
          "denominators anywhere.")

# ---- claims ---------------------------------------------------------------
claim("CL-C08", "RES08_L", "EMPTY",
      "the C08 residue equation has no solution with all leading coefficients "
      "nonzero",
      scope="Q(sqrt 17)", certificate="NONSQUARE_CLASS",
      ladder="exact-checked",
      cite="RESIDUE_LEMMAS.md:136 (disc square class 105); "
           "residue_lemmas_verify.py")
claim("CL-C20", "RES20_L", "EMPTY",
      "the C20 residue equation has no solution with all leading coefficients "
      "nonzero",
      scope="Q(sqrt 17)", certificate="NONSQUARE_CLASS",
      ladder="exact-checked",
      cite="RESIDUE_LEMMAS.md:148 (square class 170)")

claim("CL-C08-REAL", "RES08_K", "NONEMPTY",
      "the C08 support has real (hence complex) torus points",
      # ASSERTED: quoted from a lemma, no point exhibited here.  The claim is
      # load-bearing -- it is what makes the C08 refusal a TRUE positive rather
      # than a conservative one -- and nothing in this graph could tell a real
      # torus point from a confident sentence about one.
      witness_kind="ASSERTED",
      scope="R", ladder="exact-checked",
      cite="RESIDUE_LEMMAS.md:162-166, quoted at FIELD_SCOPE_AUDIT.md sec.0")
claim("CL-C20-REAL", "RES20_K", "NONEMPTY",
      "the C20 support has real (hence complex) torus points too",
      witness_kind="ASSERTED",   # same lemma, same absence of an exhibited point
      scope="R", ladder="exact-checked",
      cite="RESIDUE_LEMMAS.md:162-166, quoted verbatim in edge E9's witness "
           "in whetstone_dag.py; recorded here as a CLAIM so that the "
           "true-positive grading of the C20 flag is DERIVED, not asserted.")

claim("CL-POSSLICE", "GSYS_POS", "EMPTY",
      "on a10_b0000 the three positive-slice conditions have no common "
      "solution in any characteristic-zero field",
      certificate="NONZERO_RESULTANT", ladder="exact-checked",
      cite="POSITIVE_SLICE.md sec.6: res(p,q) = 561971200, confirmed twice by "
           "two disjoint mechanisms; positive_slice.py 63/63 + _verify 79/79")
claim("CL-KSYZ", "GSYS_K", "EMPTY",
      "emptiness statements proved on the sparse K-row system",
      certificate="UNIT_IDEAL_CERT", ladder="exact-checked",
      cite="DIVISOR_SYZYGY.md sec.1")
claim("CL-KSYZ-ID", "GSYS", "IDENTITY",
      "G5 = K/2 - d2*G3 - d1*G2 - d0*G1: the dense G5 row is recovered from "
      "the sparse K row",
      # AMBIENT, and this one is CHECKED rather than judged.  divisor_syzygy.py
      # C3 computes `sp.expand(recovered - G5) == 0` -- symbolic expansion in
      # the polynomial ring, no ideal reduction and no equation assumed -- and
      # returns residual 0.  Re-run 2026-07-26: 7/7 pass.  So the relation holds
      # before any of GSYS's equations are imposed and survives dropping them.
      # DIVISOR_SYZYGY.md sec.1 already draws the distinction in prose without
      # having a field for it: "K is not merely a consequence, it is
      # exchangeable."
      identity_origin="AMBIENT",
      ladder="exact-checked", cite="divisor_syzygy.py check C3")
claim("CL-SUB2-EMPTY", "GSYS_POS", "EMPTY", "standard sub2 is EMPTY",
      certificate="NONZERO_RESULTANT", ladder="exact-checked",
      cite="POSITIVE_SLICE.md HEADLINE")

claim("CL-PSLICE-COND", "GERM", "PREDICATE",
      "(P<): t^(14-2M) | [u^(8-M)]H^2, equivalently t^(2n-2) | p_n; and (Q); "
      "and the cascade base v_t(h_k) >= 2k-1",
      zariski_closed=True, ladder="independently-audited",
      cite="POSITIVE_SLICE.md sec.2; SLICE_OBSTRUCTION.md sec.3 "
           "(audited 56/56)")
claim("CL-DICT", "GERM", "IDENTITY",
      "the shift dictionary: d2 = h_2 - (3/8)h_1^2, e = h_5, "
      "R = h_6 + (1/4)h_1h_5, S = h_7 + (1/2)h_1h_6 + (1/16)h_1^2h_5",
      # AMBIENT, and INDEPENDENTLY RECOMPUTED rather than read.  An external
      # check derived the dictionary from scratch by two genuinely different
      # routes -- series composition of (1-au)^4 H(u/(1-au)), and a literal
      # Taylor shift x -> x - h_1/4 of the Laurent polynomial -- with the h_k
      # as FREE symbols, importing nothing from the source repo.  Both match,
      # difference exactly 0.  Ambience probes: adding h_9, h_10, h_11 leaves
      # h~_0..h~_7 unchanged, and a generic rational specialisation satisfying
      # NO equation still satisfies the dictionary.  So it holds before any
      # germ equation is imposed and survives dropping them.
      #
      # THE ONE NON-FREE INPUT is the normalisation h_0 = D_4 = 1.  With h_0
      # generic the shift is a = h_1/(4h_0) and the constants become
      # 3/(8h_0), 1/(4h_0), 1/(16h_0^2) -- so 3/8 and friends encode "top
      # degree 4, leading coefficient normalised", a coordinate choice, not an
      # equation of the germ.  Ambient stands.
      #
      # CORRECTION TO AN EARLIER JUSTIFICATION IN THIS FILE.  A previous
      # version of this comment credited AT_LE9_AUDIT.md's claim that the
      # dictionary was "checked by two independent mechanisms (falling
      # factorials, and the generating function) against each other".  THAT
      # CLAIM IS FALSE and a mutation test proves it: swapping gbinom's falling
      # factorial for a rising one breaks C4-C7 and leaves C9 PASSING, because
      # gf_transform and htil are the same summation over the same shared
      # gbinom primitive.  C9 has zero discriminating power over the
      # dictionary.  The honest independent derivation is window_caps_verify.py
      # W3, which does an actual sp.series recomposition -- so
      # `independently-audited` stands, on different evidence than was cited.
      #
      # (That is a finding about the source repo's own evidence grading, inside
      # the audit whose headline result C-1 is that two proofs were less
      # independent than advertised.  Recorded here; not our repo to fix.)
      #
      # SCOPE LIMIT, and it matters: this is ambient as a COEFFICIENT identity
      # only.  i3_audit.py E4b proves the d3-killing shift is NOT an
      # automorphism of K[x,y], so divisibility and valuation conditions do not
      # transport through it freely -- which is AT_LE9_AUDIT's severe finding
      # C-2 against SLICE_PHI_YPLACE.md, and is why E13 carries only the
      # dictionary and why GE-style chart edges stay lossy.
      identity_origin="AMBIENT",
      ladder="independently-audited",
      cite="AT_LE9_AUDIT.md C4-C7; window_caps_verify.py W3 (the genuinely "
           "independent derivation); recomputed from scratch 2026-07-26")
claim("CL-ATLE9-SYZ", "SYZCOLL", "EMPTY",
      "a_t >= 10 is refuted: a_t + v_t(B) = 30 with v_t(B) forced too high",
      certificate="EXACT_VALUATION_COLLISION", ladder="independently-audited",
      cite="AT_LE9_AUDIT.md sec.2(7), E4-E9; syzygy_collision.py 25/25")
claim("CL-ATLE9-PHI", "SLICEPHI", "EMPTY",
      "a_t >= 10 is refuted: the four leading-jet equations generate the unit "
      "ideal at the shifted profile",
      certificate="UNIT_IDEAL_CERT", ladder="exact-checked",
      cite="SLICE_PHI_YPLACE.md sec.4; reproduced at AT_LE9_AUDIT.md F1-F9")

claim("CL-A10-SURV", "ELIM_CLOSURE", "NONEMPTY",
      "the a10_b0000_T1 family satisfies the four canonical G rows "
      "identically, so the ideal is genuinely non-empty and no Groebner engine "
      "can close it",
      # EXHIBITED: the family is written down and satisfies the rows
      # identically, which is a substitution check.
      witness_kind="EXHIBITED",
      scope="Q", ladder="exact-checked", cite="POSITIVE_SLICE.md HEADLINE")
claim("CL-R9-NONEMPTY", "R9_RELAXED", "NONEMPTY",
      "R9 z = 4,5,6 are exactly NON-EMPTY (exact witnesses)",
      witness_kind="EXHIBITED",  # the statement says so: exact witnesses
      scope="Q", ladder="exact-checked",
      cite="EMPTINESS_TRIAGE.md; emptiness_triage.py 6/6 gate")

# ---- inferences: error 1, as it shipped in public v0.3.2 -------------------
inference("INF-C08-HIST", "CL-C08", [["E8", "ALONG"]],
          "the branch of the option tree does not exist -- consumed as "
          "GEOMETRIC emptiness over the theorem's arbitrary char-0 K",
          era="HISTORICAL",
          cite="FIELD_SCOPE_AUDIT.md sec.1.2: the guard is "
               "`APPLY_RESIDUE_KILLS and (level, exponent_set) in "
               "FORBIDDEN_RISES` -- the boolean flag and nothing else; no field "
               "parameter anywhere in cascade_engine.py.  Shipped in public "
               "v0.3.2.")
inference("INF-C20-HIST", "CL-C20", [["E9", "ALONG"]],
          "same, for C20", era="HISTORICAL",
          cite="FIELD_SCOPE_AUDIT.md sec.1.2")
inference("INF-C08-CURRENT", "CL-C08", [],
          "KILL -> CONSTRAINT: the equation is retained as a residue "
          "constraint and no transport across the field extension is asserted",
          era="CURRENT",
          cite="FIELD_SCOPE_REPAIR.md sec.0-1.1; APPLY_RESIDUE_KILLS = False",
          note="The repaired inference must NOT be flagged, or the framework "
               "cannot tell a defect from its fix.")

# ---- inferences: error 3, the chart error ---------------------------------
inference("INF-SLICEPHI", "CL-PSLICE-COND", [["E12", "ALONG"]],
          "(P<)/(Q) and the cascade base hold in the SHIFTED chart, so the "
          "slice calculus may be run there",
          era="HISTORICAL",
          cite="SLICE_PHI_YPLACE.md sec.1, sec.3: 'the lane's cascade leaves "
               "h_1 free, so the shifted chart h_1 = 0 is a specialisation and "
               "the bound holds there a fortiori.'")
inference("INF-SLICEPHI-KILL", "CL-ATLE9-PHI", [["E12", "AGAINST"]],
          "a_t <= 9, as an INDEPENDENT second proof",
          era="HISTORICAL", cite="SLICE_PHI_YPLACE.md sec.4",
          note="The emptiness transport itself IS licensed; what is not "
               "licensed is the predicate import INF-SLICEPHI the model rests "
               "on.  A licensed conclusion drawn in a model built by an "
               "unlicensed step is still unsound -- see the TAINT rule.")

# ---- the sound leg, which must NOT be flagged -----------------------------
inference("INF-SYZCOLL-DICT", "CL-DICT", [["E13", "ALONG"]],
          "the shift dictionary may be used to rewrite S, R, e",
          era="CURRENT", cite="AT_LE9_AUDIT.md C1-C9, F13")
inference("INF-SYZCOLL", "CL-ATLE9-SYZ", [["E13", "AGAINST"]],
          "a_t <= 9 for every germ", era="CURRENT",
          cite="AT_LE9_AUDIT.md sec.0 C-4: 'entirely in the unshifted chart "
               "and untouched by C-2 ... it is the load-bearing proof, and it "
               "is sound.'")

# ---- the positive controls ------------------------------------------------
inference("INF-KSYZ", "CL-KSYZ", [["E3", "ALONG"]],
          "emptiness proved on <G1,G2,G3,K> is emptiness of <G1,G2,G3,G5>",
          era="CURRENT", cite="DIVISOR_SYZYGY.md sec.1")
inference("INF-KSYZ-REV", "CL-KSYZ-ID", [["E3", "AGAINST"]],
          "the dense G5 row may be replaced by the sparse K row, with no "
          "saturation and no division by e",
          era="CURRENT", cite="divisor_syzygy.py C3",
          note="This is the direction that would be FORBIDDEN on a "
               "NECESSARY_CONDITION edge.  The sharpest positive control here.")
inference("INF-POSSLICE", "CL-POSSLICE", [["E6", "AGAINST"]],
          "no germ lies over a10_b0000: the cell is EMPTY with no field-scope "
          "caveat",
          era="CURRENT", cite="POSITIVE_SLICE.md HEADLINE and sec.6",
          note="Contrast pair with INF-C08-HIST: both emptiness results were "
               "COMPUTED over Q.  This one has a certificate (a nonzero "
               "rational resultant) and base-changes; that one does not.")
inference("INF-G4-MONO", "CL-SUB2-EMPTY", [["E5b", "AGAINST"]],
          "adding the G4 row cannot reopen sub2, so sub2 need not be recomputed",
          era="CURRENT",
          cite="SESSION_HANDOFF.md G4 acceptance criteria ('Must not resurrect "
               "anything in sub2'); G4_ROW.md ('kills nothing')")

# ---- the closure / image type ---------------------------------------------
inference("INF-A10-SURV", "CL-A10-SURV", [["E10", "AGAINST"]],
          "a10_b0000_T1 SURVIVES -- read as 'a counterexample germ may live "
          "here'",
          era="HISTORICAL",
          cite="POSITIVE_SLICE.md HEADLINE ('That cell survives because the "
               "surviving family satisfies the four canonical G rows "
               "identically')",
          severity_override="TRIAGE",
          severity_why="NOT an accusation.  The project's own recorded wording "
                       "was 'that cell survives', which is CORRECT, and this "
                       "project diagnosed the closure/image gap itself.  The "
                       "type layer's contribution is only to route the "
                       "survivor to ARTIFACT-CANDIDATE (refine the model) "
                       "instead of to 'buy more solver time'.  The derived "
                       "severity is UNSOUND_PREMISE because the graph holds no "
                       "claim contradicting the conclusion; the downgrade "
                       "reflects what was historically asserted, which is not "
                       "a fact about the graph.")
inference("INF-R9", "CL-R9-NONEMPTY", [],
          "solver spending on that target is futile -- a statement about the "
          "MODEL, with no transport to the germs asserted",
          era="CURRENT", cite="SESSION_HANDOFF.md emptiness-triage criteria",
          note="Positive control for IMAGE_CLOSURE: the project got this right "
               "and the framework must agree.")

# ---- provenance -----------------------------------------------------------
built_by("SLICEPHI", "INF-SLICEPHI")


with open(OUT, "w", encoding="utf-8") as fh:
    fh.write("# JC(2) plane (72,108) typed relaxation DAG.\n")
    fh.write("# Ported from math-stuff/whetstone/whetstone_dag.py.\n")
    for e in EV:
        fh.write(json.dumps(e, sort_keys=True) + "\n")
print("wrote %s (%d events)" % (OUT, len(EV)))
