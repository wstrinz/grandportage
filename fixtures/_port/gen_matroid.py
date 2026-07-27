"""Emit fixtures/matroid/graph.jsonl -- matroid realizability, Whetstone's
second domain.

Ported from math-stuff/whetstone/matroid_transfer.py.  Same discipline as the
JC(2) port: identifiers, types and citations unchanged, answer key removed to
expect.json.

Two substantive changes, both forced by Grand Portage's stricter fold and both
recorded here rather than buried:

  1. THE FANO NO-SATURATION CONTROL WAS ON A DISCONNECTED PATH.
     matroid_transfer.py routes IM-FANO-NO-SAT (a claim about the Fano ideal
     over Q) across M-E4, which is the NON-Fano saturation edge over F_2.  The
     prototype has no path-continuity check, so this passed silently.  Grand
     Portage's fold rejects it.  Ported as its own edge M-E4f between two new
     models FANO_Q_UNSAT -> FANO_Q_SAT, which is what the control was always
     about.  The verdict is unchanged (licensed); only the route is now real.

  2. CM-NF-F2-EMPTY IS ADDED.
     The published fact -- non-Fano is representable iff char != 2 -- was in
     matroid_transfer.py's prose but not in its graph.  Recorded as a claim so
     that IM-NF-SKIP-SAT's grading as a TRUE POSITIVE is derived from a
     contradiction in the graph rather than hand-assigned.  Note the kernel
     forces its certificate to be declared field-relative, which is correct:
     non-Fano IS realizable over Q.
"""

import json
import os

OUT = os.path.abspath(os.path.join(
    os.path.dirname(os.path.abspath(__file__)), "..", "matroid", "graph.jsonl"))

EV = []


def certificate(cid, base_changes, why):
    EV.append({"ev": "certificate", "id": cid, "base_changes": base_changes,
               "why": why})


def model(mid, desc, field=None, cite=""):
    e = {"ev": "model", "id": mid, "desc": desc, "cite": cite}
    if field:
        e["field"] = field
    EV.append(e)


def edge(eid, src, dst, etype, why, map_kind="IDENTITY_MAP", drops=None,
         cite="", witness="", ring_iso=None):
    e = {"ev": "edge", "id": eid, "src": src, "dst": dst, "type": etype,
         "why": why, "map_kind": map_kind, "cite": cite}
    if ring_iso is not None:
        e["ring_iso"] = ring_iso
    if drops:
        e["drops"] = drops
    if witness:
        e["witness"] = witness
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
         "asserted": asserted, "era": "matroid", "cite": cite}
    if note:
        e["note"] = note
    EV.append(e)


def note(text, **kw):
    e = {"ev": "note", "text": text}
    e.update(kw)
    EV.append(e)


# ===========================================================================
note("Matroid realizability: Whetstone's second domain.  Ported from "
     "math-stuff/whetstone/matroid_transfer.py.  Ground truth is externally "
     "published (Oxley; Sage matroid database; Brandt-Wiebe arXiv:1804.05264; "
     "MacLane 1936; Coxeter's Moebius-Kantor coordinates).",
     domain="matroid", source="math-stuff/whetstone/matroid_transfer.py")

# ---- certificates ---------------------------------------------------------
certificate("FINITE_ORIENTATION_EXHAUSTION", True,
            "An orientation is a combinatorial object with no field in it: "
            "the sign-vector axioms are checked over a finite search space.  "
            "Non-orientability therefore carries no field dependence at all.")
certificate("PAPPUS_IDENTITY", True,
            "A realization over any commutative field would violate Pappus's "
            "hexagon theorem, which holds over every commutative field.  The "
            "obstruction is an identity, not an arithmetic accident.")
certificate("FINITE_FIELD_EXHAUSTION", False,
            "Realization spaces over a FINITE field are finite and can be "
            "enumerated -- but the resulting emptiness is a fact about that "
            "one field and nothing else.  It must not base-change: non-Fano "
            "is empty over F_2 and NONEMPTY over Q.")

# ---- models ---------------------------------------------------------------
model("ML8_Q", "realization space of ML8 over Q", field="Q")
model("ML8_QS", "realization space of ML8 over Q(sqrt(-3)), the MINIMAL "
      "extension in which the obstruction dissolves", field="Q(sqrt(-3))")
model("ML8_R", "realization space of ML8 over R", field="R")
model("ML8_C", "realization space of ML8 over C", field="C")
model("ML8_NORM_C", "the frame-normalised system for ML8 over C (4 points "
      "pinned to the standard frame)", field="C")
model("ML8_ORIENT", "the oriented matroid model of ML8: sign vectors "
      "satisfying the oriented-matroid axioms.  NO FIELD.")
model("FANO_Q", "realization space of the Fano matroid over Q", field="Q")
model("FANO_C", "realization space of the Fano matroid over C", field="C")
model("FANO_F2", "realization space of the Fano matroid over F_2", field="F_2")
model("FANO_Q_SAT", "V(I_sat) for the Fano matroid over Q: the SATURATED "
      "determinantal ideal, i.e. the realization space proper", field="Q")
model("FANO_Q_UNSAT", "V(I_unsat) for the Fano matroid over Q: the line "
      "determinants with NO saturation", field="Q")
model("NF_Q", "realization space of the non-Fano matroid over Q", field="Q")
model("NF_F2", "realization space of the non-Fano matroid over F_2",
      field="F_2")
model("NF_F2_SAT", "V(I_sat) over F_2: the SATURATED determinantal ideal, "
      "i.e. the Zariski closure of the realization space", field="F_2")
model("NF_F2_UNSAT", "V(I_unsat) over F_2: the ideal of the line determinants "
      "(equivalently the 4x4 minors of the slack matrix) with NO saturation",
      field="F_2")
model("U35_REAL", "the realization space of U_3,5: the complement of six "
      "lines in the (a,b) plane.  Locally closed, NOT closed.", field="Q")
model("U35_CLOSURE", "its Zariski closure, the whole affine plane -- what an "
      "elimination or a saturated ideal actually returns", field="Q")
model("NP_REAL", "realization space of the non-Pappus matroid over R",
      field="R")
model("NP_ORIENT", "the oriented matroid model of the non-Pappus matroid")

# ---- edges ----------------------------------------------------------------
edge("M-E1", "ML8_R", "ML8_C", "BASE_EXTENSION",
     "The coefficient field changes from R to C.",
     drops=["every field-relative arithmetic fact, in particular square "
            "classes"],
     witness="ML8 has an exact realization over Q(sqrt(-3)) subset C and none "
             "over R, so the extension is genuinely lossy.",
     cite="Coxeter's coordinates, Moebius-Kantor configuration")
edge("M-E1q", "ML8_Q", "ML8_QS", "BASE_EXTENSION",
     "Q to Q(sqrt(-3)): a degree-2 extension, the SMALLEST field change that "
     "defeats the certificate.  Verbatim the case the NONSQUARE_CLASS comment "
     "names -- 'this quadratic form has no zero because its discriminant is a "
     "non-square' does not survive adjoining the square root.",
     drops=["the square class of -3"],
     witness="ML8 has an exact realization over Q(sqrt(-3)) and none over Q, "
             "so a degree-2 extension already flips the answer.",
     cite="derived in matroid_transfer.py; G-ML8-C-WITNESS exhibits the "
          "realization")
edge("M-E1c", "ML8_QS", "ML8_C", "BASE_EXTENSION",
     "Q(sqrt(-3)) to C: the direction in which a witness DOES travel.",
     witness="carries a positive control, whose whole point is that "
             "BASE_EXTENSION licenses NONEMPTY along the arrow while refusing "
             "EMPTY -- the reversed asymmetry.",
     cite="derived in matroid_transfer.py")
edge("M-E2", "ML8_C", "ML8_NORM_C", "EQUIVALENCE",
     "Frame normalisation.  Given four points in general position there is a "
     "UNIQUE element of PGL(3,K) carrying them to the standard frame, over "
     "every field K.  Realizations and normalised solutions correspond "
     "bijectively -- an EQUIVALENCE, not a relaxation.",
     map_kind="POLYNOMIAL",
     # A ring isomorphism: the normalisation is a linear change of coordinates
     # by a UNIQUE element of PGL(3,K), so it is invertible on the coordinate
     # ring and not merely bijective on realizations.  The uniqueness is what
     # supplies the inverse; a bijection alone would not.
     ring_iso=True,
     cite="standard; empirically confirmed by G-ML8-C-WITNESS, which lifts a "
          "normalised solution to a full realization satisfying all 56 rank "
          "conditions")
edge("M-E3", "ML8_R", "ML8_ORIENT", "NECESSARY_CONDITION",
     "Every realization over an ORDERED field induces an orientation (take "
     "the signs of the bracket determinants).  The orientation forgets the "
     "coordinates.  Tighter -> looser.",
     drops=["the coordinates themselves; every metric and arithmetic fact"],
     witness="the non-Pappus matroid is ORIENTABLE (Folkman-Lawrence: a rank-3 "
             "matroid is orientable iff it has a pseudoline arrangement, and "
             "non-Pappus has one) yet is NOT representable over any "
             "commutative field.  So the edge is strictly lossy.",
     cite="Folkman-Lawrence topological representation theorem; "
          "Richter-Gebert & Ziegler, Handbook of Discrete and Computational "
          "Geometry ch.6")
edge("M-E3np", "NP_REAL", "NP_ORIENT", "NECESSARY_CONDITION",
     "The same forgetful map for the non-Pappus matroid.",
     drops=["the coordinates themselves"],
     witness="same as M-E3", cite="same as M-E3")
edge("M-E4", "NF_F2_SAT", "NF_F2_UNSAT", "NECESSARY_CONDITION",
     "Dropping the saturation.  I_sat = I_unsat : (prod of the non-basis "
     "determinants)^infinity is a LARGER ideal, so V(I_sat) subset "
     "V(I_unsat).  Tighter -> looser.",
     drops=["the nonvanishing of the basis determinants -- i.e. exactly the "
            "conditions saturation removes"],
     witness="the rigid point (1,1,0),(1,0,1),(0,1,1) reduced mod 2 lies in "
             "V(I_unsat) over F_2 -- all six line determinants vanish, the "
             "slack matrix still has rank 3 -- but det(3,5,6) = -2 == 0, so it "
             "is not a realization.  An explicit point of "
             "V(I_unsat) \\ V(I_sat).",
     cite="Brandt & Wiebe, 'The slack realization space of a matroid', "
          "arXiv:1804.05264, Algebraic Combinatorics 2 (2019)")
edge("M-E4f", "FANO_Q_SAT", "FANO_Q_UNSAT", "NECESSARY_CONDITION",
     "The same saturation edge for the Fano matroid over Q.  Declared "
     "separately because a claim about the Fano ideal cannot travel along the "
     "NON-Fano edge -- see this file's docstring, item 1.",
     drops=["the nonvanishing of the basis determinants"],
     witness="same structure as M-E4; here the point is that the UNSATURATED "
             "ideal is already the unit ideal, so the relaxation is empty too.",
     cite="G-FANO-Q-NO-SAT in matroid_transfer.py: zero charts reach the "
          "saturation stage")
edge("M-E5", "FANO_Q", "FANO_C", "BASE_EXTENSION",
     "Q to C for the Fano matroid: the CONTRAST edge, structurally identical "
     "to M-E1.",
     witness="a positive control: the SAME edge type gives the OPPOSITE "
             "verdict on a differently-certified claim.",
     cite="derived in matroid_transfer.py")
edge("M-E6", "U35_REAL", "U35_CLOSURE", "IMAGE_CLOSURE",
     "The realization space is a nonempty OPEN subset of the plane; passing "
     "to its Zariski closure is exactly what an elimination -- or reading V(I) "
     "off a saturated ideal -- hands you.",
     map_kind="POLYNOMIAL",
     drops=["the six line-nonvanishing open conditions"],
     witness="the boundary point makes exactly one triple dependent.  It is a "
             "limit of genuine realizations (the line boundary + t*(1,0) "
             "consists of realizations for all but finitely many t) yet is not "
             "itself a realization.  A closure point that does not lift.",
     cite="Chevalley; verified in matroid_transfer.py")

# ---- claims ---------------------------------------------------------------
claim("CM-ML8-R-EMPTY", "ML8_R", "EMPTY",
      "ML8 has no realization over R",
      scope="R", cert="NONSQUARE_CLASS", ladder="exact-checked",
      cite="G-ML8-ELIMINANT/G-ML8-DISC: the realization space is cut out by "
           "x^2-x+1, whose discriminant -3 is not a square in R.  PUBLISHED: "
           "'It is not possible to draw points and lines having this pattern "
           "of incidences in the Euclidean plane'; MacLane 1936.")
claim("CM-ML8-Q-EMPTY", "ML8_Q", "EMPTY",
      "ML8 has no realization over Q",
      scope="Q", cert="NONSQUARE_CLASS", ladder="exact-checked",
      cite="G-ML8-ELIMINANT: x^2-x+1 is irreducible over Q, disc -3.")
claim("CM-ML8-QS-NONEMPTY", "ML8_QS", "NONEMPTY",
      "ML8 HAS a realization over Q(sqrt(-3))",
      scope="Q(sqrt(-3))", ladder="exact-checked",
      cite="G-ML8-C-WITNESS: the realization's coordinates lie in "
           "Q(sqrt(-3)), not merely in C")
claim("CM-ML8-C-NONEMPTY", "ML8_C", "NONEMPTY",
      "ML8 HAS a realization over C",
      scope="C", ladder="exact-checked",
      cite="G-ML8-C-WITNESS (exact, both roots).  PUBLISHED: Coxeter's "
           "coordinates with w a complex cube root of 1; 'the configuration is "
           "possible in the complex projective plane'.")
claim("CM-ML8-NORM-C", "ML8_NORM_C", "NONEMPTY",
      "the frame-normalised ML8 system has a solution over Q(sqrt(-3))",
      scope="C", ladder="exact-checked",
      cite="G-ML8-UNIQUE-CHART/G-ML8-ELIMINANT")
claim("CM-ML8-NONORIENT", "ML8_ORIENT", "EMPTY",
      "ML8 admits NO orientation",
      cert="FINITE_ORIENTATION_EXHAUSTION", ladder="certified",
      cite="MacLane 1936; ML8 is a minor-minimal non-orientable matroid.  This "
           "is THE published proof that ML8 is not realizable over R.")
claim("CM-NP-ORIENTABLE", "NP_ORIENT", "NONEMPTY",
      "the non-Pappus matroid IS orientable (it has a pseudoline arrangement)",
      scope="combinatorial", ladder="certified",
      cite="Folkman-Lawrence; Richter-Gebert & Ziegler, Handbook ch.6")
claim("CM-NP-NONREAL", "NP_REAL", "EMPTY",
      "the non-Pappus matroid is not representable over any commutative field",
      cert="PAPPUS_IDENTITY", ladder="certified",
      cite="Sage matroid database: NonPappus 'is not representable over any "
           "commutative field'; a realization would violate Pappus's hexagon "
           "theorem.")
claim("CM-FANO-Q-EMPTY", "FANO_Q", "EMPTY",
      "the Fano matroid has no realization over Q",
      cert="UNIT_IDEAL_CERT", ladder="exact-checked",
      cite="G-FANO-Q-EMPTY: EVERY one of the 27 charts dies with 1 in the "
           "ideal, over Q.  PUBLISHED: Fano 'is representable over a field if "
           "and only if that field has characteristic two'.")
claim("CM-FANO-UNSAT-EMPTY", "FANO_Q_UNSAT", "EMPTY",
      "even the UNSATURATED ideal of the Fano matroid is the unit ideal over Q",
      cert="UNIT_IDEAL_CERT", ladder="exact-checked",
      cite="G-FANO-Q-NO-SAT: zero charts reach the saturation stage")
claim("CM-NF-UNSAT-NONEMPTY", "NF_F2_UNSAT", "NONEMPTY",
      "the UNSATURATED determinantal ideal of the non-Fano matroid has an "
      "F_2-point",
      scope="F_2", ladder="exact-checked",
      cite="G-SAT-WITNESS-IN-IDEAL/G-SLACK-RANK-F2: the rigid point mod 2")
claim("CM-NF-F2-EMPTY", "NF_F2_SAT", "EMPTY",
      "the non-Fano matroid has NO realization over F_2",
      scope="F_2", cert="FINITE_FIELD_EXHAUSTION", ladder="certified",
      cite="PUBLISHED: non-Fano is representable over a field iff that field "
           "does NOT have characteristic two (Oxley; Sage matroid database).  "
           "Recorded as a claim so that the true-positive grading of "
           "IM-NF-SKIP-SAT is DERIVED from the graph rather than asserted.")
claim("CM-U35-CLOSURE-NONEMPTY", "U35_CLOSURE", "NONEMPTY",
      "the Zariski closure of U_3,5's realization space has rational points",
      scope="Q", ladder="exact-checked",
      cite="G-U35-IN-CLOSURE: the closure is the whole affine plane")
claim("CM-U35-RANK", "U35_REAL", "PREDICATE",
      "every realization's slack matrix has rank <= 3 (the 4x4 minors vanish)",
      zariski_closed=True, ladder="exact-checked",
      cite="G-U35-RANK-EXTENDS; Brandt & Wiebe arXiv:1804.05264")

# ---- inferences that must be REFUSED --------------------------------------
inference("IM-ML8-BASE-EXT", "CM-ML8-R-EMPTY", [["M-E1", "ALONG"]],
          "ML8 is not realizable over R, THEREFORE it is not realizable over C",
          cite="the retrodiction: exactly the shape of the JC(2) C08/C20 "
               "error, in a domain whose answer is externally known")
inference("IM-ML8-Q-BASE-EXT", "CM-ML8-Q-EMPTY", [["M-E1q", "ALONG"]],
          "ML8 is not realizable over Q, THEREFORE it is not realizable over "
          "Q(sqrt(-3))",
          cite="the minimal instance: a degree-2 extension already flips it")
inference("IM-ML8-DESCENT", "CM-ML8-C-NONEMPTY", [["M-E1", "AGAINST"]],
          "ML8 is realizable over C, THEREFORE it is realizable over R",
          cite="the reversed asymmetry of BASE_EXTENSION, read the wrong way")
inference("IM-NF-SKIP-SAT", "CM-NF-UNSAT-NONEMPTY", [["M-E4", "AGAINST"]],
          "the 4x4 minors of the symbolic slack matrix have an F_2-solution, "
          "THEREFORE the non-Fano matroid is realizable over F_2",
          cite="the saturation trap: NONEMPTY read AGAINST a "
               "NECESSARY_CONDITION edge")
inference("IM-U35-CLOSURE", "CM-U35-CLOSURE-NONEMPTY", [["M-E6", "AGAINST"]],
          "the eliminated/saturated variety has a rational point, THEREFORE "
          "that point is a realization of U_3,5",
          cite="Chevalley: a point of the closure need not lift",
          note="Expected to grade UNSOUND_PREMISE, not UNSOUND_CONCLUSION, and "
               "the distinction is real: U_3,5 IS realizable, so the "
               "conclusion happens to hold -- but the ROUTE does not, and the "
               "specific boundary point exhibited is not a realization.  The "
               "graph holds no claim contradicting it, so the derivation "
               "reaches that grading on its own.")
inference("IM-ORIENT-TO-REAL", "CM-NP-ORIENTABLE", [["M-E3np", "AGAINST"]],
          "the non-Pappus matroid is orientable, THEREFORE it is realizable "
          "over R",
          cite="the converse of MacLane's argument")

# ---- positive controls, which must stay clean -----------------------------
inference("IM-MACLANE", "CM-ML8-NONORIENT", [["M-E3", "AGAINST"]],
          "ML8 admits no orientation, THEREFORE ML8 is not realizable over R",
          cite="MacLane 1936 -- the actual published argument",
          note="POSITIVE CONTROL: EMPTY travelling AGAINST a "
               "NECESSARY_CONDITION edge.  Must not be flagged.")
inference("IM-FANO-CONTRAST", "CM-FANO-Q-EMPTY", [["M-E5", "ALONG"]],
          "the Fano matroid is not realizable over Q, THEREFORE it is not "
          "realizable over C",
          cite="G-FANO-Q-EMPTY: 1 lies in the ideal over Q, hence over every "
               "field containing Q",
          note="THE CONTRAST PAIR.  Same edge type, same direction, same claim "
               "kind, an emptiness ALSO computed over a small field -- and it "
               "is LICENSED, because its certificate base-changes.")
inference("IM-ML8-ASCEND", "CM-ML8-QS-NONEMPTY", [["M-E1c", "ALONG"]],
          "ML8 is realizable over Q(sqrt(-3)), THEREFORE it is realizable "
          "over C",
          cite="a Q(sqrt(-3))-point IS a C-point",
          note="POSITIVE CONTROL for the REVERSED ASYMMETRY: on the very same "
               "edge type that refuses EMPTY along the arrow, NONEMPTY passes "
               "freely.  Both halves of the asymmetry are exercised on ML8.")
inference("IM-ML8-UP", "CM-ML8-NORM-C", [["M-E2", "AGAINST"]],
          "the frame-normalised system has a solution, THEREFORE ML8 has a "
          "realization",
          cite="G-ML8-C-WITNESS lifts the normalised solution explicitly",
          note="THE SHARP CONTROL.  NONEMPTY read AGAINST the arrow is "
               "FORBIDDEN on a NECESSARY_CONDITION edge and licensed only "
               "because frame normalisation is a genuine EQUIVALENCE.")
inference("IM-U35-RANK", "CM-U35-RANK", [["M-E6", "ALONG"]],
          "rank <= 3 holds on every realization, THEREFORE it holds on the "
          "whole closure -- which is WHY the slack ideal may be generated by "
          "the 4x4 minors",
          cite="G-U35-RANK-EXTENDS: rank 3 at the boundary point too",
          note="POSITIVE CONTROL for IMAGE_CLOSURE's one conditional cell.  A "
               "Zariski-CLOSED predicate extends to the closure; this is why "
               "elimination is a sound way to DERIVE equations even though it "
               "is unsound as a source of witnesses.")
inference("IM-FANO-NO-SAT", "CM-FANO-UNSAT-EMPTY", [["M-E4f", "AGAINST"]],
          "the UNSATURATED ideal is already empty, THEREFORE the matroid is "
          "not realizable -- no saturation needed",
          cite="G-FANO-Q-NO-SAT",
          note="POSITIVE CONTROL, and the useful corollary: emptiness DOES "
               "travel against the saturation edge, so a non-realizability "
               "certificate may skip the saturation.  A witness may not.  "
               "NOTE: routed over M-E4f, the FANO saturation edge; "
               "matroid_transfer.py routed it over the non-Fano edge M-E4, "
               "which is not a connected path.")

with open(OUT, "w", encoding="utf-8") as fh:
    fh.write("# Matroid realizability typed DAG (Whetstone's second domain).\n")
    fh.write("# Ported from math-stuff/whetstone/matroid_transfer.py.\n")
    for e in EV:
        fh.write(json.dumps(e, sort_keys=True) + "\n")
print("wrote %s (%d events)" % (OUT, len(EV)))
