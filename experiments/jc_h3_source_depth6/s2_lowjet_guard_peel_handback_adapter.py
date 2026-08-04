#!/usr/bin/env python3
"""Read-only GP projection of the exact S2 low-jet Sigma guard peel."""
from __future__ import annotations
import argparse, copy, hashlib, json, os, tempfile
from pathlib import Path
from grandportage import evidence as EV
from grandportage import frontier as F

ROOT = Path(__file__).resolve().parents[2]
NATIVE_ROOT = ROOT.parent / "math-stuff" / "d2_plane_72_108"
FIXTURE = ROOT / "fixtures" / "jc_source_depth6" / "s2_lowjet_guard_peel_handback_v1.json"
REVIEW_RECEIPT = ROOT / "review" / "jc-h3-s2-lowjet-guard-peel-frontier-v1.json"
SCHEMA = "gp-jc-h3-s2-lowjet-guard-peel-handback/v1"
SCOPE = "JC.H3.B0.S2_LOWJET_WALL"
SIGMA = "JC.H3.B0.S2.SIGMA_GUARD_EXCLUSION"
COVER = "JC.H3.B0.S2.LOWJET_COVER_COMPLETE"

class S2GuardPeelError(ValueError): pass
def require(ok, tag, message):
    if not ok: raise S2GuardPeelError(f"{tag}: {message}")
def normalized_sha256(path):
    return hashlib.sha256(Path(path).read_bytes().replace(b"\r\n", b"\n")).hexdigest()
def load_fixture(path=FIXTURE): return json.loads(Path(path).read_text(encoding="utf-8"))

def validate_handback_value(value):
    require(value.get("schema") == SCHEMA, "H1", "schema changed")
    require(value.get("binding_digest_algo") == "sha256-lf-normalized", "H2", "digest convention changed")
    c = value.get("closeout", {})
    require(c.get("wall") == "b = 0, R = 0, Delta = 0 (S2 substituted)", "C1", "wall widened")
    require(c.get("scope") == "declared S2 low-jet cover universe only", "C2", "scope widened")
    require(c.get("verdict") == "SIGMA_FULLY_SOURCE_EXCLUDED_INVARIANT_J" and c.get("corollary") == "LOWJET_COVER_COMPLETE", "C3", "closeout changed")
    require((c.get("residual_degree"), c.get("residual_squarefree"), c.get("candidate_count"), c.get("terminal_guard")) == (15, True, 15, "det5 = 0"), "C4", "residual/guard data changed")
    require(c.get("checks") == 31 and c.get("new_localization") is False, "C5", "replay/localization changed")
    for key in ("source_sufficiency_licensed", "global_b0_licensed", "s1_s3_s4_licensed", "h3_licensed", "verdict_75125_licensed"):
        require(c.get(key) is False, "C6", key + " was promoted")
    b = value.get("authority_boundary", "")
    require("does not assert source sufficiency" in b and "global b=0" in b and "S1/S3/S4" in b, "C7", "nonclaims lost")
    return value

def check_native_bindings(value, native_root=NATIVE_ROOT):
    for name, digest in value["source_bindings"].items():
        p = Path(native_root) / name
        require(p.exists(), "B1", "missing native binding: " + name)
        require(normalized_sha256(p) == digest, "B2", "native binding drifted: " + name)

def item(identifier, proposition, status, evidence):
    return {"id": identifier, "proposition": proposition, "status": status,
            "frontier_state": "CLOSED", "scope": {"id": SCOPE, "description": "the declared b=R=Delta=0 S2 low-jet wall universe"},
            "exports_to_scopes": [], "premises": [], "blocked_downstream": [],
            "superseding_evidence": list(evidence), "smallest_next_artifact": None,
            "estimated_cost": None, "potential_impact": []}

def frontier_input(value):
    validate_handback_value(value)
    c = value["closeout"]
    return {"schema": "frontier-input/v1", "discharges": [],
      "items": [
        item(SIGMA, "Every invariant-J Sigma candidate on the declared S2 wall is the illegal det5 guard root.", c["verdict"], ("a6ef029 exact 31-check guard peel",)),
        item(COVER, "The low-jet cover is complete on the declared S2 wall because Sigma was its only remaining hole.", c["corollary"], ("a6ef029 scoped low-jet corollary",)),
      ],
      "sources": [{"commit": value["jc_commit"], "path": "d2_plane_72_108/f2_h3_sigma_guard_peel_certificate.json", "sha256": value["source_bindings"]["f2_h3_sigma_guard_peel_certificate.json"], "verdict": c["verdict"]}],
      "bound_source_names": sorted(value["source_bindings"])}

def build_report(value):
    d = frontier_input(copy.deepcopy(value)); r = F.build(d["items"], d["discharges"], d["sources"])
    r["consumer"] = "jc-h3-s2-lowjet-guard-peel-handback"; r["source_authority_ceiling"] = "S2_LOWJET_SOURCE_EXCLUSION_ONLY"
    c = value["closeout"]
    r["evidence_envelope"] = EV.EvidenceEnvelope(schema=SCHEMA, context=EV.AffineContext(characteristic=0, coefficient_domain="declared S2 low-jet guarded source-face universe", point_universe=None, ring_vars=()), source_bindings=tuple(EV.SourceBinding(n, "sha256:"+x) for n,x in sorted(value["source_bindings"].items())), checked_proposition="the invariant-J Sigma residual on the declared S2 wall consists only of illegal det5 guard roots", licenses=("S2_invariant_J_Sigma_source_exclusion", "S2_lowjet_cover_complete"), outstanding_premises=("global b=0", "S1/S3/S4", "source sufficiency", "H3"), graph_effect=EV.GRAPH_EFFECT_NONE, authority_boundary=value["authority_boundary"], certificate_payload={"verdict": c["verdict"], "corollary": c["corollary"], "terminal_guard": c["terminal_guard"], "global_b0_licensed": c["global_b0_licensed"]}).as_dict()
    return r

def review_receipt(r):
    return {"schema": "gp-jc-h3-s2-lowjet-guard-peel-frontier-review/v1", "projection_schema": r["schema"], "authority": r["authority"], "graph_effect": r["graph_effect"], "consumer": r["consumer"], "history": r["history"], "source_authority_ceiling": r["source_authority_ceiling"], "open_items": r["open_items"], "item_observations": F.item_observations(r), "evidence_envelope": r["evidence_envelope"]}

def emit_review_receipt(receipt, path=REVIEW_RECEIPT):
    path=Path(path); path.parent.mkdir(parents=True, exist_ok=True); payload=F.canonical_json(receipt).encode("utf-8")
    h,tmp=tempfile.mkstemp(prefix=path.name+".",suffix=".tmp",dir=str(path.parent))
    try:
        with os.fdopen(h,"wb") as s: s.write(payload); s.flush(); os.fsync(s.fileno())
        os.replace(tmp,path)
    except BaseException:
        try: os.unlink(tmp)
        except FileNotFoundError: pass
        raise
    return hashlib.sha256(payload.replace(b"\r\n",b"\n")).hexdigest()

def main(argv=None):
    p=argparse.ArgumentParser(description=__doc__); p.add_argument("--fixture",type=Path,default=FIXTURE); p.add_argument("--native-root",type=Path,default=NATIVE_ROOT); p.add_argument("--check-native-bindings",action="store_true"); p.add_argument("--emit",action="store_true"); a=p.parse_args(argv)
    try:
        v=validate_handback_value(load_fixture(a.fixture))
        if a.check_native_bindings: check_native_bindings(v,a.native_root)
        r=build_report(v)
        if a.emit: print(json.dumps({"path":str(REVIEW_RECEIPT),"sha256_lf_normalized":emit_review_receipt(review_receipt(r))},indent=2,sort_keys=True))
        else: print(F.canonical_json(r),end="")
        return 0
    except (S2GuardPeelError,F.FrontierError,OSError,json.JSONDecodeError) as e:
        print(json.dumps({"schema":SCHEMA,"verdict":"REFUSED","error":str(e)},sort_keys=True)); return 1
if __name__ == "__main__": raise SystemExit(main())
