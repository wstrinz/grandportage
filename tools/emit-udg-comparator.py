#!/usr/bin/env python3
"""Emit stock-Comparator challenge/solution pairs for the u(22) lemmas (Highway 61 Revisited G-4).

usage: python tools/emit-udg-comparator.py --out <dir> [--root GPUDGComparator] [--clean]

Separate from Track E's 3P emitter. Each challenge holds the rope vocabulary (`UDGRope.Defs`,
verbatim), any GP-side definition its statement names, and one theorem with `sorry`. The solution
is one module for all challenges: the Mathlib-only sources (rope R1a, `GPBinding/UDG/System.lean`,
`GPBinding/UDG/Spine.lean`) concatenated without their `import` lines, under the union of their
Mathlib imports. So the proofs Comparator checks are the repository's proofs, byte for byte.

Controls (must be refused): per challenge one solution module that is wrong in a stated way:
`sorry` (proof by `sorry`), `axiom` (proof from a custom axiom), `weaker` (a different statement,
proved), `redef` (a definition the statement uses is redefined, then the statement proved).

Writes <out>/<root>/Solution.lean, <out>/<root>/<Name>/Challenge.lean, <out>/<root>/Ctl/<Name>.lean,
<out>/comparator/<name>.json and <out>/comparator/ctl-<name>.json, and <out>/MANIFEST.json with
SHA-256 of every input and output. Same sources give byte-identical outputs.
"""
import argparse
import hashlib
import json
import re
import shutil
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
UDG = ROOT / "binding/GPBinding/UDG"
ROPE = UDG / "Rope/UDGRope"
SOURCES = [ROPE / "Defs.lean", ROPE / "Basic.lean", ROPE / "Rhombus.lean", ROPE / "Gadgets.lean",
           ROPE / "Schade.lean", UDG / "System.lean", UDG / "Spine.lean"]
AXIOMS = ["propext", "Quot.sound", "Classical.choice"]
EMITTER = "gp-udg-comparator-emit/v1"
ROPE_CTX = "namespace UDGRope\nopen scoped Finset\n"
GP_CTX = "noncomputable section\n\nnamespace GPBinding.UDG\nopen UDGRope\nopen scoped Finset\n"

# name -> (source file, qualified theorem, context, extra definitions, control kind)
CHALLENGES = {
    "Rhombus": ("Rope/UDGRope/Rhombus.lean", "UDGRope.rhombus", "rope", [], "weaker"),
    "Gadget0": ("Rope/UDGRope/Gadgets.lean", "UDGRope.gadget0_tu", "rope", [], "sorry"),
    "Gadget1": ("Rope/UDGRope/Gadgets.lean", "UDGRope.gadget1_tu", "rope", [], "axiom"),
    "Gadget2": ("Rope/UDGRope/Gadgets.lean", "UDGRope.gadget2_tu", "rope", [], "sorry"),
    "Gadget3": ("Rope/UDGRope/Gadgets.lean", "UDGRope.gadget3_tu", "rope", [], "weaker"),
    "Gadget4": ("Rope/UDGRope/Gadgets.lean", "UDGRope.gadget4_tu", "rope", [], "sorry"),
    "Gadget5": ("Rope/UDGRope/Gadgets.lean", "UDGRope.gadget5_tu", "rope", [], "axiom"),
    "Schade": ("Rope/UDGRope/Schade.lean", "UDGRope.schade", "rope", [], "redef"),
    "Hereditary": ("Spine.lean", "GPBinding.UDG.tu_hereditary", "gp", [], "weaker"),
    "SystemIff": ("System.lean", "GPBinding.UDG.udg_system_iff", "gp", [], "weaker"),
    "Spine": ("Spine.lean", "GPBinding.UDG.spine_sound", "gp", ["CoverComplete"], "redef"),
    "Realize": ("Spine.lean", "GPBinding.UDG.realize_sound", "gp", [], "weaker"),
}

# Control bodies: (replacement text for the statement block, proof)
CONTROLS = {
    "Rhombus": ("rhombus", "theorem rhombus {V : Type*} {G : SimpleGraph V} (f : G.UnitDistEmbedding ℝ²) {a b c d : V}\n"
                "    (hfake : f.p a - f.p b + f.p c - f.p d = 0) : f.p a - f.p b + f.p c - f.p d = 0 := hfake\n"),
    "Gadget3": ("gadget3_tu", "theorem gadget3_tu :\n"
                "    ¬ gadget3.Adj 3 7 ∧ ∀ f : gadget3.UnitDistEmbedding ℝ², dist (f.p 2) (f.p 6) = 1 :=\n"
                "  ⟨by simp [gadget3], fun f => f.unit_dist (by simp [gadget3])⟩\n"),
    "Hereditary": ("tu_hereditary", "theorem tu_hereditary {N M : ℕ} (hu : ∀ P : Finset ℝ², P.card = N → unitDistNum P ≤ M)\n"
                   "    (G : SimpleGraph (Fin N)) [DecidableRel G.Adj] (hM : M ≤ #G.edgeFinset) : True := trivial\n"),
    "Realize": ("realize_sound", "theorem realize_sound {n m : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]\n"
                "    (hG : Nonempty (G.UnitDistEmbedding ℝ²)) (hm : m ≤ #G.edgeFinset) :\n"
                "    ∃ P : Finset ℝ², P.card = n := by\n"
                "  obtain ⟨f⟩ := hG\n"
                "  exact ⟨Finset.univ.map f.p, by simp⟩\n"),
    "SystemIff": ("udg_system_iff", "theorem udg_system_iff {n : ℕ} (G : SimpleGraph (Fin n)) :\n"
                  "    Nonempty (G.UnitDistEmbedding ℝ²) → Nonempty (G.UnitDistEmbedding ℝ²) := id\n"),
}
# Redefinitions: (definition name, replacement definition, proof of the original statement under it)
REDEFS = {
    "Schade": ("maxUnitDistances", "noncomputable def maxUnitDistances (n : ℕ) : ℕ := 0\n",
               "theorem schade (n : ℕ) (hn : 3 ≤ n) :\n"
               "    maxUnitDistances n ≤ n * maxUnitDistances (n - 1) / (n - 2) := by\n"
               "  simp [maxUnitDistances]\n"),
    "Spine": ("CoverComplete", "def CoverComplete (n m : ℕ) (L : List (SimpleGraph (Fin n))) : Prop := False\n",
              "theorem spine_sound {n m : ℕ} {L : List (SimpleGraph (Fin n))} (hc : CoverComplete n m L)\n"
              "    (hL : ∀ G ∈ L, IsEmpty (G.UnitDistEmbedding ℝ²)) :\n"
              "    ¬ ∃ P : Finset ℝ², P.card = n ∧ m ≤ unitDistNum P := hc.elim\n"),
}


def sha(b):
    return hashlib.sha256(b).hexdigest()


def read(p):
    return p.read_bytes().decode("utf-8")


def split_imports(text):
    lines = text.split("\n")
    imports = [l for l in lines if l.startswith("import ")]
    body = "\n".join(l for l in lines if not l.startswith("import ")).strip("\n") + "\n"
    return imports, body


def block(text, kind, name):
    """The docstring and statement of `theorem name` / `def name` up to its `:=`, and the full block."""
    m = re.search(rf"^(/--(?:(?!-/).)*?-/\n)?{kind} {re.escape(name)}\b", text, re.M | re.S)
    if not m:
        raise SystemExit(f"{kind} {name} not found")
    start = m.start()
    end = text.index("\n\n", start)
    full = text[start:end] + "\n"
    stmt_end = re.search(r":=( by)?\n", text[start:end] + "\n")
    stmt = text[start:start + stmt_end.start()].rstrip() + " :="
    return stmt, full


def defs_body():
    _, body = split_imports(read(ROPE / "Defs.lean"))
    return body


def mathlib_imports():
    out = []
    for p in SOURCES:
        for l in split_imports(read(p))[0]:
            if l.startswith("import Mathlib") and l not in out:
                out.append(l)
    return out


def header(what):
    return f"/-! {what} Generated by `tools/emit-udg-comparator.py` ({EMITTER}). -/\n\n"


def challenge_text(name, imports):
    src, thm, ctx, extra, _ = CHALLENGES[name]
    text = read(UDG / src)
    short = thm.split(".")[-1]
    stmt, _ = block(text, "theorem", short)
    out = "\n".join(imports) + "\n\n" + header(f"Comparator challenge `{thm}`.") + defs_body() + "\n"
    if ctx == "rope":
        out += ROPE_CTX + "\n" + stmt + " by\n  sorry\n\nend UDGRope\n"
    else:
        out += GP_CTX + "\n"
        for d in extra:
            out += block(text, "def", d)[1] + "\n"
        out += stmt + " by\n  sorry\n\nend GPBinding.UDG\n"
    return out


def solution_text(imports):
    out = "\n".join(imports) + "\n\n" + header("Comparator solution for the u(22) lemmas: the repository's "
                                                "Mathlib-only sources, concatenated.")
    for p in SOURCES:
        out += f"-- source: {p.relative_to(ROOT).as_posix()}\n" + split_imports(read(p))[1] + "\n"
    return out


def control_text(name, imports):
    src, thm, ctx, extra, kind = CHALLENGES[name]
    text = read(UDG / src)
    short = thm.split(".")[-1]
    stmt, full = block(text, "theorem", short)
    defs = defs_body()
    gp_defs = "".join(block(text, "def", d)[1] + "\n" for d in extra)
    if kind == "sorry":
        thm_text = stmt + " by\n  sorry\n"
    elif kind == "axiom":
        thm_text = "axiom udg_cheat : False\n\n" + stmt + "\n  udg_cheat.elim\n"
    elif kind == "weaker":
        thm_text = CONTROLS[name][1]
    else:
        dname, new, proof = REDEFS[name]
        thm_text = proof
        if dname == "maxUnitDistances":
            _, old = block(defs, "noncomputable def", dname)
            defs = defs.replace(old, new)
        else:
            gp_defs = gp_defs.replace(block(text, "def", dname)[1], new)
    out = "\n".join(imports) + "\n\n" + header(f"Comparator control ({kind}) for `{thm}`: must be refused.") + defs + "\n"
    if ctx == "rope":
        out += ROPE_CTX + "\n" + thm_text + "\nend UDGRope\n"
    else:
        out += GP_CTX + "\n" + gp_defs + thm_text + "\nend GPBinding.UDG\n"
    return out


def write(path, text):
    path.parent.mkdir(parents=True, exist_ok=True)
    data = text.encode("utf-8")
    path.write_bytes(data)
    return sha(data)


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--out", required=True, type=Path)
    ap.add_argument("--root", default="GPUDGComparator")
    ap.add_argument("--clean", action="store_true")
    args = ap.parse_args(argv)
    if not re.fullmatch(r"[A-Z][A-Za-z0-9]*", args.root):
        ap.error("bad --root")
    for d in (args.out / args.root, args.out / "comparator"):
        if d.exists():
            if not args.clean:
                ap.error(f"{d} exists (use --clean)")
            shutil.rmtree(d)
    imports = mathlib_imports()
    manifest = {"schema": EMITTER, "root": args.root, "permitted_axioms": AXIOMS,
                "inputs": {p.relative_to(ROOT).as_posix(): sha(p.read_bytes()) for p in SOURCES},
                "solution": None, "challenges": []}
    manifest["solution"] = {"module": f"{args.root}.Solution",
                            "sha256": write(args.out / args.root / "Solution.lean", solution_text(imports))}
    for name, (src, thm, ctx, extra, kind) in CHALLENGES.items():
        c = write(args.out / args.root / name / "Challenge.lean", challenge_text(name, imports))
        k = write(args.out / args.root / "Ctl" / f"{name}.lean", control_text(name, imports))
        cfg = {"challenge_module": f"{args.root}.{name}.Challenge", "solution_module": f"{args.root}.Solution",
               "theorem_names": [thm], "permitted_axioms": AXIOMS}
        ctl = dict(cfg, solution_module=f"{args.root}.Ctl.{name}")
        j = write(args.out / "comparator" / f"{name.lower()}.json", json.dumps(cfg, indent=1) + "\n")
        jk = write(args.out / "comparator" / f"ctl-{name.lower()}.json", json.dumps(ctl, indent=1) + "\n")
        manifest["challenges"].append({"name": name, "theorem": thm, "source": f"binding/GPBinding/UDG/{src}",
                                       "challenge_sha256": c, "config_sha256": j,
                                       "control": {"kind": kind, "sha256": k, "config_sha256": jk}})
    write(args.out / "MANIFEST.json", json.dumps(manifest, indent=1, ensure_ascii=False, sort_keys=True) + "\n")
    print(f"{len(CHALLENGES)} challenges, {len(CHALLENGES)} controls, 1 solution -> {args.out}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
