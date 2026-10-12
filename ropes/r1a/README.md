# Rope R1a: rhombus lemma, six TU gadgets, heredity, Schade averaging

**Tier: T1 candidate. There are no hypotheses.** The GR1 checks were run on 2026-10-10:
- CI on a fresh runner passed;
- a non-builder agent found all nine statements faithful;
- a fresh agent reproduced the result.

Delivery at GR1 is Will's call.

## Main theorems (verbatim; vocabulary in `UDGRope/Defs.lean`)

```lean
theorem rhombus {V : Type*} {G : SimpleGraph V} (f : G.UnitDistEmbedding ℝ²) {a b c d : V}
    (hab : G.Adj a b) (hbc : G.Adj b c) (hcd : G.Adj c d) (hda : G.Adj d a)
    (hac : a ≠ c) (hbd : b ≠ d) :
    f.p a - f.p b + f.p c - f.p d = 0
theorem gadget0_tu :
    ¬ gadget0.Adj 1 5 ∧ ∀ f : gadget0.UnitDistEmbedding ℝ², dist (f.p 1) (f.p 5) = 1
theorem heredity_nonempty {V W E : Type*} [MetricSpace E] {G : SimpleGraph V} {H : SimpleGraph W}
    (f : H.Copy G) (h : Nonempty (G.UnitDistEmbedding E)) : Nonempty (H.UnitDistEmbedding E)
theorem schade (n : ℕ) (hn : 3 ≤ n) :
    maxUnitDistances n ≤ n * maxUnitDistances (n - 1) / (n - 2)
```

`gadget1_tu` … `gadget5_tu` have the same shape (`Gadgets.lean`).

- `ℝ²` is `EuclideanSpace ℝ (Fin 2)`.
- `UnitDistEmbedding` is Mathlib's injective, not necessarily faithful, embedding.
- `maxUnitDistances` is formal-conjectures' definition, copied verbatim.
- The gadgets come from artwaste's `data/tu-gadgets.json`.

## Check

- Pinned to Lean and Mathlib **v4.34.1**.
- Stock Comparator accepts all 9 challenges.
- It refuses all 4 controls, each with the expected reason:
  - a `sorry` proof;
  - a custom axiom;
  - a weaker statement;
  - a redefined `maxUnitDistances`.
- The only axioms are `propext`, `Classical.choice` and `Quot.sound`.

## Reproduce

```
bash REPRODUCE
```

Prerequisites:
- Linux 5.13 or later with Landlock enabled (where securityfs is mounted, `/sys/kernel/security/lsm` lists `landlock`) and a non-root user;
- elan (https://github.com/leanprover/elan), Go 1.24 or later (https://go.dev/dl/) and git, all on `PATH`.

Notes:
- `systemd-run --user` is used when it is available; it is optional.
- A fresh checkout needs no `.lake/`.
- Tools are built under `$R1A_TOOLS` (default `.lake/r1a-tools`).
- Comparator and lean4export are tag `v4.34.0` built with v4.34.1, since no v4.34.1 tag exists.
- It takes about 16 minutes and 8 GB of disk.
- Exit 0 means all 13 runs behaved as expected.

## Independence

These are the same lemmas artwaste and AMP rely on. What is added is a kernel check through stock Comparator, against Mathlib's and formal-conjectures' vocabulary, with no code shared with artwaste's checkers. The Lean was produced with Claude models. "Independent verification" covers only that kernel check.

## Provenance

The Lean proofs were written by Grand Portage's builder agent. The ud22 campaign agent (Claude Opus 5.5, Claude Code) did the assembly, the challenges, the controls and these documents. **No human has reviewed any of it.**

## Not checked

- That these constants equal formal-conjectures'. The bodies match textually, up to renamed constants (namespaces `UDGRope` and `Erdos90`). Formal-conjectures pins Mathlib v4.33.1 and this rope uses v4.34.1, so equality of the elaborated terms is unchecked.
- **Gadget non-vacuity.** The rope does not prove that the gadgets embed. That rests on PROOFS.md's coordinates in ℚ(√3) and on Grand Portage-internal exact records (`P2-gadget*-embeds`), which outsiders cannot inspect.
- The mapping from the JSON gadgets to the Globus–Parshall and AMP figures. The GR1 reviewer matched them by brute force, but the rope does not check it.
- Anything about u(22). That is rope R1b.

`gadget4_tu` also follows from `gadget5_tu` and heredity. See `FIDELITY.md` and `formalization.yaml`.
