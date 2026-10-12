# Reviewer brief: Grand Portage v0.50.0-alpha

**What it is.** Grand Portage (GP) is a ledger for computational mathematics that holds a claim only through current, bound evidence and sound admitted rules, and only throughout the scope the evidence earns. If a certificate divides by 2, the claim it supports does not reach characteristic 2. The alpha is the 0.50 rework at its G3a gate:
- a small Lean kernel;
- one algebraic profile (polynomial systems over characteristic-set scopes);
- a Mathlib proof that the profile's checkers and rules are sound.

It is a research alpha, not a tool for production use.

**Where.** [github.com/wstrinz/grandportage](https://github.com/wstrinz/grandportage), tag `v0.50.0-alpha`. Lean 4 `v4.34.0-rc2`, Mathlib `85e3a25e`, HexMvPoly `v0.6.0`.

**What we would most like checked.**
1. **The meaning theorem.** `fold_held_meaning_receipts_rules` (`binding/GPBinding/Admission/RuleSound.lean`): every claim the kernel fold holds means its statement in every field of its scope. Is `Holds`/`Means` (`Semantics.lean`, `Profile.lean`, `means_iff`) the right meaning, and are there gaps between it and what the executable checks?
2. **Reach.** `check_sound` and the `reach_*_sound` lemmas (`Sound.lean`). A certificate replayed exactly over ℚ reaches characteristic 0 and every prime avoiding its denominators. A certificate whose rational residual vanishes mod p reaches exactly {p}. Are any of these scope computations too generous?
3. **The kernel's lifecycle properties** (`phase2/lean`, pinned by `KERNEL-PIN.json`): the fold is sound, complete, order independent, total and deterministic, and retraction removes exactly what depended on the retracted support. Do the statements say what the README claims?
4. **The trusted base.** `TCB.md` lists what is trusted and why: the Hex-to-Mathlib bridge, the compiled checker, and the binder's environment stamp. Is anything trusted that should be proved, or missing from the list?
5. **The corpus claim.** There are no false ACCEPTs across the 242 profile cases (`reports/PHASE-3A-SAFETY.json`). Are the case expectations themselves sound? `corpus/` cites a source for each one.

**How to reproduce.** CI job `gp50` (`.github/workflows/ci.yml`) is the recipe:
- install elan;
- materialize the v0.37 oracle (it clones the public `v0.37.0` tag);
- `lake build` in `phase2/lean` and in `profile`;
- `lake exe cache get && lake build GPBinding` in `binding`;
- `python -m pytest tests/test_phase2_*.py tests/test_gp50_*.py tests/test_layer_tags.py`.

Every Kernel module passes `leanchecker`, and the soundness theorems use only `propext`, `Classical.choice` and `Quot.sound`.

**Out of scope for this release** (`LIMITS.md`, `KNOWN-CONSERVATISM.md`):
- real and number-field claims;
- census and combinatorial certificates;
- campaign operations.

GP refuses some sound claims by design, and those refusals are listed. A refusal of something true is a conservatism report; an acceptance of something false is a soundness bug.

**Reporting.** Open an issue on the repository. Give the claim, the receipt or case, what GP did, and what it should have done. Soundness bugs are the priority.
