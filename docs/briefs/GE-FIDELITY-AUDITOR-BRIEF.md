# Gate GE statement-fidelity audit: brief

For a fresh agent session that is **not** the GP builder. Will starts it once Track E has emitted the 3P Comparator challenges. Authority: post-G4 handoff §4 (gate GE).

## Purpose

GP emits, for each held 3P claim, a Comparator **challenge**: a Lean statement in Mathlib vocabulary. It also emits a **solution** that proves the challenge. Comparator checks that the solution proves the challenge. It cannot check that the challenge says what the claim means. You check that.

## Inputs

- **The challenge set:** generated, not committed. At the commit Will names, run `python tools/comparator-emit.py --campaign campaigns/3p-matroids --out <dir>` in the workspace repo.
  - Each shard `<dir>/GPComparator/<Shard>/` has `Challenge.lean` (the statement) and `Solution.lean`.
  - `<dir>/comparator/<shard>.json` is the Comparator config.
  - `campaigns/3p-matroids/warrants/comparator-MANIFEST.json` lists every challenge's claim, class and hash, plus the deferred EMPTY class.
  - Check that your emitted hashes match the manifest before reading.
- **For each challenge, the claim it warrants:** the ledger entry (`campaigns/3p-matroids/ledger.jsonl`), the matroid file (`campaigns/3p-matroids/matroids/<name>.json` or `catalog/`), and the meaning of its kind (`docs/GP-CLI.md`):
  - **NONEMPTY at p:** realizable over every field of characteristic p.
  - **NOT_IN_IDEAL(1) at p:** realizable over an algebraically closed field of characteristic p.
  - **EMPTY at p:** realizable over no field of characteristic p.
  - **Characteristic 0, and "every prime except S":** read the same way over those characteristics.
- **The pitfall list** from Lane O, if it exists by then. Otherwise use the starter list below.

## Procedure

1. Draw 20 challenges uniformly at random, with a seed you record. Stratify so that at least 5 come from map-rule claims, and at least 2 each from point witnesses and from bridge/source claims. EMPTY claims are deferred and not emitted.
2. For each challenge, work from the Lean statement alone first. Write down in one sentence what it claims about the matroid, then compare that with the claim's meaning above.
3. Check every pitfall, recording each as checked:
   - **Wrong lines:** the challenge's matroid data (its lines) differ from the matroid file.
   - **Wrong quantifiers:** the quantifier over fields or characteristics is weaker or stronger than the kind's meaning, or over the wrong set of characteristics.
   - **Vacuity:** the hypotheses are vacuous or contradictory (e.g. `CharP K p` with `p` not prime, or an empty index type).
   - **Degenerate witnesses:** collinear triples are encoded the wrong way round, or bases and non-bases are swapped.
   - **Junk values:** `ℕ` subtraction, division by zero, or `sSup` of an unbounded set.
   - **Unfaithful vocabulary:** `Matrix.det` or definitions that do not mean what their names say.
   - **Out-of-scope imports:** imports or definitions outside Mathlib that the statement depends on.

## Output

`GE-AUDIT.json`, with:
- the seed;
- the 20 challenge names;
- for each challenge: your one-sentence reading, verdict (`faithful` or `defect`), the defect if any, and the pitfalls checked.

Also a short `GE-AUDIT.md` summary. Gate GE needs **zero** defects. Report any defect to Will and the builder as found; do not fix challenges yourself.

## Rules

- Read only; never edit the workspace.
- No outside contact.
- Running stock `comparator` on a challenge is optional and does not replace the reading.
