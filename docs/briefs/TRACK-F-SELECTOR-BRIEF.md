# Foreign-incident selector: brief

For a fresh agent session that is **not** the GP builder. Will starts it. Authority: post-G4 handoff §6 and post-G3a handoff §7. This brief is self-contained. **Do not open the Grand Portage repository or its checkouts.** In particular, do not open `INCIDENT-INVENTORY.md` or anything about GP's Phase 3b. Work in your own directory, outside every checkout of the workspace.

## Purpose

GP's final gate compares GP with two baselines on 18 incidents. Six of them are **foreign**: errors from outside GP's own history, so GP cannot win on home ground. You build the candidate list now, and on 2026-11-06 you pick six from it.

## Criteria (all three required)

1. **A computational claim.** A stated result that some computation establishes: a count, a search, an exact identity, a certificate, a classification, or a computer-checked proof.
2. **Replayable exact inputs.** The inputs that produced the claim are public and exact, so the computation can be re-run. Examples: code, data, a Lean challenge, or a certificate.
3. **An error confirmed in a primary source**, publicly, by the authors or an independent party. Examples: an erratum, a retraction, a correction note, an issue acknowledged by the maintainers, or a published refutation. An error only you or another agent believe in does not count.

## Where to look

- Published or posted errors in AI-assisted computational mathematics.
- Errors in other people's computational campaigns.
- Corrected or retracted computational claims.
- **OpenAI's mathematics release** ([openai/math](https://github.com/openai/math), 2026-10-06). Its errata qualify on the same criteria. The likely kinds are a wrong certified computation, or a Comparator challenge whose statement is shown not to mean what its paper claims. These count only once OpenAI or an independent party confirms the error in public. **At most two of the six** may come from this release.

## Deliverables

1. **`candidates.jsonl`**, kept current from now to 2026-11-06, one candidate per line:
   - `id`;
   - `title`;
   - `claim` (one sentence);
   - `inputs` (URLs plus a short description);
   - `error` (one sentence);
   - `confirmation` (URL plus a quoted sentence, under 15 words);
   - `confirmed_by` (authors, maintainer, or an independent party);
   - `date_confirmed`;
   - `from_openai_release` (true or false);
   - `criteria_met` (three booleans with one-line reasons).
2. **At the freeze (2026-11-06):** pick six against the criteria, at most two from the release, and write `FOREIGN-SET.json` with the six candidate records. Report its SHA-256. Will approves the list before it is used.
3. **A short `NOTES.md`:** sources searched, near-misses and why each failed.

## Rules

- Reading public sources is fine. **No outside contact:** no posting, filing issues, emailing or commenting. Report anything that seems to need contact to Will.
- Do not run large computations; replay belongs to the gate.
- If fewer than six candidates meet all three criteria by the freeze, say so; do not relax the criteria.
