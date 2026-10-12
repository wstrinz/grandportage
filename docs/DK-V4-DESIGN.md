# DK V4 slice: census design

2026-10-06. Builder design for G4's DK condition (DECISIONS 2026-10-04), following the V4-action extension Will accepted. Profile-only: no Kernel change.

## What is counted

DK counts bare (n_4) types T, up to isomorphism, that admit a faithful V4 action passing the geometric fences, with a given point orbit inventory I = (f; b1, b2, b3; a).

GP states this with the action in DK's own normal form a₀(I): the concrete permutations of points 0..n−1 that DK's enumerators use (`small_control.Sys`, and the `perms` of every n = 23 type file).

The statement is a new census kind over 2-coloured Levi graphs on 2n vertices (points 0..n−1, then lines):

- **S(a₀, φ)**: the labelled graphs where
  - points carry colour 0;
  - each a₀(g) extends to a colour-preserving automorphism A(g);
  - `φ` holds with action atoms read from A.
- **`v4Count a₀ φ m`**: exactly m isomorphism classes meet S's isomorphism closure.
- **`v4CountGiven a₀ φ L m`**: the same, assuming the catalog L is complete for that closure. This is the n = 23 premise.

`φ` is first-order with counting, plus one new atom, `act g i j` (A(g) sends i to j). It carries:
- the (n_4) axioms;
- DK's fences (`av4.necessary_conditions`, with Theorem A);
- the line inventory, where wanted.

`φ` is written once in Lean, with comments tying each conjunct to DK's DERIVATION section. Before any claim relies on it, a differential test checks GP's evaluation of `φ` against DK's Python on every n = 19 structure, fence-valid or not, and on all 5,299 n = 23 types.

## The bridge premise

"Admits some action with inventory I" equals "is isomorphic to a graph in S(a₀(I))". This is the classification of V4-sets: actions with equal orbit-type counts are conjugate. GP's held claims are exact about a₀. The bridge to DK's wording is the named premise **V4-NORMAL-FORM**.
- It is standard and closable in principle.
- A Lean proof of it is optional follow-up. The census profile is Mathlib-free, so it is not cheap.

## n = 19 control: `v4Count`, fully checked

- **The CNF fixes the point action to a₀.** Line-action variables are permutation matrices, constrained to be automorphisms. The symmetry break uses relabellings that commute with a₀ (`Centralizing`): adjacent line transpositions, plus 200 elements of the point centraliser.
- **The certificate lists every labelled model:** 13,824 in the spike, 1,536 per type.
  - A refutation of "none of these" is checked by LRAT. The spike's proof was 168 MB, found in 18 s.
  - Every listed model must have the same canonical form as one of 9 representatives.
  - The representatives have pairwise distinct canonical forms, and each is shown in S by its line action.
- **New theorem:** a lex-minimum over centralising relabellings meets every constraint from those labels. This is `orbit_min` restricted to a subgroup, and centralising relabellings preserve S.
- **Result** (`reports/DK-V4-RECEIPT.json`): 3,840 models; a Lean CNF of 2.0 M variables and 6.0 M clauses; a 592 MB LRAT proof; held.
- **Independence:** DK's normalised proposer and this SAT listing are separate code, with a separate encoding, solver and canonical labeller. The spike's listing recovers exactly DK's 9 types.

## n = 23 cells: `v4CountGiven`

- **One claim per cell**, six in all. Cells overlap: 72 types lie in two cells, giving 5,371 memberships but a union of 5,299. So the claims are per cell, not a partition.
- **GP checks each type file directly:** membership in S with its line action, the cell's line inventory, and pairwise distinct canonical forms. The cell sizes must come out as 1361, 1286, 693, 669, 693 and 669.
- **The completeness premise is CELL-COMPLETE.** Two routes agree: DK's direct enumerator `v4census.py`, and the audit lane's `indep_enum.py`. Not independent for b12: those two cells come from duality in the shared `join.py`.
- **Custody:** the builder reran `v4census.py`. It regenerated all 5,299 type files, equal as JSON; the bytes differ only by Windows CRLF.

## Order

1. Formula action atom and evaluation, with invariance under isomorphism.
2. The S membership check and the `v4` kinds.
3. Encoding and the subgroup listing theorem.
4. `φ` in Lean, and the differential test against DK's Python.
5. n = 19 claims.
6. n = 23 claims.
7. G4 controls.

Data stays in the git-ignored `corpus/harvest/dk-v4/`. Tests use a generated small control, and receipts bind the harvest by digest.
