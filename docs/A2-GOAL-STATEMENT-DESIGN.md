# A2: the goal verdict held by the Kernel (design for review)

Builder, 2026-10-12. Release plan item A2 (DECISIONS 2026-10-12). This adds statement kinds to the 3b profile, which is a stop-and-ask item. **Implementation waits for Will's approval of this note.**

## The problem

`gp status` decides a DECIDE goal (Q(n, m) or ¬Q(n, m)) by a Python join over held claims (`status_goal`, `spine_verdict`, `cover_join`). The pieces are proved in Lean:
- `udg_frame_iff`;
- `realize_sound`;
- `spine_sound`;
- `candidate_isEmpty`.

The **matching** is Python, and `TCB.md` lists it as trusted. That matching covers:
- that a claim's graph is the cover's candidate;
- n and m;
- that an exclusion reaches ℝ;
- that the frame is equal.

A bug there could print "decided" with no checker refusing. Named premises (ENUM-COMPLETE and others) are Python metadata, not Kernel objects. So "¬Q conditional on X" is a Python sentence.

## The design: four statements, three rules, all in the 3b profile

The Kernel is unchanged; the new statement kinds are profile data. Each has a meaning in the binding over `EuclideanSpace ℝ (Fin 2)` (`ℝ²`), held at scope `real`:

| Statement | Meaning (binding) |
|---|---|
| `goal n m true` | `∃ P : Finset ℝ², P.card = n ∧ m ≤ unitDistNum P` (Q) |
| `goal n m false` | `¬ Q(n, m)` |
| `cover n m L` | `CoverComplete n m L` (L a list of graphs on `Fin n`) |
| `spine n m L` | `CoverComplete n m L → ¬ Q(n, m)` |

| Rule | Premises (held claims) | Conclusion | Admission check (profile, Lean) | Soundness (binding) |
|---|---|---|---|---|
| `realize` | one `--udg` NONEMPTY claim at `real` | `goal n m true` | the premise's statement **equals** `UDG.Data.stmt ⟨n, edges⟩ .nonempty` for its graph, the graph has n vertices, and `edges.length ≥ m` | `udg_frame_iff`, `realize_sound` |
| `spine` | one `--udg` EMPTY-over-ℝ claim per graph in L, in order | `spine n m L` | each premise's statement equals `UDG.Data.stmt ⟨n, Lᵢ⟩ .empty` | `candidate_isEmpty`, `spine_sound` |
| `decide` | `spine n m L` and `cover n m L` | `goal n m false` | same n, m and L | modus ponens |

`cover n m L` is held only by evidence that proves it: the existing exhaustive-list check (`coverComplete_of_all`). It is never held by a named premise.

**What changes in meaning:**
- A goal whose cover rests on named premises today shows "¬Q conditional on …". Under this design the **Kernel holds `spine n m L`**, the theorem "if the cover L is complete, no graph on n vertices has m unit edges". Its proof checks each exclusion in Lean.
- `cover n m L` stays open, with its named premises listed. `goal n m false` stays unheld.
- The conditional sentence is now a held implication plus an open claim, both Kernel facts. The view only prints them.
- The graph-and-claim matching moves into Lean: the rule's admission check compares statements exactly, using the Mathlib-free encoder that `udg_frame_iff` is about.

## The CLI after the change

- `gp cover` files the `spine` claim (rule `spine`, with the candidates' exclusion claims as premises) and the `cover` claim. The cover's evidence is an exhaustive list if one is given; otherwise it is open, with its named premises.
- The DECIDE goal's two claims (`goal n m true` and `goal n m false`) are filed at `init`, or on the first command for an existing ledger.
- `--goal yes` on a `--udg` claim also files a `realize` attempt.
- `status`, `frontier` and `explain` read held/open from the fold. `status_goal`, `spine_verdict` and `cover_join` become **display only**: they print fold results and decide nothing.
- G-1's refusals stay: `--goal no` is refused, and so is `--goal yes` on `--system`.
- **Legacy ledgers:** a `cover` record written before A2 shows as "legacy cover record: refile with `gp cover`". It is never read as a verdict. Refiling is a campaign action.

## Controls (tests)

Each of these must be refused or must not decide:
1. a `realize` premise whose statement differs from the encoder's (a tampered frame), has a different n, or has fewer than m edges;
2. a `spine` premise on a different graph (K₂,₃ for K₄), or held only at semireal or characteristic 0;
3. `decide` with mismatched n, m or L;
4. a cover without a completeness proof (an empty L, or a non-exhaustive list): the cover is not held, and the goal is not decided.

The existing yes and no fixtures (Q(4,5) held; Q(4,6) through the K4 cover) keep passing, now held by the Kernel.

## Size and risk

- Profile: about 250 lines (statements, rules, admission). Binding: about 300 (meanings, rule soundness, extending `fold_held_meaning3`). CLI: about 200. Tests: about 250.
- **Risk:** `UDG.Data.stmt` equality inside admission makes the rule check run the encoder for 22-vertex graphs (231 guards). That is fine: the Lean encoder already runs as `udgFrames` in `gp_ledger3`.
- No Kernel change. Every new theorem uses the standard axioms only.

## Decisions for Will

1. Adopt the four statements and three rules. In particular, `spine` is a held *implication*, and a cover is held only by a completeness proof, never by a named premise.
2. Legacy cover records are display-only "refile" notices. Refiling a cover is the campaign owner's step.
