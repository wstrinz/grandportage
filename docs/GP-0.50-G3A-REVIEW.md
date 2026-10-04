# G3a external review (received 2026-10-03)

Verbatim copy of the external review of Phase 3a at workspace `master` `fccccec`. Will adopted its rulings as written on 2026-10-03 (DECISIONS.md).

---

3a is in good shape where it matters most. It is thinner than its headline numbers in a couple of places, and most of your seven questions turn out to be consequences of one semantic fact that's worth naming first. I cloned master at `fccccec` and read the report, both authority docs, the receipts, `profile/` and `binding/`. Below is what I'd rule on each question, a handful of defects I found that you didn't ask about, and a sequencing to close G3a.

## Overall read

**What's real.** There's now a sound path from the canonical AST, through replay checkers and the K3 rules, to the Kernel fold, proved against Mathlib on standard axioms. `fold_held_meaning_rules` is the theorem the whole rework was for, and it exists. Computed reach does something Lean doesn't: G3a-0 already showed AutoGeneralization misses A08c and X125's F_p reach. The Fano demo does exactly what it should. And the strict-keys episode is a genuinely important empirical result: adapters that silently ignored unknown keys produced nine false ACCEPTs.

**What's thinner than the numbers.**
- "25 inferences, 0 disagreements" is 1 executed agreement, 6 consistent-by-rule with no polynomial data to run, and 18 inexpressible.
- The 14 kernel re-executions executed zero.
- 3 of 44 held claims carry theorem warrants.
- Custody got four stale-binding refusals.

None of that is hidden; the JSONs say it plainly. But the differential test is effectively a G3b test. G3a establishes "semantics and soundness proved, corpus fit adjudicated", not "carrying between worlds tested in anger".

## The shape 3a uncovered

`Means` quantifies over every field whose characteristic is in the scope, and every characteristic-set scope is closed under algebraic closure. That makes 3a ideal theory over the prime field, plus rational points:

- **EMPTY** means geometrically empty, which by the Nullstellensatz is equivalent to IN_IDEAL(1).
- **VANISHES_ON** means radical membership.
- **IN_IDEAL** depends only on the characteristic (flatness).
- **NONEMPTY** means a prime-field point, because ℚ or F_p is itself in the scope.

So ¬EMPTY and NONEMPTY are not complements. The gap between them is exactly the varieties with geometric points but no rational ones.

Also, EMPTY ≡ IN_IDEAL(1) holds in 3a but stops holding the moment 3b adds a scope atom like ℝ, which isn't closed under algebraic closure. ML8's base-extension errors live precisely in that gap. Keep this frame in hand; it answers 2 and 6 and part of 1.

## Your seven questions

**1. Ownership.** I'd adopt one rule for the whole sidecar: *0.50 checks, never constructs.* A case about checking a supplied object (a map, a point, a certificate) belongs to a profile. A case about the operation that constructs it is campaign-op. Under that rule:

- **The 10 operation contracts → campaign-op: agree.** `construct_from_matching_generator`, `check_power_identity` and the rest are v0.37 API questions.
- **The 20 moved to 3b split three ways:**
  - **X319–X336 → 3b: correct.** They're claims about a specific number field, signature ℤ[1/S][t]/(m), carry kind 1.
  - **X275–X280 → 3b: correct.** Their lesson only becomes live once "EMPTY over ℝ" is statable.
  - **X69 should come back to 3a.** It uses the same custody mechanism as X70 (chart change) and X71 (cite change), which pass, and `universe:` is already in `extrasOf`. The move is just inconsistent.
  - **A24 and X45–X50 are statable in 3a** (see 6).
- **The 33 ambiguous:** have the builder run a try-as-3a pass under the construct/check rule. If a case is expressible through the shared frontend with no case-keyed family, it's 3a-owned, whether it then passes or fails; otherwise campaign-op. You rule only on the residue. I'd expect X73–X81 ("or 3a C4"), X51/X52 and X408/X409 to land in 3a as R3 checks of supplied maps.

**Rings: no profile should have ring contexts now.** 3a and 3b are field semantics. The ring-flavoured truth campaigns actually want ("this integral identity holds everywhere") already shows up as reach. Assign the ten ring cases by what they test:

| Cases | What they are | Owner |
|---|---|---|
| X355, X356 | Deleted-premise countermodels | Admission controls on the C1 and rule soundness theorems, where 1≠0 and no-zero-divisors are actual hypotheses. Not profile-owned corpus. |
| X358–X360 | ℤ→ℤ[i] operation map | Campaign-op. X360's field analogue is already the R3 refusal. |
| X357, X361–X363 | ℤ analogues of X141, A03a and localization | Campaign-op regression |
| X366–X367 | Finite carriers with maps | Census |

Revisit rings only if a campaign needs integer points; u(22), Cloquet and DK don't.

**2. AST extensions.**

*NOT_IN_IDEAL: right kind, wrong coupling.* A point with h(a) ≠ 0 proves something stronger, ¬VANISHES_ON. That is NONEMPTY on the system with h added as a guard, which `witnessSystem` literally constructs. Instead:
- hold that augmented-system claim;
- derive NOT_IN_IDEAL through a bridge rule.

That keeps the stronger earned claim in the ledger. It also leaves NOT_IN_IDEAL free to get a genuinely ideal-level certificate later (x ∉ (x²), via Gröbner normal form) without changing the statement.

*NONUNIT: redundant.* NONUNIT(h) on (E, G) is exactly NOT_IN_IDEAL(1) on (E+[h], G). Two encodings of one fact; canonicalize in the frontend and let `gp explain` render it back.

*COVER: right instinct, currently inert.* No rule consumes a COVER premise (`ruleReach` in `Rules.lean`). Inclusion into one branch is complete only for degenerate covers, which happens to be all that X269–X272 test. The fix:
- Make COVER the conclusion of a split-tree certificate:
  - depth 0 is today's single-branch inclusion;
  - depth 1 is today's R4 structural split;
  - leaves are discharged by C4 inclusion or C1 emptiness.
- Generalize R4 to take a COVER premise plus per-branch EMPTY or VANISHES_ON claims.

This is the algebraic twin of the cube-and-conquer coverage that Phase 4 wires as COVERAGE premises, so getting the shape right now pays off at G4. The common principle is *no kind without a consumer*: COVER needs one now, and it's why I'd defer ZERODIVISOR below.

*`contra` wasn't extended.* It still knows only EMPTY/NONEMPTY. Add:
- IN_IDEAL(h) vs NOT_IN_IDEAL(h);
- EMPTY vs NOT_IN_IDEAL(h), since empty means the unit ideal, so every h is in it.

**3. IN_IDEAL semantics** are correct: saturation membership is membership in the localization.

The transport is more conservative than it needs to be. Part of that is the handoff spec's fault: it said m = 1, k = 0, and the builder added identical guards on top. The sound condition is:
- each loose equation is IN_IDEAL on the tight system with its guards (m = 1, any k);
- each loose guard is nonvanishing on the tight locus, by the C1 obligation locus inclusion already uses.

The proof is three lines. In R = K[x][1/g_T]/I_T the loose equations are zero, and the guard obligation makes each loose guard a unit, so h·g_Lʲ = 0 forces h = 0.

This matters. Today R2 refuses "an identity survives restriction to a chart", which is the most basic fact about localization. The same obligations along a polynomial map give the missing R3 IN_IDEAL row. The handoff's R3 table has no IN_IDEAL row at all, and A11b needs one. Whatever conservatism remains should go in `KNOWN-CONSERVATISM.md`; none of this is logged there yet.

**4. Frontend policy.**

*Strict keys: yes.* This is Elm decoders failing on unknown fields, and arguably the most important finding of 3a. Add only an explicit ignored namespace (e.g. `meta`), so provenance notes don't turn into losses.

*ℚ default:* fine as a corpus-adapter convention. It should never apply on the user-facing statement surface, where charters should declare scope.

*The sharper problem is `fieldChar?` mapping R/RR/C/CC to characteristic 0.* It's sound, because it only ever strengthens the claim. It's exact for ℂ on EMPTY, VANISHES_ON and IN_IDEAL (C01 is exact). But it strengthens ℂ NONEMPTY and every ℝ locus claim. Two consequences:
- Rows that got through by strengthening should be tagged as such, not counted as plain "expressible".
- On the user surface, "over ℝ" should be a friendly elaboration error ("ℝ-specific claims arrive in 3b; did you mean every char-0 field?"), not a silent upgrade to a possibly false claim.

*Elaboration refusals:* they count when the elaboration error *is* the case's mathematics. A09, X134 and X137 are exactly that: an unbound symbol after elimination, and an incomplete simultaneous substitution. That's Elm's best feature applied to math. They must never count when the error is a decode failure. All three current ones are the good kind; make the scoping/decode split structural in the harness so it stays true.

Separately, X124 and X128 are refused as "unsupported" even though each supplies an exact counterexample. The frontend should file the counterexample and let `contra` do the refusing. X128 can do that today: NONEMPTY at {23} vs EMPTY at {23}.

**5. Binder trust.** The boundary is right in kind: trusting the export is the theorem-side counterpart of trusting the compiled checker. But there are three holes before G1 decision 2 is honestly met.

- **(a) Axioms are checked by name, not by proof.** `Export.lean` collects axioms for the declaration named by the string, while the registry's `proof` field is an independent term. An entry `⟨"w_clean", stmt, scope, sneaky⟩` where `sneaky` uses `sorry` would export `bound: true`. Fix: check that each entry's proof is literally the named constant, or run `collectAxioms` on `registry` itself.
- **(b) Identity is `reprStr` in both the binder and the profile.** That's Lean's Repr instances plus Format at width 120. It's deterministic within one toolchain. But A2 treats a toolchain move as routine, and any Repr or Format change would invalidate every binding at once. It fails closed, but all at once. Define canonical text explicitly (canonical JSON, per §3.1), with a golden test shared by both packages.
- **(c) The validator reads a JSON file and filters on `"bound": true`.** That's uncomfortably close to "a build flag is never enough". Make records receipts of the binder run:
  - bind the binding commit, the Mathlib pin, the toolchain and the module hash;
  - refuse records from a mismatched environment;
  - route them through the commit guard before Phase 5.

Also, generated warrants are minted at char-0 scope while the same receipts reach cofinite sets. X125's warrant is char 0 only, though its reach excludes just {2, 23}. The proofs already carry `natCast_ne_zero_of_factors`, so extend the generator to the computed reach. Otherwise the widest-claim policy and A5(a) are measuring different claims.

**6. Characteristic-only scopes.** Agree with the deferral, with one reframe. Base-field-only claims (ML8 over ℝ, EMPTY over ℚ alone) need scope atoms that aren't closed under algebraic closure, and those belong in 3b.

The point universe isn't one of them. Geometric nonemptiness is NOT_IN_IDEAL(1), which is characteristic-invariant, so ALGEBRAIC_CLOSURE is a statement kind, not a scope flag. Decide that now, so 3b doesn't add a closure flag and end up with two encodings.

Doing it in 3a is cheap:
- **(i)** a rule NONEMPTY ⇒ NOT_IN_IDEAL(1);
- **(ii)** NOT_IN_IDEAL(1) moves tight→loose under R2 and S→T under R3, with the existing C4 obligations. The proof is purely algebraic: in the source's localized quotient, the obligations make the transported guards units and the transported equations nilpotent, and a unit that is nilpotent forces the zero ring;
- **(iii)** one base checker: a univariate m whose leading coefficient is a unit generates a proper ideal.

A point with coordinates in ℚ[a]/(m) is then just an R3 map from (a; {m}). No HexNumberField is needed, and m needn't even be irreducible, because you only claim geometric nonemptiness. A24's √3 point and X45–X50's i points fit this directly. Number fields in 3b are then only for claims *about* a specific field.

**7. Schematic cases and the stragglers.**

Criteria for acceptable fixtures:
- a sidecar keyed by case id and case-bytes hash, so case bytes stay unchanged;
- signed in `CHANGES.md`;
- minimal;
- for REFUSE cases, an instance where the attempted conclusion is *false*, so a wrong rule shows up as a false ACCEPT (a soundness test, not just a discipline test);
- the refusal comes from the named mechanism;
- certificates found externally and replayed.

Concrete proposals:

- **A11b:** T = (w, x; x² − w − 1), with h = x⁴ − (w+1)² and cofactor x² + w + 1. Apply φ = (w ↦ −7−w, x ↦ −x), giving S = (x² + w + 6). Expect IN_IDEAL(x⁴ − (w+6)²) on S. This needs the R3 ideal-level row from (3). Drop the embedding (that part is 3b); the inverse composition isn't needed for this direction.
- **A12:** (x) vs (x²) under the identity map, with an m = 2 certificate. The attempted IN_IDEAL(x) on (x²) is false. It overlaps A03a, which is fine.
- **A23:** chart (x; guard x) is EMPTY by 1·x = x¹. Attempted EMPTY on the parent (x) is false at x = 0.
- **C02:** L = (x, y; {x, x−1}), EMPTY by the integral certificate x − (x−1) = 1. Inclusion into T = (x, y; {x, x−1, y}) gives EMPTY in every field, so this doubles as an earned-widening fixture.
- **X59:** VANISHES_ON(y) holds on (x, y; {x, y}). The attempt on the relaxation (x) is false at (0, 1).
- **X03 → campaign-op.** Its lesson needs an image-closure (elimination-completeness) relation certificate, which 3a doesn't have. For an empty source that certificate degenerates to C1 on the target, so a fixture would test nothing.
- **X13 → census.** Binding a combinatorial certificate to field points is carry kind 2.
- **X120 → campaign-op for now.** The claim needs a non-zero-divisor (NZD) kind, whose consumer would be "drop a guard from an identity". No 3a rule does that, and X362's lesson is structurally enforced. If a campaign ever needs guard removal, NZD and its witness-refuted negative ZERODIVISOR arrive together. The case's own annihilator data is already that witness: IN_IDEAL(a·h) plus NOT_IN_IDEAL(a).
- **X138 stays in 3a**, but needs typed non-evidence. `searched_exponents` should decode into a recorded bounded-search attempt with no admission path, in the TIMEOUT-as-non-evidence lineage, so the refusal is "no certificate" rather than "unknown key". No witness can exist anyway, since y is in the saturation. X129's certificate makes `contra` fire.
- **X141 → campaign-op.** It's the completeness contract of a generator-producing operation. In 0.50 its lesson is structural: inclusions only travel by direction-checked certificates, and there's no ideal-equality kind.

## Smaller notes

- **The A3 deviation is a good one.** Reduction mod p is a ring hom on p-integral rationals, so one arithmetic and one soundness path replace a dependency. Revisit only if census brings large modular certificates where rational coefficient growth bites.
- **chart/cite/universe binding extras.** They're semantically inert in 3a, and staling receipts on them is fine. Document them as provenance bindings so nobody reads them as meaning.
- **Receipt schema nit.** In the corpus receipts `mechanism` is sometimes a bare string ("elaboration") instead of a list.

## Proceeding

G3a is a ruling package plus a modest patch away:

1. **Your rulings:** ownership under construct/check, the geometric-nonemptiness encoding, and the reassignments in (7). Also the Fano intake; I'd sign it, since the schema change is mechanical.
2. **A 3a.1 patch:**
   - binder holes (a)–(c), plus canonical identity;
   - `contra` extension;
   - R2 relaxation and the R3 IN_IDEAL row, with proofs;
   - COVER split tree and the generalized R4;
   - NONUNIT canonicalization and the NOT_IN_IDEAL bridge rule;
   - typed non-evidence;
   - counterexample filing;
   - warrant scope equal to reach;
   - `KNOWN-CONSERVATISM.md` entries.
3. **Fixtures** for A11b, A12, A23, C02 and X59, then geometric nonemptiness if you take it into 3a. That brings A24 and X45–X50 in.
4. **Re-run and gate.**

Phase 4 still looks like the right next test. COVER and coverage is the natural cross-profile probe of whether the kernel really is domain-independent.

On publication: prepare the alpha, but hold it until the identity format changes. Once bindings are public, moving off `reprStr` becomes a breaking change for anyone holding them, which is cheap to avoid now and annoying later.

On the A5 trend: "custody and reach layer over Lean" is tracking. Theorem warrants are cheap and limited by generator coverage. GP-specific value is concentrating in reach, refusal at elaboration and the earned surface. Custody remains the untested half, and 3a gave it almost nothing to chew on.
