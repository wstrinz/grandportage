# Grand Portage v0.27 consolidation release

Date: 2026-08-23. Implementation commit:
`af4f6a8f6872521f4f814ab8cdb22af32a11d52c`.

Graph format **5** and kernel epoch **10** are unchanged. ARR15 custody was
read-only: no campaign graph was appended, rewritten, revalidated, or promoted.

## Findings and regressions

| observation | before | regression and result |
|---|---|---|
| CAS-less cold clone | 48 live tests errored through an unreachable CAS | collection probes once and skips only `live` with the QUICKSTART reason; `GP_REQUIRE_LIVE=1` removes the skip escape; CAS-less simulation: 52 skipped, 0 failed |
| checker trust migrated | sparse parser/arithmetic/cofactor replay was its own anchor | 256-line independent dict/Fraction oracle; accepted deterministic replay records `REFERENCE_CHECKED` or explicit `REFERENCE_UNCHECKED`; drop/sign/variable mutations refused by both |
| historical substitution defect | sequential replacement could reverse or collapse a simultaneous map | retained v0.2 corpus case reintroduces the sequential algorithm and disagrees with the independent simultaneous result |
| README mixed introduction and specification | 549 lines, with operational history obscuring the first-use path | README is 112 lines with a ≤160 drift gate; complete text moved to `SPEC.md`; table drift now checks SPEC |
| authority declarations were scattered | transport, standalone schemas, and graph effects printed from separate partial registries | unified printable manifest covers all transport rows, evidence schemas, verifier commands, effects, ceilings, consumed/minted kinds, and classification; zero unclassified |
| JC campaign residence | campaign adapters and fixtures lived under broad public prefixes | adapter contract/harness, complete relocation inventory, two destination options, and `CAMP1` re-accretion guard landed; no move crossed the human gate |
| seven read models lacked a compact review object | largest source artifact was tens of MB | lattice/recommendation landed; 46,190,592-byte ARR15 JSONL produced a 351,463-byte digest-bound projection over 129,024 records |
| scope derivation was a Python lookup | certificate stability was prose around a Boolean | Lean admission interface requires a stability proof or countermodel and proves derived scope admissible and maximal |

## Classification

### FIXED

- W1 cold-clone live-test behavior and authorized-live refusal control.
- W2 independent reference oracle, retained corpus, seeded deterministic/live
  differential lane, adversarial mutations, and historical-bug control.
- W3 README/SPEC split and introduction drift tests.
- W4 unified printable registry and complete classification inventory.
- W5 adapter contract, conformance harness, inventory, move options, and
  campaign re-accretion guard.
- W6 read-model lattice and compact content-addressed projection prototype.
- Framework probe: certificate-scope stability calculus and append-only theory
  ledger. The Lean shadow remains explicitly non-authoritative.

### STILL CORRECTLY REFUSED

- Campaign file moves: destination and public/private custody need Will's
  sign-off. Nothing moved.
- Gamma-window retrodiction promotion: no independently pinned final answer key
  for all four original obligations was found in the available campaign
  records, so the fixture remains a historical live front.
- A certificate kind without a stability theorem or retained countermodel has
  no formal admission path.
- A real live CAS failure after collection cannot become a skip.

### DEFERRED

- Macaulay2 as a second untrusted oracle (optional environment coupling).
- Checker extraction/proof, typed-claim redesign, a seventh edge type, fifth
  model claim kind, leases, schedulers, and read-model CLI consolidation.
- REVIEW section and campaign artifact moves, pending the W5 destination gate.
- A timed independent cold-agent reading. Automated tests prove the five
  questions are findable from README + QUICKSTART, but no independent cold
  reader was dispatched in this lane; no timing is fabricated.

## Validation

- Collection: **1,752 tests**.
- Ordinary deterministic: **1,613 passed, 8 skipped** (the new historical
  oracle control was separately rerun after the 1,612-pass full gate).
- Frozen replay: **72 passed, 1 skipped**.
- Exhaustive non-live: **6 passed**.
- CAS-less live simulation: **52 skipped with the documented reason, 0
  failed**.
- Authorized real-CAS probe: **failed loudly** with
  `WSL/Service/CreateInstance/E_ACCESSDENIED`; counted as no live result, never
  as a pass. The live reference-fuzz test reached this boundary.
- Lean: `lake build` completed **27 jobs**, with no `sorry`.
- Public snapshot at the implementation commit: **READY**, 401 public files,
  snapshot SHA-256
  `957e94c70fbc2224cf83e55dcfe2f2db7de78b4380d41230b2f8ae704a821e93`.
- `git diff --check`: clean.

Live-tier authorization note: only CAS reachability is skippable during normal
collection. `GP_REQUIRE_LIVE=1` was used for the real probe, so the environmental
failure remained a failure.

## Negative findings and rejected alternatives

- The deterministic oracle and seeded corpus found **no fast/oracle
  disagreement**. A disagreement remains a hard fast-path failure; no helpers
  are shared between implementations.
- The W4 pass found **no verifier whose actual licensing contradicted its
  documented contract**, so no soundness preemption was triggered. The closest
  classification call was localization membership: it stays `CORE`, while the
  JC-motivated factor/Laurent/triangular layers are `GENERAL-CONTRIB`.
- Defaulting the live tier off was rejected; collection-time reachability skip
  preserves bare `pytest` while a reachable or required live run remains live.
- Deleting operational README prose was rejected; it was retained in SPEC.
- Turning the compact projection into an eighth CLI read model was rejected;
  it is a bounded prototype inside the existing projection substrate.
- Moving JC material before the destination decision was rejected by the W5
  gate.
