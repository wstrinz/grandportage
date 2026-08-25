# GP030: field-scope validation repair receipt

Lane: `agent/local-sonnet/gp030-field-scope-validation-v1`. Base:
`9ada7187b9dca8f2fd0bb3fc5680de3e11ee4297` (`codex/v0.30-native-witnesses`,
"Repair historical migration provenance boundary"). Decision: **FIXED**.

## Trigger and reproduction

Two independent CFG23 scratch assays reported that a field-relative `EMPTY`
claim accepted an arbitrary `scope` string -- `"ALL_FIELDS"`, `"banana"` --
with no structural refusal. Reproduced cold at the pinned base commit:

```
>>> from grandportage import kernel as K
>>> K.derive_scope(K.EMPTY, "NONSQUARE_CLASS", "banana")
'banana'
>>> K.derive_scope(K.EMPTY, "NONSQUARE_CLASS", "ALL_FIELDS")
'ALL_FIELDS'
```

Confirmed at the full-fold boundary (declaration), through the legacy
epoch-0 compatibility read path (`S.load` on an unversioned log with no
`meta` event), and through `migration.migrate_kernel_epoch` on an
older-kernel-epoch native log -- all three accepted `scope: "banana"`
identically, because all three fold every event through the single
`Graph._apply_claim` method, which calls `K.derive_scope` once per claim.
That shared boundary is good news structurally: one fix closes all three
surfaces (see "Where the defect lived" below), and there is no separate
migration-laundering path to patch independently.

## Root cause

`derive_scope` (`grandportage/kernel.py`) exists specifically to stop an
author asserting field-independence on the strength of a field-relative
certificate (`NONSQUARE_CLASS`, `NO_RATIONAL_POINT_SEARCH`, `CITED_PROOF`).
Its check was:

```python
if declared_scope in (None, SCHEME):
    raise ScopeError(...)
return declared_scope
```

This refuses exactly two values -- `None` and the literal string `SCHEME` --
and accepts *everything else unexamined*, including a string that never
named a field at all. The claim then reads as typed (it carries a `scope`
field, the fold did not raise) while asserting nothing checkable. That is
the worse failure mode: a graph that *looks* audited.

`NONEMPTY`'s `scope` was, and remains, entirely unvalidated by design --
`derive_scope` returns `kind != EMPTY` claims' declared scope unconditionally.
That is correct as found: no transport rule in the whole `TRANSPORT` table
consults `scope` except `(BASE_EXTENSION, ALONG, EMPTY)`
(`kernel.py`'s `_SCHEME_SCOPE` rule). `NONEMPTY`'s scope is prose; only
`EMPTY`'s is load-bearing, and only for that one edge/direction cell.

## Inventory: five distinct "scope" dimensions, kept separate

The packet asked not to collapse these into one enum. They are unrelated in
the code and this repair touches exactly one:

| Dimension | Where it lives | Validated? |
|---|---|---|
| **EMPTY field-relative scope** (this defect) | `kernel.derive_scope`, consulted only by `_SCHEME_SCOPE` | Was: only `None`/`SCHEME` rejected. Now: closed grammar (below). |
| Model `coefficient_domain` / `characteristic` | `store._apply_model`, `store.exact_coefficient_domain` | Already exact: must equal `"Q"` or `"F_%d" % characteristic`. |
| Model `point_universe` (`BASE`/`ALGEBRAIC_CLOSURE`/`REAL_CLOSURE`) | `store.POINT_UNIVERSES`, `store._apply_model` | Already a closed enum; `REAL_CLOSURE` additionally requires characteristic 0, domain `Q`, and a `REAL` embedding. |
| Selected embedding identity | `kernel._SELECTED_EMBEDDING_IDENTITY`, `store._validate_embedding`, `store.selected_embedding_identity` | Already a closed, structurally validated vocabulary (`var`/`kind`/`isolating_interval`/etc.). |
| Frontier discharge "scope" (e.g. `scope.exact`, `scope.narrow`) | `tests/test_frontier.py`, `frontier.py` | Unrelated free-text namespace for discharge premises; shares only the English word "scope". Out of scope for this repair. |

## The fix

`grandportage/kernel.py`: added `ATOMIC_FIELD_SCOPES`, `valid_field_scope`,
and one new check inside `derive_scope`'s existing field-relative-EMPTY
branch, after the pre-existing `None`/`SCHEME` refusal:

```python
if not valid_field_scope(declared_scope):
    raise ScopeError(...)   # names the offending value and the repair path
```

`valid_field_scope` is a **closed** grammar, deliberately not a permissive
one, read directly off every field-relative scope value already live across
CFG23 fixtures and tests (`Q`, `R`, `F_2`, `Q(sqrt 17)`, `Q(sqrt(-3))`):

- **Atomic**: `Q`, `R`, `C` -- exact rationals, reals, and complexes, the
  three fields this kernel already has other structure for
  (`REAL_CLOSURE`/`ALGEBRAIC_CLOSURE` point universes).
- **Finite**: `F_p` for prime `p` (own small primality check; no import from
  `store.py`, since `kernel.py` is deliberately dependency-free stdlib).
- **Simple extension**: `Q(...)` / `R(...)` with non-blank parenthesized
  content -- exactly the shape `Q(sqrt 17)` and `Q(sqrt(-3))` use. The
  content is **not** parsed as mathematics; this kernel has no number-field
  grammar, and inventing one to validate free-text math prose would be
  guessing at semantics nothing here can check. Only the outer shape is
  required, which is precisely enough to reject `"banana"` and
  `"ALL_FIELDS"` (neither matches any of the three shapes) while admitting
  every live extension string unchanged.

**Deliberately excluded: `"combinatorial"`.** It is live in
`fixtures/_port/gen_matroid.py` (`CM-NP-ORIENTABLE`), but only on a
`NONEMPTY` claim, and `NONEMPTY`'s scope is untouched by this fix. No
field-relative `EMPTY` certificate anywhere cites it, and it names no field.
Admitting it into the `EMPTY` grammar would be inventing a vocabulary item no
live claim demonstrates -- exactly what the packet says to avoid when the
right vocabulary can't be inferred safely. If a future claim needs
"established without reference to a specific field" as an `EMPTY` scope, that
is a new RFC, not a silent widening of this grammar.

**Considered and reverted: restricting `scope` to `EMPTY`/`NONEMPTY`
claims only.** `EVENT_FIELDS["claim"]` in `format.py` lists `scope` as
generic to any claim kind, and `kernel.LICENSING_FIELDS` tracks it generically
for supersession-staleness grading regardless of kind --
`test_adversarial.py::test_a_superseded_premise_is_graded_by_what_actually_changed`
deliberately declares `scope: "Q(sqrt 17)"` on a `PREDICATE` claim to exercise
exactly that generic mechanism. An applicability gate was written, ran the
suite, and broke that legitimate pre-existing test; it was reverted rather
than "fixed" by changing the test, since the test's use is intentional and
correct. `scope` on `PREDICATE`/`IDENTITY`/`COUNT` remains legal, unvalidated
bookkeeping prose, same as before this lane.

## Tests added

`tests/test_field_scope_validation.py`, 47 cases, covering every item the
packet asked for:

- every currently-accepted value (`Q`, `R`, `C`, `F_2`, `F_3`, `F_101`,
  `Q(sqrt 17)`, `Q(sqrt(-3))`, `R(sqrt 2)`, and `NONEMPTY`'s `combinatorial`)
  at both the unit (`derive_scope`) and full-fold level;
- unknown strings (`banana`, `ALL_FIELDS`, `over Q`, `Qbar`, `F_4` (not
  prime), `F_0`, `F_-2`, `Q()` (blank extension), `Qsqrt17` (no parens), ...);
- missing/`null` scope on a field-relative certificate;
- case/whitespace drift (`q`, `scheme`, `f_2`, `q(sqrt 17)`, padded `SCHEME`);
- scope on an inapplicable claim kind (`PREDICATE`) -- confirmed **still
  legal**, per the reverted-overreach note above, with a value
  (`banana`) that would be refused if the claim were `EMPTY`;
- a malformed historical (epoch-0, no `meta` event) graph -- refused on
  `S.load`, not laundered by the legacy read path;
- migration laundering -- `migration.migrate_kernel_epoch` on an
  older-kernel-epoch native log refuses a malformed scope and, critically,
  **leaves no destination file behind** (a partially-written laundered
  migration would be worse than a refusal);
- a valid selected-embedding witness composed with a named field scope --
  confirms the two dimensions in the inventory table above don't interact:
  a model selecting a `REAL` embedding over `REAL_CLOSURE` still gets its
  unrelated `EMPTY` claim's `Q(sqrt 17)` scope validated and refused across
  `BASE_EXTENSION` exactly as an embedding-free model would.

Also amended one pre-existing test, `test_adversarial.py`'s
`test_the_unit_verifier_refuses_a_certificate_it_does_not_decide`: it
declared `scope: "over Q"` as incidental flavor text (the test verifies a
*verifier* refusal, unrelated to the scope string's exact form). Changed to
`scope: "Q"`, the field the test's own docstring says the claim is over; no
other line changed.

## Commands run, counts, and hashes

Worktree HEAD: `9ada7187b9dca8f2fd0bb3fc5680de3e11ee4297` (unchanged;
this lane's commit goes on top, see the branch head).

```
$ python3 -m pytest -q -m "not live"
1 failed, 1572 passed, 50 deselected in 55.80s
```

The one failure is `test_adversarial.py::test_every_marked_check_count_in_the_docs_is_the_real_one`
-- a pre-existing doc/count-sync guard, unrelated to this defect, that
compares the real collected-test count against `<!--checks-->1576<!--/checks-->`
spans in root-level docs (`CURRENT.md`, `HANDOFF.md`, `README.md`,
`REVIEW.md`, `SPEC.md`, `TESTPLAN.md`). This lane's 47 new tests move the
real count to 1623 (`python3 -m pytest -q --collect-only` confirms
`1623 tests collected`). Those root docs are **outside this lane's allowed
write paths** (`grandportage/**`, `tests/**`, `docs/**`,
`review/v0.30/field-scope-validation-v1/**`), so the resync (`gp docs`) is
left for the coordinator or a lane with root-doc write authority, rather
than silently widened here. Every other test, including the new file run
alone, is green:

```
$ python3 -m pytest -q tests/test_field_scope_validation.py
47 passed in 0.30s (0 skipped, 0 failed)
```

**Real CFG23 canonical graph**, read-only, copied to an isolated scratch
root (`campaigns/cfg23/.portage/` -> job-scoped tmp; original never
written):

```
$ python3 -m grandportage.cli --root <scratch-copy> check --full
graph: 7 models, 0 edges, 11 claims, 0 inferences
0 finding(s) at or above UNSOUND_PREMISE: 0 LIVE, 0 carried
```

The real graph carries zero `EMPTY` claims and zero `scope` declarations
of any kind (all `IDENTITY`/`NONEMPTY`/`PREDICATE`, all `scope: None`), so
this repair has **no observable effect** on it -- it was never exposed to
the defect. No format/kernel-epoch bump: no serialization change, no new
required field, no new event kind; `graph_format` stays `7`, `kernel_epoch`
stays `11`.

## Schema-boundary postmortem

**Why the bug was possible.** `derive_scope` was written to refuse exactly
the failure mode its author had in mind -- an author declaring `SCHEME` (or
nothing) on a certificate that cannot support field-independence. That is a
real and well-guarded refusal. But the *positive* case -- "an explicit field
was named" -- was never itself validated, because at the time every author
who reached that line happened to type an actual field name. The check
enforced "is not one specific wrong answer" rather than "is a member of the
right type", which is the general shape of this defect class: a validator
that recognizes the wrong values it has seen, not the right grammar of
values it should accept. `store.py`'s sibling fields
(`coefficient_domain`, `point_universe`) show the fix already existed as a
pattern elsewhere in this codebase -- both are validated against a closed,
exact vocabulary -- so the gap was that `scope` never got the same
treatment, not that the technique was unknown here.

**Which layer now owns validation.** `kernel.derive_scope`, unchanged in
location -- still the single point where every declaration, every native and
legacy-format graph read, and every kernel-epoch migration converge (they
all fold through `Graph._apply_claim`). No new boundary was introduced;
the existing one was made to check the right thing. This is why no
migration-specific or read-specific patch was needed once the kernel-level
check was fixed: there was never a second entry point to patch.

**One adjacent fuzz/property test that would have caught this earlier.**
A property test asserting *closure* rather than *specific refusals*: for
every claim kind and every certificate kind, generate a random printable
string as `scope` and assert that `derive_scope` either raises `ScopeError`
or returns a value satisfying `valid_field_scope(...) or kind != EMPTY`. Put
differently -- "every non-raising return is drawn from the recognized
grammar" -- rather than "these two specific bad inputs raise". A test suite
that enumerates known-bad values (as this codebase's pre-existing
`test_kernel.py` did: `SCHEME`, `None`, `"VIBES"` as a certificate) will
always miss the next arbitrary string; a property test asserting the
*positive* invariant (accept implies grammar-valid) cannot miss it, because
it does not need to guess the adversarial input in advance.
