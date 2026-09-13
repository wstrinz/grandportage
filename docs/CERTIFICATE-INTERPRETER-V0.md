# Certificate interpretation and composed reach, v0

This continues packages B and C of the
[preservation-atlas program](PRESERVATION-ATLAS-PROGRAM.md). It is a bounded
integer-expression slice of `rational_sos_cofactor_v1`, with one shared example,
not a verified implementation of the complete rational-polynomial parser.

## The proof boundary moved

The original `Atlas.orderedSOS_contradiction` starts from an evaluated equality.
`CertificateInterpreter.certificate_empty` starts from a syntactic derivation
between polynomial expressions. It proves the evaluation step and uses the
model equations to make each cofactor term zero before applying ordered
contradiction. Its premises do not include the evaluated certificate identity.

The formal vocabulary consists of zero, one, variables, addition, multiplication,
and negation. `Derivation` is a small equational calculus; its rules require
explicit ordinary algebraic laws. `derivation_sound` proves those rules sound
under recursive evaluation. It is not a complete normalization algorithm.

`sample_derivation` supplies the actual proof for:

    -1 = x*x + (-1)*(x*x + 1).

The derivation distributes negation, reassociates, cancels opposite terms, and
removes zero. `integer_laws` and `integer_order` discharge every interface premise
for ordinary integers, yielding `integer_no_root`. The generic theorem also
applies to other algebras when those laws and ordering are supplied; this work
does not instantiate a formal library of rational or real fields.

`unordered_solution_and_replay` evaluates both the generator and the certificate
at the explicit Gaussian-integer pair `(0,1)`. The generator is zero and the
certificate equality still holds. `gaussian_has_no_ordering` proves that these
operations cannot satisfy the required ordering. Thus the negative control
isolates interpretation, rather than breaking the polynomial equality.

## Executable correspondence with GP

The checked example is shared with the graph tests through
`tests/fixtures/atlas/ordered_certificate.json`.
`lean/InterpreterParity.lean` serializes the expressions from the formal sample.
`scripts/check_interpreter_parity.py` normalizes syntactic differences such as
`x*x` versus `x^2`, runs GP's actual SOS replay, and compares the resulting
receipt with the fixture's receipt. A different valid square, `-x`, is rejected
by this comparison: checking only that both examples prove something true
would not establish that they are the same example.

This is executable example correspondence. The renderer, JSON decoding, Python
polynomial normalizer, full rational coefficient vocabulary, and runtime receipt
binding are not verified by the Lean theorem. The runtime still earns authority
through its existing verifier and binder. Lean supplies no new runtime licence.

## Composition experiments

`tests/test_certificate_composition.py` replays the shared proof through real
graph creation, verification, reload, and inference audit.

| Experiment | Observed boundary |
|---|---|
| Declaration before replay | The full path is refused; naming ORDERED_SOS_CERT grants no reach |
| ANY_ORDERED → R → Q | After replay, both steps carry EMPTY; the Q → R base-extension edge is crossed AGAINST on the second step |
| Point predicate R → Q | The same edge direction remains refused by concrete point context |
| Append Q → C or Q → F_2 | The two-step prefix succeeds; the third step refuses |
| Change BASE to ALGEBRAIC_CLOSURE | Graph construction refuses the unsupported point-functor change before inference checking |
| Supply the false cofactor +1 | Replay grants no EMPTY authority, and the path stays closed |
| Change the model while retaining its old receipt | Replaying that adversarial history produces no current reach; composition cannot launder stale evidence |

These cover the ordered-certificate composition slice. The program's separate
ideal-certificate specialization, family, image/witness, and point/ring routes
remain follow-on experiments; the existing atlas and prior tests describe
their semantic boundaries but are not relabeled as new graph fixtures here.

## Review and reproduction

From `lean/`, run `lake build`. Then from the repository root:

```text
python scripts/check_atlas_parity.py
python scripts/check_interpreter_parity.py
python -m pytest -q tests/test_certificate_composition.py
```

The CI Lean job runs both executable comparisons. The ordinary deterministic
job runs the graph and comparison mutation tests. No graph format, kernel epoch,
transport rule, certificate verifier, or backend implementation changed.

Evaluation transport along explicit operation-preserving maps is now proved in
[EXPRESSION-TRANSPORT-V0](EXPRESSION-TRANSPORT-V0.md). Rational-polynomial
normalization remains an open proof boundary. The [unit-cofactor follow-up](ATLAS-FOLLOWUP-V1.md) now tests a second
certificate interpretation across composed routes with different algebraic
requirements. General rational normalization remains separate.
