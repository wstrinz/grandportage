# Verbatim GP output for the six transports that did not come out clean

Requested follow-up, item 1. GP 0.31.2, source `fa5644dd6f50cf904ad2c1be5f37e7371fe9bf0d`,
graph format 7, kernel epoch 11. Captured 2026-09-09 by re-running
`transports/run.sh <cell>` and piping through `fixtures/normalize.sed`, which
replaces the absolute graph path and drops the two-line hook advisory (see
`fixtures/README.md` — that advisory is a fact about the operator's editor
config, not about GP, and it appeared between the two capture dates because
`~/.claude/settings.json` changed).

**Which three are the partials: X5, X8 and X9.** The four fully correct cells are
X1, X3, X7 and X10; the three wrong ones are X2, X4 and X6. Every cell below is
one of those six, plus the repair variants each one forced.

| cell | file | one line |
|---|---|---|
| X2 | `transports/X2.json` | order certificate, scope `any ordered field` — **refused at fold** |
| X2b | `transports/X2b.json` | first offered repair: name the field (`R`) — folds, then flagged |
| X2c | `transports/X2c.json` | second offered repair: `base_changes: true` — **folds clean, exit 0** |
| X4 | `transports/X4.json` | ℚ-witness → ℝ existence — **refused at fold** |
| X4b | `transports/X4b.json` | repair attempt: `REAL_CLOSURE` — refused at fold |
| X5 | `transports/X5.json` | bare embedding swap — refused (correct) |
| X5b | `transports/X5b.json` | the licensed route via the Galois automorphism — **both transports refused** |
| X6 | `transports/X6.json` | capped residual recorded as an exclusion — folds silently |
| X6b | `transports/X6b.json` | …and transports AGAINST a `NECESSARY_CONDITION` — **clean, exit 0** |
| X6c | `transports/X6c.json` | the honest record: `EMPTY` with no certificate — **refused at fold** |
| X8 | `transports/X8.json` | as the packet writes it — **crashes**, defect D1 |
| X8-X10 | `transports/X8-X10.json` | X8 rewritten with an open premise slot, plus X9 and X10 |

---

## The rule that refused X4

**It is the P0 rule itself, and it is not a check id — there is none.**

The refusal happens at *fold* time, inside `Graph.validate()`
(`grandportage/store.py:2601`), at the per-edge point-universe guard
`store.py:2780-2802`. It raises `GraphError` through `store.py:73`'s `_require`,
which `gp declare` prints as `REFUSED` and nothing is written. Fold-time guards in
GP are anonymous by design: only findings emitted by `check.py` carry ids like
`TRANSPORT:` or `FIELD-EMPTY-MODEL-SCOPE:`, and X4 never reaches the checker.
"P0" is cfg23's own label for the repair it requested on 2026-08-23; grand-portage
does not use the string anywhere.

So it is the rule itself rather than a neighbour — but it is worth being precise
about *which half* of the rule fires, because it is not the false-descent half.
The guard is one `_require` with two jobs:

```python
if e.get("type") != K.UNTYPED:
    src_universe = declared_point_universe(self.models[e["src"]])
    dst_universe = declared_point_universe(self.models[e["dst"]])
    if src_universe is not None or dst_universe is not None:
        _require(
            src_universe is not None and dst_universe is not None
            and src_universe == dst_universe, ...)
```

The false-descent hazard the message narrates — `Q[x]/(x^2+1)` having a point over
`ALGEBRAIC_CLOSURE` and none over `BASE` — is the *mismatch* clause. X4 is refused
by the *omission* clause: `M-E1-Q` declares `BASE`, `M-E1-R` declares nothing, and
the source comment says exactly why that is not allowed to be the softer option:

> The moment EITHER endpoint commits to one, though, leaving the other silent
> cannot become the escape route from an explicit mismatch — that is what
> "omission must not become a bypass" rules out — so the two are required to
> agree once either speaks.

Two consequences follow, and both matter for the next packet.

First, the guard covers **every** declarable edge type, not just `EQUIVALENCE`:
`_POINT_RELATION_CAPABILITIES` in `kernel.py` grants all of them some
point-transport capability, so the check sits once in `store.py` — the only place
that owns both endpoint models — rather than six times in the kernel. Its audit is
`tests/test_adversarial.py:5201`,
`test_other_edge_types_refuse_the_same_point_universe_bypass`. A repair aimed only
at `BASE_EXTENSION` would be aimed at the wrong layer.

Second, `store.py:2768-2778` says the missing vocabulary out loud, unprompted:

> `point_universe` currently has exactly two values and no edge type is typed to
> move an object between them — BASE_EXTENSION is a coefficient-field axis (Q into
> a number field), a different and separate obligation the handoff already carves
> out. A model genuinely changing point universe today has one honest spelling:
> UNTYPED with `debt_why`. The reduction in future misuse is a typed operation for
> exactly that step (name to be chosen with the eventual ordered/real-closed and
> number-field vocabulary, so it is not invented twice) — out of scope here on
> purpose.

That is the same axis this follow-up's item 6 asks about, named by the source
before we asked. See `followup/06-field-class.md`, which reports a run showing the
situation is worse than "unencodable".

---

## Verbatim

```
### X2
--- gp declare ---
REFUSED
  EMPTY claim CL-ORDER-EMPTY declares scope 'any ordered field', which this kernel does not recognize as a field.  A field-relative certificate (ORDER_CERTIFICATE) must name the exact field it is relative to: an atomic field (Q, R, C), a finite field `F_p` for prime p, or a simple extension `Q(...)`/`R(...)` (e.g. "Q(sqrt 17)").  Repair path: correct the scope to name that field, or register a wider certificate if the claim base-changes.

  Nothing was written. The graph is unchanged.
--- gp check ---
graph: 0 models, 0 edges, 0 claims, 0 inferences

clean inferences (0): 

0 finding(s) at or above UNSOUND_PREMISE: 0 LIVE, 0 carried
--- exit: 0 ---

### X2b
--- gp declare ---
declared 4 event(s) to <GRAPH>.
--- gp check ---
graph: 1 models, 0 edges, 1 claims, 0 inferences
       1 of them record no ideal, so nothing algebraic can be checked there
       (`generators: []` says a model imposes no equations; omitting it says nobody wrote them down)

UNSOUND_PREMISE  FIELD-EMPTY-MODEL-SCOPE:CL-ORDER-EMPTY-R
    field-relative EMPTY claim CL-ORDER-EMPTY-R declares scope R at model M-ORDERED, but that model does not declare BOTH a coefficient domain and a point universe. A field name on the claim cannot turn a bare combinatorial model into a space of field-valued points.
      this action locus is empty over every ordered field, by an exact sign/Sturm certificate -- but the recordable scope is R alone
    -> DISCHARGE: Declare the exact model point scope (`coefficient_domain` plus `point_universe`), or keep the combinatorial/topological EMPTY at its own model with SCHEME scope and transport it over an honestly typed edge.

clean inferences (0): 

1 finding(s) at or above UNSOUND_PREMISE: 1 LIVE, 0 carried
--- exit: 1 ---

### X2c
--- gp declare ---
declared 7 event(s) to <GRAPH>.
--- gp check ---
graph: 2 models, 1 edges, 1 claims, 1 inferences
       2 of them record no ideal, so nothing algebraic can be checked there
       (`generators: []` says a model imposes no equations; omitting it says nobody wrote them down)

clean inferences (1): INF-X2C

0 finding(s) at or above UNSOUND_PREMISE: 0 LIVE, 0 carried
--- exit: 0 ---

### X4
--- gp declare ---
REFUSED
  edge 'E-Q-TO-R' is BASE_EXTENSION from 'M-E1-Q' (point_universe='BASE') to 'M-E1-R' (point_universe=None). A coordinate-ring identity or isomorphism says nothing about points if the two endpoints select different point functors: Q[x]/(x^2+1) has no point over BASE and a point over ALGEBRAIC_CLOSURE, so identifying those models would license the false inference that closure-nonemptiness descends to the base field. Once either endpoint declares `point_universe`, both must, and they must be equal; leaving one unstated is not a lesser claim, it is not a claim. If the two universes genuinely differ and no typed operation for that change exists yet, record the step UNTYPED with `debt_why` instead.

  Nothing was written. The graph is unchanged.
--- gp check ---
graph: 0 models, 0 edges, 0 claims, 0 inferences

clean inferences (0): 

0 finding(s) at or above UNSOUND_PREMISE: 0 LIVE, 0 carried
--- exit: 0 ---

### X4b
--- gp declare ---
REFUSED
  <new>:2: model 'M-E1-Q' REAL_CLOSURE requires a selected REAL embedding; an abstract field selects no ordering

  Nothing was written. The graph is unchanged.
--- gp check ---
graph: 0 models, 0 edges, 0 claims, 0 inferences

clean inferences (0): 

0 finding(s) at or above UNSOUND_PREMISE: 0 LIVE, 0 carried
--- exit: 0 ---

### X5
--- gp declare ---
REFUSED
  edge 'E-POS-TO-NEG' is an IDENTITY_MAP between models 'M-E2-POS' and 'M-E2-NEG' that select different serialized embeddings. The coordinate ring does not choose a root: use the actual POLYNOMIAL automorphism when one exists, or record the relation UNTYPED when selected-root compatibility has not been certified.

  Nothing was written. The graph is unchanged.
--- gp check ---
graph: 0 models, 0 edges, 0 claims, 0 inferences

clean inferences (0): 

0 finding(s) at or above UNSOUND_PREMISE: 0 LIVE, 0 carried
--- exit: 0 ---

### X5b
--- gp declare ---
declared 8 event(s) to <GRAPH>.
--- gp check ---
graph: 2 models, 1 edges, 2 claims, 2 inferences

UNSOUND_PREMISE  TRANSPORT:INF-X5B-NZ
    the coefficient pair is nonvanishing at the selected embedding: w^2-17+1 is nonzero
      asserted: X5b-nonvanishing: the coefficient pair is also nonvanishing at the other embedding -- scout-1's actual argument
      refused : this EQUIVALENCE relates abstract coordinate rings but does not identify the endpoints' selected embeddings. A nontrivial field automorphism can carry identities through substitution, but an embedding-sensitive predicate cannot be copied unchanged to a different selected root
    E-CONJ ALONG   NO  this EQUIVALENCE relates abstract coordinate rings but does not identify the endpoints' selected embeddings. A nontrivial field automorphism can carry identities through substitution, but an embedding-sensitive predicate cannot be copied unchanged to a different selected root
    -> DISCHARGE: Re-examine this step: the transport it needs is not licensed by the type it was given.  Either the type is wrong (prove the stronger relation) or the step is wrong (do not take it).

UNSOUND_PREMISE  TRANSPORT:INF-X5B-SIGN
    w-4 is positive at the selected embedding
      asserted: X5b-sign: the same SIGN holds at the other embedding -- which is FALSE, since w-4 is negative at the negative root
      refused : this EQUIVALENCE relates abstract coordinate rings but does not identify the endpoints' selected embeddings. A nontrivial field automorphism can carry identities through substitution, but an embedding-sensitive predicate cannot be copied unchanged to a different selected root
    E-CONJ ALONG   NO  this EQUIVALENCE relates abstract coordinate rings but does not identify the endpoints' selected embeddings. A nontrivial field automorphism can carry identities through substitution, but an embedding-sensitive predicate cannot be copied unchanged to a different selected root
    -> DISCHARGE: Re-examine this step: the transport it needs is not licensed by the type it was given.  Either the type is wrong (prove the stronger relation) or the step is wrong (do not take it).

TRIAGE  UNTESTED-CONDITION:untested:CL-NONVANISH
    structured PREDICATE CL-NONVANISH stores exact ZERO/NONZERO atoms, but nothing has checked whether they hold at M-E2-POS. Accepted exact syntax may not disappear from both verification and checking.
    -> DISCHARGE: Run `gp verify`. ZERO atoms are checked by certified ideal membership; NONZERO atoms are checked by proving their vanishing loci empty. An inconclusive sufficient test remains visible and does not become a refutation.

TRIAGE  UNTESTED-CONDITION:untested:CL-SIGN
    structured PREDICATE CL-SIGN stores exact ZERO/NONZERO atoms, but nothing has checked whether they hold at M-E2-POS. Accepted exact syntax may not disappear from both verification and checking.
    -> DISCHARGE: Run `gp verify`. ZERO atoms are checked by certified ideal membership; NONZERO atoms are checked by proving their vanishing loci empty. An inconclusive sufficient test remains visible and does not become a refutation.

clean inferences (0): 

2 finding(s) at or above UNSOUND_PREMISE: 2 LIVE, 0 carried
--- exit: 1 ---

### X6
--- gp declare ---
declared 3 event(s) to <GRAPH>.
--- gp check ---
graph: 1 models, 0 edges, 1 claims, 0 inferences

clean inferences (0): 

0 finding(s) at or above UNSOUND_PREMISE: 0 LIVE, 0 carried
--- exit: 0 ---

### X6b
--- gp declare ---
declared 6 event(s) to <GRAPH>.
--- gp check ---
graph: 2 models, 1 edges, 1 claims, 1 inferences

DEBT  CONTAINMENT:E-ACTION-TO-CELL
    edge E-ACTION-TO-CELL asserts V(M-ACTION) subset V(M-CELL) and both models carry ideals, so the containment is CHECKABLE and unchecked.
      This is the assertion every cell on this edge rests on, and it is currently the author's word.
    -> DISCHARGE: Run `gp verify` to reduce each generator of M-CELL's ideal modulo M-ACTION's. It is one reduction per generator and it either confirms the containment or refutes the edge.

clean inferences (1): INF-X6B

0 finding(s) at or above UNSOUND_PREMISE: 0 LIVE, 0 carried
--- exit: 0 ---

### X6c
--- gp declare ---
REFUSED
  EMPTY claim CL-NO-CERT has no certificate.  An emptiness with no certificate has no derivable scope, and a scope taken on trust is exactly the failure this kernel exists to refuse.

  Nothing was written. The graph is unchanged.
--- gp check ---
graph: 0 models, 0 edges, 0 claims, 0 inferences

clean inferences (0): 

0 finding(s) at or above UNSOUND_PREMISE: 0 LIVE, 0 carried
--- exit: 0 ---

### X8
--- gp declare ---
Traceback (most recent call last):
  File "<PY>/runpy.py", line 196, in _run_module_as_main
    return _run_code(code, main_globals, None,
  File "<PY>/runpy.py", line 86, in _run_code
    exec(code, run_globals)
  File "<PY>/Scripts/gp.exe/__main__.py", line 7, in <module>
  File "<GP>/grandportage/cli.py", line 3117, in main
    return args.func(args)
  File "<GP>/grandportage/cli.py", line 727, in cmd_declare
    S.append(events, args.root, graph=target)
  File "<GP>/grandportage/store.py", line 3374, in append
    g.apply_all(batch).validate()
  File "<GP>/grandportage/store.py", line 2967, in validate
    at = self.claims[pr["claim"]]["model"]
KeyError: 'model'
--- gp check ---
graph: 0 models, 0 edges, 0 claims, 0 inferences

clean inferences (0): 

0 finding(s) at or above UNSOUND_PREMISE: 0 LIVE, 0 carried
--- exit: 0 ---

### X8-X10
--- gp declare ---
declared 10 event(s) to <GRAPH>.
--- gp check ---
graph: 1 models, 0 edges, 5 claims, 3 inferences
       1 of them record no ideal, so nothing algebraic can be checked there
       (`generators: []` says a model imposes no equations; omitting it says nobody wrote them down)

UNSOUND_PREMISE  TRANSPORT:INF-X10
    E5a: every faithful real V4 action is simultaneously diagonalizable to the standard sign group
      asserted: X10: E5a-c proved plus the generative bridge -> E5
      refused : this argument needs a PREDICATE claim at M-23-4-REAL and the graph has none: E5-gap, the generative bridge: that every fence-valid type produced by E5a-c is present in the frozen 5,299-pin corpus. E5-argument.md section 5 declines to certify it and names the missing same-method n=22 census retrodiction. This is the SOLE open obligation under E5.
    (missing) PREMISE NO  this argument needs a PREDICATE claim at M-23-4-REAL and the graph has none: E5-gap, the generative bridge: that every fence-valid type produced by E5a-c is present in the frozen 5,299-pin corpus. E5-argument.md section 5 declines to certify it and names the missing same-method n=22 census retrodiction. This is the SOLE open obligation under E5.
    -> DISCHARGE: SUPPLY THE MISSING CLAIM, or stop asserting the conclusion.  This is not a transport refusal and there is no edge to retype: the argument declares a premise it does not have, and says so on purpose.
  The slot names the KIND and the MODEL it needs. Establish exactly that and record it, and this argument becomes checkable in the ordinary way.
  If it cannot be established, that is the finding -- and the slot is how it stays visible. Do not close it by writing the claim as though it held; a graph that states a falsehood is worse than one that states a gap. Withdraw the conclusion instead, or weaken it to something the premises you DO have will carry.

UNSOUND_PREMISE  TRANSPORT:INF-X8
    E3b: for every geometric (23_4) in RP^2, |Sym(X)| is in {1,2,4}; order four implies V4
      asserted: X8: therefore the V4-symmetric real (23_4) configurations are exactly E1 and E2
      refused : this argument needs a PREDICATE claim at M-23-4-REAL and the graph has none: X8 cites E4 (exactly 2 of the 5,395 actions realizable) and E3b and stops. E5 -- that the 5,395-action census is COMPLETE -- is not among the premises and is not in this graph as a settled claim. Without it, 'exactly 2 of the census' does not become 'exactly 2 in the world'. E4 itself is a COUNT claim at a family and cannot be cited as a premise at all in GP 0.31.2 (defects/D1).
    (missing) PREMISE NO  this argument needs a PREDICATE claim at M-23-4-REAL and the graph has none: X8 cites E4 (exactly 2 of the 5,395 actions realizable) and E3b and stops. E5 -- that the 5,395-action census is COMPLETE -- is not among the premises and is not in this graph as a settled claim. Without it, 'exactly 2 of the census' does not become 'exactly 2 in the world'. E4 itself is a COUNT claim at a family and cannot be cited as a premise at all in GP 0.31.2 (defects/D1).
    -> DISCHARGE: SUPPLY THE MISSING CLAIM, or stop asserting the conclusion.  This is not a transport refusal and there is no edge to retype: the argument declares a premise it does not have, and says so on purpose.
  The slot names the KIND and the MODEL it needs. Establish exactly that and record it, and this argument becomes checkable in the ordinary way.
  If it cannot be established, that is the finding -- and the slot is how it stays visible. Do not close it by writing the claim as though it held; a graph that states a falsehood is worse than one that states a gap. Withdraw the conclusion instead, or weaken it to something the premises you DO have will carry.

clean inferences (1): INF-X9

2 finding(s) at or above UNSOUND_PREMISE: 2 LIVE, 0 carried
--- exit: 1 ---

```
