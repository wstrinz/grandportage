# Trust architecture

Grand Portage has a small semantic nucleus, but it no longer has a uniformly
small implementation. This document names the actual trust zones and the rules
between them. The zones are logical boundaries; they are not yet Python package
directories.

## 1. Semantic core

Owns:

- graph-format vocabulary and compatibility constants;
- the six transport relations and their claim transformers;
- operation contracts and discharge descriptions;
- pure inference decisions.

Representative modules: `kernel`, `format`, `contracts`, `discharge`.

Rules:

- pure standard-library code;
- no CAS processes or backend protocols;
- no specialized certificate checker;
- no CLI, MCP, artifact, projection, or visualization imports.

## 2. Exact affine evidence

Owns bounded, deterministic certificate replay over exact polynomial or finite
Laurent syntax. It may confirm a narrowly stated proposition, but a standalone
report has no graph effect.

Representative modules: `groebner`, `coefficient_expansion`, `localization`,
`factor_power`, `factor_power_contradiction`, `product_split`,
`laurent_lowering`, `laurent_coefficient_pipeline`, `triangular`, and the
shared descriptive `evidence` manifest.

Rules:

- closed, versioned schemas and exact deterministic arithmetic;
- explicit resource budgets;
- no graph mutation;
- no import of campaign adapters, CAS execution, CLI, MCP, or visualization;
- reported licenses and outstanding premises remain distinct.

## 3. Authority binding

Owns the narrow transition

```text
checked evidence + exact graph/model binding -> current persisted authority
```

Representative responsibilities currently live across `store`, `check`,
`verify`, `operations`, and `provenance`. This is the seam to make smaller
and more explicit; it is not a reason to move the graph fold into Lean.

Rules:

- bind coefficient domain, point universe, ring order, generators, guards,
  source receipts, and input fingerprints as required by the proposition;
- replay evidence rather than trusting a producer verdict string;
- mint only the authority named by the verifier contract;
- stale or mismatched evidence loses authority;
- evidence producers may search, but their search is never authoritative.

Current dependency debt: `verify.py` still combines certificate production,
backend calls, replay, and verdict-event construction; `check.py` imports two
pure lexical helpers from `cas.py`. Consolidation should separate these seams
incrementally, with behavior-preserving tests, rather than by a package-wide
move.

## 4. Adapters and read surfaces

Own CAS execution, backend translation, artifact storage, MCP and hook
enforcement, CLI presentation, native campaign adapters, proof-frontier and
campaign projections, and visualization.

Rules:

- treated as untrusted producers or derived views;
- may consume trusted layers, never define their mathematics;
- projection output is marked `DERIVED_READ_MODEL_ONLY` and cannot overwrite
  an authoritative graph;
- `frontier/v1` premise updates are exact-scope overlays over immutable
  historical envelopes; they infer no geometric containment or assumption
  weakening;
- `frontier-bundle/v1` never resolves repeated semantic IDs by input order;
  every overlap requires an exact-scope agreement or explicit supersession;
- backend disagreements block promotion rather than selecting a winner;
- a native campaign remains the source of its discovery artifacts.

## Dependency direction

The desired direction is:

```text
semantic core
      ^
exact affine evidence
      ^
authority binding
      ^
adapters and read surfaces
```

Some authority orchestration currently calls adapters to produce certificates.
That is a known implementation seam, not permission for semantic-core imports
to flow downward. `tests/test_architecture.py` enforces the boundaries already
made true and records the remaining crossings explicitly.

## Evidence promotion

A live campaign may create an experimental standalone checker for one concrete
need. It becomes a stable generic evidence contract after either two genuinely independent consumers,
or one consumer plus a compelling generic theorem and adversarial controls. It receives graph authority only after an end-to-end
binding assay and a kernel-epoch review.

Before adding graph authority, attempt to compile specialized evidence into an
existing smaller certificate. The JC p-axis factor/affine contradiction, for
example, compiles to a localized-unit-ideal cofactor identity. That path keeps
the trusted authority surface smaller than the family of producer languages.

`gp evidence` renders the shared manifest. It names standalone graph effects,
compilation targets, graph-bound verifier effects, and containment boundaries;
it does not dynamically register checkers or grant authority.
