# Grand Portage v0.23 public-stable packet

This release refreshes the public repository from the old v0.4-era mirror to
the current certifying-compiler and durable-campaign-graph implementation. It
does not enlarge the semantic kernel: graph format remains 4 and kernel epoch
remains 10.

## Stable surface

The package now has four explicit trust zones:

1. the small transport/claim kernel;
2. exact replay for bounded algebraic evidence;
3. graph binding that grants only scoped current authority; and
4. untrusted adapters plus deterministic derived read models.

The release includes transactional exact-target declaration through
`portage_declare`, graph migration and merge support, evidence provenance,
structured operations, exact certificate verifiers, campaign projection,
visualization, `frontier/v1`, and fail-closed `frontier-bundle/v1` composition.

## Frontier composition

`frontier-bundle/v1` combines immutable consumer receipts without granting
graph authority. Receipts must be valid `frontier/v1` projections with exact
input fingerprints and unique normalized path/content bindings. Repeated
semantic items require explicit `AGREE_OPEN` or `SUPERSEDE` records; a closing
observation must itself bind the exact replacement IDs asserted by the bundle.

The canonical checked example combines three research consumers into 20
current items, retaining 12 open obligations and eight resolved items. A
synthetic non-domain-specific fixture demonstrates the same merge algebra.

## Release discipline

Plain `pytest` remains the full release gate. Explicit subsets are:

```text
pytest -m "not live and not replay and not exhaustive"
pytest -m "replay and not live and not exhaustive"
pytest -m "live and not exhaustive"
pytest
```

The release workspace collects 1,576 tests. A tracked-files-only public
snapshot, isolated from any sibling math-stuff checkout, passed 1,268 non-live
tests with 268 explicit JC-integration skips and 40 live deselections in 64.58
seconds. Its separately authorized WSL/Singular tier passed 38 tests with two
environment-dependent skips in 447.40 seconds. Cross-repository native-binding
checks are deliberately not a release gate for this GP-only publication.

`SHA256SUMS` hashes LF-normalized bytes so Windows and Unix checkouts bind the
same tracked content.

## Public/private boundary

The public release contains the package, generic and research-pressure tests,
fixtures, exact adapters, Lean contracts, release packets, examples, and user
documentation. It deliberately omits private campaign state, blind-trial
runbooks, coordinator requests, local MCP/Codex configuration, and workspace
handoffs.

## Authority correctly refused

The derived frontier does not claim graph authority, infer scope containment,
or treat file order and timestamps as proof strength. The included JC pressure
artifacts do not establish source sufficiency, component coverage, H3, or a
`(75,125)` result. They are public regression and review material around the
general-purpose authority boundaries, not a mathematical release claim.
