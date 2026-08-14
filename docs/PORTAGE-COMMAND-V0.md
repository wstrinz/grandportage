# Portage Command v0

Portage Command is the provisional research-operations layer over Grand
Portage. It turns exact frontier observations into digest-bound work packets,
records attempts without rewriting their outcomes, and projects maturity plus
verification debt for a future console.

It is a derived read surface. Every schema in this document has authority
`DERIVED_READ_MODEL_ONLY` and graph effect `NONE`.

## Current JC pilot

The first packet set binds all three attacks to the still-open
`JC.H3.SOURCE.REMAINING_COEFFICIENT_MAP` observation:

- `JC.H3.SIGMA.WEIGHTED_PROJECTIVE.CLASSIFY.v0` records the second-component
  counterexample as a completed useful refutation;
- `JC.H3.SIGMA.D_ANSATZ.TEST.v0` records the failed compression as a completed
  useful refutation;
- `JC.H3.SIGMA.Q51_HYPERPLANE.CLASSIFY.v0` is the active narrowed mission.

Compile the exact packet set:

```text
gp campaign-packet fixtures/campaign/jc_sigma/packets.json
```

Generate the active cold-agent prompt from the same packet:

```text
gp campaign-packet fixtures/campaign/jc_sigma/packets.json \
  --packet JC.H3.SIGMA.Q51_HYPERPLANE.CLASSIFY.v0 \
  --format agent
```

Inspect the immutable attempt ledger or console overlay:

```text
gp campaign-ledger fixtures/campaign/jc_sigma/ledger.json
gp campaign-ledger fixtures/campaign/jc_sigma/ledger.json --overlay
```

The matroid packet is the first non-JC shape check:

```text
gp campaign-packet fixtures/campaign/matroid/packets.json --format human
```

## Binding model

A `campaign-packet/v0` binds:

1. the exact `frontier-bundle/v1` manifest and observation;
2. the selected source receipt and its evidence envelope;
3. the complete task-catalog entry;
4. source artifact descriptors;
5. replay and required mutation controls;
6. advisory maturity, cost, lifecycle, dependencies, and attack history.

The compact frontier bundle remains compact. Full task prose does not become
mathematical authority merely because a campaign catalog records it.

## Ledger rules

`ACCEPTED_ARTIFACT` and `USEFUL_REFUTATION` require a content-addressed
artifact, passing replay, and every mutation named by the packet. A
`PENDING_VERIFICATION` artifact is counted as debt. If a ledger binds a prior
ledger, every prior attempt must reappear exactly; deletion, changed packet
fingerprints, and rewritten outcomes fail closed.

The outcome vocabulary deliberately distinguishes closure, useful negative
results, correct refusals, packet defects, worker defects, unverifiable
returns, and verification debt. A planner must not collapse these into a
single score.

## What remains deferred

- freezing any of these schemas as `v1`;
- automated packet synthesis or priority scoring;
- distributed mission infrastructure;
- the territorial/RTS visual projection;
- any campaign-driven kernel relation, claim kind, or evidence contract.

The next gate is a real cold-agent trial. Only after its failure matrix is
understood should the existing Three.js explorer gain a campaign overlay.
