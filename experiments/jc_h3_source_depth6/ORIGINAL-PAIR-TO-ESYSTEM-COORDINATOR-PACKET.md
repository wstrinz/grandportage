# JC coordinator request: original pair to reduced E-system seam

> **Resolution (2026-08-01):** JC commit d4a18b4 landed the requested honest
> manifest and replay. It certifies the conditional normalized-root-to-five-row
> segment and explicitly refuses the unmaterialized coefficient-level
> original-pair-to-normalized-root segment. GP now binds that result without
> minting original-source, reverse-lift, coverage, H3, or verdict authority.

**Date:** 2026-08-01  
**Audience:** lead Jacobian implementation/coordinator agent  
**Priority:** useful but non-blocking; do not interrupt the mathematical critical path

## Executive request

Please preserve or expose the smallest native, replayable artifact describing the
transition

    original polynomial source pair
        -> finite normalized root/coefficient data
        -> five reduced E-system rows

Grand Portage does not need JC to emit GP-native JSON, adopt GP schemas, or run a
new expensive computation solely for this integration. A stable native receipt
and a native replay command are preferred. If the required information already
exists across current source files or landed receipts, a small manifest that
binds those existing artifacts may be sufficient.

## Why this is now the useful seam

GP v0.22 has closed the downstream composition path:

1. five exact reduced E-system rows;
2. all 147 nonzero coefficient equations of their complete finite template;
3. the selected 25 depth-2..6 face equations;
4. the landed 23-step solve chain;
5. the two depth-6 boundary residuals.

The complete reduced E-system model has 78 active variables and 424,934 sparse
terms. GP independently verifies that the selected faces are necessary
conditions of that complete model and records the corresponding directed point
inclusion. Lean proves the one-way transport law and provides a reverse-
transport countermodel.

The remaining upstream premise is whether, and in exactly what sense, the five
reduced rows follow from the original polynomial-pair source problem. Until
that transition is bound, GP correctly grants no original-source membership,
reverse lift, chart coverage, H3, or (75,125) verdict promotion.

## Preferred native deliverable

Please retain the following in the native JC lane.

### 1. Exact source identity

- the exact original polynomial pair or source equations;
- coefficient domain and characteristic;
- variable order and grading conventions;
- finite support or truncation assumptions;
- source commit and SHA-256 bindings for every load-bearing input.

### 2. Ordered transformation manifest

For each stage between the source pair and the reduced E-system, record:

- operation name and mathematical description;
- exact input and output fingerprints;
- deterministic producer function or command;
- substitutions, derivatives, products, compositions, or coefficient
  extractions performed;
- normalization and denominator-clearing receipts;
- every localization guard or assumed unit;
- support bounds required for a coefficient identity;
- whether the stage is literal equality, equality modulo declared relations,
  localization equivalence, one-way necessary condition, or another relation.

This need not duplicate large expressions if stable content addresses point to
existing native artifacts.

### 3. Exact reduced output

- the five reduced E-system row polynomials in a deterministic exact format;
- the row order and variable order;
- the precise normalizing relation, including 15*t^3 + 1 where applicable;
- a digest matching the rows already frozen by the GP
  graded_face_extraction_v1 fixture, or an explicit explanation of any
  difference.

### 4. Independent native replay

A reviewer should be able to run one documented command that:

1. starts from the bound source inputs;
2. reconstructs or validates every declared transformation;
3. reproduces the five reduced rows and their digests;
4. refuses a mutated input, guard, normalization receipt, support bound, or
   output coefficient; and
5. reports approximate runtime and whether any step remains asserted.

The replay may validate existing frozen outputs rather than repeat the full
discovery search. Please write receipts atomically so an interrupted long run
cannot leave a plausible partial certificate.

## The key semantic question

Please state explicitly which proposition the native work supports:

- every original-source solution maps to a solution of the reduced E-system;
- equivalence on a declared principal-open chart;
- equality only after normalization or localization;
- a bounded coefficient consequence under stated support assumptions; or
- something weaker or different.

GP will not infer this direction from filenames or from the fact that the
polynomials look equal. If different stages have different relations, preserve
that sequence rather than collapsing it into one broad extraction label.

## Reuse before recomputation

Before launching new work, please check whether the needed seam can be assembled
from existing:

- source-pair definitions;
- root-support data;
- E-system constructors;
- normalization or triangular-elimination receipts;
- coefficient-extraction programs;
- landed depth-chain artifacts; and
- current native replay tests.

A manifest plus a thin replay wrapper around those files is preferable to an
expensive duplicate run.

## Explicit non-goals

- Do not put this request on the critical path for the depth computation.
- Do not migrate JC discovery code into Grand Portage.
- Do not emit GP-native campaign events.
- Do not build a general formal-series framework.
- Do not claim reverse lifting, source sufficiency, chart coverage, H3, or a
  final Jacobian verdict.
- Do not treat a generic nonvanishing observation as a localization guard.
- Do not rerun a long computation merely to reproduce information that can be
  bound and replayed from existing exact artifacts.

## Handoff back to the GP adapter lane

When something suitable lands, please report:

- JC commit;
- artifact paths and SHA-256 digests;
- exact replay command, result, and runtime;
- stable field/schema description;
- the supported relation and its direction;
- all localization, normalization, and support premises; and
- any stage that remains asserted or unmaterialized.

The GP lane will then freeze an isolated native projection, write the adapter,
add mutation/refusal tests, and seek only the narrow graph authority actually
supported by the receipt.

## Current GP references

- released authority milestone: v0.22.0 / e86b09c;
- current GP master after projection optimization: 11b0732;
- graded extraction adapter:
  experiments/jc_h3_source_depth6/face_extraction_adapter.py;
- complete-template graph assay:
  experiments/jc_h3_source_depth6/full_template_campaign.py;
- frozen extraction fixture:
  fixtures/jc_source_depth6/graded_face_extraction_v1.json;
- release review packet: review/v0.22/README.md.

## Bottom line

The downstream calculation is now independently replayed and graph-bound. The
highest-value JC contribution to GP is a precise native account of how the
original polynomial pair enters the reduced E-system—preferably assembled from
existing work, and without disturbing ongoing discovery.
