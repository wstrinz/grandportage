# Phase 0a Cramer power-one provenance review

The pinned adapter does not replay a full-model derivation of the recorded power-one pair. Fixture construction executes the native producer and computes the numerator from captured `PHI`/`FIX`; it serializes the denominator from captured `sD`. Ordinary validation reconstructs the stored Cramer identity at A6, then only checks nondivisibility of the stored univariate pair at A7.

The fixture digest and optional source-file hashes provide custody, not a fresh derivation. The exact supported neutral scope is supplied-polynomial nondivisibility. It cannot claim that the denominator is the specialized `det5`, that the numerator is the required full-model specialization, or that square clearing is wall-wide necessary.

Three provenance links remain absent: derivation of `sD`; recomputation of the pair from the retained fixture fields; and a checked bridge from A7 to A6.
