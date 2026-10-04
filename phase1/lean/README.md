# Phase1 typed specification target
Lean4.32.1, Mathlib-free. Build with the installed direct Lake executable and F TEMP/TMP as in the Phase0c build script.

SoundnessStatement.lean defines a proof-obligation proposition against an ImplementationSlot. It does not implement fold/held, assume their soundness, or prove every arbitrary slot correct. The slot must be replaced/bound to actual Phase2 executable functions before the global soundness proof can be claimed.
weakening_sound proves the polarity-independent universal-scope implication without axioms. No sorry or new axiom is used.

The illustrative eventBytes and authority lists are placeholders for the proposed typed log/registry schema. Parser correctness, authenticated registry/version binding, warrant identities, lifecycle and finite closure require specification/scoring before production implementation. Successful elaboration does not close G1.
