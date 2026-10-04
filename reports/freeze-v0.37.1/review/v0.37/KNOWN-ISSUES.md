# Known issues in frozen GP v0.37.0

The frozen implementation is retained unchanged. These are limitations of
its advice or expressiveness, not claims that the new rework is implemented.

## Point containment versus ideal containment

The NOT_BY_IDEAL finding in grandportage/check.py recommends radical
membership as an alternative way to establish containment and says every
licensed cell rests on that containment. Radical membership earns point
containment, not every coordinate-ring identity pullback. With the models
(x^2) and (x), point containment does not make x zero in Q[x]/(x^2).
IDENTITY transport needs the relevant ideal-containment or ring-map evidence.
Do not apply the radical-membership advice to those identity cells.

This is a diagnostic/admission-guidance defect. The existence of that advice
alone is not a reproduced end-to-end false-authority result.

## Specialization conservatism described as a theorem

The SPECIALIZATION table refuses EMPTY and NONEMPTY transport across a
characteristic change even with additional p-integral evidence. SPEC.md and
the specialization discharge text overstate that refusal as a theorem.

Unconditional transport is unsound. With suitable integral model data, a
p-integral unit-ideal certificate can instead be replayed after reduction,
and a p-integral rational witness can be reduced and checked in characteristic
p. Any open-locus guards must also survive reduction. The frozen table does
not express these sufficient conditions.

For example, 1=(2*x)+(1-2*x) replays modulo 3, while x=1/2 on 2*x-1=0 reduces
to x=2 modulo 3. These do not authorize arbitrary characteristic changes.

Sources: the frozen grandportage/kernel.py transport table,
grandportage/check.py NOT_BY_IDEAL finding, grandportage/discharge.py
specialization guidance, and SPEC.md's corresponding transport notes.
