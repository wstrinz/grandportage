# JC H3 unilateral adjoint-recurrence assay

This experiment is the first `parametric_recurrence_v1` consumer. It checks the
corrected constant-coefficient annihilator statement in the landed JC adjoint
receipt without giving the result graph authority.

Constant shift coefficients are explicitly typed over `QQ`; sequence values
are exact sparse polynomial matrices with faithful rational scaling. Finite
operators are canonically padded to width at least eight before the Lean
characterization is applied.

The mathematical seam is intentionally split:

1. The adapter independently decodes the frozen padded `5 x 2` operator
   matrices and verifies their exact jump sequence.
2. It checks the instance premises `B_d = 0` for `d >= 14` and `B_13 != 0` on
   the unilateral domain `d >= 6`.
3. `lean/GrandPortage/ParametricRecurrence.lean` proves generically that those
   premises characterize constant-coefficient annihilators by vanishing of all
   coefficients below shift `14-6 = 8`.

Consequently, and conditional on the native sequence assumptions, the
annihilator ideal is exactly `(S^8)`. Pure forward truncation annihilates;
`S^7` does not; no annihilator has nonzero constant term; and no reversible
backward recurrence exists.

The adapter also independently reconstructs the jump set
`{7, 9, 11, 13}`. This verifies the degree-one polynomial-coefficient operator

```text
(d-7)(d-9)(d-11)(d-13)(S-1)
```

and the necessity of each displayed linear factor. It makes no minimality
claim among higher-`S`-degree polynomial-coefficient operators.
It also does not adopt a blanket “minimal `S-1` within every regime” reading:
the final padded regimes are zero and therefore admit the unit annihilator.

Normal replay uses only the frozen fixture:

```powershell
python experiments\jc_h3_adjoint_recurrence\adapter.py
python experiments\jc_h3_adjoint_recurrence\adapter.py --check-native-bindings
```

The producer replay is opt-in and requires the JC Python environment, including
SymPy:

```powershell
python experiments\jc_h3_adjoint_recurrence\adapter.py --native-replay
```

Authority explicitly retained as open or refused:

- P1..P5, S2, the pin, and especially H8 remain native assumptions;
- cokernel bases and depth-8 straggler identities are outside this adapter;
- no additive value such as `Omega_8` or `Omega_9` is computed;
- no geometric exclusion, source membership, H3, `(75,125)`, graph claim, or
  transport authority follows.

The evidence report therefore has graph effect `NONE`.
