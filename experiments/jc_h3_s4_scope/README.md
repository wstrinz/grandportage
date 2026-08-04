# JC S4 constructible-scope assay

This adapter freezes the S4 fitting receipt from `../math-stuff` as a bounded
Grand Portage consumer.  It checks one exact point over
`K = QQ[t]/(15*t^3 + 1)` on the closed piece

```text
C = 0, C2 = 0
```

and records the complementary principal-open piece

```text
C = 0, C2 != 0
```

as **OPEN**.  The two pieces form the structural zero/nonzero cover of the
necessary-boundary model, but the cover carries no union-wide mathematical
claim.  In particular, the 24 deterministic off-locus seeds are retained only
as bounded search provenance.  They do not establish off-locus emptiness or
confinement of all `K`-points to `C2 = 0`.

The default replay is producer-independent.  It checks frozen sparse bodies
for the 952-term fitting condition `C`, its exact 24-term `p^2` coefficient
`C2`, and the 12-term rank witness using a small exact cubic-field evaluator.
It does not import or execute JC code.

```powershell
.\.venv\Scripts\python.exe experiments\jc_h3_s4_scope\adapter.py
.\.venv\Scripts\python.exe experiments\jc_h3_s4_scope\adapter.py --check-native-bindings
.\.venv\Scripts\python.exe experiments\jc_h3_s4_scope\adapter.py --native-replay
```

Fixture regeneration is an explicit producer-side operation and refuses to
overwrite by default:

```powershell
.\.venv\Scripts\python.exe experiments\jc_h3_s4_scope\adapter.py --write-fixture --force
```

Authority earned:

- the exact closed piece is nonempty over the declared `K`;
- the parent necessary-boundary model is nonempty over the same `K`, witnessed
  by that same point;
- `C2 = 0` and `C2 != 0` are a structural constructible cover.

Authority explicitly not earned:

- emptiness or nonemptiness of the `C2 != 0` piece;
- confinement of all `K`-points to `C2 = 0`;
- source-image sufficiency or actual-source membership;
- H3 or `(75,125)` promotion.

This remains a standalone evidence projection with graph effect `NONE`.  It
does not add a kernel relation or claim kind.
