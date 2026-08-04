# JC H3 on-wall `OB≠0` local-EMPTY compilation

This experiment compiles a landed JC identity into an existing Grand Portage
authority path. It adds no evidence schema, claim kind, relation, graph field,
or kernel epoch.

The frozen native receipt proves, in the Δ-substituted S2 presentation,

```text
value_24 = OB - 45*c2_3*t*R*c8_9.
```

The adapter independently extracts and freezes the exact 502-term `value_24`
and 499-term ambient `OB`. On the constructible piece `R=0, OB≠0`, it checks
the cofactor identity

```text
OB = value_24 + 45*c2_3*t*c8_9*R.
```

Thus `OB` belongs to the declared ideal while also being inverted. The
existing `localization_membership_v1` checker and graph-bound
`LOCALIZED_UNIT_IDEAL_CERT` can mint `LOCAL_EMPTY` for that exact consequence
model.

## Deliberate boundary

The complete nine-body parent is not materialized here. Its future edge to
this dead-row consequence model is also not invented. Therefore this assay
does not by itself grant nine-body, component, actual-source, H3, or
`(75,125)` authority. The complementary closed piece `R=OB=0` is untouched;
the native JC work has exact witnesses there, so it must not be erased by the
open-piece contradiction.

## Replay

```powershell
python experiments\jc_h3_wall_ob_open\adapter.py
python experiments\jc_h3_wall_ob_open\adapter.py --check-native-bindings
python experiments\jc_h3_wall_ob_open\adapter.py --native-replay
python experiments\jc_h3_wall_ob_open\adapter.py `
  --campaign-root C:\tmp\gp-wall-ob-open --record
```

`--write-fixtures` is the only path that imports native JC producer modules.
Ordinary replay uses the frozen sparse polynomials and exact GP checker only.
