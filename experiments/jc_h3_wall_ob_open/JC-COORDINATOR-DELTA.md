# JC coordinator delta: on-wall `OB != 0` obstruction

Grand Portage now independently replays the landed S2 on-wall dead-row
identity and compiles it to existing graph authority.

Supported wording:

> On the exact Delta-substituted dead-row consequence model with `R = 0` and
> `OB != 0`, GP verified a localized unit-ideal certificate and minted local
> `EMPTY` authority. The certificate is current for the frozen model,
> generator list, guards, coefficient domain, and algebraic-closure point
> universe.

Not supported:

- the complete nine-body model is empty;
- the whole S2 wall or its component is empty;
- the complementary closed piece `R = OB = 0` is empty;
- actual-source membership, H3, or the `(75,125)` verdict changes.

The complete nine-body parent and its necessary-condition edge to the exact
dead-row consequence model are intentionally not materialized. That missing
composition seam is the first additional authority needed before this local
result can participate in a broader exclusion.

Review/replay surfaces:

- `review/jc-h3-wall-ob-open-v1.json`
- `fixtures/jc_wall_ob_open/native_v1.json`
- `fixtures/jc_wall_ob_open/localized_unit_ideal_v1.json`
- `experiments/jc_h3_wall_ob_open/adapter.py`
- `tests/test_jc_h3_wall_ob_open.py`

Routine exact replay:

```powershell
python experiments\jc_h3_wall_ob_open\adapter.py
```

Native binding and producer cross-check:

```powershell
python experiments\jc_h3_wall_ob_open\adapter.py --check-native-bindings
python experiments\jc_h3_wall_ob_open\adapter.py --native-replay
```

Real graph-bound Singular promotion test (use a fresh campaign root):

```powershell
python experiments\jc_h3_wall_ob_open\adapter.py `
  --campaign-root C:\tmp\gp-wall-ob-open-review --record
```
