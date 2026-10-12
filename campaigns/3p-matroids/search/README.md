# Search tooling (untrusted, campaign-op)

Singular (WSL Ubuntu) and sympy helpers the campaign agent used to find points and certificates. GP replays everything they produce. `realize.py` places points constructively over Q, F_p[a]/(m) and Q(w). `sat.py` minimizes guards by sequential saturation and lifts. `maproute.py` builds the GP-CLI map route. Paths inside are the run's own and may need editing.

F2: `f2.py` searches a Q point and field points per catalog entry, placing one point at a time with per-point retry (it replaces `realize.search`, whose `tries=1` path always uses one element order). `f2_empty.py` gets Singular emptiness certificates. `f2_build.py` writes receipts to `receipts/f2/` and the `cmds-batch*.txt` lists. `f2_run.py` runs them through gp. `f2-timing.jsonl` holds the per-call fold times.
