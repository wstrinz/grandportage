# Quickstart — a campaign in ten minutes

Minimal and rough-and-ready on purpose. Everything here is exercised by the
test suite or by a live session; nothing is aspirational.

## Install

```bash
git clone <this repo> grand-portage
cd grand-portage
pip install -e .
python -m pytest -q -m "not live"     # ~20s, no CAS needed
```

Two commands are installed, `gp` and `gport`. They are the same program.
**In PowerShell use `gport`** — `gp` is a built-in alias for
`Get-ItemProperty` and the alias wins, so `gp check` fails with
*"Cannot find path '…\check'"*, which names neither the cause nor the cure.
Everywhere else — cmd, bash, zsh — `gp` is fine.

A CAS is optional. Without one you get the checker, the graph and every
refusal; you lose `gp verify` and the live tests. With one, set it up so that
`wsl.exe -- Singular -q` works (or edit `cas._argv`). A cold WSL can take ~45
seconds to answer the first time — that is normal, not a broken install.

## Start a campaign

```bash
mkdir my-campaign && cd my-campaign
gp init
```

That is the whole setup. The campaign is the directory; its state is
`.portage/graph.jsonl`, an append-only log. **The graph is the state** — not
your notes, not the transcript. A fresh reader should be able to pick the
campaign up from it alone, and that is the property worth protecting.

## The loop

```bash
gp declare --file events.json    # write; folds first or writes nothing
gp check                         # what is licensed, and what is not
gp show                          # what is in the graph
gp history                       # where the campaign struggled
```

`gp declare --help` lists every event kind with its required fields and all
the vocabularies. Read it before your first write; it is the one place that
does not drift, because the lists are pulled from the modules that own them.

### A first campaign, whole

```json
[
  {"ev": "model", "id": "TIGHT", "what": "the system with the extra equation",
   "ring_vars": ["x", "y"], "generators": ["x*y-1", "x-1"]},

  {"ev": "model", "id": "LOOSE", "what": "the same system without it",
   "ring_vars": ["x", "y"], "generators": ["x*y-1"]},

  {"ev": "edge", "id": "E", "src": "TIGHT", "dst": "LOOSE",
   "type": "NECESSARY_CONDITION", "map_kind": "POLYNOMIAL",
   "why": "drops the equation x - 1 = 0"},

  {"ev": "claim", "id": "C", "model": "LOOSE", "kind": "NONEMPTY",
   "statement": "(2, 1/2) lies on the hyperbola", "witness_kind": "EXHIBITED",
   "established_by": "RAN", "ladder": "exact-checked"},

  {"ev": "inference", "id": "I", "claim": "C", "path": [["E", "AGAINST"]],
   "concludes_kind": "NONEMPTY",
   "asserted": "so the tighter system has a point too"}
]
```

`gp check` refuses that inference, and the refusal is the product:

> a witness in the relaxation is not a witness in the source — it need not
> satisfy the equation the edge drops

Edges run **tighter → looser**, `V(src) ⊆ V(dst)`. `ALONG` follows the arrow;
`AGAINST` runs back against it, which is the direction emptiness travels and
the direction that closes cases.

## The three things worth knowing on day one

**Declare what a step LOSES, not what it is.** The edge type is a question
about information: does this drop equations (`NECESSARY_CONDITION`),
inequalities (`RESTRICTION`), change the field (`BASE_EXTENSION`), project
(`IMAGE_CLOSURE`), change characteristic (`SPECIALIZATION`), or nothing at all
with a converse you can exhibit (`EQUIVALENCE`)? If you do not know,
`UNTYPED` with a `debt_why` is legal and licenses nothing.

**A refusal is a result.** It is not a failure to route around. `gp why
<TYPE> <DIRECTION> <KIND>` explains any cell, and says whether the refusal is
a theorem or a deliberate conservatism — those need different responses.

**Ignorance is expressible.** `UNKNOWN`, `UNTYPED`, an open premise slot, a
`doubt`. All of them license nothing and all of them are visible. None of them
requires inventing a fact.

## Changing something already declared

Do not redeclare it — the fold refuses conflicting redeclarations, deliberately.
Send the new version with `supersedes` and a `discharge_kind`:

```json
{"ev": "claim", "id": "C2", "supersedes": "C", "discharge_kind": "RESTATE",
 "model": "LOOSE", "kind": "NONEMPTY", "statement": "...", ...}
```

`gp why supersession` explains the four kinds. The kind is **computed**, not
taken on your word — call something an `AMEND` when a licensing field moved
and you will be refused, and told which field.

## MCP

`.mcp.json` in the repo registers the server. Every `portage_*` tool takes an
optional `root`, and **you should pass it**: without one the server writes to
its own working directory, which is the session root and usually not the
campaign you mean.

The CLI is the better-tested path today. Prefer `gp declare` unless you have a
reason.

## When something goes wrong

| symptom | move |
|---|---|
| `GRAPH ERROR` naming a record | `gp migrate --dry-run`, then an `erratum` if it still will not fold |
| a refusal you think is wrong | `gp why <type> <dir> <kind>` — it says theorem or conservatism |
| a finding you will carry | `gp accept --only <id>` with a reason; it stops failing the exit code |
| stale entries piling up | `gp accept --prune` |

An `erratum` voids a record that **will not fold**. A record that folds and is
merely wrong is superseded instead — and the tool refuses the confusion.
