# Stacks applicability sidecar spike

This experiment tests a narrow question: can semantic theorem discovery plus a
pinned Stacks source make missing mathematical hypotheses more visible without
creating a new GP authority path?

The answer from the three JC assays is yes. The experiment remains outside the
`grandportage` package and has **no graph effect**.

## Trust boundary

```text
natural-language query
        |
        v
TheoremSearch MCP                 discovery only; untrusted ranking
        |
        v
candidate Stacks tag
        |
        v
pinned official Stacks checkout  tag, source label, statement, references
        |
        v
application packet               every theorem and bridge premise accounted for
        |
        v
READY_FOR_GP_REVIEW or REFUSED   still no automatic graph mutation
```

Search scores and generated slogans are forbidden in `theorem_shelf.json`.
They may appear in a discovery response, whose `authority` is always `NONE`.

## Frozen shelf

The shelf contains three official Stacks results at commit
`a04446e57ec1fbc252a871afcec7752fb2807b14`:

- `00IP`, Krull's intersection theorem;
- `01Z2`, nonemptiness of a directed inverse limit; and
- `08SL`, cotangent-complex amplitude for an lci map.

For each tag, `sidecar.py validate-shelf --checkout ...` checks:

- the exact Stacks Git commit;
- `tags/tags` maps the tag to the frozen source label;
- the labelled theorem environment has the exact frozen statement and digest;
- every explicit `\ref` in the statement and proof is declared; and
- every declared dependency tag maps to its expected source label.

Portable validation without a checkout still checks schemas, full digests,
unique hypotheses, and the exclusion of discovery-only fields.

## JC assays

The packets in `applications/` distinguish:

- theorem hypotheses printed by Stacks; and
- application-specific bridge premises needed to use the theorem in JC.

That distinction matters immediately. Tag `00IP` assumes a Noetherian local
ring, a proper ideal, and a finite module. To conclude that one JC discrepancy
class vanishes, the application must additionally identify that class as an
element of the module and prove it lies in every `I^n M`. Those are not printed
hypotheses of `00IP`, but the argument is invalid without them.

All three current JC packets are intentionally refused:

| Tag | Intended use | Main blockers |
| --- | --- | --- |
| `00IP` | persistent discrepancy vanishes | ring/module construction and all-depth membership |
| `01Z2` | compatible truncations have a limit point | no typed inverse system, all-stage nonemptiness, or source-limit bridge |
| `08SL` | two-term cotangent model at depth 7 | lci and presentation identification are not established |

`MISSING` means a needed campaign claim has not been bound. `OPEN` is an active
mathematical question. `UNSUPPORTED` means the current exact-affine GP graph has
no suitable semantic sort. None is silently weakened to the others.

## Commands

From the GP repository root:

```powershell
.\.venv\Scripts\python.exe experiments\stacks_applicability\sidecar.py validate-shelf

.\.venv\Scripts\python.exe experiments\stacks_applicability\sidecar.py `
  validate-shelf --checkout C:\path\to\stacks-project

.\.venv\Scripts\python.exe experiments\stacks_applicability\sidecar.py `
  audit experiments\stacks_applicability\applications\jc_00IP.json

.\.venv\Scripts\python.exe experiments\stacks_applicability\sidecar.py `
  render experiments\stacks_applicability\applications\jc_00IP.json

.\.venv\Scripts\python.exe experiments\stacks_applicability\sidecar.py `
  discover "persistent I-adic divisibility forces a finite-module class to vanish"
```

`discover` needs network access. Everything else is deterministic and offline.

## Why this is not a core feature yet

GP's current `citation` event records resolution hazards: it says which external
object an ambiguous written identifier denotes. It is deliberately not a
general theorem database. Overloading that event would blur a useful boundary.

Likewise, the existing multi-premise inference machinery is promising but does
not yet need modification. This spike first asks whether theorem pins and
hypothesis audits are useful artifacts. A later adapter could translate a
reviewed packet into ordinary cited claims and open premise slots.

No new operation contract, relation, verifier authority, graph format, or
kernel epoch is introduced here.

## Likely durable architecture

TheoremSearch MCP is a good optional discovery accelerator. A pinned local
Stacks checkout is the durable authority substrate because it supplies exact
source, stable tags, direct references, licensing, and a reproducible commit.
A future local index should live in a cache or separate data checkout rather
than vendoring the full Stacks corpus into GP.

Stacks content is licensed under the GNU Free Documentation License. This
experiment retains attribution and only freezes three short theorem statements
plus identifying metadata.
