# Wiring Grand Portage into an agent session

Copy `.mcp.json` and `settings.json` into the project's `.claude/` (or merge
them into what is already there).

Two halves, and they do different jobs:

**`.mcp.json` — the forcing function.** Registers the server whose CAS tools
require a transport declaration. `edge` is `required` in the schema, so the
model is told; the handler validates, so a model that ignores its own schema is
still refused; and `run_cas` takes it as a keyword-only argument with no
default, so no future refactor can introduce a path that skips both.

**`settings.json` — the teeth.** Runs the checker after every tool call and
returns exit 2 when the graph licenses a conclusion it should not. Claude Code
feeds the hook's stderr back to the model as blocking feedback, so the refusal
and its discharge move arrive where the work is happening.

## Seed the baseline FIRST — this is not optional

**Wiring the hook onto a graph that already has findings blocks every single
tool call.** That is correct behaviour and a terrible first experience: it
looks like a broken install, and the rational response to a broken install is
to delete the hook. Do this before the first session:

```bash
gp accept -m "the errata this campaign is knowingly carrying"
```

That writes `.portage/baseline.json`. Only findings **not** in it block, so a
new unsound step still stops the session. Accept one at a time when you can —
`gp accept --only TRANSPORT:GI-BRIDGE -m "..."` — since accepting everything is
the blunt instrument and accepting one thing is the honest one.

Commit the file. Accepting a finding is a decision with a cost, and it belongs
somewhere a reviewer can see it rather than in someone's memory of which
warnings are the normal ones.

`gp check` always reports the full picture, baseline or no baseline.

## Order of operations

```bash
gp init                       # or drop an existing graph at .portage/graph.jsonl
gp check                      # see what is there
gp accept -m "..."            # record what you are carrying
cp examples/.mcp.json .mcp.json
cp examples/settings.json .claude/settings.json
# now start the session
```

Reversing it is one file: delete `.claude/settings.json`'s hook block and the
enforcement is gone, with `gp check` still available on demand.

## Environment

`GP_ROOT` sets the project root the server reads and writes (default `.`).
`GP_SINGULAR_ARGV` overrides how Singular is invoked — on Windows the default
is `wsl.exe -- Singular -q`, elsewhere `Singular -q`.
