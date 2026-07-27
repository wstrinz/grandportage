"""The enforcement hook: the only part of Grand Portage that can say no.

Everything else informs.  The MCP layer records, the checker decides, the
discharge table advises -- and an agent can ignore all three by not looking.
This runs after each tool call whether anyone wants it to or not, and returns a
blocking exit status when the graph licenses a conclusion it should not.

Wire it into `.claude/settings.json`:

    {"hooks": {"PostToolUse": [{"matcher": "*", "hooks": [
        {"type": "command",
         "command": "python -m grandportage.hook"}]}]}}

Design notes that are not obvious and cost something to get wrong:

FAIL CLOSED, BUT ONLY ON THE THINGS WE OWN.  A malformed graph blocks -- that
is a real defect and the agent just caused it.  A MISSING graph does not: most
tool calls in most repos have nothing to do with a proof campaign, and a hook
that blocks every session without a `.portage/` would be turned off within a
day.  A hook that is turned off enforces nothing.

BLOCK ON NEW FINDINGS, NOT ON ALL FINDINGS.  A campaign mid-flight legitimately
carries known-unsound historical inferences it has not finished repairing --
the JC(2) graph has four of them by construction.  Blocking on those would make
every single tool call fail forever, which trains the operator to disable the
hook, which is worse than no hook.  So the baseline is recorded and only
findings that were not there before block.  `gp check` remains the full picture.
"""

import json
import os
import sys

from . import check as C
from . import store as S

BASELINE = "baseline.json"

BLOCK_MESSAGE = """\
GRAND PORTAGE REFUSED THIS STEP.

%(body)s
This is not advice.  The transport recorded in the graph does not license the
conclusion drawn from it, so proceeding builds on an unsound premise.  Discharge
the finding above, or record explicitly why the type is wrong, before continuing.
"""

# Shown when the hook is live, the graph already has findings, and no baseline
# has ever been recorded.  Without this the operator's first experience is
# every tool call failing for reasons that look like a broken install, and the
# rational response to that is to delete the hook.
NO_BASELINE_HINT = """\

--- FIRST RUN? ---
No baseline has been recorded for this project, so every finding above is
blocking -- including any this campaign already knew about and is deliberately
carrying.  That is almost certainly not what you want on a graph with existing
history.

Record what is knowingly carried, once:

    gp accept -m "why these are being carried"

Only findings NOT in .portage/baseline.json block after that, so a NEW unsound
step still stops the session.  `gp check` always shows the full picture.
"""


def baseline_path(root="."):
    return os.path.join(root, S.GRAPH_DIR, BASELINE)


def read_baseline(root="."):
    """The raw baseline document, normalised.

    `accepted` is stored as {finding id: {"why": ...}} so a REASON TRAVELS WITH
    EACH FINDING rather than with the file.  A single campaign-level note cannot
    say why one particular obligation is carried, and the first real user
    immediately wanted to -- they wrote a paragraph about one finding into the
    shared note because there was nowhere else to put it.

    The legacy list form is still read, so an existing baseline keeps working.
    """
    p = baseline_path(root)
    if not os.path.exists(p):
        return {"accepted": {}, "note": ""}
    try:
        with open(p, "r", encoding="utf-8") as fh:
            doc = json.load(fh)
    except (ValueError, OSError):
        return {"accepted": {}, "note": ""}
    accepted = doc.get("accepted") or {}
    if isinstance(accepted, list):        # legacy: a bare list of ids
        accepted = {fid: {"why": ""} for fid in accepted}
    doc["accepted"] = accepted
    doc.setdefault("note", "")
    return doc


def load_baseline(root="."):
    """The set of accepted finding ids."""
    return set(read_baseline(root)["accepted"])


def save_baseline(root=".", findings=None, note="", merge=True, prune=False):
    """Record the findings a campaign is knowingly carrying.

    MERGES BY DEFAULT, and that default is the whole point of this function.

    The first version replaced the file wholesale.  Accepting one finding with
    `--only` therefore DELETED every previously accepted entry and the note
    explaining them -- silently, on a version-controlled file that humans read
    as the authoritative record of what a campaign knows it is carrying.  It
    was caught by luck: the hook went red again with untouched findings.  Had
    it been the last accept of a session it would have destroyed the record
    without a trace.

    That is the failure this whole project exists to prevent, occurring inside
    the tool, so the repair is not just "merge" -- it is that DESTROYING AN
    ACCEPTANCE MUST BE AN EXPLICIT ACT.  `prune=True` is the only way to drop
    entries, and it only drops findings that no longer appear in the graph.
    """
    p = baseline_path(root)
    d = os.path.dirname(p)
    if d and not os.path.isdir(d):
        os.makedirs(d)

    doc = read_baseline(root) if merge else {"accepted": {}, "note": ""}
    accepted = dict(doc["accepted"])
    for f in (findings or []):
        entry = dict(accepted.get(f.fid) or {})
        # A NOTE APPLIES TO WHAT IS BEING ACCEPTED NOW, NOT TO WHAT WAS
        # ACCEPTED BEFORE.  `gp accept -m "..."` without `--only` used to
        # overwrite the per-finding `why` of every already-accepted finding,
        # replacing a version-controlled record of distinct reasons with one
        # sentence.  That is the `--only` baseline wipe (REVIEW.md sec.7.4)
        # again, narrower only because the ids survive: the reasons are the
        # part a reviewer actually reads.
        #
        # An existing reason is now overwritten only by an explicit
        # single-finding accept, which is a deliberate act aimed at one row.
        if not entry.get("why"):
            entry["why"] = note or ""
        elif note and len(findings) == 1:
            entry["why"] = note
        entry.setdefault("severity", f.severity)
        # What was actually agreed to, not just which slot it sat in.  Writing
        # it here is also the migration path: a legacy entry with no
        # fingerprint is grandfathered by `evaluate` and acquires one the next
        # time it is accepted.
        entry["fingerprint"] = f.fingerprint
        accepted[f.fid] = entry

    dropped = []
    if prune:
        live = {f.fid for f in (findings or [])}
        dropped = sorted(k for k in accepted if k not in live)
        for k in dropped:
            del accepted[k]

    payload = {"accepted": {k: accepted[k] for k in sorted(accepted)},
               "note": doc.get("note") or
               "findings this campaign is knowingly carrying"}
    with open(p, "w", encoding="utf-8") as fh:
        json.dump(payload, fh, indent=2)
    payload["dropped"] = dropped
    return payload


def evaluate(root=".", floor=C.UNSOUND_PREMISE):
    """Return (block: bool, message: str).  Pure -- no I/O beyond reading."""
    path = S.graph_path(root)
    if not os.path.exists(path):
        return False, ""
    try:
        graph = S.load(path)
    except Exception as exc:                     # malformed graph: fail CLOSED
        return True, ("the graph at %s does not fold:\n  %s\n\nA log that "
                      "cannot be folded is worse than a rejected write -- "
                      "nothing downstream of it can be trusted."
                      % (path, exc))
    accepted = read_baseline(root)["accepted"]
    findings = C.run(graph, accepted)
    rank = C.SEVERITY_RANK[floor]
    new, stale = [], []
    for f in findings:
        if C.SEVERITY_RANK[f.severity] < rank:
            continue
        entry = accepted.get(f.fid)
        if entry is None:
            new.append(f)
            continue
        recorded = entry.get("fingerprint")
        # A legacy entry predates fingerprinting.  Grandfather it rather than
        # reopening every carried obligation at once -- a hook that blocks every
        # tool call is the day-one trap this module already warns about -- and
        # it acquires a fingerprint at the next `gp accept`.
        if recorded and recorded != f.fingerprint:
            stale.append((f, entry))
    if not new and not stale:
        return False, ""
    body = []
    for f, entry in stale:
        body.append("%s  %s   [ACCEPTANCE IS STALE]" % (f.severity, f.fid))
        body.append("    This finding was accepted, but what it SAYS has "
                    "changed since -- the edge, the claim, the path or the "
                    "refusal is no longer the one that was agreed to.")
        body.append("    accepted because: %s" % (entry.get("why") or "(no reason recorded)"))
        for line in f.detail.splitlines():
            body.append("    " + line)
        body.append("    -> DISCHARGE: re-read it against the reason above. If "
                    "the obligation is still one you mean to carry, re-accept "
                    "it (gp accept --only %s -m \"...\") and the record will "
                    "match what is actually in the graph." % f.fid)
        body.append("")
    for f in new:
        body.append("%s  %s" % (f.severity, f.fid))
        for line in f.detail.splitlines():
            body.append("    " + line)
        body.append("    -> DISCHARGE: %s" % f.discharge)
        body.append("")
    message = BLOCK_MESSAGE % {"body": "\n".join(body)}
    if not os.path.exists(baseline_path(root)):
        message += NO_BASELINE_HINT
    return True, message


# Tools that cannot change the graph and that you NEED in order to understand
# a block.  A gate that stops you reading the thing it is complaining about
# forces you to disable it to investigate, which is the same as not having it.
#
# The first real user hit exactly this: they could not write down what the hook
# had blocked until they had un-blocked it.
READ_ONLY_TOOLS = frozenset([
    "Read", "Grep", "Glob", "NotebookRead", "TodoWrite", "WebFetch",
    "WebSearch", "mcp__grand-portage__portage_check",
    "mcp__grand-portage__portage_show",
    "mcp__grand-portage__portage_transport_table",
])

LAST_BLOCK = "last-block"


def _repeat_state(root, fids):
    """Return (is_repeat, writer).  Suppresses re-printing an identical wall.

    The same 40-line block arriving five times in a row is not five pieces of
    information; it is one, and the repetition buries the discharge move under
    its own restatement.
    """
    p = os.path.join(root, S.GRAPH_DIR, LAST_BLOCK)
    key = "\n".join(sorted(fids))
    previous = None
    if os.path.exists(p):
        try:
            with open(p, "r", encoding="utf-8") as fh:
                previous = fh.read()
        except OSError:
            previous = None

    def write():
        try:
            d = os.path.dirname(p)
            if d and not os.path.isdir(d):
                os.makedirs(d)
            with open(p, "w", encoding="utf-8") as fh:
                fh.write(key)
        except OSError:
            pass

    return previous == key, write


def main(argv=None):
    argv = sys.argv[1:] if argv is None else argv
    root, tool = ".", ""
    try:
        raw = sys.stdin.read()
        if raw.strip():
            payload = json.loads(raw)
            root = payload.get("cwd") or "."
            tool = payload.get("tool_name") or ""
    except (ValueError, OSError):
        pass
    if "--root" in argv:
        root = argv[argv.index("--root") + 1]

    if tool in READ_ONLY_TOOLS:
        return 0

    block, message = evaluate(root)
    if not block:
        # Clear the repeat marker so the next genuine block prints in full.
        marker = os.path.join(root, S.GRAPH_DIR, LAST_BLOCK)
        if os.path.exists(marker):
            try:
                os.remove(marker)
            except OSError:
                pass
        return 0

    fids = [l.split("  ", 1)[-1] for l in message.splitlines()
            if l.startswith(tuple(C.SEVERITY_ORDER))]
    repeat, remember = _repeat_state(root, fids)
    remember()
    if repeat:
        sys.stderr.write(
            "GRAND PORTAGE: still refused, unchanged -- %s.\n"
            "Full detail and the discharge move were printed above, or run "
            "`gp check`.\n" % (", ".join(fids) or "see gp check"))
        return 2
    sys.stderr.write(message)
    return 2        # Claude Code feeds stderr back to the model as blocking


if __name__ == "__main__":
    sys.exit(main())
