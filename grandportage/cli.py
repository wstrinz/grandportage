"""`gp` -- the command line.

Deterministic, read-only by default, exits nonzero when the graph licenses a
conclusion it should not.  No model in the loop: everything here is a fold and
a table lookup.
"""

import argparse
import json
import os
import re
import sys

from . import check as C
from . import hook as H
from . import kernel as K
from . import store as S
from .discharge import (DISCHARGE_KINDS, KNOWN_CONSERVATISM,
                        KNOWN_UNSOUND, discharge_for)


def _graphs(args):
    if args.graph:
        return list(args.graph)
    default = S.graph_path(args.root)
    if not os.path.exists(default):
        sys.stderr.write(
            "no graph at %s.  Pass --graph, or start one with `gp init`.\n"
            % default)
        raise SystemExit(2)
    return [default]


def _load(args):
    try:
        return S.load(*_graphs(args))
    except S.GraphError as exc:
        sys.stderr.write("GRAPH ERROR\n  %s\n" % exc)
        raise SystemExit(2)
    except K.KernelRefusal as exc:
        # EVERY kernel refusal, not an enumeration of the ones that existed
        # when this line was written.  Four subclasses were added in a week and
        # none reached this clause, so a graph tripping them produced a Python
        # traceback instead of the message written to explain it.
        sys.stderr.write("REFUSED\n  %s\n" % exc)
        raise SystemExit(2)


def cmd_check(args):
    g = _load(args)
    accepted = H.read_baseline(args.root)["accepted"]
    findings = C.run(g, accepted)
    if args.json:
        print(json.dumps({
            "findings": [f.as_dict() for f in findings],
            "clean": C.clean_inferences(g, findings),
            "counts": {"models": len(g.models), "edges": len(g.edges),
                       "claims": len(g.claims),
                       "inferences": len(g.inference_order)},
        }, indent=2))
        return C.exit_code(findings, args.floor)

    if not args.quiet:
        print("graph: %d models, %d edges, %d claims, %d inferences"
              % (len(g.models), len(g.edges), len(g.claims),
                 len(g.inference_order)))
        print()
    accepted = H.read_baseline(args.root)["accepted"]
    for f in findings:
        carried = f.fid in accepted
        if args.quiet:
            print("%-18s %-20s %-28s %s"
                  % (f.severity, f.rule, f.subject,
                     "CARRIED" if carried else "live"))
            continue
        if carried and not args.full:
            # Compact, but never silent.  Printing nothing about accepted
            # findings is what made a resuming agent report a healthy campaign
            # as five live blockers.
            print("%s  %s   [CARRIED]" % (f.severity, f.fid))
            print("    because: %s"
                  % ((accepted[f.fid] or {}).get("why")
                     or "(no reason recorded)"))
            print()
            continue
        print("%s  %s%s" % (f.severity, f.fid,
                            "   [CARRIED]" if carried else ""))
        for line in f.detail.splitlines():
            print("    " + line)
        if f.overridden:
            print("    severity OVERRIDDEN from %s -- %s"
                  % (f.derived_severity, f.severity_why))
        for eid, direction, ok, reason in f.trace:
            print("    %-6s %-7s %-3s %s"
                  % (eid, direction, "ok" if ok else "NO", reason))
        print("    -> DISCHARGE: %s" % f.discharge)
        print()

    if not args.quiet:
        clean = C.clean_inferences(g, findings)
        print("clean inferences (%d): %s" % (len(clean), ", ".join(clean)))
        print()
        rank = C.SEVERITY_RANK[args.floor]
        at_floor = [f for f in findings
                    if C.SEVERITY_RANK[f.severity] >= rank]
        live = [f for f in at_floor if f.fid not in accepted]
        print("%d finding(s) at or above %s: %d LIVE, %d carried"
              % (len(at_floor), args.floor, len(live),
                 len(at_floor) - len(live)))
        if at_floor and not live:
            print("Nothing live. Every finding at this floor was examined and "
                  "accepted deliberately -- this campaign is carrying debt in "
                  "the open, not failing.")
    return C.exit_code(findings, args.floor)


def cmd_migrate(args):
    """Fill required fields a graph predates, with their IGNORANCE value.

    Required fields break existing graphs, and that cost came due all at once:
    three live campaign logs stopped folding when `witness_kind` and the
    `ladder` vocabulary landed. Hand-editing an append-only log is the thing
    this project refuses to make people do.

    THE PRINCIPLE SURVIVES, and that is why this is safe. "No silent defaults"
    exists because a default writes a fact nobody vouched for. A migration
    writes the value that says NOBODY VOUCHED -- `UNKNOWN` for an identity's
    origin, `ASSERTED` for a witness -- which is not a guess, it is the truth:
    the claim was recorded before anyone was asked. Both are reported as debt,
    so the graph gets louder rather than quieter.

    WHAT IT WILL NOT DO is repair a field whose value is WRONG rather than
    missing. An invalid `ladder` might belong in `established_by`, or in
    `caveat`, or be a genuine strength claim -- only the author knows, so those
    are reported and left alone.

    THE HALF-GRADE IS THE THIRD CASE, and it is neither of those. A `ladder` of
    `exact-checked` with no `established_by` is not missing a field and not
    holding a wrong value: it is a value with nothing under it. There is no
    ignorance value for `established_by` -- `NOT_REACHED` would be a lie, and
    it is refused against these grades anyway -- so the ignorance value has to
    be written on the OTHER axis. `claimed` is exactly it: the author says so,
    and nothing recorded here says a run happened.

    That downgrade can be wrong, and the direction it is wrong in is the point.
    A claim that really was checked gets under-graded, which costs the campaign
    a little standing and costs its conclusions nothing. The reverse -- leaving
    an unsupported `exact-checked` in place -- is the failure this project
    exists to avoid, so the migration takes the false negative every time and
    says in the caveat where the strength went.
    """
    paths = _graphs(args)
    fills = {("claim", "identity_origin"): (K.UNKNOWN,
             lambda e: e.get("kind") == K.IDENTITY),
             ("claim", "witness_kind"): (K.ASSERTED,
             lambda e: e.get("kind") == K.NONEMPTY)}
    # A RULE NAME USED AS A FIELD NAME.  Renaming is safe for exactly one of
    # them: `ring_isomorphism` and `ring_iso` are both booleans meaning the
    # same thing, so the key is wrong and the value is not, and the tool knows
    # the single right answer.
    #
    # The others in `store._NOT_A_FIELD` are NOT renameable and are left to a
    # human on purpose: `map_polynomial: true` has to become
    # `map_kind: POLYNOMIAL` (a value change, and which of the three?), and
    # `ambient_identity` / `integral_identity` / `scheme_scope` belong on the
    # CLAIM, not the edge the author put them on. Guessing any of those is the
    # thing this command refuses to do.
    renames = {"ring_isomorphism": "ring_iso"}
    _LADDER_MANUAL = set()   # which `manual` rows are bad-`ladder` rows
    changed, manual, downgraded, renamed = [], [], [], []
    for path in paths:
        # A LINE-KEYED REWRITE, not a re-serialization.  The first version of
        # this rebuilt the file from parsed events, which silently deleted
        # every `#` comment and every blank line -- because `load_events`
        # discards them, and anything a parser discards a round-trip destroys.
        # An append-only log is a FILE FORMAT with human content in it, not the
        # serialized form of a data structure.  So only the lines that actually
        # changed are rewritten; every other byte in the file is left alone.
        edits = {}
        for ev, n in S.load_events(path):
            before = json.dumps(ev, sort_keys=True)
            for bad, real in sorted(renames.items()):
                if bad in ev:
                    ev[real] = ev.pop(bad)
                    renamed.append((path, n, ev.get("id"), bad, real))
            # AN EDGE CARRYING A CLAIM'S DISCHARGE VOCABULARY. Silently
            # accepted until edges got their supersession validated, and a live
            # campaign had done it -- unsurprisingly, since the edge vocabulary
            # appeared nowhere in the tool's own surface.
            #
            # NOT auto-mapped, and the reason is the usual one: RELICENSE says
            # a transport-deciding attribute moved, which on an edge is true of
            # both DERIVE (the missing mathematics now exists) and RETYPE (the
            # relation was mis-stated). Those differ in whether the OLD edge
            # was wrong or merely unproven, and only the author knows which.
            if ev.get("ev") == "edge" and ev.get("supersedes") \
                    and ev.get("discharge_kind") in K.SUPERSESSION_KINDS:
                manual.append((path, n, ev.get("id"),
                               "discharge_kind=%s is a CLAIM kind; an edge "
                               "takes DERIVE (the missing mathematics now "
                               "exists) or RETYPE (it was mis-stated) or "
                               "ACCEPT" % ev["discharge_kind"]))
            for bad in sorted(set(S.Graph._NOT_A_FIELD) - set(renames)):
                if bad in ev:
                    manual.append((path, n, ev.get("id"),
                                   "%s -> %s (value must change too)"
                                   % (bad, S.Graph._NOT_A_FIELD[bad][0])))
            for (kind, field), (value, applies) in sorted(fills.items()):
                if ev.get("ev") == kind and applies(ev) and not ev.get(field):
                    ev[field] = value
                    changed.append((path, n, ev.get("id"), field, value))
            if ev.get("ev") == "claim" and ev.get("ladder") \
                    and ev["ladder"] not in K.LADDER:
                manual.append((path, n, ev.get("id"), ev["ladder"]))
                _LADDER_MANUAL.add(ev["ladder"])
            elif ev.get("ev") == "claim" \
                    and ev.get("ladder") in K.LADDER_ASSERTS_A_RUN \
                    and not ev.get("established_by"):
                was = ev["ladder"]
                ev["ladder"] = "claimed"
                note = ("DOWNGRADED BY MIGRATION from %r: the grade asserted a "
                        "run and the log records no `established_by`, so "
                        "nothing here vouches for it. If a run does back this "
                        "claim, name it and restore the grade." % was)
                ev["caveat"] = (ev["caveat"] + " | " + note
                                if ev.get("caveat") else note)
                downgraded.append((path, n, ev.get("id"), was))
            after = json.dumps(ev, sort_keys=True)
            if after != before:
                edits[n] = after
        if not args.dry_run and edits:
            with open(path, "r", encoding="utf-8") as fh:
                lines = fh.readlines()
            for n, text in edits.items():
                lines[n - 1] = text + "\n"
            with open(path, "w", encoding="utf-8") as fh:
                fh.writelines(lines)

    for p, n, cid, field, value in changed:
        print("%s:%d  %s  %s <- %s" % (p, n, cid, field, value))
    print("\n%d field(s) filled with their ignorance value%s."
          % (len(changed), " (DRY RUN, nothing written)" if args.dry_run else ""))
    if changed:
        print("Each is reported as a debt by `gp check`: the graph is now "
              "louder, not quieter.")
    if renamed:
        print("\n%d field(s) RENAMED -- a transport RULE name was used where "
              "the field has a different name, so the value was being stored "
              "and silently ignored:" % len(renamed))
        for p_, n, cid, bad, real in renamed:
            print("  %s:%d  %s  %s -> %s" % (p_, n, cid, bad, real))
    if downgraded:
        print("\n%d claim(s) DOWNGRADED to `claimed` -- each graded itself on "
              "a run it never named:" % len(downgraded))
        for p, n, cid, was in downgraded:
            print("  %s:%d  %s  ladder %s -> claimed" % (p, n, cid, was))
        print("  No value for `established_by` would have been honest here, so "
              "the ignorance went on the other axis. Each carries a caveat "
              "saying where its strength went. If a run does back one of "
              "these, name the run and take the grade back.")
    if manual:
        # ONE LIST, TWO KINDS OF PROBLEM, and the first version printed the
        # `ladder` advice over both -- so an edge carrying a claim's discharge
        # vocabulary was reported as `ladder=...` and told to consider
        # `established_by`. A repair that misdescribes what it found is worse
        # than one that says less.
        ladder_bad = [m for m in manual if m[3] in _LADDER_MANUAL]
        other = [m for m in manual if m[3] not in _LADDER_MANUAL]
        print("\n%d field(s) NEED A HUMAN -- the value is wrong, not missing, "
              "and only you know where it belongs:" % len(manual))
        for p, n, cid, val in ladder_bad:
            print("  %s:%d  %s  ladder=%r" % (p, n, cid, val[:60]))
        if ladder_bad:
            print("  `ladder` is a strength ordering (%s). How you came to "
                  "believe it is `established_by`; a limitation is `caveat`."
                  % ", ".join(K.LADDER))
        for p, n, cid, val in other:
            print("  %s:%d  %s\n      %s" % (p, n, cid, val))
    return 1 if manual else 0


def cmd_history(args):
    """Where did this campaign STRUGGLE?  `gp show` cannot answer that.

    `gp show` prints the FOLD -- what is being carried now -- which is right for
    resumption and wrong for this.  Supersession and repair make a graph tidier
    over time, so the fold systematically under-represents difficulty exactly
    where the most work happened.  This session made that worse on purpose:
    withdrawn edges, withdrawn inferences and their findings all stopped
    reporting, which removed real baseline dilution and removed the scar tissue
    with it.

    The append-only log kept everything.  Nothing surfaced it.

    WHAT IT CAN SEE, and the limit is worth stating first: the log records what
    was DECLARED, never what was REFUSED.  A refusal that made an author think
    again and write something different leaves no direct trace -- only the
    something-different.  So this is a record of REPAIRS, not of attempts, and
    the count of repairs is a floor on the difficulty rather than a measure of
    it.

    What survives is still the best struggle record available anywhere in the
    system, because it is produced as a side effect of the soundness discipline
    rather than by anybody remembering to write a log:

      * supersession chains -- an object replaced once was reconsidered, an
        object replaced three times was hard;
      * the discharge kind that finally worked, against the ones tried before;
      * obligations still carried, with the reasons their authors gave.

    A finished proof erases its own search.  This is the search, retained
    because an append-only log cannot help retaining it.
    """
    paths = _graphs(args)
    events = []
    for p in paths:
        for ev, n in S.load_events(p):
            events.append((p, n, ev))

    # Supersession chains, in declaration order.
    replaced_by = {}
    order = {}
    for i, (_p, _n, ev) in enumerate(events):
        if ev.get("id") and ev.get("ev") in ("edge", "claim", "inference"):
            order.setdefault((ev["ev"], ev["id"]), i)
        if ev.get("supersedes"):
            replaced_by[(ev["ev"], ev["supersedes"])] = (
                ev["id"], ev.get("discharge_kind"), ev.get("ev"))
    chains = []
    for key in sorted(order, key=lambda k: order[k]):
        if key in replaced_by and not any(
                replaced_by.get(k, (None,))[0] == key[1] for k in replaced_by):
            chain, cur = [key[1]], key
            while cur in replaced_by:
                nxt, kind, ent = replaced_by[cur]
                chain.append("--%s-->" % (kind or "?"))
                chain.append(nxt)
                cur = (ent, nxt)
            chains.append((key[0], chain))

    print("HISTORY -- what this campaign reconsidered\n")
    if chains:
        print("SUPERSESSION CHAINS  (an object replaced N times was hard N times)")
        for ent, chain in sorted(chains, key=lambda c: -len(c[1])):
            print("  %-9s %s" % (ent, " ".join(chain)))
        print()
    else:
        print("No supersessions recorded. Either nothing was reconsidered, or\n"
              "reconsideration happened before anything was written down --\n"
              "which the log cannot distinguish and should not pretend to.\n")

    from . import hook as H
    accepted = H.read_baseline(args.root)["accepted"]
    if accepted:
        print("OBLIGATIONS STILL CARRIED  (%d), with the reason given"
              % len(accepted))
        for fid in sorted(accepted):
            why = (accepted[fid] or {}).get("why") or "(no reason recorded)"
            admits = (accepted[fid] or {}).get("admits")
            print("  %s%s" % (fid, "   admits only %s" % ", ".join(admits)
                              if admits else ""))
            print("      %s" % why[:200])
        print()

    notes = [ev for _p, _n, ev in events if ev.get("ev") == "note"]
    print("%d model(s)/edge(s)/claim(s)/inference(s) declared across %d log "
          "line(s); %d note(s) carried and never typed."
          % (len(order), len(events), len(notes)))
    if notes:
        print("A note is prose that happens to live in a JSONL file. If a "
              "load-bearing\npremise is in one, it is invisible to every rule "
              "in the checker.")
    return 0


def cmd_why(args):
    """Explain one transport cell: what it means, what it licenses, what closes it.

    THE REFUSAL IS WHERE THIS TOOL DELIVERS ITS VALUE, and every piece of
    evidence points the same way.  A campaign returning cold reported that the
    only artifact doing real cross-session work was a hint attached to an edge
    and surfaced at the moment of refusal, while every prose claim about the
    vocabulary had rotted within one session.  Another campaign spent its most
    expensive hour on a refusal that was correct and whose correct answer could
    not be looked up from the tool.

    So this reads the material the refusal path already uses -- `TYPE_MEANS`,
    the transport table, `MOVES`, `KNOWN_CONSERVATISM` -- rather than restating
    it anywhere.  A second copy of an explanation is a second thing to rot, and
    this file has already watched five README cells document licences that were
    withdrawn two versions earlier.

    THE REGISTER IS PRINTED WITH THE CELL ON PURPOSE.  A refusal that is a
    deliberate conservatism -- where the mathematics is on the user's side and
    the tool is being careful -- reads exactly like a refusal that is a theorem,
    and a user who cannot tell them apart learns to route around both.  Routing
    around a refusal is the T1 failure mode.
    """
    etype, direction, kind = args.type, args.direction, args.kind
    if etype not in K.DECLARABLE_TYPES:
        sys.stderr.write("unknown type %r; declarable: %s\n"
                         % (etype, ", ".join(K.DECLARABLE_TYPES)))
        return 2
    print("%s -- %s\n" % (etype, K.TYPE_MEANS[etype]))
    dirs = [direction] if direction else list(K.DIRECTIONS)
    kinds = [kind] if kind else list(K.CLAIM_KINDS)
    for d in dirs:
        for kd in kinds:
            r = K.transport(etype, d, kd)
            rule = K.TRANSPORT[etype][d][kd]
            verdict = ("licensed" if rule is True else
                       "REFUSED" if rule is False else
                       "conditional on `%s`" % rule)
            print("  %-8s %-9s  %s" % (d, kd, verdict))
            if rule is not True and (direction or kind):
                print("    %s" % r.reason)
                print("    -> %s" % discharge_for(etype, d, kd).replace(
                    "\n", "\n       "))
            # THE MATHEMATICS IS ON YOUR SIDE AND THE TOOL IS NOT.
            for c in KNOWN_CONSERVATISM:
                if c["cell"] == (etype, d, kd):
                    print("    NOTE -- THIS REFUSAL IS A DELIBERATE "
                          "CONSERVATISM, not a theorem against you.")
                    print("      the kernel says : %s" % c["kernel_says"])
                    print("      the truth is    : %s" % c["truth"])
                    print("      kept because    : %s" % c["why_kept"])
            for c in KNOWN_UNSOUND:
                if c.get("cell") == (etype, d, kd):
                    print("    WARNING -- THIS CELL IS KNOWN UNSOUND: %s"
                          % c.get("why", ""))
        if not kind:
            print()
    return 0


CHECKS_SPAN = re.compile(r"(<!--checks-->)(\d+)(<!--/checks-->)")


def cmd_docs(args):
    """Rewrite the machine-computable numbers in the documentation.

    SIX DIFFERENT CHECK COUNTS were live across the docs at once -- 160, 171,
    251, 273, 307, 338 -- against an actual 384.  The file labelled READ THIS
    FIRST IF YOU HAVE NO CONTEXT disagreed with the README, which disagreed
    with REVIEW.md, which disagreed with TESTPLAN.md.

    That is not housekeeping.  The project's thesis is that prose read surfaces
    rot first, and these are the surfaces a cold session reads; a campaign
    whose headline measurement is cold resumption cannot have its resumption
    documents lying about how much evidence exists.  It is REVIEW.md section 7
    happening inside the documents that argue for section 7.

    A NAIVE `\\d+ checks` SWEEP WOULD BE A FALSE-POSITIVE GENERATOR, which is
    the one thing this project must not ship.  Several of those numbers are
    TRUE HISTORY -- "the suite went 171 -> 251 checks", "171 checks agreed with
    it" -- and a rule that cannot tell a current-state claim from a narrative
    one would demand the history be falsified to go green.  So current-state
    numbers are MARKED and only marked ones are checked:

        gated: <!--checks-->384<!--/checks--> checks

    The comment renders as nothing, so the prose reads normally.

    Precedent: `gp table` prints from the kernel so a document quoting it
    cannot drift from the code applying it.  This is that principle applied to
    every number a machine can compute.
    """
    import subprocess
    root = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
    n = args.count
    if n is None:
        out = subprocess.run([sys.executable, "-m", "pytest", "-q",
                              "--collect-only", os.path.join(root, "tests")],
                             capture_output=True, text=True, cwd=root).stdout
        m = re.search(r"(\d+) tests? collected", out)
        if not m:
            sys.stderr.write("could not collect the test count\n")
            return 2
        n = int(m.group(1))
    changed = []
    for name in sorted(os.listdir(root)):
        if not name.endswith(".md"):
            continue
        path = os.path.join(root, name)
        with open(path, encoding="utf-8") as fh:
            text = fh.read()
        new = CHECKS_SPAN.sub(lambda mm: mm.group(1) + str(n) + mm.group(3), text)
        if new != text:
            with open(path, "w", encoding="utf-8") as fh:
                fh.write(new)
            changed.append(name)
    print("suite has %d checks" % n)
    for c in changed:
        print("  updated %s" % c)
    if not changed:
        print("  every marked span already agrees")
    return 0


def cmd_merge(args):
    """Fold several branch logs together and report every conflict at once."""
    graphs = list(args.graph or [])
    if len(graphs) < 2:
        sys.stderr.write("gp merge needs at least two --graph paths\n")
        return 2
    try:
        g, conflicts = S.merge_report(graphs)
    except (S.GraphError, K.KernelRefusal) as exc:
        sys.stderr.write("GRAPH ERROR (before any conflict)\n  %s\n" % exc)
        return 2
    if not conflicts:
        print("MERGE COMPOSES. %d models, %d edges, %d claims, %d inferences."
              % (len(g.models), len(g.edges), len(g.claims),
                 len(g.inference_order)))
        print("Concatenating these logs and folding gives a well-formed graph.")
        return 0

    print("MERGE CONFLICTS: %d\n" % len(conflicts))
    for c in conflicts:
        print("%s %r -- declared differently in two branches" % (c["kind"], c["id"]))
        print("  fields that differ: %s" % ", ".join(c["fields"]))
        for side in ("a", "b"):
            s = c[side]
            print("  %s  %s:%d" % (side.upper(), s["path"], s["line"]))
            for f in c["fields"]:
                print("        %-10s %s" % (f, json.dumps(s["event"].get(f))))
        print()
    print("Neither version is preferred and the fold will not blend them. Two "
          "cases, with opposite resolutions:")
    print("  SAME OBJECT, described differently -- both branches are right. "
          "Reconcile the wording into one declaration; whoever merges picks it.")
    print("  DIFFERENT OBJECTS that collided on a name -- rename one. If the "
          "two are related, say how with an edge; if they are the same object "
          "under two names, record a `same_as`.")
    print("\nWhich it is, is mathematics. This can only put them side by side.")
    return 1


def cmd_table(args):
    """Print the transport table from the kernel itself, so a document quoting
    it and the code applying it cannot drift apart."""
    width = max(len(t) for t in K.DECLARABLE_TYPES)
    hdr = "| %-*s | %-7s | %s |" % (width, "edge type", "dir",
                                    " | ".join("%-9s" % k
                                               for k in K.CLAIM_KINDS))
    print(hdr)
    print("|" + "-" * (len(hdr) - 2) + "|")
    for t in K.DECLARABLE_TYPES:
        for d in K.DIRECTIONS:
            cells = []
            for k in K.CLAIM_KINDS:
                v = K.TRANSPORT[t][d][k]
                cells.append("%-9s" % ("yes" if v is True else
                                       "NO" if v is False else v))
            print("| %-*s | %-7s | %s |" % (width, t, d, " | ".join(cells)))
    print()
    print("WHAT THE TYPES MEAN. A transport row does not say what a name")
    print("denotes, and a name read generically gets used generically:")
    for t in K.DECLARABLE_TYPES:
        print("  %s" % t)
        for line in _wrap(K.TYPE_MEANS[t], 64):
            print("      " + line)
    print()
    print("Conditional cells resolve against edge/claim attributes:")
    print("  scheme_scope        EMPTY base-changes only if its certificate does")
    print("  map_polynomial      IDENTITY rewriting needs a denominator-free map")
    print("  closed_condition    only Zariski-closed predicates reach a closure")
    print("  ambient_identity    a rewriting DERIVED from the source's own")
    print("                      equations does not survive dropping them")
    print("  ring_isomorphism    an EQUIVALENCE carries a rewriting only if it")
    print("                      preserves the coordinate ring, not just points")
    print("  integral_identity   reducing mod p needs p-integral coefficients")
    print("  coefficients_in_base descending needs both sides defined over the")
    print("                      base field")
    print()
    print("Certificates that base-change (an emptiness proved this way is")
    print("field-independent):")
    for c, bc in sorted(K.BUILTIN_CERTIFICATES.items()):
        print("  %-28s %s" % (c, "yes" if bc else "NO -- field-relative"))
    print()
    print("Known conservatism -- cells refused more strictly than the")
    print("mathematics requires, kept deliberately:")
    for kc in KNOWN_CONSERVATISM:
        print("  %s/%s/%s:" % kc["cell"])
        for line in _wrap(kc["truth"]):
            print("      " + line)
    print()
    # Printed even when empty, and that is deliberate.  The absence of this
    # register is why a knowingly-false licence once lived only in a test
    # docstring; printing "(none)" is a positive assertion that there is
    # nothing here, which a missing section would not be.
    print("Known UNSOUND -- cells knowingly licensed more loosely than the")
    print("mathematics allows.  Any entry is a bug with a deadline:")
    if not KNOWN_UNSOUND:
        print("  (none)")
    for ku in KNOWN_UNSOUND:
        print("  %s/%s/%s:" % ku["cell"])
        for line in _wrap(ku["truth"]):
            print("      " + line)
    return 0


def _wrap(text, width=68):
    import textwrap
    out = []
    for para in str(text).split("\n"):
        out.extend(textwrap.wrap(para, width) or [""])
    return out


def cmd_show(args):
    g = _load(args)
    for mid in sorted(g.models):
        m = g.models[mid]
        bits = [b for b in (m.get("chart"), m.get("field")) if b]
        print("MODEL %-14s %s" % (mid, " ".join(bits)))
        print("    %s" % m.get("desc", ""))
    print()
    for eid in sorted(g.edges):
        e = g.edges[eid]
        print("EDGE  %-6s %-14s -> %-14s %s" % (eid, e["src"], e["dst"],
                                                e["type"]))
    print()
    # CERTIFICATE and ORIGIN are printed, and INFERENCES are printed at all.
    #
    # `gp show` used to print models, edges and claims only -- no inferences,
    # and no certificate on a claim -- while the MCP `portage_show` printed
    # both.  A fresh agent resuming a campaign through the CLI named exactly
    # this as its biggest hole: "the two headline results are EMPTY claims
    # whose field-independence I cannot check."  The certificate is the field
    # `derive_scope` calls the most load-bearing in the system, and the one
    # view a human is most likely to use was the one that hid it.
    for cid in sorted(g.claims):
        c = g.claims[cid]
        extra = []
        if c.get("certificate"):
            extra.append("cert=%s" % c["certificate"])
        if c.get("identity_origin"):
            extra.append("origin=%s" % c["identity_origin"])
        if c.get("established_by"):
            extra.append("by=%s" % c["established_by"])
        if c.get("ladder"):
            extra.append("ladder=%s" % c["ladder"])
        # A WITHDRAWN RECORD THAT LOOKS LIVE is the whole reason supersession
        # exists.  Before it, a reminted claim left its predecessor sitting in
        # the graph, printed identically to everything around it, and the only
        # thing distinguishing the two was a prose note somebody had to read.
        mark = ("  [SUPERSEDED by %s]" % c["superseded_by"]
                if c.get("superseded_by") else "")
        print("CLAIM %-20s %-9s @%-14s scope=%-10s %s%s"
              % (cid, c["kind"], c["model"], c.get("scope"),
                 " ".join(extra), mark))
        if c.get("supersedes"):
            print("    supersedes %s (%s)"
                  % (c["supersedes"], c.get("discharge_kind")))
        # A caveat that is not printed is a caveat that was not recorded.
        if c.get("caveat"):
            print("    caveat: %s" % c["caveat"])
    if g.inference_order:
        print()
    for iid in g.inference_order:
        i = g.inferences[iid]
        mark = ("  [SUPERSEDED by %s]" % i["superseded_by"]
                if i.get("superseded_by") else "")
        print("INFER %-20s %s via %s -> %s%s"
              % (iid, i["claim"],
                 " ".join("%s/%s" % s for s in i["path"]) or "(no path)",
                 i["concludes_at"], mark))
        print("    %s" % i.get("asserted", ""))
        if i.get("supersedes"):
            print("    supersedes %s (%s)"
                  % (i["supersedes"], i.get("discharge_kind")))
    return 0


def cmd_accept(args):
    """Record the findings this campaign is knowingly carrying.

    Accepting a finding is a decision with a cost, so it lands in a file a
    reviewer can read -- and one that belongs in version control -- rather than
    in someone's memory of which warnings are the normal ones.
    """
    from . import hook as H
    g = _load(args)
    # THE BASELINE HAS TO GO IN, and leaving it out made one whole finding
    # class unacceptable.
    #
    # `check_supersession` is the only rule that reads the baseline, because a
    # SUPERSESSION finding exists precisely WHEN a baseline entry pinned
    # `admits` and a supersession offered a discharge outside it.  Running the
    # checker without the baseline here meant that rule produced nothing, so
    # the one finding class that is definitionally baseline-derived was the one
    # class `gp accept` could not see: `--only SUPERSESSION:...` answered "no
    # such finding" while `gp check`, two functions up this file, printed it.
    #
    # It fires at UNSOUND_PREMISE, which is the hook's blocking floor, and an
    # append-only log cannot un-declare the record that caused it.  So a live
    # campaign reached a state where a finding could be neither discharged nor
    # accepted and the hook refused EVERY tool call -- Read, Write, Bash, the
    # MCP writes -- until the author bypassed the CLI and wrote the baseline by
    # hand.  `hook.py`'s own comment calls a hook that blocks every tool call
    # "the day-one trap this module already warns about".
    accepted_now = H.read_baseline(args.root)["accepted"]
    findings = C.run(g, accepted_now)
    live = list(findings)          # before any --only filtering; see below
    before = H.load_baseline(args.root)
    if args.only:
        unknown = sorted(set(args.only) - {f.fid for f in findings})
        if unknown:
            sys.stderr.write("no such finding: %s\nrun `gp check` for the "
                             "current ids\n" % ", ".join(unknown))
            return 2
        findings = [f for f in findings if f.fid in set(args.only)]
    # `live` is the UNFILTERED set and `findings` may be a subset of it.  This
    # is the whole repair: `--only` narrows what is being accepted, and must
    # never narrow what counts as still existing.
    payload = H.save_baseline(args.root, findings, note=args.message,
                              prune=args.prune, live=live,
                              admits=getattr(args, "admits", None))
    accepted = payload["accepted"]
    added = sorted(set(accepted) - before)
    print("baseline: %s" % H.baseline_path(args.root))
    print("  %d carried, %d newly accepted" % (len(accepted), len(added)))
    for fid in sorted(accepted):
        mark = "+" if fid in added else " "
        why = (accepted[fid].get("why") or "").strip()
        print("  %s %s" % (mark, fid))
        if why:
            print("      %s" % (why[:120] + ("..." if len(why) > 120 else "")))
    for fid in payload.get("dropped", []):
        print("  - %s  (pruned: no longer in the graph)" % fid)
    if not args.message and added:
        print("\n(no -m given.  A baseline entry without a reason is a warning "
              "someone decided to stop reading.)")
    return 0


def cmd_init(args):
    path = S.graph_path(args.root)
    if os.path.exists(path):
        sys.stderr.write("%s already exists\n" % path)
        return 1
    d = os.path.dirname(path)
    if d and not os.path.isdir(d):
        os.makedirs(d)
    with open(path, "w", encoding="utf-8") as fh:
        fh.write("# Grand Portage graph.  Append-only; merge by concatenation.\n")
    print("initialised %s" % path)
    return 0


def build_parser():
    p = argparse.ArgumentParser(prog="gp", description=__doc__)
    p.add_argument("--root", default=".", help="project root (default: .)")
    p.add_argument("--graph", action="append",
                   help="graph log to read; repeat to MERGE several")
    sub = p.add_subparsers(dest="cmd")

    c = sub.add_parser("check", help="type-check the graph")
    c.add_argument("--json", action="store_true")
    c.add_argument("--quiet", action="store_true")
    c.add_argument("--full", action="store_true",
                   help="print the full detail of CARRIED findings too, not "
                        "just their reason")
    c.add_argument("--floor", default=C.UNSOUND_PREMISE,
                   choices=C.SEVERITY_ORDER,
                   help="lowest severity that fails the run")
    c.set_defaults(func=cmd_check)

    t = sub.add_parser("table", help="print the transport table")
    t.set_defaults(func=cmd_table)

    s = sub.add_parser("show", help="print the graph")
    s.set_defaults(func=cmd_show)

    a = sub.add_parser("accept",
                       help="record findings this campaign knowingly carries")
    a.add_argument("-m", "--message", default="",
                   help="why these are being carried")
    a.add_argument("--only", action="append",
                   help="accept only this finding id (ADDS to the baseline; "
                        "repeat for several)")
    a.add_argument("--prune", action="store_true",
                   help="also DROP accepted findings that no longer appear in "
                        "the graph.  The only way to remove an acceptance.")
    a.add_argument("--admits", action="append",
                   choices=list(DISCHARGE_KINDS),
                   help="pin how this obligation may be discharged: DERIVE "
                        "(supply the missing mathematics), RETYPE (the "
                        "relation was mis-stated), ACCEPT.  Repeat to allow "
                        "several.  A supersession offering any other kind is "
                        "refused and the obligation stays live -- which is how "
                        "'discharge by deriving, not by naming a relaxation' "
                        "stops being prose.")
    a.set_defaults(func=cmd_accept)

    m = sub.add_parser("merge",
                       help="fold several branch logs and report every conflict")
    m.set_defaults(func=cmd_merge)

    g = sub.add_parser("migrate",
                       help="fill required fields a graph predates, with the "
                            "value that says nobody vouched")
    g.add_argument("--dry-run", action="store_true",
                   help="report what would change and write nothing")
    g.set_defaults(func=cmd_migrate)

    g = sub.add_parser("docs",
                       help="rewrite the machine-computable numbers in the "
                            "documentation, so a document quoting the suite "
                            "cannot drift from the suite")
    g.add_argument("--count", type=int, default=None,
                   help="use this count instead of collecting the suite")
    g.set_defaults(func=cmd_docs)

    g = sub.add_parser("why",
                       help="explain a transport cell: what the type means, "
                            "what it licenses, and what would close a refusal")
    g.add_argument("type", help="an edge type, e.g. RESTRICTION")
    g.add_argument("direction", nargs="?", choices=list(K.DIRECTIONS),
                   default=None)
    g.add_argument("kind", nargs="?", choices=list(K.CLAIM_KINDS), default=None)
    g.set_defaults(func=cmd_why)

    g = sub.add_parser("history",
                       help="where the campaign struggled: supersession "
                            "chains, and the obligations still carried")
    g.set_defaults(func=cmd_history)

    i = sub.add_parser("init", help="create an empty graph")
    i.set_defaults(func=cmd_init)
    return p


def main(argv=None):
    args = build_parser().parse_args(argv)
    if not getattr(args, "func", None):
        build_parser().print_help()
        return 2
    return args.func(args)


if __name__ == "__main__":
    sys.exit(main())
