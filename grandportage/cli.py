"""`gp` -- the command line.

Deterministic, read-only by default, exits nonzero when the graph licenses a
conclusion it should not.  No model in the loop: everything here is a fold and
a table lookup.
"""

import argparse
import json
import os
import sys

from . import check as C
from . import hook as H
from . import kernel as K
from . import store as S
from .discharge import DISCHARGE_KINDS, KNOWN_CONSERVATISM, KNOWN_UNSOUND


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
    changed, manual, downgraded = [], [], []
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
            for (kind, field), (value, applies) in sorted(fills.items()):
                if ev.get("ev") == kind and applies(ev) and not ev.get(field):
                    ev[field] = value
                    changed.append((path, n, ev.get("id"), field, value))
            if ev.get("ev") == "claim" and ev.get("ladder") \
                    and ev["ladder"] not in K.LADDER:
                manual.append((path, n, ev.get("id"), ev["ladder"]))
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
        print("\n%d field(s) NEED A HUMAN -- the value is wrong, not missing, "
              "and only you know where it belongs:" % len(manual))
        for p, n, cid, val in manual:
            print("  %s:%d  %s  ladder=%r" % (p, n, cid, val[:60]))
        print("  `ladder` is a strength ordering (%s). How you came to believe "
              "it is `established_by`; a limitation is `caveat`."
              % ", ".join(K.LADDER))
    return 1 if manual else 0


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
    findings = C.run(g)
    before = H.load_baseline(args.root)
    if args.only:
        unknown = sorted(set(args.only) - {f.fid for f in findings})
        if unknown:
            sys.stderr.write("no such finding: %s\nrun `gp check` for the "
                             "current ids\n" % ", ".join(unknown))
            return 2
        findings = [f for f in findings if f.fid in set(args.only)]
    payload = H.save_baseline(args.root, findings, note=args.message,
                              prune=args.prune,
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
