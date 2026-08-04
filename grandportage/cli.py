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

from . import __version__
from . import artifacts as A
from . import cas
from . import check as C
from . import coefficient_expansion as CE
from . import evidence as EV
from . import factor_power as FP
from . import factor_power_contradiction as FPC
from . import frontier as FRONT
from . import frontier_bundle as FRONT_BUNDLE
from . import format as F
from . import laurent_coefficient_pipeline as LCP
from . import laurent_lowering as LL
from . import hook as H
from . import localization as L
from . import kernel as K
from . import migration as MIG
from . import provenance as P
from . import product_split as PS
from . import projection as PROJ
from . import store as S
from . import triangular as TRI
from . import visualization as VIZ
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
        return C.exit_code(findings, args.floor, accepted)

    if not args.quiet:
        print("graph: %d models, %d edges, %d claims, %d inferences"
              % (len(g.models), len(g.edges), len(g.claims),
                 len(g.inference_order)))
        # HOW MUCH OF THIS GRAPH IS CHECKABLE AT ALL -- a HEADER LINE and
        # deliberately not a finding.
        #
        # Measured before choosing: reporting one finding per model with an
        # algebraic obligation and no algebra produces 103 findings across the
        # live campaigns and the two retrodiction fixtures, roughly doubling
        # every campaign's count. The fixtures' gate asserts its clean sets
        # EXACTLY, on the grounds that "a framework that flags a sound step is
        # a false-positive generator and unusable", and recording a model
        # without equations is not a defect -- most models legitimately have
        # none.
        #
        # But the fact is real and it is the one that explains why eleven of
        # fifteen live certificates come back UNVERIFIED. A reader planning a
        # campaign needs it ONCE, not per object. So it goes where the count
        # of models already goes.
        blind = sum(1 for m in g.models.values()
                    if m.get("generators") is None and not m.get("ideal_pending"))
        if blind:
            print("       %d of them record no ideal, so nothing algebraic can "
                  "be checked there" % blind)
            print("       (`generators: []` says a model imposes no equations; "
                  "omitting it says nobody wrote them down)")
        # IS ANYTHING ENFORCING THIS?
        #
        # A whole live session ran with the hook inert and nothing said so. Its
        # root came from the session's cwd and only matched when that was
        # exactly the campaign root, so enforcement silently did not happen --
        # and the run passed, covering the verifiers and the checker while
        # saying nothing about the layer HANDOFF calls the difference between
        # this tool and telemetry.
        #
        # A SILENT ENFORCEMENT LAYER IS INDISTINGUISHABLE FROM A SATISFIED ONE.
        # That is the defect, more than the path resolution: the absence was
        # discoverable only by hunting for a marker file that was never
        # written. One line here makes it visible to anyone who runs `check`.
        if not _hook_definition_found(args.root):
            print("       NO HOOK DEFINITION FOUND for this root -- these "
                  "findings are ADVISORY.")
            print("       Nothing visible here refuses a tool call on them. "
                  "`gp why hook` explains wiring it.")
        else:
            print("       HOOK DEFINITION FOUND, but a file cannot prove that "
                  "it is enabled or trusted.")
            print("       Codex authors must confirm it is active in `/hooks`; "
                  "a live gate must provoke a refusal before relying on it.")
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
        # THE THIRD CATEGORY, and it used to be invisible.  An inference whose
        # EDGE is flagged is not clean and is not in the findings either --
        # the finding names the edge.  A live campaign lost a true,
        # correctly-typed inference that way and said the right thing about
        # it: not refused, silently absent.
        held = C.disqualified_inferences(g, findings)
        if held:
            print("not clean, not refused (%d) -- each rests on something "
                  "flagged above:" % len(held))
            for iid, why in held:
                print("    %-24s rests on %s" % (iid, ", ".join(why)))
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
    return C.exit_code(findings, args.floor, accepted)


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
    if (getattr(args, "to_current_kernel", False)
            or getattr(args, "to_kernel2", False)):
        reports = MIG.migrate_kernel_epoch(
            _graphs(args), dry_run=args.dry_run,
            output=getattr(args, "kernel_output", None))
        for report in reports:
            print("%s -> %s" % (report["source"], report["destination"]))
            print("  source %s" % report["source_sha256"])
            print("  audit  %s" % report["audit"])
            print("  kernel %d -> %d%s"
                  % (report["from_kernel_epoch"], report["kernel_epoch"],
                     " (DRY RUN)" if report["dry_run"] else ""))
        return 0
    if getattr(args, "to_epoch1", False):
        reports = MIG.migrate_epoch1(
            _graphs(args), dry_run=args.dry_run,
            output=getattr(args, "epoch1_output", None))
        for report in reports:
            print("%s -> %s" % (report["source"], report["destination"]))
            print("  source %s" % report["source_sha256"])
            print("  audit  %s" % report["audit"])
            print("  %d event(s), %d changed record(s)%s"
                  % (report["events"], len(report["changes"]),
                     " (DRY RUN)" if report["dry_run"] else ""))
        return 0
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
    prev_records = {}        # (kind, id) -> the record, for computing a kind
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
            # A DISCHARGE KIND THAT WAS NEVER VALIDATED, on the three record
            # kinds supersession did not reach until now.
            #
            # `evidence`, `doubt` and `citation` accepted `supersedes` with no
            # existence check and no kind check, so a live session wrote AMEND
            # on both of its corrections -- and the tool printed "declared 1
            # event(s)" and did nothing. Enforcing supersession for them makes
            # those records refuse, which would leave a campaign unfoldable
            # over a value nobody was ever asked about.
            #
            # SO IT IS CORRECTED RATHER THAN REPORTED, and that is the same
            # principle as every other fill here. A declared kind that nothing
            # validated is not the author's judgement; it is a field they had
            # no way to get right. The tool computes the true kind from the two
            # records anyway, so writing it is not a guess -- and the result is
            # reported, so the graph gets louder rather than quieter.
            if (ev.get("ev") in ("evidence", "doubt", "citation")
                    and ev.get("supersedes")):
                old = prev_records.get((ev["ev"], ev["supersedes"]))
                if old is not None:
                    actual, moved = K.classify_supersession(
                        old, ev, entity=ev["ev"])
                    if ev.get("discharge_kind") != actual:
                        was = ev.get("discharge_kind")
                        ev["discharge_kind"] = actual
                        changed.append(
                            (path, n, ev.get("id"), "discharge_kind",
                             "%s (was %s; %s changed)"
                             % (actual, was, ", ".join(moved) or "nothing")))
            prev_records[(ev.get("ev"), ev.get("id"))] = dict(ev)
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


def _declare_epilog():
    """The event kinds and their required fields, derived where possible.

    Written out because a live session had to read `store.py`'s `_apply_*`
    methods to learn what an `evidence` record needs. Vocabularies come from
    the modules that own them, so this cannot drift from the validation the
    way a hand-kept list would.
    """
    return (
        "event kinds and their REQUIRED fields (all take `id` except note,\n"
        "built_by and erratum):\n"
        "\n"
        "  model       what\n"
        "  edge        src, dst, type, why\n"
        "  claim       model|family, kind, statement\n"
        "  inference   claim|premises, concludes_kind, asserted\n"
        "  partition   parent, branches, exhaustive\n"
        "  family      count, enumeration\n"
        "  same_as     models, why\n"
        "  built_by    model, inference\n"
        "  evidence    for, method, ran, what   (+ agrees_with if REPLICATION)\n"
        "  doubt       about, kind, why         (+ severity, default TRIAGE)\n"
        "  citation    cites, resolves_to, why  (+ hazard)\n"
        "  erratum     voids, why               (only for a record that will\n"
        "                                        not fold; supersede one that\n"
        "                                        does)\n"
        "  verdict     WRITTEN BY `gp verify`, never declared. Reading one in\n"
        "              the raw log: `subject` is the VERIFIER (ring_iso,\n"
        "              witness, partition...) and `of` is the OBJECT it ran on\n"
        "              (E-INV2, CL-PT...). Those read backwards and are kept\n"
        "              because renaming them would break every graph that has\n"
        "              one. `gp events --folded` shows the verdicts already\n"
        "              attached to their objects, which is the easier view.\n"
        "  note        text -- untyped prose, invisible to every rule\n"
        "\n"
        # `premises` SHAPE, because the refusal was one field-name short of
        # being self-service. "premise 0 must be an object" is correct and says
        # nothing about what the object needs; the shape lived in a docstring
        # at store.py.
        "an inference takes ONE claim or a LIST OF PREMISES:\n"
        "  \"claim\": \"C1\", \"path\": [[\"E1\", \"AGAINST\"]]\n"
        "  \"premises\": [{\"claim\": \"C1\", \"path\": [[\"E1\",\"AGAINST\"]]},\n"
        "                {\"claim\": \"C2\", \"path\": []}]\n"
        "a path is a list of [edge_id, ALONG|AGAINST] steps, and [] means the\n"
        "premise is used where it already sits.\n"
        "\n"
        # THE FIELDS THAT REACH `operation_output`, which appeared in NO
        # markdown file in the repo and in no help text. A live session found
        # them by reading verify.py and operations.py.
        "to have a CONSTRUCTED model's ideal checked against the operation\n"
        "that produced it, the edge carries `built_by_operation`\n"
        "(SaturateClosure or Eliminate) and a saturated model carries\n"
        "`saturated_at`. `gp construct` writes both for you.\n"
        "\n"
        "a mapped EQUIVALENCE uses the exact fields `forward` and `inverse`:\n"
        "  \"forward\": {\"x\": \"-x\", \"y\": \"y\"},\n"
        "  \"inverse\": {\"x\": \"-x\", \"y\": \"y\"}\n"
        "`forward` is the point map from source to target; polynomial pullback\n"
        "is contravariant. Both maps are simultaneous substitutions with one\n"
        "expression per ring variable. The current verifier requires the same\n"
        "ring-variable names at both endpoints. `gp verify` checks both ideal\n"
        "pullbacks and both inverse compositions; structured maps license\n"
        "transport only after `VERIFIED`. This does NOT also assert literal\n"
        "containment in the written coordinates. Structured conditions also\n"
        "rewrite through VERIFIED mapped equivalences: ALONG uses inverse and\n"
        "AGAINST uses forward before later operation contracts inspect them.\n"
        "Ordinary AGAINST pullback also preserves structured syntax through a\n"
        "matching exact identity map or a checked Eliminate projection.\n"
        "The spellings `maps` and `inverse_maps` are refused as inert aliases.\n"
        "\n"
        "vocabularies:\n"
        "  edge type        %s\n"
        "  claim kind       %s\n"
        "  map_kind         %s\n"
        "  identity_origin  %s\n"
        "  witness_kind     %s\n"
        "  ladder           %s\n"
        "  discharge_kind   %s   (claims, inferences)\n"
        "                   %s   (edges -- a DISJOINT set)\n"
        "  evidence method  %s\n"
        "  doubt kind       %s\n"
        "  doubt severity   %s\n"
        "  established_by   %s\n"
        "\n"
        "to CHANGE something already declared, do not redeclare it -- send the\n"
        "new version with `supersedes` and a `discharge_kind`. `gp why\n"
        "supersession` explains the four kinds. This works for EVERY record\n"
        "kind above, evidence and doubts and citations included, so `answered`\n"
        "and `decides` are reachable for a record already in the log.\n"
        "A RETRACT or WITHDRAW tombstone also requires `why`: it records why\n"
        "nothing replaces the old object. It is sparse lifecycle history, not\n"
        "a new full-shaped claim, inference, or edge.\n"
        "\n"
        "a NONEMPTY claim can HAND OVER ITS POINT instead of describing it:\n"
        "  witness_kind: EXHIBITED   you hold the point\n"
        "  witness_point: {..}       a value per ring variable, e.g.\n"
        "                            {\"x\": \"3\", \"y\": \"4\"}. `gp verify`\n"
        "                            substitutes it into the model's\n"
        "                            generators -- the cheapest check here,\n"
        "                            and the only one with no interpretation\n"
        "                            to argue about\n"
        "  witness: '..'             prose. legal, unchecked, often the more\n"
        "                            readable record. keep both\n"
        "an EMPTY claim must name a `certificate` or the graph will not fold.\n"
        "a NONEMPTY claim is where you may LITERALLY HOLD THE OBJECT, and\n"
        "without `witness_point` a fabricated point types identically to a\n"
        "real one.\n"
        "\n"
        "a model's ALGEBRA is optional, and there are THREE states, not two:\n"
        "  generators: [..]      the ideal, known. reduction can proceed\n"
        "  generators: []        the AMBIENT SPACE. imposes no equations, and\n"
        "                        an identity there is AMBIENT by construction\n"
        "  ideal_pending: '..'   the ideal is COMPUTED and has not been\n"
        "                        computed yet -- a saturation, an elimination.\n"
        "                        say what will fill it. `gp verify` refuses\n"
        "                        the question rather than answering it in the\n"
        "                        wrong ring, and `gp check` reports the model\n"
        "                        as blocking whatever rests on it.\n"
        "  (omitted entirely)    no algebra recorded. most models\n"
        "declaring `generators` and `ideal_pending` together is refused: an\n"
        "ideal is either known or waiting. record the generators with a RELICENSE\n"
        "once the computation has run.\n"
        "\n"
        "two things that have cost people real time:\n"
        "  * in PowerShell `gp` is a built-in alias for Get-ItemProperty, and\n"
        "    the alias WINS -- a wrapper function cannot shadow it. Use\n"
        "    `gport`, which is the same command under a name that shell has\n"
        "    not taken. (`gp.exe` and `python -m grandportage.cli` also work.)\n"
        "    Everywhere else -- cmd, bash, zsh -- plain `gp` is fine.\n"
        "  * DO NOT PARSE .portage/graph.jsonl BY HAND -- use `gp events`,\n"
        "    which dumps the raw log as JSON, or `gp events --folded` for the\n"
        "    graph as the tool sees it. Some graphs created before v0.4.2\n"
        "    open with a `#` comment line, which is not JSONL and which a\n"
        "    naive json.loads per line chokes on; `load_events` skips it and\n"
        "    always will, so old graphs keep working. Epoch-1 graphs start\n"
        "    with a machine-readable `meta` event, followed by the note.\n"
        % (", ".join(K.DECLARABLE_TYPES),
           ", ".join(K.CLAIM_KINDS),
           ", ".join(K.MAP_KINDS),
           ", ".join(K.IDENTITY_ORIGINS),
           ", ".join(K.WITNESS_KINDS),
           ", ".join(K.LADDER),
           ", ".join(K.SUPERSESSION_KINDS),
           ", ".join(DISCHARGE_KINDS),
           ", ".join(S.Graph.EVIDENCE_METHODS),
           ", ".join(S.Graph.DOUBT_KINDS),
           ", ".join(S.C_SEVERITIES),
           ", ".join(K.ESTABLISHED_BY)))


def cmd_declare(args):
    """Write events to the graph, transactionally.

    THE ROOT CAUSE OF THE WORST DEFECT THIS PROJECT HAS RECORDED, and it was a
    missing command rather than a broken one.

    `store.append` is transactional: it folds the batch against the existing
    graph first and writes nothing if the result would not fold.  So the
    supported write path CANNOT poison a graph.  But the only supported write
    path was the MCP server, and two consecutive live sessions reported it
    unreachable -- at which point a careful agent's only remaining option was
    to append JSONL by hand, bypassing the one guard that would have caught its
    typo.

    One of them did exactly that, wrote `supersession_kind` for
    `discharge_kind`, and spent the rest of the session unable to run `gp
    check`.  The unrecoverable graph error was the second-order consequence;
    every write in the system going through a single point of failure was the
    cause.

    Reads JSON from a file or stdin, accepting either one event object or a
    list of them.
    """
    # A READ may merge repeated `--graph` inputs. A write has exactly one
    # destination. Refuse ambiguity before reading stdin so a malformed target
    # cannot leave an interactive caller waiting for a payload we will not use.
    if args.graph and len(args.graph) != 1:
        sys.stderr.write(
            "declare needs exactly one write target; repeated --graph is "
            "read/merge syntax.\n  Nothing was written.\n")
        return 2
    target = args.graph[0] if args.graph else None

    # `--file -` MEANS STDIN, because it means that everywhere else. Without
    # it this raised a bare FileNotFoundError naming a file called "-", which
    # tells a reader the path is wrong rather than that the idiom is
    # unsupported.
    if args.file and args.file != "-":
        with open(args.file, encoding="utf-8") as fh:
            raw = fh.read()
    else:
        raw = sys.stdin.read()
    if not raw.strip():
        sys.stderr.write(
            "nothing to declare: no events on stdin and no --file given.\n"
            "  Send one event object or a list of them, e.g.\n"
            "    gp declare --file events.json\n"
            "    echo '{\"ev\":\"note\",\"text\":\"...\"}' | gp declare\n")
        return 2
    # A BOM IS NOT A SYNTAX ERROR, it is a Windows editor being helpful.
    # `Set-Content -Encoding utf8` in Windows PowerShell 5.1 writes one, and
    # this refused the file with "Unexpected UTF-8 BOM" -- a message that
    # diagnoses the problem perfectly and still costs a minute nobody needed
    # to spend, since the fix is one strip.
    raw = raw.lstrip("﻿")
    try:
        events = json.loads(raw)
    except ValueError as exc:
        sys.stderr.write(
            "that is not JSON: %s\n"
            "  Nothing was written. The graph is unchanged.\n" % exc)
        return 2
    if isinstance(events, dict):
        events = [events]
    if not isinstance(events, list):
        sys.stderr.write(
            "expected one event object or a list of them, got %s.\n"
            % type(events).__name__)
        return 2
    try:
        S.append(events, args.root, graph=target)
    except (S.GraphError, K.KernelRefusal) as exc:
        # THE WHOLE POINT: refused and NOTHING WRITTEN, so the next attempt
        # starts from a graph that still folds.
        sys.stderr.write("REFUSED\n  %s\n\n"
                         "  Nothing was written. The graph is unchanged.\n"
                         % exc)
        return 2
    where = os.path.abspath(target or S.graph_path(args.root))
    print("declared %d event(s) to %s." % (len(events), where))
    return 0


def cmd_verify(args):
    """Run the verifiers and record what they found.

    THIS COMMAND DID NOT EXIST FOR TWO RELEASES.  `verify.py` shipped with both
    halves working, `check` printed "run `gp verify`" in two rules, and the
    module's own docstring said "`gp verify` will run it" -- while the whole
    module was unreachable from every user surface.  A live session had to
    import it from Python to use it.

    The suite did not notice because GATE 2 enumerates the surfaces that EXIST
    and asserts each survives every fixture.  Nothing asked whether a
    capability had a surface at all, which is a different question and the one
    that was wrong here.
    """
    from . import verify as V
    try:
        results = V.verify_all(root=args.root, timeout=args.timeout,
                               record=not args.dry_run)
    except (A.ArtifactError, OSError) as exc:
        sys.stderr.write(
            "ARTIFACT PERSISTENCE FAILED\n  %s\n\n"
            "  No verdict was appended. The graph is unchanged.\n" % exc)
        return 2
    if not results:
        print("nothing to verify: no edge or claim carries the data a "
              "reduction needs.\n"
              "  Edges need `generators` and `ring_vars` on BOTH endpoints; "
              "IDENTITY claims need `lhs`, `rhs` and `ring_vars`.\n"
              "  A model carrying `ideal_pending` has none of this yet by "
              "design -- it is waiting on the computation that produces its "
              "ideal.\n"
              "  `gp check` reports which ones are missing them.")
        return 0
    bad = 0
    for subject, oid, verdict, why in results:
        print("%-16s %-8s %s" % (verdict, subject, oid))
        for line in why.splitlines():
            print("    " + line)
        print()
        if verdict in (V.REFUTED, V.NOT_BY_IDEAL):
            bad += 1
    if args.dry_run:
        print("--dry-run: nothing was recorded.")
    else:
        print("recorded %d verdict(s); `gp history` shows them." % len(results))
    # A refutation is a finding, not a crash: exit non-zero so a hook or a CI
    # step can act on it, but say so plainly rather than raising.
    return 1 if bad else 0


def cmd_verify_elimination(args):
    """Check one explicit polynomial section for an elimination edge."""
    from . import verify as V
    try:
        section = json.loads(args.section)
    except (TypeError, ValueError) as exc:
        sys.stderr.write("invalid --section JSON: %s\n" % exc)
        return 2
    if not isinstance(section, dict):
        sys.stderr.write("--section must decode to an object\n")
        return 2
    try:
        verdict, why, _representation = V.verify_elimination_section(
            args.root, args.edge, section, timeout=args.timeout,
            record=not args.dry_run)
    except (A.ArtifactError, OSError, S.GraphError, ValueError) as exc:
        sys.stderr.write("ELIMINATION VERIFICATION FAILED\n  %s\n" % exc)
        return 2
    print("%-20s elimination %s" % (verdict, args.edge))
    for line in why.splitlines():
        print("    " + line)
    if args.dry_run:
        print("\n--dry-run: nothing was recorded.")
    else:
        print("\nrecorded verifier verdict; `gp history` shows the diagnostic.")
    return 0 if verdict == V.SECTION_VERIFIED else 1

def cmd_verify_elimination_point_lift(args):
    """Check a finite rational-chart point-lift cover."""
    from . import verify as V
    try:
        certificate = json.loads(args.certificate)
    except (TypeError, ValueError) as exc:
        sys.stderr.write("invalid --certificate JSON: %s\n" % exc)
        return 2
    if not isinstance(certificate, dict):
        sys.stderr.write("--certificate must decode to an object\n")
        return 2
    try:
        verdict, why, _representation = V.verify_elimination_point_lift(
            args.root, args.edge, certificate, timeout=args.timeout,
            record=not args.dry_run)
    except (A.ArtifactError, OSError, S.GraphError, ValueError) as exc:
        sys.stderr.write("POINT-LIFT VERIFICATION FAILED\n  %s\n" % exc)
        return 2
    print("%-20s point lift %s" % (verdict, args.edge))
    for line in why.splitlines():
        print("    " + line)
    if args.dry_run:
        print("\n--dry-run: nothing was recorded.")
    else:
        print("\nrecorded checked point-lift cover; `gp history` shows it.")
    return 0 if verdict == V.POINT_LIFT_VERIFIED else 1

def cmd_verify_elimination_groebner(args):
    """Produce and certify exact contraction through a pure-lex proof."""
    from . import verify as V
    try:
        verdict, why, _representation = V.verify_elimination_groebner(
            args.root, args.edge, timeout=args.timeout,
            record=not args.dry_run)
    except (A.ArtifactError, OSError, S.GraphError, ValueError) as exc:
        sys.stderr.write("GROEBNER VERIFICATION FAILED\n  %s\n" % exc)
        return 2
    print("%-20s elimination %s" % (verdict, args.edge))
    for line in why.splitlines():
        print("    " + line)
    if args.dry_run:
        print("\n--dry-run: nothing was recorded.")
    else:
        print("\nrecorded checked proof and producer provenance; "
              "`gp history` shows the verdict.")
    return 0 if verdict == V.GROEBNER_VERIFIED else 1


def cmd_verify_coefficient_expansion(args):
    """Translation-validate polynomial identities lowered to coefficients."""
    try:
        with open(args.spec, "r", encoding="utf-8") as handle:
            spec = json.load(handle)
        report = CE.verify(spec)
    except (OSError, ValueError, json.JSONDecodeError,
            CE.CoefficientExpansionError) as exc:
        sys.stderr.write("COEFFICIENT EXPANSION FAILED\n  %s\n" % exc)
        return 2
    if args.json:
        print(json.dumps(report, indent=2, sort_keys=True))
    else:
        print(report["verdict"])
        print("    %d polynomial equation(s), %d scalar coordinate(s)" % (
            len(report["equations"]),
            len(report["coefficient_variables"]),
        ))
        if report["verdict"] == CE.VERIFIED_COMPLETE:
            print("    authority: polynomial identity iff every recorded "
                  "coefficient row vanishes")
        else:
            print("    authority: polynomial identity implies the selected "
                  "coefficient rows vanish; no converse")
        print("    spec sha256: %s" % report["spec_fingerprint"])
    return 0


def cmd_verify_laurent_lowering(args):
    """Translation-validate a finite exact Laurent straight-line program."""
    try:
        with open(args.spec, "r", encoding="utf-8") as handle:
            spec = json.load(handle)
        report = LL.verify(spec)
    except (OSError, ValueError, json.JSONDecodeError,
            LL.LaurentLoweringError) as exc:
        sys.stderr.write("LAURENT LOWERING FAILED\n  %s\n" % exc)
        return 2
    if args.json:
        print(json.dumps(report, indent=2, sort_keys=True))
    else:
        print(report["verdict"])
        print("    %d arithmetic node(s), %d exact equality check(s), "
              "%d polynomial export(s)" % (
                  len(report["program"]), len(report["equalities"]),
                  len(report["exports"]),
              ))
        print("    authority: exact finite Laurent arithmetic only; "
              "no chart validity, integration, or claim transport")
        print("    spec sha256: %s" % report["spec_fingerprint"])
    return 0


def cmd_verify_laurent_coefficient_pipeline(args):
    """Verify and bind Laurent lowering to coefficient expansion."""
    try:
        with open(args.spec, "r", encoding="utf-8") as handle:
            spec = json.load(handle)
        report = LCP.verify(spec)
    except (OSError, ValueError, json.JSONDecodeError,
            LCP.LaurentCoefficientPipelineError) as exc:
        sys.stderr.write("LAURENT/COEFFICIENT PIPELINE FAILED\n  %s\n" % exc)
        return 2
    if args.json:
        print(json.dumps(report, indent=2, sort_keys=True))
    else:
        print(report["verdict"])
        print("    %d exact export-to-image binding(s)" %
              len(report["bindings"]))
        print("    downstream: %s" %
              report["coefficient_report"]["verdict"])
        print("    authority: exact compiler-pass composition only; "
              "no source derivation, chart validity, or claim transport")
        print("    spec sha256: %s" % report["spec_fingerprint"])
    return 0

def cmd_verify_factor_power(args):
    """Translation-validate exact unit-times-positive-power identities."""
    try:
        with open(args.spec, "r", encoding="utf-8") as handle:
            spec = json.load(handle)
        report = FP.verify(spec)
    except (OSError, ValueError, json.JSONDecodeError,
            FP.FactorPowerError) as exc:
        sys.stderr.write("FACTOR POWER FAILED\n  %s\n" % exc)
        return 2
    if args.json:
        print(json.dumps(report, indent=2, sort_keys=True))
    else:
        print(report["verdict"])
        print("    %d exact unit-times-positive-power receipt(s)" %
              len(report["receipts"]))
        print("    authority: factor identity only; no base-vanishing, "
              "emptiness, or claim transport")
        print("    open obligations: target equation vanishing, "
              "no zero divisors, and interpreted coefficient/generator units")
        print("    spec sha256: %s" % report["spec_fingerprint"])
    return 0

def cmd_verify_factor_power_contradiction(args):
    """Compose a factor receipt with an exact affine unit contradiction."""
    try:
        with open(args.spec, "r", encoding="utf-8") as handle:
            spec = json.load(handle)
        report = FPC.verify(spec)
    except (OSError, ValueError, json.JSONDecodeError,
            FPC.FactorPowerContradictionError) as exc:
        sys.stderr.write("FACTOR POWER CONTRADICTION FAILED\n  %s\n" % exc)
        return 2
    if args.json:
        print(json.dumps(report, indent=2, sort_keys=True))
    else:
        print(report["verdict"])
        print("    factor: %s" % report["factor_receipt"])
        print("    consequence: %s -> %s" % (
            report["consequence"]["id"],
            report["consequence"]["residual"],
        ))
        print("    authority: exact contradiction pattern only; "
              "no model binding, emptiness, or claim transport")
        print("    spec sha256: %s" % report["spec_fingerprint"])
    return 0

def cmd_verify_product_split(args):
    """Translation-validate exact binary product-split identities."""
    try:
        with open(args.spec, "r", encoding="utf-8") as handle:
            spec = json.load(handle)
        report = PS.verify(spec)
    except (OSError, ValueError, json.JSONDecodeError,
            PS.ProductSplitError) as exc:
        sys.stderr.write("PRODUCT SPLIT FAILED\n  %s\n" % exc)
        return 2
    if args.json:
        print(json.dumps(report, indent=2, sort_keys=True))
    else:
        print(report["verdict"])
        print("    %d exact binary product receipt(s)" %
              len(report["receipts"]))
        print("    authority: product identity only; no factor disjunction, "
              "branch creation, coverage, emptiness, or claim transport")
        print("    spec sha256: %s" % report["spec_fingerprint"])
    return 0

def cmd_verify_localization_membership(args):
    """Check one exact identity in a declared principal-open localization."""
    try:
        with open(args.spec, "r", encoding="utf-8") as handle:
            spec = json.load(handle)
        report = L.verify(spec)
    except (OSError, ValueError, json.JSONDecodeError,
            L.LocalizationError) as exc:
        sys.stderr.write("LOCALIZATION MEMBERSHIP FAILED\n  %s\n" % exc)
        return 2
    if args.json:
        print(json.dumps(report, indent=2, sort_keys=True))
    else:
        print(report["verdict"])
        normalized = report["normalized"]
        print("    guards: %s" % ", ".join(normalized["guards"]))
        print("    expression numerator: %s" %
              normalized["expression"]["numerator"])
        print("    authority: identity in the declared localization only; "
              "no ambient identity or point transport")
        print("    spec sha256: %s" % report["spec_fingerprint"])
    return 0


def cmd_verify_localized_triangular_chain(args):
    """Check an ordered chain of exact localized affine substitutions."""
    try:
        with open(args.spec, "r", encoding="utf-8") as handle:
            spec = json.load(handle)
        report = TRI.verify(spec)
    except (OSError, ValueError, json.JSONDecodeError,
            TRI.TriangularChainError) as exc:
        sys.stderr.write("LOCALIZED TRIANGULAR CHAIN FAILED\n  %s\n" % exc)
        return 2
    if args.json:
        print(json.dumps(report, indent=2, sort_keys=True))
    else:
        print(report["verdict"])
        print("    %d exact ordered solve step(s)" % report["checked_steps"])
        if report["normalization_generators"]:
            print("    normalization generators: %d" %
                  len(report["normalization_generators"]))
        print("    final state: %s" % report["final_state_fingerprint"])
        print("    authority: standalone translation validation only; "
              "no graph equivalence, emptiness, coverage, source, or H3 claim")
        print("    spec sha256: %s" % report["spec_fingerprint"])
    return 0


def cmd_materialize_elimination_groebner(args):
    """Discover, certify, and declare one elimination target as one batch."""
    from . import verify as V
    eliminated = [value.strip() for value in args.vars.split(",")]
    if not all(eliminated):
        sys.stderr.write("--vars must be a nonempty comma-separated list\n")
        return 2
    try:
        result = V.materialize_elimination_groebner(
            args.root, args.src, eliminated, args.produces,
            timeout=args.timeout, record=not args.dry_run,
        )
    except (A.ArtifactError, cas.CASError, K.KernelRefusal, OSError,
            S.GraphError, ValueError) as exc:
        sys.stderr.write("GROEBNER MATERIALIZATION FAILED\n  %s\n" % exc)
        return 2
    print("%-20s elimination %s" % (
        result["contraction_verdict"], result["edge"]
    ))
    print("    target %s: %d retained pure-lex generator(s)" % (
        result["model"], len(result["generators"])
    ))
    print("    operation output: %s" % result["operation_verdict"])
    if args.dry_run:
        print("\n--dry-run: model, edge, verdicts, and artifacts were not recorded.")
    else:
        print("\nrecorded model, constructor edge, both checked verdicts, and "
              "producer artifacts in one prevalidated graph batch.")
    return 0
def cmd_artifacts_check(args):
    """Audit raw execution objects without making graph folding ambient."""
    if args.graph:
        audits = []
        for path in args.graph:
            absolute = os.path.abspath(path)
            parent = os.path.dirname(absolute)
            artifact_root = (
                os.path.dirname(parent)
                if os.path.basename(parent) == ".portage" else parent)
            audits.append((path, artifact_root, S.load(path)))
    else:
        audits = [(S.graph_path(args.root), args.root, _load(args))]
    problems = []
    for path, artifact_root, graph in audits:
        for problem in A.audit_graph(artifact_root, graph):
            problems.append(
                "%s: %s" % (path, problem) if len(audits) > 1 else problem)
    if problems:
        sys.stderr.write(
            "ARTIFACT AUDIT FAILED (%d problem%s)\n"
            % (len(problems), "" if len(problems) == 1 else "s"))
        for problem in problems:
            sys.stderr.write("  %s\n" % problem)
        return 1
    references = 0
    for _path, _artifact_root, graph in audits:
        for event in graph.verdicts.values():
            manifest = P.backend_provenance(
                event.get("backend"), current_only=False)
            if manifest is not None and manifest.get("schema") == 2:
                references += len(manifest["executions"])
        for note in graph.notes:
            try:
                if A.note_reference(note.get("source")) is not None:
                    references += 1
            except A.ArtifactError:
                pass
    print("artifact audit clean: %d execution reference%s checked."
          % (references, "" if references == 1 else "s"))
    return 0


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
    # THE TALLY COUNTED FOUR KINDS OUT OF TWELVE.  A live session wrote six
    # events -- a claim, two evidence records, two doubts and a citation --
    # and watched this number move by one.  A count that silently omits most
    # of what you just wrote is worse than no count: it reads as confirmation
    # that little happened.
    kinds = [ev.get("ev") for _p, _n, ev in events]
    said = ", ".join("%d %s" % (kinds.count(w), w)
                     for w in ("evidence", "doubt", "citation", "verdict",
                               "erratum")
                     if kinds.count(w))
    print("%d model(s)/edge(s)/claim(s)/inference(s)%s declared across %d log "
          "line(s); %d note(s) carried and never typed."
          % (len(order), (", " + said) if said else "",
             len(events), len(notes)))
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
    # SUPERSESSION IS A VOCABULARY TOO, and `why` did not know it existed.
    #
    # This command takes EDGE TYPES, and its refusal listed only those -- so
    # someone asking `gp why supersession`, or `gp why IDENTITY`, was told the
    # word was unknown with no hint that the thing they asked about is real and
    # documented somewhere else.  That is the same defect as a message pointing
    # at a command that does not exist: it teaches that the answer is absent
    # when it is merely elsewhere.
    if etype and etype.upper() in K.SUPERSESSION_KINDS:
        print("%s -- a SUPERSESSION kind, which is not a transport question.\n"
              % etype.upper())
        print(K.supersession_help())
        return 0
    if etype and etype.lower() in ("supersession", "supersede", "supersedes"):
        print("SUPERSESSION -- how a record is replaced without erasing what "
              "used it.\n")
        print(K.supersession_help())
        return 0
    # ADDED BECAUSE `gp check` STARTED NAMING IT. A message pointing at a
    # command that does not exist is the exact defect GATE 3 was built for,
    # and I wrote one into the very line reporting that enforcement was
    # missing.
    if etype and etype.lower() == "hook":
        print(
            "THE HOOK -- the layer that makes a finding REFUSE rather than\n"
            "report. Without it this tool is a linter nobody runs, and a\n"
            "silent absence is indistinguishable from a satisfied one: a live\n"
            "session ran to completion with it inert and nothing said so.\n"
            "\n"
            "It runs after each tool call, reads the graph, and blocks when a\n"
            "finding sits at or above the floor. Claude Code receives exit 2\n"
            "and stderr; Codex receives its structured PostToolUse block. Wire\n"
            "the same command into `.claude/settings.json` or\n"
            "`.codex/hooks.json` beside your campaign:\n"
            "\n"
            '  {"hooks": {"PostToolUse": [{"matcher": "*", "hooks": [\n'
            '    {"type": "command",\n'
            '     "command": "python -m grandportage.hook"}]}]}}\n'
            "\n"
            "Codex requires project hook trust; inspect it with `/hooks`, or\n"
            "use `--dangerously-bypass-hook-trust` only after independently\n"
            "vetting this exact local definition.\n"
            "\n"
            "It finds the graph by walking UP from the working directory for\n"
            "a `.portage/`, the way git looks for `.git/`. It does NOT walk\n"
            "down: a directory holding several campaigns has no single graph\n"
            "to check, and picking one would be worse than silence.\n"
            "\n"
            "`gp check` says NO HOOK DEFINITION FOUND when it cannot find one, so\n"
            "the absence is visible without hunting for a marker file.")
        return 0
    if etype not in K.DECLARABLE_TYPES:
        sys.stderr.write(
            "unknown type %r.\n"
            "  edge types    : %s\n"
            "  or ask about  : supersession, or any of %s\n"
            "  claim KINDS (%s) are not asked about here -- they are the "
            "third argument, as in `gp why NECESSARY_CONDITION ALONG "
            "IDENTITY`.\n"
            % (etype, ", ".join(K.DECLARABLE_TYPES),
               ", ".join(K.SUPERSESSION_KINDS), ", ".join(K.CLAIM_KINDS)))
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
VERSION_SPAN = re.compile(
    r"(<!--version-->)([^<]+)(<!--/version-->)")
GRAPH_FORMAT_SPAN = re.compile(
    r"(<!--graph-format-->)(\d+)(<!--/graph-format-->)")
KERNEL_EPOCH_SPAN = re.compile(
    r"(<!--kernel-epoch-->)(\d+)(<!--/kernel-epoch-->)")


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
        new = CHECKS_SPAN.sub(
            lambda mm: mm.group(1) + str(n) + mm.group(3), text)
        new = VERSION_SPAN.sub(
            lambda mm: mm.group(1) + __version__ + mm.group(3), new)
        new = GRAPH_FORMAT_SPAN.sub(
            lambda mm: mm.group(1) + str(F.GRAPH_FORMAT) + mm.group(3), new)
        new = KERNEL_EPOCH_SPAN.sub(
            lambda mm: mm.group(1) + str(F.KERNEL_EPOCH) + mm.group(3), new)
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
    print("  closed_condition    Zariski-closed predicates reach a checked closure")
    print("  exact_image_identity forward identity needs exact contraction")
    print("  closed_exact_image  forward predicate needs either closed+closure or")
    print("                      point lift+structured target expressibility")
    print("                      (after verified rewrites or concrete pullback)")
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


def cmd_evidence(args):
    """Print the shared evidence and authority manifest."""
    manifest = EV.manifest()
    if args.json:
        print(json.dumps(manifest, indent=2, sort_keys=True))
        return 0
    print("STANDALONE EVIDENCE CONTRACTS")
    for contract in EV.EVIDENCE_CONTRACTS:
        print("  %-46s effect=%-11s %s" % (
            contract.schema, contract.standalone_graph_effect,
            contract.maturity))
        print("      compiles to: %s" % contract.compilation_target)
    print()
    print("GRAPH AUTHORITY CONTRACTS")
    for contract in EV.AUTHORITY_CONTRACTS:
        print("  %-34s effect=%s" % (
            contract.verifier, contract.graph_effect))
        print("      representation: %s" % contract.representation)
        print("      binds: %s" % ", ".join(contract.binds))
        print("      containment: %s" % contract.containment)
    return 0


def _wrap(text, width=68):
    import textwrap
    out = []
    for para in str(text).split("\n"):
        out.extend(textwrap.wrap(para, width) or [""])
    return out


def _representation_summary(rep):
    """Describe checked evidence without assuming one certificate layout."""
    method = rep.get("method") or "checked_evidence"
    cofactors = rep.get("cofactors")
    if method == "localized_unit_ideal_v1":
        cofactors = ((rep.get("proof") or {}).get("certificate") or {}).get(
            "cofactors")
    if isinstance(cofactors, list):
        return "rep=%s, %d cofactor(s)" % (method, len(cofactors))
    return "rep=%s" % method


def _generator_summary(value):
    """Render structured exact polynomials without dumping huge certificates."""
    if isinstance(value, str):
        return value
    if (isinstance(value, dict)
            and value.get("schema") == "sparse_polynomial_v1"
            and isinstance(value.get("terms"), list)):
        return "<sparse_polynomial_v1: %d terms>" % len(value["terms"])
    return "<structured polynomial>"


def _ideal_summary(generators, inline_limit=12):
    """Keep a large structured ideal readable without hiding its scale."""
    if not generators:
        return "0"
    rendered = [_generator_summary(value) for value in generators]
    if len(generators) <= inline_limit:
        return "(%s)" % ", ".join(rendered)
    sparse_counts = [
        len(value["terms"])
        for value in generators
        if (isinstance(value, dict)
            and value.get("schema") == "sparse_polynomial_v1"
            and isinstance(value.get("terms"), list))
    ]
    if len(sparse_counts) == len(generators):
        return (
            "<%d sparse generators; %d total terms; %d..%d "
            "terms/generator>"
            % (len(generators), sum(sparse_counts), min(sparse_counts),
               max(sparse_counts)))
    return "<%d generators; %d structured>" % (
        len(generators), sum(not isinstance(value, str)
                             for value in generators))


def cmd_show(args):
    g = _load(args)
    for mid in sorted(g.models):
        m = g.models[mid]
        bits = [b for b in (m.get("chart"),) if b]
        if m.get("coefficient_domain"):
            bits.append("coeff=%s" % m["coefficient_domain"])
        elif m.get("field"):
            bits.append(m["field"])
        if m.get("point_universe"):
            bits.append("points=%s" % m["point_universe"])
        elif m.get("universe"):
            bits.append("universe=%s" % m["universe"])
        # A SUPERSEDED MODEL PRINTED LIKE A LIVE ONE, and the model is the
        # anchor: every claim sits at one and every edge runs between two.
        # `show` marked superseded claims and inferences and left models
        # unmarked, so a live session's corrected model kept printing its
        # wrong sentence with no signal, and the claims still hanging off the
        # old one were not flagged either.
        if m.get("superseded_by"):
            bits.append("[SUPERSEDED by %s]" % S.successors(m))
        print("MODEL %-14s %s" % (mid, " ".join(bits)))
        print("    %s" % m.get("desc", ""))
        # WHAT THE MODEL IS, not only what it was called.  `desc` is a sentence
        # somebody wrote; this is the object.  Printed because a reader
        # resuming a campaign cannot otherwise tell a model built from a real
        # ideal from one asserted into existence with a label.
        if m.get("ring_vars"):
            print("    ring   k[%s]" % ", ".join(m["ring_vars"]))
        if m.get("generators") is not None:
            gens = m["generators"]
            print("    ideal  %s" % _ideal_summary(gens))
        # A MODEL WAITING ON ITS IDEAL MUST NOT LOOK LIKE ONE WITH NO IDEAL.
        # In this listing they were indistinguishable -- both simply had no
        # `ideal` line -- which is the same conflation the store now refuses
        # to let a declaration make.
        if m.get("ideal_pending"):
            print("    ideal  NOT YET COMPUTED -- waiting on %s"
                  % m["ideal_pending"])
    print()
    for eid in sorted(g.edges):
        e = g.edges[eid]
        mark = ("  [WITHDRAWN by %s]" % e["withdrawn_by"]
                if e.get("withdrawn_by") else
                ("  [SUPERSEDED by %s]" % S.successors(e)
                 if e.get("superseded_by") else ""))
        print("EDGE  %-6s %-14s -> %-14s %s%s"
              % (eid, e["src"], e["dst"], e["type"], mark))
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
    # WRITE-ONLY RECORDS ARE NOTES WITH A SCHEMA, which is the sharpest thing
    # a live session said about this layer.  Six typed events went in; `gp
    # show` rendered none of them and `gp history`'s tally moved by one.  The
    # session recorded WHAT it ran and no read command would ever have shown
    # that to the next reader -- the exact failure `gp history` warns about
    # for untyped notes, now reproduced for records the checker validates.
    for vid in sorted(g.evidence):
        v = g.evidence[vid]
        print("EVIDENCE %-13s %-12s for %s" % (vid, v["method"], v["for"]))
        print("    ran: %s" % v["ran"])
        for line in _wrap(v["what"]):
            print("    " + line)
        if v.get("agrees_with"):
            print("    agrees with: %s" % v["agrees_with"])
        if v.get("decides"):
            print("    decides: %s -- %s"
                  % (v["decides"], S.Graph.DECIDES[v["decides"]]))
    for did in sorted(g.doubts):
        d = g.doubts[did]
        mark = "  [ANSWERED]" if d.get("answered") else ""
        print("DOUBT %-16s %-12s about %s%s"
              % (did, d["kind"], d["about"], mark))
        if d.get("quote"):
            for line in _wrap('of: "%s"' % d["quote"]):
                print("    " + line)
        for line in _wrap(d["why"]):
            print("    " + line)
    # NAMED NOTES, and superseded ones marked.  Correcting a note was
    # impossible until it could carry an id; rendering it is what makes the
    # correction visible, which was the point -- an invisible correction to an
    # invisible error is no better than the error.
    for nid in sorted(g.named_notes):
        n = g.named_notes[nid]
        mark = ("  [SUPERSEDED by %s]" % S.successors(n)
                if n.get("superseded_by") else "")
        print("NOTE %-17s%s" % (nid, mark))
        for line in _wrap(n["text"]):
            print("    " + line)
    for kid in sorted(g.citations):
        c = g.citations[kid]
        print("CITATION %-13s %s" % (kid, c["cites"]))
        print("    resolves to: %s" % c["resolves_to"])
        for line in _wrap(c["why"]):
            print("    " + line)
        if c.get("hazard"):
            for line in _wrap("HAZARD: " + c["hazard"]):
                print("    " + line)
        if c.get("corrects"):
            for line in _wrap("CORRECTS THE SOURCE: " + c["corrects"]):
                print("    " + line)
    for cid in sorted(g.claims):
        c = g.claims[cid]
        extra = []
        if c.get("certificate"):
            extra.append("cert=%s" % c["certificate"])
        if c.get("certificate_verdict"):
            extra.append("cert-verdict=%s" % c["certificate_verdict"])
        if c.get("identity_origin"):
            extra.append("origin=%s" % c["identity_origin"])
        # THE REWRITING ITSELF, and whether anybody has checked it.
        #
        # `show` printed `ring_vars` for models and `identity_origin` for
        # claims, and neither side of the actual equation -- so a reader could
        # not tell a structured IDENTITY from a prose one without opening
        # graph.jsonl by hand, which is the thing having a `show` is for.
        # `origin` was visible while the two things it is DERIVED FROM were
        # not.
        if c.get("lhs") is not None:
            extra.append("%s = %s" % (c["lhs"], c["rhs"]))
        if c.get("identity_verdict"):
            extra.append("verdict=%s" % c["identity_verdict"])
        # A VERDICT WITH A REPRESENTATION IS A DIFFERENT KIND OF OBJECT from a
        # verdict without one, and the listing showed them identically. One can
        # be rechecked by expansion; the other is a report of a run.
        if c.get("representation"):
            extra.append(_representation_summary(c["representation"]))
        # THE POINT, AND WHETHER ANYBODY SUBSTITUTED IT -- for exactly the
        # reason `lhs = rhs` is printed two lines up. A reader could not tell a
        # checkable witness from a prose one without opening graph.jsonl.
        if c.get("witness_point"):
            wp = c["witness_point"]
            extra.append("at (%s)" % ", ".join(
                "%s=%s" % (v, wp[v]) for v in sorted(wp)))
        if c.get("witness_verdict"):
            extra.append("witness=%s" % c["witness_verdict"])
        if c.get("established_by"):
            extra.append("by=%s" % c["established_by"])
        if c.get("ladder"):
            extra.append("ladder=%s" % c["ladder"])
        # A WITHDRAWN RECORD THAT LOOKS LIVE is the whole reason supersession
        # exists.  Before it, a reminted claim left its predecessor sitting in
        # the graph, printed identically to everything around it, and the only
        # thing distinguishing the two was a prose note somebody had to read.
        mark = ("  [RETRACTED by %s]" % c["retracted_by"]
                if c.get("retracted_by") else
                ("  [SUPERSEDED by %s]" % S.successors(c)
                 if c.get("superseded_by") else ""))
        # A CLAIM SITS AT A MODEL OR AT A FAMILY.  Printing `c["model"]`
        # unguarded crashed the designated handoff view on the first graph to
        # carry a family -- the same subscript that took down five checker
        # rules, in the one surface a human reads to resume.
        home = c.get("model") or ("family:%s" % c["family"])
        print("CLAIM %-20s %-9s @%-14s scope=%-10s %s%s"
              % (cid, c["kind"], home, c.get("scope"),
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
        mark = ("  [RETRACTED by %s]" % i["retracted_by"]
                if i.get("retracted_by") else
                ("  [SUPERSEDED by %s]" % S.successors(i)
                 if i.get("superseded_by") else ""))
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
    # A FILE CALLED .jsonl HAD BETTER BE JSONL.
    #
    # This wrote `# Grand Portage graph. Append-only; ...` -- a comment, which
    # JSONL does not have. `load_events` skips `#` lines so the tool never
    # noticed, and the trap was DOCUMENTED instead of removed: `gp declare`'s
    # epilog warned that "a naive json.loads per line will not" work.
    #
    # That warning is in `gp declare --help`. A person opening the graph file
    # is not reading `gp declare --help`. A live session wrote a parser,
    # choked on line 1, and diagnosed it correctly in a few seconds -- which is
    # the good case; the bad case is the parser that skips the line silently
    # and reports a graph one record short.
    #
    # The same information as a `note` costs one inert record. Notes are
    # explicitly "untyped prose, invisible to every rule", so nothing downstream
    # changes, and now the header is READABLE BY THE SAME PARSER as everything
    # under it.
    with open(path, "w", encoding="utf-8") as fh:
        fh.write(json.dumps(S.F.meta_event(), sort_keys=True) + "\n")
        fh.write(json.dumps({
            "ev": "note",
            "text": ("Grand Portage graph. Append-only; merge by "
                     "concatenation. Every line is one JSON object -- read it "
                     "with `gp events`, or one json.loads per line.")},
            sort_keys=True) + "\n")
    print("initialised %s" % path)
    return 0


def _json_has_post_tool_hook(text):
    try:
        groups = json.loads(text).get("hooks", {}).get("PostToolUse", [])
    except (AttributeError, TypeError, ValueError):
        return False
    return any(
        "grandportage.hook" in str(handler.get("command", ""))
        for group in groups if isinstance(group, dict)
        for handler in group.get("hooks", []) if isinstance(handler, dict))


def _toml_has_post_tool_hook(text):
    """Recognise the documented inline TOML shape without adding a parser.

    Python 3.8 is supported and has no tomllib. Full-line comments are ignored,
    and only command assignments inside ``[[hooks.PostToolUse.hooks]]`` count;
    a mention in prose, a wrong event, or a commented example does not.
    """
    active = False
    for raw in text.splitlines():
        line = raw.strip()
        if not line or line.startswith("#"):
            continue
        if line.startswith("["):
            active = line == "[[hooks.PostToolUse.hooks]]"
            continue
        if active and re.match(r"command(?:_windows|Windows)?\s*=", line):
            if "grandportage.hook" in line:
                return True
    return False


def _hook_definition_found(root):
    """Find a syntactically active PostToolUse definition covering ``root``.

    This deliberately does NOT claim runtime enforcement. Codex project trust,
    `/hooks` disablement, feature flags, and managed policy are runtime state a
    repository file cannot prove. The caller reports that limitation aloud.
    """
    candidates = (
        (".claude", ("settings.json", "settings.local.json")),
        (".codex", ("hooks.json", "config.toml")),
    )
    here = os.path.abspath(root)
    seen = set()
    while here not in seen:
        seen.add(here)
        for directory, names in candidates:
            for n in names:
                p = os.path.join(here, directory, n)
                try:
                    with open(p, encoding="utf-8") as fh:
                        text = fh.read()
                        found = (_toml_has_post_tool_hook(text) if n.endswith(".toml")
                                 else _json_has_post_tool_hook(text))
                        if found:
                            return True
                except OSError:
                    pass
        parent = os.path.dirname(here)
        if parent == here:
            break
        here = parent
    home = os.path.expanduser("~")
    for directory, names in candidates:
        for n in names:
            p = os.path.join(home, directory, n)
            try:
                with open(p, encoding="utf-8") as fh:
                    text = fh.read()
                    found = (_toml_has_post_tool_hook(text) if n.endswith(".toml")
                             else _json_has_post_tool_hook(text))
                    if found:
                        return True
            except OSError:
                pass
    return False


def cmd_construct(args):
    """Run a structured operation and emit its events.  THE MISSING SURFACE.

    `operations.py` has had four constructors and ZERO production callers --
    no subcommand, no MCP tool, no import outside the tests. A live session
    found it and correctly called it the SECOND CONFIRMED INSTANCE of the class
    `HANDOFF.md` §4 already names as unguarded:

        "Neither asks whether a capability has a surface at all, which is how
         verify.py shipped twice while being unreachable from every
         user-facing path."

    `verify.py` was the first and got `gp verify`. This is the second, and the
    session found it the day after I added a fourth constructor to a module
    nobody could call -- while writing into HANDOFF that "the checkable
    fraction of a campaign rises as it uses constructors", a claim that was not
    available to any author through a supported path.

    THE ARGUMENT FOR CONSTRUCTORS IS THAT THE CALLER STOPS WRITING THE SAME
    THING TWICE, so this reads `ring_vars`, `generators` and `characteristic`
    off the SOURCE MODEL IN THE GRAPH rather than asking for them again. What
    the author supplies is what only they know: which model, and which
    polynomial or variables.

    Prints the events by default. `--declare` sends them through the ordinary
    write path, where every existing guard still applies -- a constructor must
    not become a second, weaker door into the graph.
    """
    from . import operations as O
    g = _load(args)
    src = g.models.get(args.src)
    if not src:
        sys.stderr.write("%s is not a model in this graph.\n" % args.src)
        return 2
    ring = src.get("ring_vars")
    if ring is None or src.get("generators") is None:
        sys.stderr.write(
            "%s records no %s, and a constructor derives its target from the "
            "source's algebra.\n"
            "  That is the point of using one: you supply which polynomial, "
            "and the ring and the ideal come from the model you already "
            "declared.\n"
            % (args.src, "ring variables" if ring is None else "ideal"))
        return 2
    if "characteristic" not in src:
        sys.stderr.write(
            "%s declares no characteristic. A constructor cannot silently "
            "choose characteristic 0 for a source whose coefficient field is "
            "unknown; declare 0 or the prime characteristic first.\n"
            % args.src)
        return 2
    gens, ch = list(src["generators"]), src["characteristic"]
    point_scope = {
        field: src[field] for field in ("coefficient_domain", "point_universe")
        if field in src
    }
    if args.op not in ("decompose", "product-split") and not args.produces:
        sys.stderr.write("construct %s requires --produces.\n" % args.op)
        return 2
    if args.op in ("localize", "saturate") and not args.at:
        sys.stderr.write("construct %s requires --at.\n" % args.op)
        return 2
    if args.op == "eliminate" and not args.vars:
        sys.stderr.write("construct eliminate requires --vars.\n")
        return 2
    if args.op == "affine-solve" and (not args.solve or args.value is None):
        sys.stderr.write(
            "construct affine-solve requires --solve and --value.\n")
        return 2
    if args.op == "product-split" and (not args.spec or not args.receipt):
        sys.stderr.write(
            "construct product-split requires --spec and --receipt.\n")
        return 2

    try:
        if args.op == "localize":
            op = O.localize(args.src, args.at, args.produces, ring, gens,
                            characteristic=ch, **point_scope)
        elif args.op == "saturate":
            op = O.saturate_closure(args.src, args.at, args.produces, ring,
                                    gens, characteristic=ch, **point_scope)
        elif args.op == "eliminate":
            variables = [v.strip() for v in args.vars.split(",")]
            op = O.eliminate(args.src, variables, args.produces, ring, gens,
                             characteristic=ch, **point_scope)
        elif args.op == "product-split":
            with open(args.spec, "r", encoding="utf-8") as handle:
                receipt_spec = json.load(handle)
            op = O.product_split(
                args.src, ring, gens, receipt_spec, args.receipt,
                produces=args.produces or "%s_F%d", characteristic=ch,
                open_conditions=src.get("open_conditions"), **point_scope)
        elif args.op == "affine-solve":
            op = O.affine_coordinate_solve(
                args.src, args.solve, args.value, args.produces, ring, gens,
                characteristic=ch,
                open_conditions=src.get("open_conditions"), **point_scope)
        else:
            op = O.decompose(args.src, ring, gens,
                             produces=args.produces or "%s_C%d",
                             characteristic=ch, timeout=args.timeout,
                             **point_scope)
        if args.run:
            op = O.execute(op, timeout=args.timeout)
    except (ValueError, OSError, cas.CASError) as exc:
        sys.stderr.write("%s\n" % exc)
        return 2
    if not op.events:
        print("%s produced no events.\n  %s" % (op.kind, op.derivation))
        return 0
    if args.declare:
        try:
            references = A.persist_all(args.root, op.artifacts)
            for index, (artifact, reference) in enumerate(
                    zip(op.artifacts, references)):
                suffix = (
                    " step %d" % (index + 1)
                    if len(references) > 1 else "")
                op.events.append(dict({
                    "ev": S.EV_NOTE,
                    "kind": "cas-execution",
                    "source": (
                        "E-%s" % args.produces
                        if args.produces else args.src),
                    "text": (
                        "the exact backend execution for %s%s; this note "
                        "records provenance and licenses no conclusion"
                        % (op.kind, suffix)),
                }, **A.reference_fields(artifact, reference)))
            S.append(op.events, args.root)
        except (A.ArtifactError, OSError, S.GraphError,
                K.KernelRefusal) as exc:
            sys.stderr.write(
                "refused; the graph is unchanged:\n%s\n"
                "  A deduplicated unreferenced artifact may remain.\n" % exc)
            return 2
        print("declared %d event(s) from %s." % (len(op.events), op.kind))
        print("  transport: %s" % op.derivation)
        print("  next: %s" % op.verify_hint)
        return 0
    print(json.dumps(op.events, indent=2, sort_keys=True))
    sys.stderr.write(
        "%d event(s), NOT written. Re-run with --declare, or pipe to "
        "`gp declare`.\n  transport: %s\n"
        % (len(op.events), op.derivation))
    return 0


def cmd_events(args):
    """Dump the log as JSON, so nobody has to parse the file by hand.

    THE REASON THE HEADER BUG WAS FOUND AT ALL.  A live session wanted to read
    a graph, found no machine-readable way to do it -- `gp check --json` was
    the only JSON any command emitted, and it returns findings rather than the
    graph -- and wrote its own parser. Then it hit a `#` on line 1.

    Two defects, and the second is the one that mattered: the file was the only
    interface to its own contents. `--folded` gives the graph as the tool sees
    it, which is not the same as the raw log and is usually what a reader
    actually wants.
    """
    events = [ev for ev, _ in S.load_events(
        S.graph_path(args.root) if not args.graph else args.graph[0])]
    if not args.folded:
        print(json.dumps(events, indent=2, sort_keys=True))
        return 0
    g = S.load(S.graph_path(args.root)) if not args.graph else _load(args)
    print(json.dumps({
        "models": g.models, "edges": g.edges, "claims": g.claims,
        "inferences": {i: g.inferences[i] for i in g.inference_order},
        "tombstones": [g.retractions[k] for k in sorted(g.retractions)],
        "partitions": g.partitions,
    }, indent=2, sort_keys=True, default=str))
    return 0


def _read_projection(args):
    graph = _load(args)
    baseline = H.read_baseline(args.root)
    findings = C.run(graph, baseline["accepted"])
    projection = PROJ.build(
        graph, sources=_graphs(args), findings=findings, accepted=baseline,
        package_version=__version__,
    )
    try:
        return PROJ.focus(projection, args.focus, args.radius)
    except ValueError as exc:
        sys.stderr.write("projection refused: %s\n" % exc)
        raise SystemExit(2)


def _write_derived_output(args, content):
    path = os.path.abspath(args.output)
    protected = {os.path.abspath(source) for source in _graphs(args)}
    if path in protected:
        sys.stderr.write(
            "refusing to overwrite an authoritative graph with a derived "
            "view: %s\n" % path)
        return 2
    if os.path.exists(path) and not args.force:
        sys.stderr.write(
            "derived output already exists: %s (pass --force to replace it)\n"
            % path)
        return 2
    directory = os.path.dirname(path)
    if directory:
        os.makedirs(directory, exist_ok=True)
    temporary = "%s.%d.tmp" % (path, os.getpid())
    try:
        with open(temporary, "x", encoding="utf-8", newline="\n") as stream:
            stream.write(content)
            stream.flush()
            os.fsync(stream.fileno())
        os.replace(temporary, path)
    finally:
        if os.path.exists(temporary):
            os.unlink(temporary)
    print(path)
    return 0


def cmd_project(args):
    """Emit the complete non-authoritative campaign read model."""
    content = PROJ.canonical_json(
        _read_projection(args), pretty=not args.compact)
    if args.output:
        return _write_derived_output(args, content)
    sys.stdout.write(content)
    return 0


def cmd_frontier(args):
    """Compile a read-only proof-frontier document from evidence envelopes."""
    try:
        with open(args.input, encoding="utf-8") as stream:
            source = json.load(stream)
        projection = FRONT.build_document(source)
    except (OSError, json.JSONDecodeError, FRONT.FrontierError) as exc:
        sys.stderr.write("frontier refused: %s\n" % exc)
        return 2
    sys.stdout.write(FRONT.canonical_json(
        projection, pretty=not args.compact))
    return 0


def cmd_frontier_bundle(args):
    """Aggregate exact-scope frontier receipts with explicit resolutions."""
    try:
        projection = FRONT_BUNDLE.build_path(args.input)
    except (OSError, FRONT_BUNDLE.FrontierBundleError) as exc:
        sys.stderr.write("frontier-bundle refused: %s\n" % exc)
        return 2
    if args.emit_review:
        digest = FRONT_BUNDLE.emit_review_receipt(projection, args.emit_review)
        sys.stdout.write(json.dumps({"path": args.emit_review,
                                     "sha256_lf_normalized": digest},
                                    indent=2, sort_keys=True) + "\n")
    else:
        sys.stdout.write(FRONT_BUNDLE.canonical_json(
            projection, pretty=not args.compact))
    return 0


def cmd_visualize(args):
    """Generate a standalone Three.js explorer around a campaign projection."""
    projection = _read_projection(args)
    content = VIZ.render(
        projection, title=args.title or "Grand Portage campaign",
        three_root=args.three_root,
    )
    return _write_derived_output(args, content)


def build_parser():
    p = argparse.ArgumentParser(prog="gp", description=__doc__)
    # `--version` printed the top-level usage and exited 2 without saying no
    # such flag existed -- argparse's default for an unknown option, which
    # reads as "you typed something wrong" rather than "that is not supported".
    p.add_argument("--version", action="version",
                   version="grand-portage %s" % __version__)
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

    e = sub.add_parser(
        "evidence", help="print the evidence and graph-authority manifest")
    e.add_argument("--json", action="store_true")
    e.set_defaults(func=cmd_evidence)

    s = sub.add_parser("show", help="print the graph")
    s.set_defaults(func=cmd_show)

    pr = sub.add_parser("project",
                        help="emit a complete derived campaign read model")
    pr.add_argument("--focus",
                    help="entity id or kind:id for a presentation neighborhood")
    pr.add_argument("--radius", type=int, default=2,
                    help="undirected presentation-neighborhood radius (default: 2)")
    pr.add_argument("--output",
                    help="write JSON to this path instead of stdout")
    pr.add_argument("--compact", action="store_true",
                    help="emit canonical compact JSON")
    pr.add_argument("--force", action="store_true",
                    help="replace an existing derived output file")
    pr.set_defaults(func=cmd_project)

    fr = sub.add_parser(
        "frontier",
        help="compile evidence envelopes to a derived proof frontier")
    fr.add_argument("input", help="frontier-input/v1 JSON document")
    fr.add_argument("--compact", action="store_true",
                    help="emit canonical compact JSON")
    fr.set_defaults(func=cmd_frontier)

    fb = sub.add_parser(
        "frontier-bundle",
        help="aggregate proof-frontier receipts with explicit supersession")
    fb.add_argument("input", help="frontier-bundle-input/v1 JSON manifest")
    fb.add_argument("--compact", action="store_true",
                    help="emit canonical compact JSON")
    fb.add_argument("--emit-review",
                    help="atomically write the compact current-bundle review receipt")
    fb.set_defaults(func=cmd_frontier_bundle)

    vz = sub.add_parser("visualize",
                        help="generate a read-only Three.js campaign explorer")
    vz.add_argument("--output", required=True,
                    help="standalone HTML file to generate")
    vz.add_argument("--title")
    vz.add_argument("--focus",
                    help="entity id or kind:id for a presentation neighborhood")
    vz.add_argument("--radius", type=int, default=2,
                    help="undirected presentation-neighborhood radius (default: 2)")
    vz.add_argument("--three-root", default=VIZ.DEFAULT_THREE_ROOT,
                    help="Three.js package root URL or relative path")
    vz.add_argument("--force", action="store_true",
                    help="replace an existing derived output file")
    vz.set_defaults(func=cmd_visualize)


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
    g.add_argument("--to-epoch1", action="store_true",
                   help="write a strict epoch-1 graph and SHA-256 audit beside "
                        "the unversioned source; never replaces the source")
    g.add_argument("--epoch1-output",
                   help="destination for --to-epoch1 (one source only; default "
                        "is graph.epoch1.jsonl beside the source)")
    g.add_argument("--to-current-kernel", action="store_true",
                   help="copy an older native graph into the current graph "
                        "format and stricter kernel epoch; prior verdicts "
                        "remain stale")
    g.add_argument("--to-kernel2", action="store_true",
                   help=argparse.SUPPRESS)
    g.add_argument("--kernel-output",
                   help="destination for --to-current-kernel (one source only; "
                        "default names the current kernel epoch beside the source)")
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

    v = sub.add_parser(
        "verify",
        help="spend CAS time to settle what the graph takes on the author's "
             "word, and record the answers",
        description=(
            "Runs every verifier that applies and records each answer as a "
            "`verdict` event. `gp check` then reads those, and the VERDICT "
            "BEATS THE DECLARATION wherever they disagree.\n\n"
            "  containment               V(src) subset V(dst), by reduction\n"
            "  identity                  the rewriting -- and mints the "
            "cofactors for a DERIVED one\n"
            "  unit_ideal                an EMPTY's certificate, by expansion\n"
            "  localized_unit_ideal      EMPTY on an exact open chart, by a "
            "guard-monomial certificate\n"
            "  ring_iso                  an EQUIVALENCE's maps, by reduction\n"
            "  point_witness             a NONEMPTY's `witness_point`, by "
            "substitution\n"
            "  partition_exhaustiveness  that the cases are all the cases\n"
            "  operation_output          that a constructor produced what it "
            "claims\n\n"
            "Silent where the data for a question is absent -- that is an "
            "UNASKED question, not a failed one, and `gp check` reports the "
            "hole."),
        formatter_class=argparse.RawDescriptionHelpFormatter)
    v.add_argument("--timeout", type=int, default=300)
    v.add_argument("--dry-run", action="store_true",
                   help="report the verdicts without recording them")
    v.set_defaults(func=cmd_verify)

    exact = sub.add_parser(
        "verify-elimination",
        help="certify exact contraction using an explicit polynomial section")
    exact.add_argument("edge", help="constructor-built Eliminate edge id")
    exact.add_argument(
        "--section", required=True,
        help='JSON object mapping each eliminated variable to a polynomial '
             'in the retained variables, e.g. {"y":"x^2"}')
    exact.add_argument("--timeout", type=int, default=300)
    exact.add_argument("--dry-run", action="store_true",
                       help="check and display without recording authority")
    exact.set_defaults(func=cmd_verify_elimination)
    point_lift = sub.add_parser(
        "verify-elimination-point-lift",
        help="check a finite rational-chart point-lift cover")
    point_lift.add_argument(
        "edge", help="constructor-built Eliminate edge id")
    point_lift.add_argument(
        "--certificate", required=True,
        help="JSON with principal-open rational charts and an all-guards-zero fallback")
    point_lift.add_argument("--timeout", type=int, default=300)
    point_lift.add_argument(
        "--dry-run", action="store_true",
        help="check and display without recording artifacts or authority")
    point_lift.set_defaults(func=cmd_verify_elimination_point_lift)
    groebner = sub.add_parser(
        "verify-elimination-groebner",
        help="produce and check a pure-lex exact-contraction certificate")
    groebner.add_argument("edge", help="constructor-built Eliminate edge id")
    groebner.add_argument("--timeout", type=int, default=300)
    groebner.add_argument(
        "--dry-run", action="store_true",
        help="run and display without recording artifacts or authority")
    groebner.set_defaults(func=cmd_verify_elimination_groebner)
    coefficient_expansion = sub.add_parser(
        "verify-coefficient-expansion",
        help="translation-validate polynomial equations lowered to coefficients")
    coefficient_expansion.add_argument(
        "--spec", required=True,
        help="closed coefficient_expansion_v1 JSON specification")
    coefficient_expansion.add_argument("--json", action="store_true")
    coefficient_expansion.set_defaults(func=cmd_verify_coefficient_expansion)
    laurent_lowering = sub.add_parser(
        "verify-laurent-lowering",
        help="translation-validate finite exact Laurent arithmetic")
    laurent_lowering.add_argument(
        "--spec", required=True,
        help="closed laurent_lowering_v1 JSON specification")
    laurent_lowering.add_argument("--json", action="store_true")
    laurent_lowering.set_defaults(func=cmd_verify_laurent_lowering)
    laurent_pipeline = sub.add_parser(
        "verify-laurent-coefficient-pipeline",
        help="verify and bind Laurent lowering to coefficient expansion")
    laurent_pipeline.add_argument(
        "--spec", required=True,
        help="closed laurent_coefficient_pipeline_v1 JSON specification")
    laurent_pipeline.add_argument("--json", action="store_true")
    laurent_pipeline.set_defaults(
        func=cmd_verify_laurent_coefficient_pipeline)
    factor_power = sub.add_parser(
        "verify-factor-power",
        help="check exact unit-times-positive-power identities")
    factor_power.add_argument(
        "--spec", required=True,
        help="closed factor_power_v1 JSON specification")
    factor_power.add_argument("--json", action="store_true")
    factor_power.set_defaults(func=cmd_verify_factor_power)
    factor_contradiction = sub.add_parser(
        "verify-factor-power-contradiction",
        help="compose a factor receipt with an affine unit contradiction")
    factor_contradiction.add_argument(
        "--spec", required=True,
        help="closed factor_power_affine_contradiction_v1 JSON specification")
    factor_contradiction.add_argument("--json", action="store_true")
    factor_contradiction.set_defaults(
        func=cmd_verify_factor_power_contradiction)
    product_split = sub.add_parser(
        "verify-product-split",
        help="check exact binary product-split identities")
    product_split.add_argument(
        "--spec", required=True,
        help="closed product_split_v1 JSON specification")
    product_split.add_argument("--json", action="store_true")
    product_split.set_defaults(func=cmd_verify_product_split)
    localization = sub.add_parser(
        "verify-localization-membership",
        help="check a rational identity after declared guards are inverted")
    localization.add_argument(
        "--spec", required=True,
        help="closed localization_membership_v1 JSON specification")
    localization.add_argument("--json", action="store_true")
    localization.set_defaults(func=cmd_verify_localization_membership)
    triangular = sub.add_parser(
        "verify-localized-triangular-chain",
        help="check an ordered localized affine solve chain")
    triangular.add_argument(
        "--spec", required=True,
        help="closed localized_triangular_solve_chain_v1/v2 JSON specification")
    triangular.add_argument("--json", action="store_true")
    triangular.set_defaults(func=cmd_verify_localized_triangular_chain)
    materialize = sub.add_parser(
        "materialize-elimination-groebner",
        help="discover, certify, and declare a pure-lex elimination target")
    materialize.add_argument(
        "--src", required=True, help="existing source model id")
    materialize.add_argument(
        "--vars", required=True,
        help="nonempty comma-separated variables to eliminate")
    materialize.add_argument(
        "--produces", required=True, help="new target model id")
    materialize.add_argument("--timeout", type=int, default=300)
    materialize.add_argument(
        "--dry-run", action="store_true",
        help="run both checks without recording artifacts or graph events")
    materialize.set_defaults(func=cmd_materialize_elimination_groebner)
    artifacts = sub.add_parser(
        "artifacts",
        help="audit durable raw CAS programs, transcripts, and certificates")
    artifact_sub = artifacts.add_subparsers(dest="artifact_cmd")
    artifact_check = artifact_sub.add_parser(
        "check", help="verify every content-addressed execution reference")
    artifact_check.set_defaults(func=cmd_artifacts_check)

    # THE HELP NAMED NOT ONE EVENT KIND AND NOT ONE FIELD.  A live session
    # reported reading `store.py`'s `_apply_*` methods to find out what an
    # `evidence` or `doubt` record needs -- "that is the exact place a person
    # looks, and it is empty".  A write command whose help omits what may be
    # written is a door with no sign on it.
    d = sub.add_parser(
        "declare",
        help="write events to the graph, transactionally: they fold first "
             "or nothing is written",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog=_declare_epilog())
    d.add_argument("--file", help="JSON file; omit to read stdin")
    d.set_defaults(func=cmd_declare)

    i = sub.add_parser("init", help="create an empty graph")
    i.set_defaults(func=cmd_init)
    con = sub.add_parser(
        "construct",
        help="run a structured operation and emit its events")
    con.add_argument("op", choices=["localize", "saturate", "eliminate",
                                    "decompose", "product-split", "affine-solve"])
    con.add_argument("--src", required=True,
                     help="the source MODEL; its ring and ideal are read from "
                          "the graph")
    con.add_argument("--at", help="the polynomial, for localize / saturate")
    con.add_argument("--vars", help="comma-separated, for eliminate")
    con.add_argument("--spec", help="receipt JSON, for product-split")
    con.add_argument("--receipt", help="selected receipt id, for product-split")
    con.add_argument("--solve", help="pivot coordinate, for affine-solve")
    con.add_argument("--value", help="pivot solution, for affine-solve")
    con.add_argument("--produces", help="model id, or branch-id pattern for product-split")
    con.add_argument("--run", action="store_true",
                     help="execute a pending saturation/elimination program "
                          "and emit completed generators")
    con.add_argument("--declare", action="store_true",
                     help="write the events instead of printing them")
    con.add_argument("--timeout", type=int, default=300)
    con.set_defaults(func=cmd_construct)
    ev = sub.add_parser("events",
                        help="dump the log as JSON (do not parse the file)")
    ev.add_argument("--folded", action="store_true",
                    help="the FOLDED graph -- models, edges, claims, "
                         "inferences, partitions -- rather than the raw log")
    ev.set_defaults(func=cmd_events)
    return p


def main(argv=None):
    args = build_parser().parse_args(argv)
    if not getattr(args, "func", None):
        build_parser().print_help()
        return 2
    # RESOLVE THE ROOT THE WAY THE HOOK DOES, because they disagreed and the
    # disagreement surfaced as advice that fails.
    #
    # The walk-up was added to the hook and not here. So from a subdirectory of
    # a campaign the hook found the root, refused the step, and printed its
    # standard line -- "run `gp check`" -- and `gp check` from that same
    # directory reported there was no graph at all. A live session hit it on
    # the first use of the feature.
    #
    # `gp init` is exempt: it CREATES a graph, and walking up would make it
    # silently initialise a parent campaign instead of here, which is the one
    # outcome worse than not finding one.
    if (getattr(args, "root", None) == "." and not getattr(args, "graph", None)
            and args.func is not cmd_init):
        args.root = S.find_root(".")
    return args.func(args)


def declare_main(argv=None):
    """Dedicated console surface for transactional declarations.

    MCP discovery depends on which Codex project owns a task. Campaigns still
    expose ``portage_declare`` through MCP, while this literal command gives a
    context-free task the same safe write path when nested MCP configuration is
    not loaded.
    """
    parser = argparse.ArgumentParser(
        prog="portage_declare",
        description="transactionally append Grand Portage graph events")
    parser.add_argument("--root", default=".", help="campaign root")
    parser.add_argument("--graph", action="append",
                        help="exact graph log to write; may be given once")
    parser.add_argument("--file", help="JSON file; omit or use - for stdin")
    args = parser.parse_args(
        sys.argv[1:] if argv is None else argv)
    forwarded = ["--root", args.root]
    for graph in args.graph or []:
        forwarded.extend(["--graph", graph])
    forwarded.append("declare")
    if args.file is not None:
        forwarded.extend(["--file", args.file])
    return main(forwarded)


if __name__ == "__main__":
    sys.exit(main())
