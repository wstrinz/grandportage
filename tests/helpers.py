"""Fixture loading and graph mutation for the gates.

Mutation works on the EVENT LIST and re-folds, never on the folded graph.  That
matters: derived state -- an emptiness scope, an inference's endpoint -- is
computed during the fold, so patching a folded graph would leave the derivation
stale and a mutation could appear to pass for the wrong reason.  Re-folding
also means a mutation that produces a MALFORMED graph raises instead of
silently checking something else, which is a result in its own right.
"""

import json
import os

from grandportage import check as C
from grandportage import store as S

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
FIXTURES = os.path.join(ROOT, "fixtures")

DOMAINS = ("jc2", "matroid")


def graph_file(domain):
    return os.path.join(FIXTURES, domain, "graph.jsonl")


def expect_file(domain):
    return os.path.join(FIXTURES, domain, "expect.json")


def raw_events(domain):
    return [ev for ev, _ in S.load_events(graph_file(domain))]


def fold(events):
    g = S.Graph()
    for n, ev in enumerate(events, 1):
        g.apply(ev, source="<mutant>", lineno=n)
    return g.validate()


def load(domain):
    return S.load(graph_file(domain))


def expected(domain):
    with open(expect_file(domain), "r", encoding="utf-8") as fh:
        return json.load(fh)


def findings_by_id(graph):
    return {f.fid: f for f in C.run(graph)}


def mutate(domain, patch):
    """Re-fold `domain`'s events with `patch` applied to each event.

    `patch(ev)` returns a (possibly modified) event, or None to drop it.
    Events are deep-copied first so a mutation cannot leak into another test.
    """
    out = []
    for ev in raw_events(domain):
        new = patch(json.loads(json.dumps(ev)))
        if new is not None:
            out.append(new)
    return fold(out)


def set_field(ev_kind, ev_id, **fields):
    """A patch that overwrites fields on one entity and leaves the rest alone."""
    def patch(ev):
        if ev.get("ev") == ev_kind and ev.get("id") == ev_id:
            ev.update(fields)
        return ev
    return patch


def flagged(graph):
    """Ids of inferences the transport rule refuses."""
    return {f.subject for f in C.run(graph) if f.rule == C.R_TRANSPORT}


def rules(graph):
    return {f.rule for f in C.run(graph)}
