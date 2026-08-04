"""Versioned graph-format boundary.

Epoch 0 is every unversioned log written before the compatibility boundary.
It remains readable, but only through :func:`import_epoch0_event`: that
adapter may preserve or remove a licence and must never invent one.

Epoch 1 is deliberately stricter.  Its first record identifies the format and
kernel epoch, every event has a closed field set, and licensing flags are real
JSON booleans rather than merely truthy values.
"""

import re

GRAPH_FORMAT = 4
KERNEL_EPOCH = 10
META_EVENT = "meta"


def created_with():
    """The writer recorded in a new graph, from the package's one version."""
    from . import __version__
    return "grandportage/%s" % __version__


def meta_event():
    return {
        "ev": META_EVENT,
        "graph_format": GRAPH_FORMAT,
        "kernel_epoch": KERNEL_EPOCH,
        "created_with": created_with(),
    }


_LIFECYCLE = {"supersedes", "discharge_kind", "why"}

# Closed schemas are intentionally data, not a forest of ad-hoc ``if key``
# checks.  Adding an authored field now requires placing it in the vocabulary
# of the event that owns it.
EVENT_FIELDS = {
    "meta": {"ev", "graph_format", "kernel_epoch", "created_with"},
    "certificate": {
        "ev", "id", "base_changes", "why",
    } | _LIFECYCLE,
    "model": {
        "ev", "id", "desc", "what", "field", "chart", "universe",
        "coefficient_domain", "point_universe",
        "characteristic", "ring_vars", "generators", "ideal_pending",
        "open_conditions", "saturated_at", "eliminated", "component_of",
        "declares", "touches", "reads", "coverage_axes", "cite",
    } | _LIFECYCLE,
    "edge": {
        "ev", "id", "src", "dst", "type", "why", "map_kind", "drops",
        "support", "debt_why", "strictness_witness", "converse_witness",
        "forward", "inverse", "ring_iso", "ring_iso_certificate",
        "refinement", "discharge_hint",
        "cite", "prime", "built_by_operation",
    } | _LIFECYCLE,
    "claim": {
        "ev", "id", "model", "family", "kind", "statement", "certificate",
        "scope", "identity_origin", "witness_kind", "witness",
        "witness_point", "lhs", "rhs", "ring_vars", "integral",
        "coefficients_in_base", "zariski_closed", "existential",
        "condition", "established_by", "ladder", "cite", "citation", "caveat",
        "groups", "splits", "method", "proves", "rests_on",
        "counts_against", "asserts_count",
    } | _LIFECYCLE,
    "inference": {
        "ev", "id", "claim", "path", "premises", "concludes_kind",
        "asserted", "severity_override", "severity_why", "cite", "citation",
        "note", "era",
    } | _LIFECYCLE,
    "built_by": {"ev", "model", "inference"},
    "partition": {
        "ev", "id", "parent", "branches", "exhaustive", "why",
        "receipt_schema", "receipt_id", "receipt_fingerprint",
    } | _LIFECYCLE,
    "same_as": {"ev", "id", "models", "why"} | _LIFECYCLE,
    "family": {"ev", "id", "count", "desc", "members"} | _LIFECYCLE,
    "evidence": {
        "ev", "id", "for", "method", "ran", "what", "decides",
        "agrees_with", "cite",
    } | _LIFECYCLE,
    "doubt": {
        "ev", "id", "about", "kind", "why", "quote", "severity",
    } | _LIFECYCLE,
    "citation": {
        "ev", "id", "cites", "resolves_to", "why", "hazard",
    } | _LIFECYCLE,
    "erratum": {"ev", "id", "voids", "why"},
    "verdict": {
        "ev", "id", "subject", "of", "verdict", "why", "representation",
        "verifier", "verifier_version", "kernel_epoch", "backend",
        "input_fingerprint",
    },
    "note": {
        "ev", "id", "text", "domain", "source", "kind", "src",
        "attempted_model", "verdict", "abort_reason",
    } | _LIFECYCLE,
}

REQUIRED_FIELDS = {
    "meta": {"ev", "graph_format", "kernel_epoch", "created_with"},
    "edge": {"ev", "id", "src", "dst", "type", "why", "map_kind"},
    "verdict": {
        "ev", "id", "subject", "of", "verdict", "why", "verifier",
        "verifier_version", "kernel_epoch", "backend",
        "input_fingerprint",
    },
}

LICENSING_BOOLEANS = {
    "certificate": {"base_changes"},
    "edge": {"refinement", "ring_iso"},
    "claim": {
        "integral", "coefficients_in_base", "zariski_closed", "existential",
    },
}


def validate_native_event(ev, where, error):
    """Validate the format-level shape of one epoch-1 event.

    ``error`` is injected to keep this bottom-level module independent of the
    store's public exception class.
    """
    if not isinstance(ev, dict):
        raise error("%s: event is not an object" % where)
    kind = ev.get("ev")
    if kind not in EVENT_FIELDS:
        raise error("%s: unknown event kind %r" % (where, kind))
    unknown = sorted(set(ev) - EVENT_FIELDS[kind])
    if unknown:
        raise error(
            "%s: epoch-1 %s event has unknown field%s %s. Native schemas are "
            "closed; fix the spelling or add the field to the format."
            % (where, kind, "s" if len(unknown) != 1 else "",
               ", ".join("`%s`" % x for x in unknown)))
    missing = sorted(REQUIRED_FIELDS.get(kind, set()) - set(ev))
    if missing:
        raise error(
            "%s: epoch-1 %s event needs %s"
            % (where, kind, ", ".join("`%s`" % x for x in missing)))
    for field in sorted(LICENSING_BOOLEANS.get(kind, set())):
        if field in ev and not isinstance(ev[field], bool):
            raise error(
                "%s: epoch-1 %s %r `%s` must be true or false, not %r"
                % (where, kind, ev.get("id"), field, ev[field]))
    if (kind == "edge" and "ring_iso_certificate" in ev
            and not isinstance(ev["ring_iso_certificate"], dict)):
        raise error(
            "%s: edge `ring_iso_certificate` must be an object" % where)
    if kind == "partition":
        receipt_fields = {
            "receipt_schema", "receipt_id", "receipt_fingerprint"}
        present = receipt_fields & set(ev)
        if present and present != receipt_fields:
            raise error(
                "%s: partition receipt binding must provide %s together"
                % (where, ", ".join("`%s`" % field
                                    for field in sorted(receipt_fields))))
        if present:
            for field in ("receipt_schema", "receipt_id"):
                if (not isinstance(ev[field], str)
                        or not ev[field].strip()):
                    raise error(
                        "%s: partition `%s` must be a non-empty string"
                        % (where, field))
            if (not isinstance(ev["receipt_fingerprint"], str)
                    or not re.match(r"^sha256:[0-9a-f]{64}$",
                                    ev["receipt_fingerprint"])):
                raise error(
                    "%s: partition `receipt_fingerprint` must be "
                    "sha256:<64 lowercase hex>" % where)
    if kind == "verdict":
        if not isinstance(ev["verifier"], str) or not ev["verifier"].strip():
            raise error("%s: verdict `verifier` must be a non-empty string"
                        % where)
        if (not isinstance(ev["verifier_version"], int)
                or isinstance(ev["verifier_version"], bool)
                or ev["verifier_version"] < 1):
            raise error("%s: verdict `verifier_version` must be a positive integer"
                        % where)
        if (not isinstance(ev["kernel_epoch"], int)
                or isinstance(ev["kernel_epoch"], bool)
                or ev["kernel_epoch"] < 0):
            raise error("%s: verdict `kernel_epoch` must be a nonnegative integer"
                        % where)
        if not isinstance(ev["backend"], str) or not ev["backend"].strip():
            raise error("%s: verdict `backend` must be a non-empty string" % where)
        if (not isinstance(ev["input_fingerprint"], str)
                or not re.match(r"^sha256:[0-9a-f]{64}$",
                                ev["input_fingerprint"])):
            raise error("%s: verdict `input_fingerprint` must be sha256:<64 lowercase hex>"
                        % where)


def validate_meta(ev, where, error):
    validate_native_event(ev, where, error)
    for field in ("graph_format", "kernel_epoch"):
        if (not isinstance(ev[field], int)
                or isinstance(ev[field], bool)):
            raise error(
                "%s: `%s` must be an integer, not %r"
                % (where, field, ev[field]))
    if ev["graph_format"] != GRAPH_FORMAT:
        raise error(
            "%s: graph_format %r is unsupported; this build reads format %d"
            % (where, ev["graph_format"], GRAPH_FORMAT))
    if ev["kernel_epoch"] != KERNEL_EPOCH:
        raise error(
            "%s: kernel_epoch %r is incompatible with this build's epoch %d"
            % (where, ev["kernel_epoch"], KERNEL_EPOCH))
    if not isinstance(ev["created_with"], str) or not ev["created_with"].strip():
        raise error("%s: `created_with` must be a non-empty string" % where)


def import_epoch0_event(ev):
    """Conservatively adapt an unversioned event without minting a licence."""
    if not isinstance(ev, dict):
        return ev
    out = dict(ev)
    kind = out.get("ev")
    for field in LICENSING_BOOLEANS.get(kind, set()):
        if field in out and not isinstance(out[field], bool):
            # Old truthiness accepted strings such as ``"false"``.  The
            # compatibility boundary resolves malformed values only downward.
            out[field] = False
    if kind == "edge" and "map_kind" not in out:
        # The old implicit IDENTITY_MAP was permissive.  A restriction really
        # is an inclusion in the same coordinates; elsewhere, unknown map
        # structure is represented by the least transporting existing kind.
        out["map_kind"] = (
            "IDENTITY_MAP" if out.get("type") == "RESTRICTION" else "RATIONAL")
    if kind == "edge":
        if "strictness_witness" not in out and out.get("witness"):
            out["strictness_witness"] = out["witness"]
        out.pop("witness", None)
        # Retracted and consulted by no transport cell.
        out.pop("zariski_dense", None)
    return out
