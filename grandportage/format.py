"""Versioned graph-format boundary.

Epoch 0 is every unversioned log written before the compatibility boundary.
It remains readable, but only through :func:`import_epoch0_event`: that
adapter may preserve or remove a licence and must never invent one.

Epoch 1 is deliberately stricter.  Its first record identifies the format and
kernel epoch, every event has a closed field set, and licensing flags are real
JSON booleans rather than merely truthy values.
"""

import re

from . import identity as I

GRAPH_FORMAT = 8
KERNEL_EPOCH = 12
META_EVENT = "meta"

# Format 5 closed the historical meta header over a portable implementation
# identity (see 59e119c); formats 1-4 predate it and never carried the field.
# Any format from this point up to (but not including) the live GRAPH_FORMAT
# is a historical format that must still preserve and validate its recorded
# identity, without asserting it matches the implementation now reading it.
IMPLEMENTATION_IDENTITY_MIN_FORMAT = 5


def created_with():
    """The writer recorded in a new graph, from the package's one version."""
    from . import __version__
    return "grandportage/%s" % __version__


def meta_event():
    from . import __version__
    return {
        "ev": META_EVENT,
        "graph_format": GRAPH_FORMAT,
        "kernel_epoch": KERNEL_EPOCH,
        "created_with": created_with(),
        "implementation": I.implementation_identity(
            __version__, GRAPH_FORMAT, KERNEL_EPOCH),
    }


LIFECYCLE_FIELDS = frozenset({"supersedes", "discharge_kind", "why"})
_LIFECYCLE = set(LIFECYCLE_FIELDS)

# Closed schemas are intentionally data, not a forest of ad-hoc ``if key``
# checks.  Adding an authored field now requires placing it in the vocabulary
# of the event that owns it.
EVENT_FIELDS = {
    "meta": {
        "ev", "graph_format", "kernel_epoch", "created_with",
        "implementation",
    },
    "certificate": {
        "ev", "id", "reach", "why",
    } | _LIFECYCLE,
    "model": {
        "ev", "id", "desc", "what", "field", "chart", "universe",
        "about", "compute_in", "coefficient_domain", "point_universe",
        "characteristic", "ring_vars", "generators", "ideal_pending",
        "embedding",
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
        "witness_point", "witness_field", "lhs", "rhs", "ring_vars", "integral",
        "coefficients_in_base", "zariski_closed", "existential",
        "condition", "established_by", "ladder", "cite", "citation", "caveat",
        "groups", "splits", "method", "proves", "rests_on",
        "counts_against", "asserts_count",
    } | _LIFECYCLE,
    "inference": {
        "ev", "id", "claim", "path", "premises", "concludes_kind",
        "asserted", "severity_override", "severity_why", "cite", "citation",
        "note", "era", "family_bridges",
    } | _LIFECYCLE,
    "built_by": {"ev", "model", "inference"},
    "partition": {
        "ev", "id", "parent", "branches", "exhaustive", "why",
        "receipt_schema", "receipt_id", "receipt_fingerprint",
    } | _LIFECYCLE,
    "same_as": {"ev", "id", "models", "why"} | _LIFECYCLE,
    "family": {
        "ev", "id", "count", "desc", "members", "enumeration",
    } | _LIFECYCLE,
    "family_bridge": {
        "ev", "id", "family", "enumeration", "coverage", "group",
        "member", "model", "why",
    } | _LIFECYCLE,
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
    "meta": {
        "ev", "graph_format", "kernel_epoch", "created_with",
        "implementation",
    },
    "edge": {"ev", "id", "src", "dst", "type", "why", "map_kind"},
    "verdict": {
        "ev", "id", "subject", "of", "verdict", "why", "verifier",
        "verifier_version", "kernel_epoch", "backend",
        "input_fingerprint",
    },
}

# Authoring requirements are data because the fold, CLI schema and MCP schema
# must not teach three subtly different event languages.  ``REQUIRED_FIELDS``
# above remains the wire-format minimum (notably for lifecycle tombstones);
# these are the fields required for a live authored record of each kind.
AUTHOR_REQUIRED_FIELDS = {
    "certificate": {"ev", "id", "reach", "why"},
    "model": {"ev", "id"},
    "edge": {"ev", "id", "src", "dst", "type", "why", "map_kind"},
    "claim": {"ev", "id", "kind", "statement"},
    "inference": {"ev", "id", "asserted"},
    "built_by": {"ev", "model", "inference"},
    "partition": {"ev", "id", "parent", "branches", "exhaustive", "why"},
    "same_as": {"ev", "id", "models", "why"},
    "family": {"ev", "id", "count", "desc"},
    "family_bridge": {
        "ev", "id", "family", "enumeration", "coverage", "group",
        "member", "model", "why",
    },
    "evidence": {"ev", "id", "for", "method", "ran", "what"},
    "doubt": {"ev", "id", "about", "kind", "why"},
    "citation": {"ev", "id", "cites", "resolves_to", "why"},
    "erratum": {"ev", "id", "voids", "why"},
    "note": {"ev", "text"},
}

EVIDENCE_METHODS = ("ENUMERATION", "REPLICATION")
EVIDENCE_DECISIONS = ("BOTH", "EXCLUSIONS", "INCLUSIONS")

# Machine-readable additions to JSON Schema.  They are intentionally small:
# the fold remains the authority for mathematical validation, while these
# rules make the common authoring mistakes discoverable without a rejected
# write first.
CONDITIONAL_REQUIREMENTS = {
    "evidence": ({"if": {"method": "REPLICATION"},
                  "required": ("agrees_with",)},),
}

TARGET_ENTITY_TYPES = {
    "evidence.for": ("claim",),
    "doubt.about": ("claim", "inference", "model", "edge"),
    "built_by.model": ("model",),
    "built_by.inference": ("inference",),
    "partition.parent": ("model",),
    "partition.branches": ("model",),
    "partition.exhaustive": ("claim",),
}

LICENSING_BOOLEANS = {
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
    tombstone = (
        isinstance(ev.get("supersedes"), str)
        and ev.get("discharge_kind") in ("RETRACT", "WITHDRAW"))
    required = REQUIRED_FIELDS.get(kind, {"ev"})
    if not tombstone:
        required = AUTHOR_REQUIRED_FIELDS.get(kind, required)
    missing = sorted(required - set(ev))
    if missing:
        raise error(
            "%s: epoch-1 %s event needs %s"
            % (where, kind, ", ".join("`%s`" % x for x in missing)))
    for field in sorted(LICENSING_BOOLEANS.get(kind, set())):
        if field in ev and not isinstance(ev[field], bool):
            raise error(
                "%s: epoch-1 %s %r `%s` must be true or false, not %r"
                % (where, kind, ev.get("id"), field, ev[field]))
    lifecycle_present = set(ev) & LIFECYCLE_FIELDS
    for field in sorted(lifecycle_present):
        if not isinstance(ev[field], str) or not ev[field].strip():
            raise error(
                "%s: epoch-1 %s `%s` must be a non-empty string"
                % (where, kind, field))
    if "supersedes" in ev and "discharge_kind" not in ev:
        raise error(
            "%s: epoch-1 %s with `supersedes` also needs `discharge_kind`"
            % (where, kind))
    if "discharge_kind" in ev and "supersedes" not in ev:
        raise error(
            "%s: epoch-1 %s with `discharge_kind` also needs `supersedes`"
            % (where, kind))
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


def _validate_implementation_identity(ev, where, error):
    """Structurally validate the closed implementation identity on ``ev``.

    This only checks that the identity is well-formed and internally
    consistent with ``ev``'s own ``graph_format``/``kernel_epoch``; it never
    asserts that the identity matches the implementation doing the reading.
    Historical formats 5+ recorded another build's identity, and that
    recorded identity must be preserved and validated, not overwritten or
    treated as the current build (see :func:`validate_meta_for_read`).
    """
    implementation = ev["implementation"]
    required = {
        "schema", "package_version", "source_commit", "source_dirty",
        "graph_format", "kernel_epoch", "mcp_protocol", "backend",
    }
    if not isinstance(implementation, dict) or set(implementation) != required:
        raise error("%s: `implementation` must be the closed %s identity"
                    % (where, I.IDENTITY_SCHEMA))
    if implementation["schema"] != I.IDENTITY_SCHEMA:
        raise error("%s: unsupported implementation identity schema %r"
                    % (where, implementation["schema"]))
    if (not isinstance(implementation["package_version"], str)
            or not implementation["package_version"].strip()):
        raise error("%s: implementation package_version must be non-empty"
                    % where)
    commit = implementation["source_commit"]
    if commit is not None and not re.match(r"^[0-9a-f]{40}$", commit):
        raise error("%s: implementation source_commit must be 40 lowercase hex"
                    % where)
    if (implementation["source_dirty"] is not None
            and type(implementation["source_dirty"]) is not bool):
        raise error("%s: implementation source_dirty must be true, false, or null"
                    % where)
    for field in ("graph_format", "kernel_epoch"):
        if (not isinstance(implementation[field], int)
                or isinstance(implementation[field], bool)):
            raise error(
                "%s: implementation `%s` must be an integer, not %r"
                % (where, field, implementation[field]))
    if (implementation["graph_format"] != ev["graph_format"]
            or implementation["kernel_epoch"] != ev["kernel_epoch"]):
        raise error("%s: implementation identity disagrees with graph metadata"
                    % where)
    if (not isinstance(implementation["mcp_protocol"], str)
            or not implementation["mcp_protocol"].strip()):
        raise error("%s: implementation mcp_protocol must be non-empty" % where)
    backend = implementation["backend"]
    backend_fields = {
        "contract", "implementation", "implementation_version",
        "protocol_version",
    }
    if (not isinstance(backend, dict) or set(backend) != backend_fields
            or not isinstance(backend["contract"], str)
            or not isinstance(backend["implementation"], str)
            or type(backend["implementation_version"]) is not int
            or type(backend["protocol_version"]) is not int):
        raise error("%s: implementation backend identity is malformed" % where)


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
    _validate_implementation_identity(ev, where, error)


def validate_meta_for_read(ev, where, error):
    """Validate a native header at the read boundary.

    Current-format metadata remains strict.  Older native formats are archival
    inputs: they may be inspected and migrated.  Formats before
    :data:`IMPLEMENTATION_IDENTITY_MIN_FORMAT` never carried an implementation
    identity and keep their original four-field header contract; their missing
    identity is preserved as unknown rather than fabricated.  Formats from
    :data:`IMPLEMENTATION_IDENTITY_MIN_FORMAT` up to (but excluding) the
    current :data:`GRAPH_FORMAT` closed over a recorded implementation
    identity, and that identity is required, preserved, and structurally
    validated -- but never checked against the implementation now reading it,
    since an archival header describes the build that wrote it, not this one.
    Writers enforce the current boundary separately before appending anything.
    """
    if not isinstance(ev, dict):
        raise error("%s: event is not an object" % where)
    if ev.get("ev") != META_EVENT:
        raise error("%s: native graph must begin with a `meta` event" % where)
    graph_format = ev.get("graph_format")
    kernel_epoch = ev.get("kernel_epoch")
    for field, value in (("graph_format", graph_format),
                         ("kernel_epoch", kernel_epoch)):
        if not isinstance(value, int) or isinstance(value, bool):
            raise error("%s: `%s` must be an integer, not %r"
                        % (where, field, value))
    if graph_format == GRAPH_FORMAT:
        validate_meta(ev, where, error)
        return
    if graph_format < 1 or graph_format > GRAPH_FORMAT:
        raise error(
            "%s: graph_format %r is unsupported; this build reads historical "
            "formats 1..%d and current format %d"
            % (where, graph_format, GRAPH_FORMAT - 1, GRAPH_FORMAT))
    if kernel_epoch < 1 or kernel_epoch > KERNEL_EPOCH:
        raise error(
            "%s: historical kernel_epoch %r cannot be read by this build's "
            "epoch %d" % (where, kernel_epoch, KERNEL_EPOCH))
    closes_over_identity = graph_format >= IMPLEMENTATION_IDENTITY_MIN_FORMAT
    expected = {"ev", "graph_format", "kernel_epoch", "created_with"}
    if closes_over_identity:
        expected = expected | {"implementation"}
    if set(ev) != expected:
        missing = sorted(expected - set(ev))
        extra = sorted(set(ev) - expected)
        raise error(
            "%s: historical meta event has the wrong fields; missing: %s; "
            "extra: %s"
            % (where, ", ".join(missing) or "(none)",
               ", ".join(extra) or "(none)"))
    if not isinstance(ev["created_with"], str) or not ev["created_with"].strip():
        raise error("%s: `created_with` must be a non-empty string" % where)
    if closes_over_identity:
        _validate_implementation_identity(ev, where, error)


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
