"""Version and fingerprint the inputs behind computed verifier verdicts.

A stored ``VERIFIED`` is executable trust.  It must therefore say which
verifier produced it, which kernel semantics interpreted it, which backend ran
it, and exactly which graph records were presented as input.  Otherwise a
verdict produced by yesterday's buggy verifier remains authoritative forever.

This module deliberately owns only verifier provenance.  Graph-format
versioning lives in :mod:`grandportage.format`; the store calls
``current_verdict`` while folding and projects a verdict into the effective
graph only when this module says it is current.
"""

import hashlib
import json
import re

from . import backend as B
from . import format as F
from . import groebner as G
from . import kernel as K


BACKEND = "singular"

# Increment one entry whenever that verifier's meaning or implementation
# changes in a way that requires stored answers to be recomputed.  Keeping
# these independent avoids invalidating every verdict when one checker changes.
VERIFIERS = {
    "claim": ("verify.identity", 2),
    "edge": ("verify.containment", 3),
    "certificate": ("verify.unit_ideal", 2),
    "ring_iso": ("verify.ring_iso", 3),
    "witness": ("verify.point_witness", 2),
    "operation": ("verify.operation_output", 2),
    "elimination": ("verify.elimination_section", 2),
    "point_lift": ("verify.elimination_point_lift", 1),
    "partition": ("verify.partition_exhaustiveness", 3),
}

# A subject names one mathematical obligation; verifier identities name
# independent algorithms that can discharge it.  Polynomial sections and
# pure-lex certificates both prove elimination completeness without becoming
# the same checker.
VERIFIER_ALTERNATIVES = {
    "certificate": {
        "verify.unit_ideal": 2,
        "verify.localized_unit_ideal": 1,
    },
    "elimination": {
        "verify.elimination_section": 2,
        "verify.elimination_groebner": 1,
    },
}


def _certificate_verifier(graph, of):
    claim = graph.claims.get(of) or {}
    if claim.get("certificate") == "LOCALIZED_UNIT_IDEAL_CERT":
        return "verify.localized_unit_ideal"
    return "verify.unit_ideal"


ELIMINATION_VERDICT_VERIFIER = {
    "VERIFIED_SECTION": "verify.elimination_section",
    "CERTIFICATE_REJECTED": "verify.elimination_section",
    "VERIFIED_GROEBNER": "verify.elimination_groebner",
    "GROEBNER_CERTIFICATE_REJECTED": "verify.elimination_groebner",
}

_FINGERPRINT_RE = re.compile(r"^sha256:[0-9a-f]{64}$")

# Verdict projection mutates the folded target.  None of those computed fields
# may feed its own input fingerprint, or a verdict would become stale at the
# instant it was applied.
_COMPUTED_FIELDS = {
    "identity_verdict", "identity_why",
    "containment", "containment_why",
    "certificate_verdict", "certificate_why",
    "ring_iso_verdict", "ring_iso_why",
    "witness_verdict", "witness_why",
    "output_verdict", "output_why",
    "contraction_verdict", "contraction_why",
    "contraction_representation",
    "point_lift_verdict", "point_lift_why",
    "point_lift_representation",
    "exhaustive_verdict", "exhaustive_why",
    "representation",
}

# Lifecycle annotations are derived only after the event fold.  Active objects
# have none when verified; including them would make fingerprints depend on
# whether supersession resolution happened before or after an otherwise
# identical read.
_LIFECYCLE_FIELDS = {
    "superseded_by", "retracted_by", "withdrawn_by",
}


def _semantic(record):
    """Return the declared, verifier-relevant form of one folded record."""
    if record is None:
        return None
    return {
        key: value
        for key, value in record.items()
        if key not in _COMPUTED_FIELDS and key not in _LIFECYCLE_FIELDS
    }


def input_payload(graph, subject, of):
    """The complete graph input consumed by one verifier subject.

    The payload names records, rather than selecting a hand-maintained subset
    of fields.  Adding a new declaration field therefore invalidates old
    verdicts conservatively until the verifier is rerun.
    """
    if subject in (
            "edge", "ring_iso", "operation", "elimination", "point_lift"):
        edge = graph.edges.get(of)
        return {
            "subject": subject,
            "of": of,
            "edge": _semantic(edge),
            "src": _semantic(graph.models.get(edge.get("src"))) if edge else None,
            "dst": _semantic(graph.models.get(edge.get("dst"))) if edge else None,
        }
    if subject in ("claim", "certificate", "witness"):
        claim = graph.claims.get(of)
        return {
            "subject": subject,
            "of": of,
            "claim": _semantic(claim),
            "model": (
                _semantic(graph.models.get(claim.get("model")))
                if claim else None
            ),
        }
    if subject == "partition":
        partition = graph.partitions.get(of)
        branches = partition.get("branches") or [] if partition else []
        return {
            "subject": subject,
            "of": of,
            "partition": _semantic(partition),
            "parent": (
                _semantic(graph.models.get(partition.get("parent")))
                if partition else None
            ),
            "branches": [
                {"id": bid, "model": _semantic(graph.models.get(bid))}
                for bid in branches
            ],
        }
    raise ValueError("unknown verdict subject %r" % subject)


def input_fingerprint(graph, subject, of, representation=None):
    """Stable SHA-256 of the canonical semantic verifier input."""
    payload = input_payload(graph, subject, of)
    # A proof object is part of what was checked, not an annotation on the
    # answer. Binding it here makes any later certificate mutation stale.
    if representation is not None:
        payload["verifier_evidence"] = representation
    encoded = json.dumps(
        payload,
        sort_keys=True,
        separators=(",", ":"),
        ensure_ascii=True,
    ).encode("utf-8")
    return "sha256:" + hashlib.sha256(encoded).hexdigest()


def event_fingerprint(value):
    """Stable SHA-256 for an execution trace or other provenance payload."""
    encoded = json.dumps(
        value, sort_keys=True, separators=(",", ":"), ensure_ascii=True
    ).encode("utf-8")
    return "sha256:" + hashlib.sha256(encoded).hexdigest()


def event_digest(event):
    """Content address one complete verdict event, excluding only its id."""
    payload = {key: value for key, value in event.items() if key != "id"}
    encoded = json.dumps(
        payload, sort_keys=True, separators=(",", ":"), ensure_ascii=True
    ).encode("utf-8")
    return hashlib.sha256(encoded).hexdigest()[:16]


_BACKEND_PREFIX = "gp-backend-v2:"
BACKEND_PROVENANCE_PREFIX = _BACKEND_PREFIX
_SYMBOL = re.compile(r"[A-Za-z_][A-Za-z0-9_]*")


def _active_model(graph, mid):
    model = graph.models.get(mid)
    return model if model and not model.get("superseded_by") else None


def _eligible_structural_containment(graph, eid):
    edge = graph.edges.get(eid)
    if (not edge or edge.get("superseded_by")
            or K.is_mapped_equivalence(edge)
            or edge.get("type") == K.SPECIALIZATION):
        return False
    source = _active_model(graph, edge.get("src"))
    target = _active_model(graph, edge.get("dst"))
    if not source or not target:
        return False
    if (source.get("ideal_pending") or target.get("ideal_pending")
            or source.get("generators") is None
            or target.get("generators") is None):
        return False
    ring = source.get("ring_vars") or []
    if (not ring or "characteristic" not in source
            or "characteristic" not in target
            or source["characteristic"] != target["characteristic"]
            or set(target.get("ring_vars") or []) != set(ring)):
        return False
    target_generators = target["generators"]
    if target_generators == []:
        return True
    source_generators = source["generators"]
    if not all(generator in source_generators
               for generator in target_generators):
        return False
    try:
        for generator in target_generators:
            G.parse_polynomial(
                generator, ring, source["characteristic"])
    except G.CertificateError:
        return False
    return True


def _eligible_structural_operation(graph, event):
    edge = graph.edges.get(event.get("of"))
    if not edge or edge.get("superseded_by"):
        return False
    kind = edge.get("built_by_operation")
    if kind not in ("SaturateClosure", "Eliminate"):
        return False
    built_id = edge.get("src") if kind == "SaturateClosure" else edge.get("dst")
    source_id = edge.get("dst") if kind == "SaturateClosure" else edge.get("src")
    built = _active_model(graph, built_id)
    source = _active_model(graph, source_id)
    if not built or not source:
        return False
    if (built.get("ideal_pending") or source.get("ideal_pending")
            or built.get("generators") is None
            or source.get("generators") is None):
        return False
    if (not (source.get("ring_vars") or [])
            or "characteristic" not in source
            or "characteristic" not in built
            or source["characteristic"] != built["characteristic"]):
        return False
    generators = built["generators"]
    if kind == "SaturateClosure" and not built.get("saturated_at"):
        return False
    if kind == "Eliminate":
        ring = source.get("ring_vars") or []
        eliminated = built.get("eliminated")
        if (not isinstance(eliminated, list) or not eliminated
                or len(eliminated) != len(set(eliminated))
                or any(variable not in ring for variable in eliminated)):
            return False
        if (built.get("ring_vars") or []) != [
                variable for variable in ring
                if variable not in set(eliminated)]:
            return False
    if event.get("verdict") == "VERIFIED":
        return generators == []
    if (event.get("verdict") != "NOT_THE_STATED_OUTPUT"
            or kind != "Eliminate"):
        return False
    kept = set(built.get("ring_vars") or [])
    return bool(generators) and all(
        any(symbol not in kept for symbol in _SYMBOL.findall(str(generator)))
        for generator in generators
    )


def _eligible_structural_elimination(graph, event):
    """A section over the zero source ideal is a proof without a CAS run."""
    if event.get("verdict") != "VERIFIED_SECTION":
        # Rejections and inability to pose a check grant no authority, but are
        # still legitimate verifier-native history when validation stops
        # before spawning a backend process.
        return event.get("verdict") in ("CERTIFICATE_REJECTED", "UNVERIFIED")
    edge = graph.edges.get(event.get("of")) or {}
    source = _active_model(graph, edge.get("src")) or {}
    target = _active_model(graph, edge.get("dst")) or {}
    rep = event.get("representation") or {}
    eliminated = target.get("eliminated")
    source_ring = source.get("ring_vars") or []
    return (
        edge.get("built_by_operation") == "Eliminate"
        and source.get("generators") == []
        and target.get("generators") is not None
        and isinstance(eliminated, list) and bool(eliminated)
        and target.get("ring_vars") == [
            v for v in source_ring if v not in set(eliminated)]
        and rep.get("method") == "polynomial_section_v1"
        and rep.get("rows") == []
        and set(rep.get("section") or {}) == set(eliminated)
    )

def _eligible_structural_ring_iso(graph, event):
    """An exact cofactor envelope is verifier-native, not an empty CAS run."""
    if (event.get("subject") != "ring_iso"
            or event.get("verdict") != "VERIFIED"):
        return False
    edge = graph.edges.get(event.get("of")) or {}
    certificate = edge.get("ring_iso_certificate") or {}
    return (
        edge.get("ring_iso") is True
        and isinstance(edge.get("forward"), dict)
        and isinstance(edge.get("inverse"), dict)
        and certificate.get("schema") == "mapped_ring_iso_v1"
    )

def _allows_empty_structural_trace(graph, event):
    """Recognize eligible verifier-native decisions with no backend run."""
    if event.get("verdict") == "UNVERIFIED":
        return True
    if event.get("subject") == "edge" and event.get("verdict") == "VERIFIED":
        return _eligible_structural_containment(graph, event.get("of"))
    if event.get("subject") == "ring_iso":
        return _eligible_structural_ring_iso(graph, event)
    if event.get("subject") == "operation":
        return _eligible_structural_operation(graph, event)
    if event.get("subject") == "elimination":
        return _eligible_structural_elimination(graph, event)
    return False

def encode_backend_provenance(execution):
    """Encode a versioned manifest inside the format-1 `backend` string."""
    if not isinstance(execution, dict):
        raise ValueError("execution provenance must be an explicit manifest")
    return _BACKEND_PREFIX + json.dumps(
        execution, sort_keys=True, separators=(",", ":"), ensure_ascii=True
    )


def backend_provenance(value, current_only=True):
    """Decode and validate a v2 backend descriptor, or return ``None``."""
    if not isinstance(value, str) or not value.startswith(_BACKEND_PREFIX):
        return None
    try:
        manifest = json.loads(value[len(_BACKEND_PREFIX):])
    except (TypeError, ValueError):
        return None
    if not isinstance(manifest, dict):
        return None
    required = {
        "schema", "contract", "implementation", "implementation_version",
        "protocol_version", "binary_version", "executions",
        "trace_fingerprint",
    }
    if set(manifest) != required:
        return None
    if manifest["schema"] != 2:
        return None
    if (not isinstance(manifest["contract"], str)
            or not manifest["contract"]
            or not isinstance(manifest["implementation"], str)
            or not manifest["implementation"]
            or type(manifest["implementation_version"]) is not int
            or manifest["implementation_version"] < 1
            or type(manifest["protocol_version"]) is not int
            or manifest["protocol_version"] < 1):
        return None
    if current_only and (
            manifest["contract"] != B.SINGULAR_CONTRACT
            or manifest["implementation"] != B.SINGULAR_IMPLEMENTATION
            or manifest["implementation_version"]
            != B.SINGULAR_IMPLEMENTATION_VERSION
            or manifest["protocol_version"] != B.BACKEND_PROTOCOL_VERSION):
        return None
    version = manifest["binary_version"]
    if (not isinstance(version, str) or not version.strip()
            or version.startswith("unavailable:")
            or version in ("unreported", "test-double")):
        return None
    trace = manifest["executions"]
    if (not isinstance(trace, list)
            or not all(B.valid_execution_trace_entry(entry)
                       for entry in trace)):
        return None
    expected = B.semantic_fingerprint("backend_execution_trace", trace)
    if manifest["trace_fingerprint"] != expected:
        return None
    return manifest


def metadata(graph, subject, of, execution=None, representation=None,
             verifier=None, verdict=None):
    """Provenance fields attached to a newly computed verdict event."""
    if execution is None:
        raise ValueError(
            "verdict v2 needs explicit execution provenance; an absent run "
            "cannot be replaced by a fabricated empty trace"
        )
    default_verifier, default_version = VERIFIERS[subject]
    verifier = verifier or (
        _certificate_verifier(graph, of)
        if subject == "certificate" else default_verifier)
    alternatives = VERIFIER_ALTERNATIVES.get(subject, {
        default_verifier: default_version,
    })
    if verifier not in alternatives:
        raise ValueError(
            "verifier %r cannot discharge subject %r" % (verifier, subject)
        )
    verifier_version = alternatives[verifier]
    required_verifier = (
        ELIMINATION_VERDICT_VERIFIER.get(verdict)
        if subject == "elimination" else None
    )
    if subject == "certificate":
        required_verifier = _certificate_verifier(graph, of)
    if required_verifier is not None and verifier != required_verifier:
        raise ValueError(
            "%s verdict must be produced by %s, not %s"
            % (verdict, required_verifier, verifier)
        )
    return {
        "verifier": verifier,
        "verifier_version": verifier_version,
        "kernel_epoch": F.KERNEL_EPOCH,
        "backend": encode_backend_provenance(execution),
        "input_fingerprint": input_fingerprint(
            graph, subject, of, representation=representation),
    }

def current_verdict(graph, event):
    """Return ``(is_current, reason)`` for a stored verdict event.

    Missing metadata is the epoch-0 form.  It remains valid log history but is
    deliberately inactive.  Mismatches are handled the same way: stale
    evidence must never overwrite a current verdict or license transport.
    """
    if getattr(graph, "graph_format", 0) != F.GRAPH_FORMAT:
        return False, "epoch-0 verdicts are compatibility history only"
    subject = event.get("subject")
    if subject not in VERIFIERS:
        return False, "unknown verifier subject"
    default_verifier, default_version = VERIFIERS[subject]
    alternatives = VERIFIER_ALTERNATIVES.get(subject, {
        default_verifier: default_version,
    })
    required = (
        "verifier", "verifier_version", "kernel_epoch",
        "backend", "input_fingerprint",
    )
    missing = [field for field in required if event.get(field) is None]
    if missing:
        return False, "legacy verdict lacks %s" % ", ".join(missing)
    expected_version = alternatives.get(event.get("verifier"))
    if expected_version is None:
        return False, "verifier identity does not match"
    required_verifier = (
        ELIMINATION_VERDICT_VERIFIER.get(event.get("verdict"))
        if subject == "elimination" else None
    )
    if subject == "certificate":
        required_verifier = _certificate_verifier(
            graph, event.get("of"))
    if (required_verifier is not None
            and event.get("verifier") != required_verifier):
        return False, "verifier identity does not match verdict method"
    if event.get("verifier_version") != expected_version:
        return False, "verifier version does not match"
    if event.get("kernel_epoch") != F.KERNEL_EPOCH:
        return False, "kernel epoch does not match"
    manifest = backend_provenance(event.get("backend"))
    if manifest is None:
        return False, "backend execution provenance is absent or invalid"
    if (not manifest["executions"]
            and not _allows_empty_structural_trace(graph, event)):
        return False, (
            "authoritative %s verdict lacks a backend execution trace and "
            "is not a verifier-native structural decision" % subject)
    fingerprint = event.get("input_fingerprint")
    if not isinstance(fingerprint, str) or not _FINGERPRINT_RE.match(fingerprint):
        return False, "input fingerprint is malformed"
    if fingerprint != input_fingerprint(
            graph, subject, event.get("of"),
            representation=event.get("representation")):
        return False, "verifier input fingerprint does not match"
    return True, "current"
