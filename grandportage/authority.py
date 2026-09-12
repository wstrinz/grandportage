"""Bind checked verifier evidence to current folded graph authority.

This module owns the small, internal transition between a verdict event whose
provenance is current and the computed fields that the checker may consume.  It
does not produce evidence, parse author declarations, or persist a new event
shape.  Subject-specific proof-object replay remains in ``store`` during the
first behavior-preserving extraction; ``bind`` is called only after that replay
succeeds.
"""

from dataclasses import dataclass, field

from . import provenance


_SEAL = object()


@dataclass(frozen=True)
class ContextBinding:
    """Exact versioned context in which verifier evidence was checked."""

    subject: str
    object_id: str
    input_fingerprint: str
    verifier: str
    verifier_version: int
    kernel_epoch: int
    execution_provenance: str


@dataclass(frozen=True)
class CheckedEvidence:
    """A current verdict admitted by provenance checking.

    The private seal prevents callers from constructing this value merely by
    importing the class.  Only ``check`` can mint it.
    """

    event_id: str
    verdict: str
    why: str
    context: ContextBinding
    _seal: object = field(repr=False, compare=False)

    def __post_init__(self):
        if self._seal is not _SEAL:
            raise TypeError("CheckedEvidence is minted only by authority.check")


@dataclass(frozen=True)
class AuthorityReceipt:
    """An internal, non-serialized license to project computed graph fields."""

    evidence: CheckedEvidence
    projections: tuple
    _seal: object = field(repr=False, compare=False)

    def __post_init__(self):
        if self._seal is not _SEAL:
            raise TypeError("AuthorityReceipt is minted only by authority.bind")


@dataclass(frozen=True)
class AuthorityRefusal:
    """Why evidence cannot become current projected authority."""

    reason: str


def _require_checked(evidence):
    if (not isinstance(evidence, CheckedEvidence)
            or evidence._seal is not _SEAL):
        raise TypeError("bind needs CheckedEvidence minted by authority.check")


def check(graph, event, check_binary_version=False):
    """Return sealed checked evidence, or a freshness/binding refusal."""

    current, reason = provenance.current_verdict(
        graph, event, check_binary_version=check_binary_version)
    if not current:
        return AuthorityRefusal(reason)
    context = ContextBinding(
        subject=event["subject"],
        object_id=event["of"],
        input_fingerprint=event["input_fingerprint"],
        verifier=event["verifier"],
        verifier_version=event["verifier_version"],
        kernel_epoch=event["kernel_epoch"],
        execution_provenance=event["backend"],
    )
    return CheckedEvidence(
        event_id=event["id"],
        verdict=event["verdict"],
        why=event["why"],
        context=context,
        _seal=_SEAL,
    )


def projects_authority(evidence):
    """Whether this current result changes the effective folded target.

    Rejected elimination and point-lift proof objects remain useful current
    history, but do not erase an earlier positive certificate on the edge.
    """

    _require_checked(evidence)
    subject = evidence.context.subject
    if subject == "elimination":
        return evidence.verdict in ("VERIFIED_SECTION", "VERIFIED_GROEBNER")
    if subject == "point_lift":
        return evidence.verdict == "VERIFIED_POINT_LIFT"
    return True


def bind(evidence, authority_field, why_field, extra_projections=()):
    """Mint one receipt after all subject-specific evidence replay succeeds."""

    _require_checked(evidence)
    if not projects_authority(evidence):
        return AuthorityRefusal(
            "%s %s is current history but grants no projected authority"
            % (evidence.context.subject, evidence.verdict))
    projections = (
        (authority_field, evidence.verdict),
        (why_field, evidence.why),
    ) + tuple(extra_projections)
    names = [name for name, _value in projections]
    if len(names) != len(set(names)):
        raise ValueError("authority receipt contains duplicate projections")
    return AuthorityReceipt(evidence, projections, _SEAL)


def project(receipt, target):
    """Apply a sealed receipt to one already-validated folded target record."""

    if (not isinstance(receipt, AuthorityReceipt)
            or receipt._seal is not _SEAL):
        raise TypeError("project needs AuthorityReceipt minted by authority.bind")
    for name, value in receipt.projections:
        target[name] = value
