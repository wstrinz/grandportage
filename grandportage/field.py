"""Pure epoch-12 field-context and certificate-reach decisions.

This module deliberately contains no graph, verifier, or process boundary.
It distinguishes concrete field extension from quantified certificate
instantiation; callers must separately establish witness transport.
"""

from dataclasses import dataclass
import re


Q = "Q"
R = "R"
C = "C"
ANY_ORDERED = "ANY_ORDERED"
ANY_CHAR_0 = "ANY_CHAR_0"

ORDERED = "ORDERED"
CHAR_0 = "CHAR_0"
FIELD_SPECIFIC = "FIELD_SPECIFIC"
NONE = "NONE"

POINT_UNIVERSES = ("BASE", "ALGEBRAIC_CLOSURE", "REAL_CLOSURE")
REACH_KINDS = (ORDERED, CHAR_0, FIELD_SPECIFIC, NONE)

_FINITE = re.compile(r"^F_([0-9]+)$")


class FieldError(ValueError):
    """A field context or reach object is malformed."""


@dataclass(frozen=True)
class Decision:
    allowed: bool
    reason: str


def _prime(value):
    if value < 2:
        return False
    if value % 2 == 0:
        return value == 2
    divisor = 3
    while divisor * divisor <= value:
        if value % divisor == 0:
            return False
        divisor += 2
    return True


def is_field_atom(value, universal=True):
    """Whether ``value`` belongs to the closed v1 about vocabulary."""
    if value in (Q, R, C):
        return True
    if universal and value in (ANY_ORDERED, ANY_CHAR_0):
        return True
    if not isinstance(value, str):
        return False
    match = _FINITE.fullmatch(value)
    return bool(match and len(match.group(1)) <= 10
                and _prime(int(match.group(1))))


def validate_about(value):
    if not is_field_atom(value):
        raise FieldError(
            "about must be Q, R, C, ANY_ORDERED, ANY_CHAR_0, or F_p "
            "for prime p")
    return value


def validate_compute_in(value):
    if value == Q:
        return value
    if is_field_atom(value, universal=False) and str(value).startswith("F_"):
        return value
    raise FieldError("compute_in supports only Q or a prime field F_p")


def model_compute_in(model):
    """Resolve the alias without accepting contradictory duplicate fields."""
    old = model.get("coefficient_domain")
    new = model.get("compute_in")
    if old is not None and new is not None and old != new:
        raise FieldError(
            "compute_in and coefficient_domain must be identical when both "
            "are declared")
    value = new if new is not None else old
    if value is None:
        return None
    return validate_compute_in(value)


def concrete_extension(source, target):
    """Decide the bounded canonical inclusion between concrete field atoms."""
    if not is_field_atom(source, universal=False):
        return Decision(False, "%r is not a concrete source field" % source)
    if not is_field_atom(target, universal=False):
        return Decision(False, "%r is not a concrete target field" % target)
    if source == target:
        return Decision(True, "the concrete field contexts are identical")
    if source == Q and target in (R, C):
        return Decision(True, "the canonical characteristic-zero inclusion applies")
    if source == R and target == C:
        return Decision(True, "the canonical real-to-complex inclusion applies")
    return Decision(False, "no compatible concrete inclusion is in the v1 table")


def validate_reach(value):
    if not isinstance(value, dict):
        raise FieldError("reach must be a closed object")
    kind = value.get("kind")
    expected = {"kind", "field"} if kind == FIELD_SPECIFIC else {"kind"}
    if kind not in REACH_KINDS or set(value) != expected:
        raise FieldError(
            "reach must be ORDERED, CHAR_0, FIELD_SPECIFIC(field), or NONE")
    if kind == FIELD_SPECIFIC:
        field = value.get("field")
        if not is_field_atom(field, universal=False):
            raise FieldError("FIELD_SPECIFIC reach must name a concrete field")
    return dict(value)


def reach_for_exact_identity(compute_in):
    """Reach earned by an exact coefficient identity in its checked domain."""
    compute_in = validate_compute_in(compute_in)
    if compute_in == Q:
        return {"kind": CHAR_0}
    return {"kind": FIELD_SPECIFIC, "field": compute_in}


def instantiate(reach, target):
    """Whether checked quantified reach applies to one target field atom."""
    reach = validate_reach(reach)
    if not is_field_atom(target):
        return Decision(False, "the target field context is missing or malformed")
    kind = reach["kind"]
    if kind == NONE:
        return Decision(False, "NONE carries no EMPTY authority")
    if kind == FIELD_SPECIFIC:
        return Decision(
            target == reach["field"],
            "the target matches the checked field"
            if target == reach["field"] else
            "FIELD_SPECIFIC reach does not match the target")
    if kind == ORDERED:
        allowed = target in (Q, R, ANY_ORDERED)
        return Decision(
            allowed,
            "the target is ordered" if allowed else
            "ORDERED reach does not apply to this target")
    allowed = target in (Q, R, C, ANY_ORDERED, ANY_CHAR_0)
    return Decision(
        allowed,
        "the target has characteristic zero" if allowed else
        "CHAR_0 reach does not apply to positive characteristic")


def compatible_point_context(source, target):
    """Conservative context gate before any claim-specific point replay."""
    if not isinstance(source, dict) or not isinstance(target, dict):
        return Decision(False, "both point contexts must be explicit objects")
    for label, context in (("source", source), ("target", target)):
        if not is_field_atom(context.get("about"), universal=False):
            return Decision(False, "%s about is not a concrete field" % label)
        if context.get("point_universe") not in POINT_UNIVERSES:
            return Decision(False, "%s point_universe is missing or unknown" % label)
    extension = concrete_extension(source["about"], target["about"])
    if not extension.allowed:
        return extension
    if source["point_universe"] != target["point_universe"]:
        return Decision(
            False, "point universes differ; an independently verified map is required")
    if source.get("embedding") != target.get("embedding"):
        return Decision(
            False, "selected embeddings differ; an independently verified map is required")
    return Decision(True, "field, point universe, and selected embedding are compatible")
