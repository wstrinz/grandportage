"""Bounded Singular producer for backend-neutral elimination certificates.

This module is deliberately outside the trusted checker.  Singular discovers a
pure-lex basis and ideal-span witnesses; every transcript value is parsed and
canonically re-emitted before reuse, and :mod:`grandportage.groebner` checks the
finished proof without executing a backend.
"""

import re
import time

from . import backend as B
from . import cas
from . import groebner as G


def _strict_indexed_polynomials(value, name, variables, characteristic,
                                expected=None, maximum=None, _budget=None):
    """Parse exactly ``NAME[1]..NAME[n]`` and make every value inert."""
    rows = value if isinstance(value, list) else [value]
    if maximum is not None and len(rows) > maximum:
        raise cas.CASError(
            "%s has %d rows; the producer limit is %d"
            % (name, len(rows), maximum)
        )
    pattern = re.compile(
        r"^%s\[([1-9][0-9]*)\][ \t]*=[ \t]*(.+)$" % re.escape(name)
    )
    parsed = {}
    for line in rows:
        match = pattern.fullmatch(str(line).strip())
        if match is None:
            raise cas.CASError(
                "%s contains a malformed indexed polynomial row: %r"
                % (name, line)
            )
        index = int(match.group(1))
        if index in parsed:
            raise cas.CASError("%s repeats row %d" % (name, index))
        try:
            parsed[index] = G.canonical_polynomial(
                match.group(2), variables, characteristic, _budget
            )
        except G.CertificateError as exc:
            raise cas.CASError(
                "%s row %d is outside the exact polynomial language: %s"
                % (name, index, exc)
            )
    count = len(parsed) if expected is None else expected
    if set(parsed) != set(range(1, count + 1)):
        raise cas.CASError(
            "%s must contain exactly the contiguous rows 1..%d"
            % (name, count)
        )
    return [parsed[index] for index in range(1, count + 1)]


def _strict_matrix(value, name, row_count, column_count, variables,
                   characteristic, _budget=None):
    """Parse one fully printed Singular matrix with no implicit padding."""
    rows = value if isinstance(value, list) else [value]

    pattern = re.compile(
        r"^%s\[([1-9][0-9]*),([1-9][0-9]*)\][ \t]*=[ \t]*(.+)$"
        % re.escape(name)
    )
    parsed = {}
    for line in rows:
        match = pattern.fullmatch(str(line).strip())
        if match is None:
            raise cas.CASError(
                "%s contains a malformed matrix row: %r" % (name, line)
            )
        position = (int(match.group(1)), int(match.group(2)))
        if position in parsed:
            raise cas.CASError("%s repeats matrix cell %s" % (name, position))
        if not (1 <= position[0] <= row_count
                and 1 <= position[1] <= column_count):
            raise cas.CASError(
                "%s contains out-of-bounds cell %s" % (name, position)
            )
        try:
            parsed[position] = G.canonical_polynomial(
                match.group(3), variables, characteristic, _budget
            )
        except G.CertificateError as exc:
            raise cas.CASError(
                "%s cell %s is outside the exact polynomial language: %s"
                % (name, position, exc)
            )
    expected = {
        (row, column)
        for row in range(1, row_count + 1)
        for column in range(1, column_count + 1)
    }
    if set(parsed) != expected:
        raise cas.CASError(
            "%s must print exactly its %d-by-%d cells; missing or additional "
            "cells are not interpreted as zero"
            % (name, row_count, column_count)
        )
    return [
        [parsed[(row, column)] for column in range(1, column_count + 1)]
        for row in range(1, row_count + 1)
    ]


def _remaining(deadline):
    remaining = deadline - time.monotonic()
    if remaining <= 0:
        raise cas.CASError("certificate production exceeded its total timeout")
    return remaining


def produce_elimination_groebner(backend, ring_vars, source_generators,
                                 eliminated, target_generators,
                                 characteristic=0, timeout=300):
    """Produce and independently check ``groebner_elimination_v1`` evidence.

    ``target_generators=None`` is the certifying-materializer mode: the
    retained part of the discovered pure-lex basis becomes the target ideal.
    Supplying a target remains the older verification mode and is unchanged.
    """
    if not isinstance(backend, cas.SingularBackend):
        raise TypeError("the v1 producer requires a SingularBackend")
    if (isinstance(timeout, bool)
            or not isinstance(timeout, (int, float)) or timeout <= 0):
        raise ValueError("timeout must be a positive number of seconds")
    deadline = time.monotonic() + timeout
    budget = G._ArithmeticBudget()
    ring_vars = list(ring_vars)
    source_generators = list(source_generators)
    eliminated = list(eliminated)
    discover_target = target_generators is None
    target_generators = (
        [] if discover_target else list(target_generators)
    )
    if len(ring_vars) > G._MAX_VARIABLES:
        raise cas.CASError(
            "producer input exceeds the %d-variable limit" % G._MAX_VARIABLES
        )
    if (len(source_generators) > G._MAX_GENERATORS
            or len(target_generators) > G._MAX_GENERATORS):
        raise cas.CASError(
            "producer input exceeds the %d-generator limit"
            % G._MAX_GENERATORS
        )
    if not source_generators:
        raise cas.CASError(
            "groebner_elimination_v1 does not produce a basis for the zero "
            "source ideal; use the structural polynomial-section route"
        )
    if (not eliminated or len(eliminated) != len(set(eliminated))
            or any(value not in ring_vars for value in eliminated)):
        raise cas.CASError("eliminated must be a nonempty unique ring subset")
    eliminated_set = set(eliminated)
    ordered_eliminated = [
        value for value in ring_vars if value in eliminated_set
    ]
    retained = [value for value in ring_vars if value not in eliminated_set]
    if not retained:
        raise cas.CASError("elimination cannot remove every ring variable")
    variables = ordered_eliminated + retained
    try:
        safe_source = [
            G.canonical_polynomial(
                expression, variables, characteristic, budget
            )
            for expression in source_generators
        ]
        for expression in target_generators:
            parsed = G.parse_polynomial(
                expression, variables, characteristic, budget
            )
            if parsed.uses_any(range(len(ordered_eliminated))):
                raise G.CertificateError(
                    "target generator uses an eliminated variable"
                )
    except G.CertificateError as exc:
        raise cas.CASError("invalid exact elimination input: %s" % exc)

    phase1 = cas.CASProgram(
        cas.SINGULAR,
        ring="GP_R",
        ring_vars=variables,
        decls=[
            ("GP_F", "ideal", ",".join(safe_source)),
            ("GP_A", "matrix", "0"),
            ("GP_G", "ideal", "liftstd(GP_F,GP_A)"),
            ("GP_B", "matrix", "lift(GP_G,GP_F)"),
        ],
        body=[],
        outputs=["GP_G", "GP_B"],
        characteristic=characteristic,
        ordering="lp",
    )
    phase1_input = {
        "operation": "produce_groebner_elimination_v1",
        "target_selection": (
            "retained_pure_lex_basis" if discover_target else "declared_ideal"
        ),
        "phase": "basis_and_source_span",
        "characteristic": characteristic,
        "ring_vars": variables,
        "eliminated": ordered_eliminated,
        "source_generators": source_generators,
        "target_generators": target_generators,
        "ordering": "lp",
    }
    first = backend.execute(
        phase1, timeout=_remaining(deadline), semantic_input=phase1_input
    )
    cas._require_success(first, "Groebner elimination basis production")
    first_values = cas._parse_result(first, phase1.outputs)
    basis = _strict_indexed_polynomials(
        first_values["GP_G"], "GP_G", variables, characteristic,
        maximum=G._MAX_BASIS, _budget=budget
    )
    if not basis or len(basis) > G._MAX_BASIS:
        raise cas.CASError(
            "producer basis must contain 1..%d nonzero polynomials"
            % G._MAX_BASIS
        )
    if any(value == "0" for value in basis):
        raise cas.CASError("producer basis contains the zero polynomial")
    source_matrix = _strict_matrix(
        first_values["GP_B"], "GP_B", len(basis),
        len(source_generators), variables, characteristic, budget
    )
    source_in_basis = [
        [source_matrix[row][column] for row in range(len(basis))]
        for column in range(len(source_generators))
    ]

    critical_pairs = []
    for left in range(len(basis)):
        for right in range(left + 1, len(basis)):
            _remaining(deadline)
            try:
                s_value = G.s_polynomial(
                    basis[left], basis[right], variables, characteristic,
                    budget
                )
                reducers = G.standard_representation(
                    s_value, basis, variables, characteristic, budget
                )
            except G.CertificateError as exc:
                raise cas.CASError(
                    "the proposed lex basis failed standard reduction for "
                    "pair (%d,%d): %s" % (left, right, exc)
                )
            critical_pairs.append({
                "i": left, "j": right, "reducers": reducers,
            })

    retained_basis = G.retained_basis(
        basis, variables, ordered_eliminated, characteristic, budget
    )
    if discover_target:
        target_generators = list(retained_basis)
    retained_in_target = []
    last = first
    last_values = first_values
    if retained_basis:
        if not target_generators:
            raise cas.CASError(
                "a nonzero retained lex-basis element cannot be represented "
                "in the recorded zero target ideal"
            )
        safe_target = [
            G.canonical_polynomial(value, retained, characteristic, budget)
            for value in target_generators
        ]
        safe_retained = [
            G.canonical_polynomial(value, retained, characteristic, budget)
            for value in retained_basis
        ]
        phase2 = cas.CASProgram(
            cas.SINGULAR,
            ring="GP_R",
            ring_vars=retained,
            decls=[
                ("GP_J", "ideal", ",".join(safe_target)),
                ("GP_H", "ideal", ",".join(safe_retained)),
                ("GP_M", "matrix", "lift(GP_J,GP_H)"),
            ],
            body=[],
            outputs=["GP_M"],
            characteristic=characteristic,
            ordering="lp",
        )
        phase2_input = {
            "operation": "produce_groebner_elimination_v1",
            "phase": "retained_target_span",
            "characteristic": characteristic,
            "ring_vars": retained,
            "eliminated": ordered_eliminated,
            "source_generators": source_generators,
            "target_generators": target_generators,
            "basis": basis,
            "retained_basis": retained_basis,
            "phase1_artifact": B.execution_artifact_fingerprint(first.artifact),
            "ordering": "lp",
        }
        second = backend.execute(
            phase2, timeout=_remaining(deadline), semantic_input=phase2_input
        )
        cas._require_success(
            second, "retained elimination membership production"
        )
        second_values = cas._parse_result(second, phase2.outputs)
        retained_matrix = _strict_matrix(
            second_values["GP_M"], "GP_M", len(target_generators),
            len(retained_basis), retained, characteristic, budget
        )
        retained_in_target = [
            [retained_matrix[row][column]
             for row in range(len(target_generators))]
            for column in range(len(retained_basis))
        ]
        last = second
        last_values = second_values

    proof = {
        "method": "groebner_elimination_v1",
        "characteristic": characteristic,
        "ring_vars": variables,
        "eliminated": ordered_eliminated,
        "source_generators": source_generators,
        "basis": basis,
        "target_generators": target_generators,
        "source_in_basis": source_in_basis,
        "critical_pairs": critical_pairs,
        "retained_in_target": retained_in_target,
    }
    _remaining(deadline)
    try:
        checked = G.check_elimination_certificate(proof)
    except G.CertificateError as exc:
        raise cas.CASError(
            "the generated proof failed the independent exact checker: %s"
            % exc
        )
    _remaining(deadline)
    # Bind the checked proof into the final immutable execution artifact.
    last.attach_parsed(last_values, certificate=proof)
    return {
        "proof": proof,
        "checked": checked,
        "basis_program": phase1,
        "last_execution": last,
    }


def produce_retained_elimination_groebner(
        backend, ring_vars, source_generators, eliminated,
        characteristic=0, timeout=300):
    """Discover and certify the pure-lex retained elimination basis.

    This is deliberately narrower than a general elimination constructor.
    The target generators are not accepted from a caller or from an earlier
    unverified CAS run: they are exactly the retained basis certified by the
    returned proof.
    """
    return produce_elimination_groebner(
        backend, ring_vars, source_generators, eliminated, None,
        characteristic=characteristic, timeout=timeout,
    )
