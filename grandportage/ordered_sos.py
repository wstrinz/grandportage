"""Backend-free replay of rational SOS/cofactor infeasibility certificates."""

from . import groebner as G


METHOD = "rational_sos_cofactor_v1"
_MAX_SQUARES = 256


class OrderedSOSError(ValueError):
    pass


def verify(model, certificate):
    """Replay ``-1 = sum s_j^2 + sum h_i f_i`` exactly over Q.

    The proof object supplies every square and cofactor.  This function performs
    no search and invokes no external algebra backend.
    """
    if not isinstance(model, dict):
        raise OrderedSOSError("the checked model must be an object")
    compute_in = model.get("compute_in", model.get("coefficient_domain"))
    if model.get("characteristic") != 0 or compute_in != "Q":
        raise OrderedSOSError("rational SOS replay requires computation over Q")
    variables = model.get("ring_vars")
    generators = model.get("generators")
    if (not isinstance(variables, list) or not variables
            or not isinstance(generators, list)
            or not all(isinstance(value, str) for value in generators)):
        raise OrderedSOSError(
            "the model must carry ring_vars and polynomial-string generators")
    required = {"method", "ring_vars", "generators", "squares", "cofactors"}
    if not isinstance(certificate, dict) or set(certificate) != required:
        raise OrderedSOSError(
            "an ordered certificate must be the closed rational_sos_cofactor_v1 object")
    if certificate.get("method") != METHOD:
        raise OrderedSOSError("ordered certificate method must be %s" % METHOD)
    if certificate.get("ring_vars") != variables:
        raise OrderedSOSError("ordered certificate ring_vars do not match the model")
    if certificate.get("generators") != generators:
        raise OrderedSOSError("ordered certificate generators do not match the model")
    squares = certificate.get("squares")
    cofactors = certificate.get("cofactors")
    if (not isinstance(squares, list) or len(squares) > _MAX_SQUARES
            or not all(isinstance(value, str) and value.strip()
                       for value in squares)):
        raise OrderedSOSError("squares must be at most 256 polynomial strings")
    if (not isinstance(cofactors, list)
            or len(cofactors) != len(generators)
            or not all(isinstance(value, str) and value.strip()
                       for value in cofactors)):
        raise OrderedSOSError(
            "cofactors must give one polynomial string per model generator")
    try:
        normalized_squares = [
            G.canonical_polynomial(value, variables, 0) for value in squares
        ]
        normalized_generators = [
            G.canonical_polynomial(value, variables, 0) for value in generators
        ]
        normalized_cofactors = [
            G.canonical_polynomial(value, variables, 0) for value in cofactors
        ]
        sum_of_squares = " + ".join(
            "(%s)^2" % value for value in normalized_squares
        ) or "0"
        target = "-1 - (%s)" % sum_of_squares
        G.check_membership_identity(
            target, normalized_generators, normalized_cofactors, variables, 0)
    except (G.CertificateError, TypeError, ValueError) as exc:
        raise OrderedSOSError("ordered SOS/cofactor identity is invalid: %s" % exc)
    return {
        "method": METHOD,
        "ring_vars": list(variables),
        "generators": normalized_generators,
        "squares": normalized_squares,
        "cofactors": normalized_cofactors,
    }
