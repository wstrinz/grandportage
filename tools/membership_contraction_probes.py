"""Bounded offline candidate-matrix and one-way-contraction probes."""
from grandportage import cas, groebner as G


def _membership(case):
    d = case["inputs"]
    matrix = "\n".join(d["matrix_rows"])

    def runner(program, timeout):
        body = "@@GP_RED:\n0" if program.outputs == ["GP_RED"] else "@@GP_M:\n" + matrix
        return {
            "returncode": 0, "aborted": False,
            "stdout": body + "\n" + program.completion_marker + "\n",
            "stderr": "", "argv": ["injected"],
        }

    backend = cas.SingularBackend(runner=runner, binary_version="test-double")
    candidate = backend.membership(d["ring_vars"], d["target"], d["generators"])
    attached = backend.executions[-1].artifact.certificate is not None
    try:
        exact = G.check_membership_identity(
            d["target"], d["generators"], candidate["cofactors"], d["ring_vars"])
        exact_accepts, exact_error = True, None
    except G.CertificateError as exc:
        exact, exact_accepts, exact_error = None, False, str(exc)
    accepted = bool(candidate["is_member"] and attached and exact_accepts)
    return {
        "observed_verdict": "ACCEPT" if accepted else "REFUSE",
        "reason": ("Candidate identity verifies by exact expansion."
                   if accepted else exact_error or "No checked membership candidate."),
        "producer_is_member": candidate["is_member"],
        "candidate_cofactors": candidate["cofactors"],
        "attached_candidate_certificate": attached,
        "exact_checker_accepts": exact_accepts,
        "exact_checker_result": exact,
        "can_record_verdicts": backend.can_record_verdicts,
        "external_execution": False,
    }


def _contraction(case):
    d = case["inputs"]
    cert = d["certificate"]
    try:
        forward = G.check_elimination_certificate(cert)
        forward_accepts, forward_error = True, None
    except G.CertificateError as exc:
        forward, forward_accepts, forward_error = None, False, str(exc)
    reverse_results = []
    for target, cofactors in zip(cert["target_generators"], d["reverse_cofactors"]):
        try:
            checked = G.check_membership_identity(
                target, cert["source_generators"], cofactors,
                cert["ring_vars"], cert["characteristic"])
            reverse_results.append({"target": target, "accepts": True, "checked": checked})
        except G.CertificateError as exc:
            reverse_results.append({"target": target, "accepts": False, "error": str(exc)})
    if len(reverse_results) != len(cert["target_generators"]):
        raise ValueError("Reverse witness count does not match target generators")
    requested = d["requested_conclusion"]
    if requested == "completeness_inclusion":
        accepted = forward_accepts
    elif requested == "exact_contraction":
        accepted = forward_accepts and all(row["accepts"] for row in reverse_results)
    else:
        raise ValueError("Unknown requested conclusion")
    return {
        "observed_verdict": "ACCEPT" if accepted else "REFUSE",
        "reason": ("Requested inclusion verifies." if accepted and requested == "completeness_inclusion"
                   else "Both exact inclusions verify." if accepted
                   else forward_error or next((r["error"] for r in reverse_results if not r["accepts"]), "Reverse inclusion lacks witnesses.")),
        "requested_conclusion": requested,
        "forward_inclusion_accepted": forward_accepts,
        "forward_checker_result": forward,
        "reverse_membership": reverse_results,
        "external_execution": False,
        "graph_admission": False,
    }


def probe(case, route):
    layer = route["layer"]
    if layer == "injected_candidate_exact_replay":
        return _membership(case)
    if layer == "elimination_and_reverse_identity":
        return _contraction(case)
    raise ValueError("Unknown membership/contraction layer")
