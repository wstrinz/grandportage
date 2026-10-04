"""Exact reference arithmetic for a deleted dm4 zero-chart quantifier claim.

This is a transparent SymPy calculation on the three displayed equations,
not a pinned predecessor rational-lift verifier or a full v13 target check.
"""
import sympy as sp

DOCUMENT = {
    "path": "docs/JC-DM4-POLYNOMIAL-LIFT.md",
    "deletion_commit": "2cac30114573f7b6923c43d86fb22679c4dbedfb",
    "git_blob": "36e9e90cecee7209ef1098ca8f79118c02381bb6",
    "sha256": "b7674294174236b795081138306e3c7a086271047808e105d952f93a44f668d1",
}


def probe(case, route):
    d = case["inputs"]
    if (d["source_document"] != DOCUMENT
            or d["coefficient_ring"] != "Q[y]"
            or d["fraction_field"] != "Q(y)"
            or d["parameter"] != "y"
            or d["displayed_equations"] != ["G1", "G2", "G3"]
            or d["retained"] != {key: "0" for key in ("a", "b", "c", "d0", "d1", "d2")}):
        raise ValueError("Unknown deleted dm4 zero-chart interpretation")
    y = sp.Symbol("y")
    a, b, c, d0, d1, d2, q = sp.symbols("a b c d0 d1 d2 q")
    equations = (
        sp.Rational(3, 2)*d1*a**2 + 3*d2*a*b + 3*a*q + 3*b*c,
        -sp.Rational(3, 2)*d0*a**2 + sp.Rational(3, 2)*d2*b**2
        + 3*b*q + sp.Rational(3, 2)*c**2,
        -3*d0*a*b - sp.Rational(3, 2)*d1*b**2
        - sp.Rational(1, 2)*a**3 + 3*c*q,
    )
    zero_chart = {name: sp.Integer(0) for name in (a, b, c, d0, d1, d2)}
    if d["control"] == "universal_counterexample":
        if d["q"] != "1/y":
            raise ValueError("Changed rational counterexample")
        value = 1/y
        verdict, reason = ("REFUSE", "q=1/y solves G1-G3 on the all-zero retained chart but has reduced denominator y, so universal polynomiality fails.")
    elif d["control"] == "polynomial_existence":
        if d["q"] != "0":
            raise ValueError("Changed polynomial existence witness")
        value = sp.Integer(0)
        verdict, reason = ("ACCEPT", "q=0 is polynomial and solves G1-G3 on the same retained chart.")
    else:
        raise ValueError("Unknown dm4 zero-chart control")
    residuals = [sp.cancel(eq.subs({**zero_chart, q: value})) for eq in equations]
    if residuals != [sp.Integer(0)]*3:
        raise ValueError("Displayed equations did not vanish exactly")
    numerator, denominator = sp.fraction(sp.cancel(value))
    denominator_degree = sp.Poly(denominator, y, domain=sp.QQ).degree()
    polynomial = denominator_degree == 0
    if polynomial != (verdict == "ACCEPT"):
        raise ValueError("Polynomial membership disagrees with expected control")
    return {
        "observed_verdict": verdict,
        "reason": reason,
        "equation_residuals": {name: str(value) for name, value in zip(d["displayed_equations"], residuals)},
        "reduced_q_numerator": str(numerator),
        "reduced_q_denominator": str(denominator),
        "q_in_Qy_polynomial_ring": polynomial,
        "same_retained_zero_chart": True,
        "conclusion_scope": "displayed_G1_G2_G3_only",
        "full_v13_target_checked": False,
        "nonzero_chart_valuation_theorem_tested": False,
        "native_rational_lift_verdict": None,
        "reference_engine": "sympy " + sp.__version__,
        "external_execution": False,
    }
