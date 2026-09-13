"""Diagnostic premise subsets. Lean declaration links are checked by the build."""
from itertools import combinations
import json
import sys

PREFIX = "GrandPortage.CertificateInterpreter."
UNIT_PREMISES = ("DERIVATION", "GENERATOR_VANISHING", "NONTRIVIAL")
PREMISES = UNIT_PREMISES + ("ORDERING", "NO_ZERO_DIVISORS", "COEFFICIENT_NONZERO", "GOAL_NONZERO")
CATALOG = {
    "unit": {"premises": UNIT_PREMISES, "theorem": "unit_certificate_empty",
             "countermodel": "nontriviality_deletion_countermodel", "deleted": "NONTRIVIAL",
             "support": ["zeroAlgebra_laws", "unit_sample_derivation"]},
    "ordered": {"premises": ("DERIVATION", "GENERATOR_VANISHING", "ORDERING"),
                "theorem": "certificate_empty", "countermodel": "modTwo_sos_countermodel",
                "deleted": "ORDERING", "support": ["modTwo_laws", "sample_derivation", "modTwo_not_ordered"]},
    "cancellation": {"premises": ("DERIVATION", "GENERATOR_VANISHING", "NO_ZERO_DIVISORS",
                                  "COEFFICIENT_NONZERO", "GOAL_NONZERO"),
                     "theorem": "cancellation_contradiction",
                     "countermodel": "cancellation_deletion_countermodel", "deleted": "NO_ZERO_DIVISORS",
                     "support": ["modFour_laws", "cancel_derivation"]},
}
RULES = ((frozenset(UNIT_PREMISES), PREFIX + CATALOG["unit"]["theorem"]),)
COUNTERMODELS = ((frozenset(UNIT_PREMISES[:2]), PREFIX + CATALOG["unit"]["countermodel"]),)


def classify(available, rules=RULES, countermodels=COUNTERMODELS):
    available = frozenset(available)
    if not available <= set(PREMISES):
        raise ValueError("unknown premise")
    positive = [(needed, proof) for needed, proof in rules if needed <= available]
    negative = [proof for satisfied, proof in countermodels if available <= satisfied]
    if positive and negative:
        raise ValueError("inconsistent proof/countermodel catalog")
    minimal = [(needed, proof) for needed, proof in positive
               if not any(other < needed for other, _ in positive)]
    return {"premises": sorted(available),
            "status": "PROVED" if positive else "REFUTED" if negative else "UNKNOWN",
            "sufficient_alternatives": [{"premises": sorted(needed), "proof": proof}
                                        for needed, proof in minimal],
            "countermodels": negative, "authority": "NONE"}


def inventory(interpreter="unit"):
    item = CATALOG[interpreter]
    vocabulary = item["premises"]
    rules = ((frozenset(vocabulary), PREFIX + item["theorem"]),)
    countermodels = ((frozenset(vocabulary) - {item["deleted"]}, PREFIX + item["countermodel"]),)
    return [dict(classify(choice, rules, countermodels), interpreter=interpreter)
            for count in range(len(vocabulary) + 1) for choice in combinations(vocabulary, count)]


def lean_names():
    names = {PREFIX + name for item in CATALOG.values()
             for name in [item["theorem"], item["countermodel"]] + item["support"]}
    names.update(PREFIX + name for name in ["ordered_nontrivial", "integer_domain",
                 "modTwo_domain", "product_laws", "product_order", "product_not_domain",
                 "zeroAlgebra_no_zero_divisors", "zeroAlgebra_not_nontrivial", "modFour_not_no_zero_divisors"])
    return sorted(names)


def lean_checks():
    return "import GrandPortage.CancellationInterpreter\n\n" + "".join(
        "#check " + name + "\n" for name in lean_names())


if __name__ == "__main__":
    if "--lean-checks" in sys.argv:
        print(lean_checks(), end="")
    else:
        print(json.dumps({"model_class": "Operations + Laws; interpreter-specific expressions and points",
                          "claim": "the listed assumptions imply contradiction",
                          "cells": [cell for name in CATALOG for cell in inventory(name)]}, indent=2))
