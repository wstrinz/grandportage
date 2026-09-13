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



def target_discharge():
    """Universal target-class discharge, with explicit uninstantiated interfaces."""
    rows=[]
    for target in ("Q", "R", "C", "F_p", "ANY_ORDERED", "ANY_CHAR_0"):
        for profile in ("U", "O", "Z"):
            proof = "field_target_"+profile if profile != "O" else None
            status = "PROVED_UNDER_FIELD_INTERFACE" if proof else "UNKNOWN"
            countermodel = None
            if profile == "O" and target == "ANY_ORDERED":
                proof="ordered_target_O"; status="PROVED_UNDER_ORDERED_INTERFACE"
            if profile == "O" and target == "F_p":
                countermodel="modTwo_not_ordered"; status="REFUTED_AS_UNIFORM_DISCHARGE"
            rows.append({"target":target,"profile":profile,"status":status,
                         "proof":PREFIX+proof if proof else None,
                         "countermodel":PREFIX+countermodel if countermodel else None,
                         "instance_status":"F_2 instance checked; general prime adapter missing" if target=="F_p" else
                         "class interface" if target.startswith("ANY_") else "canonical instance adapter UNKNOWN",
                         "authority":"NONE"})
    return rows

def lean_names():
    names = {PREFIX + name for item in CATALOG.values()
             for name in [item["theorem"], item["countermodel"]] + item["support"]}
    names.update(PREFIX + name for name in ["ordered_nontrivial", "integer_domain",
                 "modTwo_domain", "product_laws", "product_order", "product_not_domain",
                 "zeroAlgebra_no_zero_divisors", "zeroAlgebra_not_nontrivial", "modFour_not_no_zero_divisors"])
    names.update(row[key] for row in target_discharge() for key in ("proof","countermodel") if row[key])
    names.add(PREFIX+"modTwo_field_target")
    return sorted(names)


def lean_checks():
    return "import GrandPortage.TargetDischarge\n\n" + "".join(
        "#check " + name + "\n" for name in lean_names())


if __name__ == "__main__":
    if "--lean-checks" in sys.argv:
        print(lean_checks(), end="")
    else:
        print(json.dumps({"model_class": "Operations + Laws; interpreter-specific expressions and points",
                          "claim": "the listed assumptions imply contradiction",
                          "cells": [cell for name in CATALOG for cell in inventory(name)], "target_discharge": target_discharge()}, indent=2))
