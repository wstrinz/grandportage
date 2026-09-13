"""Bounded diagnostic atlas: supplied proof rules and retained countermodels only."""
from itertools import combinations
import json

PREMISES = ("DERIVATION", "GENERATOR_VANISHING", "NONTRIVIAL")
RULES = ((frozenset(PREMISES), "GrandPortage.CertificateInterpreter.unit_certificate_empty"),)
COUNTERMODELS = ((frozenset(PREMISES[:2]),
                  "GrandPortage.CertificateInterpreter.nontriviality_deletion_countermodel"),)


def classify(available, rules=RULES, countermodels=COUNTERMODELS):
    available = frozenset(available)
    if not available <= set(PREMISES):
        raise ValueError("unknown premise")
    positive = [(needed, proof) for needed, proof in rules if needed <= available]
    negative = [proof for satisfied, proof in countermodels if available <= satisfied]
    if positive and negative:
        raise ValueError("inconsistent proof/countermodel catalog")
    # Preserve incomparable sufficient alternatives; minimize within this catalog.
    minimal = [(needed, proof) for needed, proof in positive
               if not any(other < needed for other, _ in positive)]
    return {"premises": sorted(available),
            "status": "PROVED" if positive else "REFUTED" if negative else "UNKNOWN",
            "sufficient_alternatives": [{"premises": sorted(needed), "proof": proof}
                                        for needed, proof in minimal],
            "countermodels": negative, "authority": "NONE"}


def inventory():
    return [classify(choice) for count in range(len(PREMISES) + 1)
            for choice in combinations(PREMISES, count)]


if __name__ == "__main__":
    print(json.dumps({"model_class": "Operations + Laws; arbitrary cofactor terms and points",
                      "claim": "no point satisfies all available assumptions",
                      "cells": inventory()}, indent=2))
