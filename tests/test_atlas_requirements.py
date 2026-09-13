from collections import Counter
import pytest
from scripts import atlas_requirements as A


def test_bounded_inventory_retains_unknown_and_deletion_countermodel():
    cells = A.inventory()
    assert len(cells) == 8
    assert Counter(c["status"] for c in cells) == {"PROVED": 1, "REFUTED": 4, "UNKNOWN": 3}
    assert all(c["authority"] == "NONE" for c in cells)
    assert A.classify({"DERIVATION", "GENERATOR_VANISHING"})["status"] == "REFUTED"
    assert A.classify({"NONTRIVIAL", "GENERATOR_VANISHING"})["status"] == "UNKNOWN"


def test_incomparable_catalog_rules_remain_alternatives():
    # Synthetic solver control, not additional mathematical admission rules.
    rules = ((frozenset({"DERIVATION"}), "rule-a"),
             (frozenset({"NONTRIVIAL"}), "rule-b"))
    result = A.classify(A.PREMISES, rules=rules, countermodels=())
    assert len(result["sufficient_alternatives"]) == 2
    with pytest.raises(ValueError, match="inconsistent"):
        A.classify({"DERIVATION"}, rules=rules)
    with pytest.raises(ValueError, match="unknown"):
        A.classify({"MAGIC"})
