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


def test_three_interpreters_and_their_lean_dictionary_are_complete():
    from pathlib import Path
    assert set(A.CATALOG) == {"unit", "ordered", "cancellation"}
    assert sum(len(A.inventory(name)) for name in A.CATALOG) == 48
    for name, item in A.CATALOG.items():
        cells = A.inventory(name)
        assert sum(c["status"] == "PROVED" for c in cells) == 1
        removed = set(item["premises"]) - {item["deleted"]}
        assert next(c for c in cells if set(c["premises"]) == removed)["status"] == "REFUTED"
    check_file = Path(__file__).resolve().parents[1] / "lean/GrandPortage/RequirementChecks.lean"
    assert check_file.read_text(encoding="utf-8") == A.lean_checks()
