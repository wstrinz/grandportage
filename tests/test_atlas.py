"""Keep the audit complete and make its executable comparison fail closed."""

from pathlib import Path

import pytest

from grandportage import kernel
from scripts import check_atlas_parity as parity


def test_atlas_inventory_matches_every_live_transport_cell_once():
    doc = (Path(__file__).parents[1] / "docs" /
           "ATLAS-MAPPING-V0.md").read_text(encoding="utf-8")
    observed = {}
    for line in doc.splitlines():
        cells = [part.strip() for part in line.split("|")[1:-1]]
        if len(cells) != 6 or cells[1] not in kernel.DIRECTIONS:
            continue
        key = tuple(cells[:3])
        assert key not in observed, key
        observed[key] = cells[3]
    expected = {(edge, direction, kind): str(rule)
                for edge, directions in kernel.TRANSPORT.items()
                for direction, kinds in directions.items()
                for kind, rule in kinds.items()}
    assert observed == expected


def parity_output():
    return "\n".join("\t".join(key + (str(value).lower(),))
                     for key, value in parity.expected_rows().items())


def test_parity_comparison_accepts_complete_output():
    assert parity.compare(parity_output()) == 139


@pytest.mark.parametrize("mutation", ["missing", "duplicate", "flip", "extra",
                                      "malformed"])
def test_parity_comparison_rejects_missing_or_corrupt_evidence(mutation):
    rows = parity_output().splitlines()
    if mutation == "missing":
        rows.pop()
    elif mutation == "duplicate":
        rows.append(rows[0])
    elif mutation == "flip":
        parts = rows[0].split("\t")
        parts[-1] = "false" if parts[-1] == "true" else "true"
        rows[0] = "\t".join(parts)
    elif mutation == "extra":
        rows.append("reach\tINVENTED\tQ\ttrue")
    else:
        rows[0] = "not a Lean decision"
    with pytest.raises(ValueError):
        parity.compare("\n".join(rows))
