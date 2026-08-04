import importlib.util
import json
from pathlib import Path

import pytest


ROOT = Path(__file__).resolve().parents[1]
SCRIPT = ROOT / "experiments" / "jc_h3_source_depth6" / "status_block.py"


def _load():
    spec = importlib.util.spec_from_file_location("jc_h3_status_block_test", SCRIPT)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def _ledger(module):
    return module.REPLAY.run_gate(full=False)


def _frozen_ledger():
    return json.loads((ROOT / "review" /
                       "jc-h3-depth6-seam-replay-v2.json").read_text(
                           encoding="utf-8"))


@pytest.mark.replay
def test_projection_keeps_supported_and_unsupported_authority_distinct():
    module = _load()
    projection = module.status_projection(_ledger(module))

    assert projection["overall_verdict"] == (
        "VERIFIED_TO_EXPLICIT_OPEN_OBLIGATION")
    assert projection["aggregate_graph_effect"] == "NONE"
    assert "H3 promotion" in projection["not_supported"]
    assert {item["id"] for item in projection["open_frontier"]} >= {
        "R5", "R6", "R7", "R6.Q_side_relocation",
        "target_pair_to_normalized_laurent_root",
    }
    assert any(item["stage_id"] == "r1_r7_source_frontier"
               for item in projection["supported"])
    assert projection["binding_digest_algo"] == "sha256-lf-normalized"


def test_exact_delimited_replacement_reaches_a_fixed_point(tmp_path):
    module = _load()
    path = tmp_path / "status.md"
    path.write_text("before\n%s\nold\n%s\nafter\n" %
                    (module.BEGIN, module.END), encoding="utf-8")
    ledger = _frozen_ledger()

    first = module.refresh_file(path, ledger)
    after_first = path.read_bytes()
    second = module.refresh_file(path, ledger)

    assert first == {"target": str(path), "delimiters_found": True,
                     "changed": True}
    assert second == {"target": str(path), "delimiters_found": True,
                      "changed": False}
    assert path.read_bytes() == after_first
    assert path.read_text(encoding="utf-8").startswith("before\n")
    assert path.read_text(encoding="utf-8").endswith("\nafter\n")


def test_missing_delimiters_are_a_diagnosed_noop(tmp_path):
    module = _load()
    path = tmp_path / "unowned.md"
    path.write_text("human-owned status\n", encoding="utf-8")

    report = module.refresh_file(path, _frozen_ledger())

    assert report["delimiters_found"] is False
    assert report["changed"] is False
    assert path.read_text(encoding="utf-8") == "human-owned status\n"


@pytest.mark.parametrize("text", [
    "prefix %s only" %
    "<!-- GP-STATUS-BLOCK:BEGIN schema=gp-status-block/v1 -->",
    "%s x %s y %s" % (
        "<!-- GP-STATUS-BLOCK:BEGIN schema=gp-status-block/v1 -->",
        "<!-- GP-STATUS-BLOCK:BEGIN schema=gp-status-block/v1 -->",
        "<!-- GP-STATUS-BLOCK:END -->"),
    "%s before %s" % (
        "<!-- GP-STATUS-BLOCK:END -->",
        "<!-- GP-STATUS-BLOCK:BEGIN schema=gp-status-block/v1 -->"),
])
def test_unbalanced_duplicate_or_reversed_delimiters_refuse(text):
    module = _load()
    with pytest.raises(module.StatusBlockError):
        module.replace_block(text, module.render_block(_frozen_ledger()))


def test_v1_review_ledger_is_visibly_lossy_after_migration():
    module = _load()
    old = json.loads((ROOT / "review" /
                      "jc-h3-depth6-full-replay-v1.json").read_text(
                          encoding="utf-8"))

    projection = module.status_projection(old)

    assert projection["migration"]["status"] == "LOSSY_EXPLICIT"
    assert projection["binding_digest_algo"] == "sha256-mixed-legacy"


def test_empty_open_frontier_is_refused():
    module = _load()
    ledger = _frozen_ledger()
    ledger["open_frontier"] = []

    with pytest.raises(module.StatusBlockError,
                       match="no explicit open frontier"):
        module.status_projection(ledger)
