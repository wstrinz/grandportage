import hashlib
import json
from pathlib import Path
import shutil

import pytest

from grandportage import campaign as C
from grandportage import cli


ROOT = Path(__file__).resolve().parents[1]
PACKET_MANIFEST = ROOT / "fixtures" / "campaign" / "matroid" / "packets.json"
LEDGER_MANIFEST = ROOT / "fixtures" / "campaign" / "matroid" / "ledger.json"
PACKET_ID = "MATROID.RETRODICTION.BASE_EXTENSION.v0"


def _digest(path):
    return hashlib.sha256(path.read_bytes().replace(b"\r\n", b"\n")).hexdigest()


def _write(path, value):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n",
                    encoding="utf-8")


def _copy_fixture(tmp_path):
    relative = [
        Path("fixtures/campaign/matroid/bundle.json"),
        Path("fixtures/campaign/matroid/receipt.json"),
        Path("fixtures/campaign/matroid/tasks_v0.json"),
        Path("fixtures/campaign/matroid/packets.json"),
        Path("fixtures/campaign/matroid/ledger.json"),
        Path("fixtures/matroid/expect.json"),
        Path("fixtures/matroid/graph.jsonl"),
        Path("tests/test_retrodiction.py"),
    ]
    for item in relative:
        target = tmp_path / item
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(ROOT / item, target)
    return (tmp_path / "fixtures/campaign/matroid/packets.json",
            tmp_path / "fixtures/campaign/matroid/ledger.json")


def _manifest_root(path):
    value = json.loads(path.read_text(encoding="utf-8"))
    return value, (path.parent / value.get("root", ".")).resolve()


def _refresh_packet(packet_path):
    packet, root = _manifest_root(packet_path)
    packet["frontier_bundle"]["sha256"] = _digest(
        root / packet["frontier_bundle"]["path"])
    packet["task_catalog"]["sha256"] = _digest(
        root / packet["task_catalog"]["path"])
    _write(packet_path, packet)


def _refresh_ledger(packet_path, ledger_path):
    ledger = json.loads(ledger_path.read_text(encoding="utf-8"))
    ledger["packet_manifest"]["sha256"] = _digest(packet_path)
    _write(ledger_path, ledger)


def test_neutral_packet_binds_exact_frontier_and_authority_ceiling():
    packet_set = C.build_packets_path(PACKET_MANIFEST)
    packet = packet_set["packets"][0]
    assert packet_set["counts"] == {"packets": 1, "active": 0}
    assert packet["packet_id"] == PACKET_ID
    assert packet["frontier_binding"]["observation"] == {
        "id": "MATROID.RETRODICTION.BASE_EXTENSION.EMPTY_DIRECTION",
        "scope_id": "MATROID.ML8.Q_TO_QSQRT_MINUS3",
        "state": "CLOSED",
        "status": "RETRODICTED_WITH_POSITIVE_AND_NEGATIVE_CONTROLS",
        "receipts": ["matroid"],
    }
    assert packet["authority"] == "DERIVED_READ_MODEL_ONLY"
    assert packet["graph_effect"] == "NONE"
    assert packet["authority_ceiling"]["source_label"] == (
        "RETRODICTION_FIXTURE_ONLY")


def test_packet_generation_is_deterministic_selectable_and_domain_neutral():
    first = C.build_packets_path(PACKET_MANIFEST)
    second = C.build_packets_path(PACKET_MANIFEST)
    selected = C.build_packets_path(PACKET_MANIFEST, [PACKET_ID])
    assert C.canonical_json(first) == C.canonical_json(second)
    assert selected["packets"][0]["packet_id"] == PACKET_ID
    assert "does not transport" in selected["packets"][0][
        "statement"]["proposition"]
    assert "coefficient" not in selected["packets"][0][
        "requested_output"]["must_identify"]
    with pytest.raises(C.CampaignError, match="unknown campaign packet"):
        C.build_packets_path(PACKET_MANIFEST, ["ABSENT"])


def test_human_and_agent_views_quote_the_same_contract():
    packet_set = C.build_packets_path(PACKET_MANIFEST)
    packet = packet_set["packets"][0]
    for text in (C.render_packets(packet_set, "human"),
                 C.render_packets(packet_set, "agent")):
        assert packet["packet_fingerprint"] in text
        assert packet["statement"]["proposition"] in text
        assert packet["authority_ceiling"]["boundary"] in text
        for mutation in packet["acceptance"]["required_mutations"]:
            assert mutation["id"] in text
    assert "Return artifacts, not mathematical authority" in C.render_packets(
        packet_set, "agent")


def test_packet_refuses_bundle_and_catalog_digest_drift(tmp_path):
    packet_path, _ = _copy_fixture(tmp_path)
    packet = json.loads(packet_path.read_text(encoding="utf-8"))
    packet["frontier_bundle"]["sha256"] = "0" * 64
    _write(packet_path, packet)
    with pytest.raises(C.CampaignError, match="frontier bundle digest changed"):
        C.build_packets_path(packet_path)

    packet_path, _ = _copy_fixture(tmp_path / "catalog")
    packet = json.loads(packet_path.read_text(encoding="utf-8"))
    packet["task_catalog"]["sha256"] = "0" * 64
    _write(packet_path, packet)
    with pytest.raises(C.CampaignError, match="task catalog digest changed"):
        C.build_packets_path(packet_path)


def test_packet_refuses_frontier_drift_and_missing_envelope(tmp_path):
    packet_path, _ = _copy_fixture(tmp_path)
    packet, root = _manifest_root(packet_path)
    catalog_path = root / packet["task_catalog"]["path"]
    catalog = json.loads(catalog_path.read_text(encoding="utf-8"))
    catalog["tasks"][0]["frontier"]["status"] = "DRIFTED"
    _write(catalog_path, catalog)
    _refresh_packet(packet_path)
    with pytest.raises(C.CampaignError, match="frontier status drifted"):
        C.build_packets_path(packet_path)

    packet_path, _ = _copy_fixture(tmp_path / "envelope")
    packet, root = _manifest_root(packet_path)
    bundle_path = root / packet["frontier_bundle"]["path"]
    bundle, bundle_root = _manifest_root(bundle_path)
    receipt_path = bundle_root / bundle["receipts"][0]["path"]
    receipt = json.loads(receipt_path.read_text(encoding="utf-8"))
    receipt.pop("evidence_envelope")
    _write(receipt_path, receipt)
    bundle["receipts"][0]["sha256"] = _digest(receipt_path)
    _write(bundle_path, bundle)
    _refresh_packet(packet_path)
    with pytest.raises(C.CampaignError, match="lacks an evidence envelope"):
        C.build_packets_path(packet_path)


def test_packet_paths_cannot_escape_declared_root(tmp_path):
    packet_path, _ = _copy_fixture(tmp_path)
    packet = json.loads(packet_path.read_text(encoding="utf-8"))
    packet["task_catalog"]["path"] = "../outside.json"
    _write(packet_path, packet)
    with pytest.raises(C.CampaignError, match="escapes the campaign root"):
        C.build_packets_path(packet_path)


def test_packet_refuses_missing_or_drifted_task_sources(tmp_path):
    packet_path, _ = _copy_fixture(tmp_path)
    packet, root = _manifest_root(packet_path)
    catalog_path = root / packet["task_catalog"]["path"]
    catalog = json.loads(catalog_path.read_text(encoding="utf-8"))
    catalog["tasks"][0]["source_bindings"][0]["sha256"] = "0" * 64
    _write(catalog_path, catalog)
    _refresh_packet(packet_path)
    with pytest.raises(C.CampaignError, match="source matroid_expectations digest changed"):
        C.build_packets_path(packet_path)

    packet_path, _ = _copy_fixture(tmp_path / "missing")
    packet, root = _manifest_root(packet_path)
    catalog_path = root / packet["task_catalog"]["path"]
    catalog = json.loads(catalog_path.read_text(encoding="utf-8"))
    catalog["tasks"][0]["source_bindings"][0]["path"] = "absent.json"
    _write(catalog_path, catalog)
    _refresh_packet(packet_path)
    with pytest.raises(C.CampaignError, match="source matroid_expectations is absent"):
        C.build_packets_path(packet_path)


def test_neutral_ledger_is_digest_bound_and_checked():
    ledger = C.build_ledger_path(LEDGER_MANIFEST)
    assert ledger["counts"]["attempts"] == 1
    assert ledger["counts"]["outcomes"]["ACCEPTED_ARTIFACT"] == 1
    assert ledger["counts"]["verification_debt"] == 0
    assert ledger["attempts"][0]["packet_fingerprint"].startswith("sha256:")
    assert ledger["graph_effect"] == "NONE"


def test_checked_attempt_requires_command_artifact_and_every_mutation(tmp_path):
    packet_path, ledger_path = _copy_fixture(tmp_path)
    ledger = json.loads(ledger_path.read_text(encoding="utf-8"))
    ledger["attempts"][0]["refused_mutations"].pop()
    _write(ledger_path, ledger)
    with pytest.raises(C.CampaignError, match="did not refuse every"):
        C.build_ledger_path(ledger_path)

    ledger["attempts"][0]["refused_mutations"] = [
        "erase_positive_witness_control", "promote_fixture_to_new_theorem",
        "reverse_base_extension_direction"]
    ledger["attempts"][0]["replay"]["command"] = "python wrong.py"
    _write(ledger_path, ledger)
    with pytest.raises(C.CampaignError, match="command disagrees"):
        C.build_ledger_path(ledger_path)

    ledger["attempts"][0]["replay"]["command"] = (
        "python -m pytest -q tests/test_retrodiction.py")
    ledger["attempts"][0]["artifact_bindings"] = []
    _write(ledger_path, ledger)
    with pytest.raises(C.CampaignError, match="needs passing replay and artifacts"):
        C.build_ledger_path(ledger_path)
    assert packet_path.is_file()


def test_pending_artifact_becomes_visible_verification_debt(tmp_path):
    packet_path, ledger_path = _copy_fixture(tmp_path)
    ledger = json.loads(ledger_path.read_text(encoding="utf-8"))
    ledger["attempts"] = [{
        "id": "MATROID.ATTEMPT.BASE_EXTENSION.002",
        "packet_id": PACKET_ID,
        "worker_ref": "cold-agent/unverified-return",
        "outcome": "PENDING_VERIFICATION",
        "summary": "Returned an unchecked directional classification.",
        "artifact_bindings": [{"id": "candidate", "sha256": "4" * 64}],
        "replay": {"status": "NOT_RUN",
                   "command": "python -m pytest -q tests/test_retrodiction.py",
                   "receipt": None},
        "refused_mutations": [], "value_categories": [],
        "successor_packet_ids": [],
    }]
    _write(ledger_path, ledger)
    built = C.build_ledger_path(ledger_path)
    overlay = C.build_overlay(C.build_packets_path(packet_path), built)
    assert built["counts"]["verification_debt"] == 1
    assert overlay["counts"]["verification_debt"] == 1
    assert overlay["items"][0]["outcomes"] == ["PENDING_VERIFICATION"]


def test_prior_ledger_is_an_append_only_prefix(tmp_path):
    _, ledger_path = _copy_fixture(tmp_path)
    prior = C.build_ledger_path(ledger_path)
    prior_path = tmp_path / "prior.json"
    prior_path.write_text(C.canonical_json(prior), encoding="utf-8")
    manifest = json.loads(ledger_path.read_text(encoding="utf-8"))
    manifest["prior_ledger"] = {"path": "prior.json",
                                "digest_algo": C.DIGEST_ALGO,
                                "sha256": _digest(prior_path)}
    _write(ledger_path, manifest)
    assert C.build_ledger_path(ledger_path)["extends"]["sha256"] == (
        "sha256:" + _digest(prior_path))
    manifest["attempts"] = []
    _write(ledger_path, manifest)
    with pytest.raises(C.CampaignError, match="changed or disappeared"):
        C.build_ledger_path(ledger_path)


def test_cli_packet_ledger_and_overlay_match_library(capsys):
    assert cli.main(["campaign-packet", str(PACKET_MANIFEST),
                     "--packet", PACKET_ID, "--format", "agent"]) == 0
    assert "Return artifacts, not mathematical authority" in capsys.readouterr().out
    assert cli.main(["campaign-ledger", str(LEDGER_MANIFEST), "--overlay"]) == 0
    actual = json.loads(capsys.readouterr().out)
    assert actual == C.build_overlay(C.build_packets_path(PACKET_MANIFEST),
                                    C.build_ledger_path(LEDGER_MANIFEST))


def test_cli_refusal_is_nonzero_and_explanatory(tmp_path, capsys):
    packet_path, _ = _copy_fixture(tmp_path)
    packet = json.loads(packet_path.read_text(encoding="utf-8"))
    packet["task_catalog"]["sha256"] = "0" * 64
    _write(packet_path, packet)
    assert cli.main(["campaign-packet", str(packet_path)]) == 2
    assert "task catalog digest changed" in capsys.readouterr().err
