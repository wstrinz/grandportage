import copy
import hashlib
import json
import os
from pathlib import Path
import shutil

import pytest

from grandportage import campaign as C
from grandportage import cli


ROOT = Path(__file__).resolve().parents[1]
JC_PACKET_MANIFEST = ROOT / "fixtures" / "campaign" / "jc_sigma" / "packets.json"
JC_LEDGER_MANIFEST = ROOT / "fixtures" / "campaign" / "jc_sigma" / "ledger.json"
MATROID_PACKET_MANIFEST = ROOT / "fixtures" / "campaign" / "matroid" / "packets.json"
ACTIVE_PACKET = "JC.H3.SIGMA.Q51_HYPERPLANE.CLASSIFY.v0"


def _digest(path):
    return hashlib.sha256(path.read_bytes().replace(b"\r\n", b"\n")).hexdigest()


def _write(path, value):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n",
                    encoding="utf-8")


def _copy_jc(tmp_path):
    relative = [
        Path("fixtures/campaign/jc_sigma/tasks_v0.json"),
        Path("fixtures/campaign/jc_sigma/packets.json"),
        Path("fixtures/campaign/jc_sigma/ledger.json"),
        Path("fixtures/frontier/current_v1.json"),
    ]
    frontier = json.loads((ROOT / relative[-1]).read_text(encoding="utf-8"))
    relative.extend(Path(item["path"]) for item in frontier["receipts"])
    for item in relative:
        target = tmp_path / item
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(ROOT / item, target)
    return (tmp_path / "fixtures/campaign/jc_sigma/packets.json",
            tmp_path / "fixtures/campaign/jc_sigma/ledger.json")


def _refresh_catalog(packet_manifest):
    packet = json.loads(packet_manifest.read_text(encoding="utf-8"))
    root = (packet_manifest.parent / packet["root"]).resolve()
    packet["task_catalog"]["sha256"] = _digest(
        root / packet["task_catalog"]["path"])
    _write(packet_manifest, packet)


def _refresh_bundle(packet_manifest):
    packet = json.loads(packet_manifest.read_text(encoding="utf-8"))
    root = (packet_manifest.parent / packet["root"]).resolve()
    packet["frontier_bundle"]["sha256"] = _digest(
        root / packet["frontier_bundle"]["path"])
    _write(packet_manifest, packet)


def _refresh_packet_binding(packet_manifest, ledger_manifest):
    ledger = json.loads(ledger_manifest.read_text(encoding="utf-8"))
    ledger["packet_manifest"]["sha256"] = _digest(packet_manifest)
    _write(ledger_manifest, ledger)


def _packets_by_id(packet_set):
    return {item["packet_id"]: item for item in packet_set["packets"]}


def test_jc_packet_set_binds_current_open_frontier_and_evidence_ceiling():
    packet_set = C.build_packets_path(JC_PACKET_MANIFEST)
    packets = _packets_by_id(packet_set)

    assert packet_set["counts"] == {"packets": 3, "active": 1}
    assert set(packets) == {
        "JC.H3.SIGMA.WEIGHTED_PROJECTIVE.CLASSIFY.v0",
        "JC.H3.SIGMA.D_ANSATZ.TEST.v0",
        ACTIVE_PACKET,
    }
    for packet in packets.values():
        observation = packet["frontier_binding"]["observation"]
        assert observation == {
            "id": "JC.H3.SOURCE.REMAINING_COEFFICIENT_MAP",
            "scope_id": "JC.H3.SOURCE.TARGET_PAIR.SEAM",
            "state": "OPEN",
            "status": "OPEN_REMAINING_COEFFICIENT_MAP",
            "receipts": ["source-target-first-value"],
        }
        assert packet["authority"] == "DERIVED_READ_MODEL_ONLY"
        assert packet["graph_effect"] == "NONE"
        assert "does not construct a pair" in packet[
            "authority_ceiling"]["boundary"]
        assert packet["packet_fingerprint"].startswith("sha256:")


def test_active_jc_packet_is_the_narrowed_hyperplane_mission():
    packet = _packets_by_id(C.build_packets_path(JC_PACKET_MANIFEST))[ACTIVE_PACKET]

    assert packet["planning"]["lifecycle"] == "ACTIVE"
    assert packet["planning"]["maturity"] == "DECOMPOSABLE"
    assert "Q_(5,1)=0" in packet["statement"]["proposition"]
    assert "sparse_rational_nullstellensatz_certificate" in packet[
        "requested_output"]["acceptable_forms"]
    assert {item["id"] for item in packet["acceptance"]["required_mutations"]} == {
        "promote_modular_membership_to_rational",
        "drop_q51_hyperplane_scope",
        "infer_reverse_source_transport",
        "erase_surviving_stratum",
    }


def test_packet_generation_is_deterministic_and_selectable():
    first = C.build_packets_path(JC_PACKET_MANIFEST)
    second = C.build_packets_path(JC_PACKET_MANIFEST)
    selected = C.build_packets_path(JC_PACKET_MANIFEST, [ACTIVE_PACKET])

    assert C.canonical_json(first) == C.canonical_json(second)
    assert selected["counts"] == {"packets": 1, "active": 1}
    assert selected["packets"][0]["packet_id"] == ACTIVE_PACKET
    with pytest.raises(C.CampaignError, match="unknown campaign packet"):
        C.build_packets_path(JC_PACKET_MANIFEST, ["ABSENT"])


def test_human_and_agent_views_quote_the_same_contract():
    packet_set = C.build_packets_path(JC_PACKET_MANIFEST, [ACTIVE_PACKET])
    packet = packet_set["packets"][0]
    human = C.render_packets(packet_set, "human")
    agent = C.render_packets(packet_set, "agent")

    for text in (human, agent):
        assert packet["packet_fingerprint"] in text
        assert packet["statement"]["proposition"] in text
        assert packet["authority_ceiling"]["boundary"] in text
        assert packet["planning"]["argument"] in text
        for artifact in packet["inputs"]["artifacts"]:
            assert artifact["path"] in text
            assert artifact["sha256"] in text
        for mutation in packet["acceptance"]["required_mutations"]:
            assert mutation["id"] in text
    assert "Return artifacts, not mathematical authority" in agent
    assert "Return artifacts, not mathematical authority" not in human


def test_packet_manifest_refuses_bundle_or_catalog_digest_drift(tmp_path):
    packet_path, _ledger_path = _copy_jc(tmp_path)
    manifest = json.loads(packet_path.read_text(encoding="utf-8"))
    manifest["frontier_bundle"]["sha256"] = "0" * 64
    _write(packet_path, manifest)
    with pytest.raises(C.CampaignError, match="frontier bundle digest changed"):
        C.build_packets_path(packet_path)

    packet_path, _ledger_path = _copy_jc(tmp_path / "other")
    manifest = json.loads(packet_path.read_text(encoding="utf-8"))
    manifest["task_catalog"]["sha256"] = "0" * 64
    _write(packet_path, manifest)
    with pytest.raises(C.CampaignError, match="task catalog digest changed"):
        C.build_packets_path(packet_path)


def test_packet_refuses_frontier_status_or_receipt_disagreement(tmp_path):
    packet_path, _ledger_path = _copy_jc(tmp_path)
    root = tmp_path
    catalog_path = root / "fixtures/campaign/jc_sigma/tasks_v0.json"
    catalog = json.loads(catalog_path.read_text(encoding="utf-8"))
    catalog["tasks"][0]["frontier"]["status"] = "OPEN_BUT_DIFFERENT"
    _write(catalog_path, catalog)
    _refresh_catalog(packet_path)
    with pytest.raises(C.CampaignError, match="frontier status drifted"):
        C.build_packets_path(packet_path)

    catalog["tasks"][0]["frontier"]["status"] = "OPEN_REMAINING_COEFFICIENT_MAP"
    catalog["tasks"][0]["frontier"]["receipt_id"] = "support-seam"
    _write(catalog_path, catalog)
    _refresh_catalog(packet_path)
    with pytest.raises(C.CampaignError, match="does not observe the item"):
        C.build_packets_path(packet_path)


def test_packet_refuses_missing_evidence_envelope(tmp_path):
    packet_path, _ledger_path = _copy_jc(tmp_path)
    frontier_path = tmp_path / "fixtures/frontier/current_v1.json"
    frontier = json.loads(frontier_path.read_text(encoding="utf-8"))
    binding = next(item for item in frontier["receipts"]
                   if item["id"] == "source-target-first-value")
    receipt_path = tmp_path / binding["path"]
    receipt = json.loads(receipt_path.read_text(encoding="utf-8"))
    receipt.pop("evidence_envelope")
    _write(receipt_path, receipt)
    binding["sha256"] = _digest(receipt_path)
    _write(frontier_path, frontier)
    _refresh_bundle(packet_path)

    with pytest.raises(C.CampaignError, match="lacks an evidence envelope"):
        C.build_packets_path(packet_path)


def test_packet_paths_cannot_escape_declared_root(tmp_path):
    packet_path, _ledger_path = _copy_jc(tmp_path)
    manifest = json.loads(packet_path.read_text(encoding="utf-8"))
    manifest["task_catalog"]["path"] = "../outside.json"
    _write(packet_path, manifest)
    with pytest.raises(C.CampaignError, match="escapes the campaign root"):
        C.build_packets_path(packet_path)


def test_matroid_packet_proves_the_schema_is_not_jc_shaped():
    packet_set = C.build_packets_path(MATROID_PACKET_MANIFEST)
    packet = packet_set["packets"][0]

    assert packet["packet_id"] == "MATROID.RETRODICTION.BASE_EXTENSION.v0"
    assert packet["frontier_binding"]["observation"]["state"] == "CLOSED"
    assert "does not transport" in packet["statement"]["proposition"]
    assert "coefficient" not in packet["requested_output"]["must_identify"]
    assert packet["authority_ceiling"]["source_label"] == (
        "RETRODICTION_FIXTURE_ONLY")


def test_jc_ledger_records_map_redrawing_refutations_without_closure():
    ledger = C.build_ledger_path(JC_LEDGER_MANIFEST)

    assert ledger["counts"]["attempts"] == 2
    assert ledger["counts"]["outcomes"]["USEFUL_REFUTATION"] == 2
    assert ledger["counts"]["verification_debt"] == 0
    assert all(item["outcome"] == "USEFUL_REFUTATION"
               for item in ledger["attempts"])
    assert all(item["packet_fingerprint"].startswith("sha256:")
               for item in ledger["attempts"])
    assert ledger["graph_effect"] == "NONE"


def test_checked_attempt_requires_packet_command_artifact_and_all_mutations(tmp_path):
    packet_path, ledger_path = _copy_jc(tmp_path)
    ledger = json.loads(ledger_path.read_text(encoding="utf-8"))
    ledger["attempts"][0]["refused_mutations"].pop()
    _write(ledger_path, ledger)
    with pytest.raises(C.CampaignError, match="did not refuse every"):
        C.build_ledger_path(ledger_path)

    ledger["attempts"][0]["refused_mutations"] = [
        "mutate_second_component_coordinate",
        "promote_family_to_exhaustive",
        "promote_to_source_pair",
    ]
    ledger["attempts"][0]["replay"]["command"] = "python wrong.py"
    _write(ledger_path, ledger)
    with pytest.raises(C.CampaignError, match="command disagrees"):
        C.build_ledger_path(ledger_path)

    ledger["attempts"][0]["replay"]["command"] = (
        "python d2_plane_72_108/f2_h3_sigma_weighted_projective.py --verify")
    ledger["attempts"][0]["artifact_bindings"] = []
    _write(ledger_path, ledger)
    with pytest.raises(C.CampaignError, match="needs passing replay and artifacts"):
        C.build_ledger_path(ledger_path)

    assert packet_path.is_file()


def test_pending_artifact_becomes_visible_verification_debt(tmp_path):
    packet_path, ledger_path = _copy_jc(tmp_path)
    ledger_value = json.loads(ledger_path.read_text(encoding="utf-8"))
    ledger_value["attempts"].append({
        "id": "JC.H3.ATTEMPT.SIGMA_Q51.001",
        "packet_id": ACTIVE_PACKET,
        "worker_ref": "cold-agent/unverified-return",
        "outcome": "PENDING_VERIFICATION",
        "summary": "Returned a candidate sparse rational combination awaiting replay.",
        "artifact_bindings": [{"id": "candidate", "sha256": "4" * 64}],
        "replay": {
            "status": "NOT_RUN",
            "command": "python d2_plane_72_108/f2_h3_sigma_q51_hyperplane.py --verify",
            "receipt": None,
        },
        "refused_mutations": [],
        "value_categories": [],
        "successor_packet_ids": [],
    })
    _write(ledger_path, ledger_value)
    ledger = C.build_ledger_path(ledger_path)
    packet_set = C.build_packets_path(packet_path)
    overlay = C.build_overlay(packet_set, ledger)

    assert ledger["counts"]["verification_debt"] == 1
    assert overlay["counts"]["verification_debt"] == 1
    item = next(item for item in overlay["items"]
                if item["packet_id"] == ACTIVE_PACKET)
    assert item["verification_debt"] == 1
    assert item["outcomes"] == ["PENDING_VERIFICATION"]
    assert overlay["graph_effect"] == "NONE"


def test_prior_ledger_is_an_append_only_prefix(tmp_path):
    _packet_path, ledger_path = _copy_jc(tmp_path)
    prior = C.build_ledger_path(ledger_path)
    prior_path = tmp_path / "prior.json"
    prior_path.write_text(C.canonical_json(prior), encoding="utf-8")
    manifest = json.loads(ledger_path.read_text(encoding="utf-8"))
    manifest["prior_ledger"] = {
        "path": "prior.json",
        "digest_algo": C.DIGEST_ALGO,
        "sha256": _digest(prior_path),
    }
    _write(ledger_path, manifest)
    extended = C.build_ledger_path(ledger_path)
    assert extended["extends"]["sha256"] == "sha256:" + _digest(prior_path)

    manifest["attempts"].pop()
    _write(ledger_path, manifest)
    with pytest.raises(C.CampaignError, match="changed or disappeared"):
        C.build_ledger_path(ledger_path)


def test_cli_packet_ledger_and_overlay_match_library(capsys):
    code = cli.main(["campaign-packet", str(JC_PACKET_MANIFEST),
                     "--packet", ACTIVE_PACKET, "--format", "agent"])
    captured = capsys.readouterr()
    assert code == 0
    assert ACTIVE_PACKET in captured.out
    assert "Return artifacts, not mathematical authority" in captured.out

    code = cli.main(["campaign-ledger", str(JC_LEDGER_MANIFEST), "--overlay"])
    captured = capsys.readouterr()
    assert code == 0
    assert json.loads(captured.out) == C.build_overlay(
        C.build_packets_path(JC_PACKET_MANIFEST),
        C.build_ledger_path(JC_LEDGER_MANIFEST))


def test_cli_refusal_is_nonzero_and_explains_the_boundary(tmp_path, capsys):
    packet_path, _ledger_path = _copy_jc(tmp_path)
    manifest = json.loads(packet_path.read_text(encoding="utf-8"))
    manifest["task_catalog"]["sha256"] = "0" * 64
    _write(packet_path, manifest)

    code = cli.main(["campaign-packet", str(packet_path)])
    captured = capsys.readouterr()
    assert code == 2
    assert "campaign-packet refused" in captured.err
    assert "task catalog digest changed" in captured.err
