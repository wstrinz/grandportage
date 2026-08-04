import hashlib
import json
from pathlib import Path

import pytest

from grandportage import cli
from grandportage import frontier_bundle as B


def _receipt(observations, consumer="test"):
    return {
        "schema": "test-frontier-review/v1",
        "projection_schema": "frontier/v1",
        "consumer": consumer,
        "authority": "DERIVED_READ_MODEL_ONLY",
        "graph_effect": "NONE",
        "history": {"input_fingerprint": "sha256:" + "1" * 64},
        "item_observations": observations,
        "open_items": [item["id"] for item in observations
                       if item["state"] == "OPEN"],
    }


def _observation(identifier, state="OPEN", status="OPEN",
                 scope="scope.exact", replacements=None):
    observation = {"id": identifier, "scope_id": scope,
                   "state": state, "status": status}
    if replacements is not None:
        observation["replacement_ids"] = list(replacements)
    return observation


def _write_bundle(tmp_path, receipts, resolutions=()):
    bindings = []
    for receipt_id, value in receipts.items():
        path = tmp_path / (receipt_id + ".json")
        path.write_text(json.dumps(value, sort_keys=True, indent=2) + "\n",
                        encoding="utf-8")
        digest = hashlib.sha256(
            path.read_bytes().replace(b"\r\n", b"\n")).hexdigest()
        bindings.append({"id": receipt_id, "path": path.name,
                         "digest_algo": B.DIGEST_ALGO, "sha256": digest})
    manifest = tmp_path / "bundle.json"
    manifest.write_text(json.dumps({
        "schema": B.INPUT_SCHEMA,
        "receipts": bindings,
        "resolutions": list(resolutions),
    }), encoding="utf-8")
    return manifest


def _agree(identifier="A", receipts=("old", "new"),
           scope="scope.exact"):
    return {"id": "resolution.agree", "item_id": identifier,
            "mode": "AGREE_OPEN", "scope_id": scope,
            "receipts": list(receipts), "reason": "exact agreement"}


def _supersede(identifier="A"):
    return {"id": "resolution.supersede", "item_id": identifier,
            "mode": "SUPERSEDE", "scope_id": "scope.exact",
            "prior_receipts": ["old"], "current_receipt": "new",
            "current_status": "RESOLVED", "replacements": ["B"],
            "reason": "new scoped result replaces the artifact request"}


def test_duplicate_open_item_requires_explicit_exact_agreement(tmp_path):
    receipts = {name: _receipt([_observation("A")], consumer=name)
                for name in ("old", "new")}
    manifest = _write_bundle(tmp_path, receipts)

    with pytest.raises(B.FrontierBundleError, match="explicit resolution"):
        B.build_path(manifest)

    report = B.build_path(_write_bundle(
        tmp_path, receipts, [_agree()]))
    assert report["open_items"] == ["A"]
    assert report["items"][0]["receipts"] == ["new", "old"]


def test_agreement_refuses_scope_or_status_conflicts(tmp_path):
    receipts = {
        "old": _receipt([_observation("A")], consumer="old"),
        "new": _receipt([_observation("A", scope="scope.other")], consumer="new"),
    }
    with pytest.raises(B.FrontierBundleError, match="incompatible exact scopes"):
        B.build_path(_write_bundle(tmp_path, receipts, [_agree()]))

    receipts["new"] = _receipt(
        [_observation("A", status="OPEN_OTHER")], consumer="new")
    with pytest.raises(B.FrontierBundleError, match="statuses conflict"):
        B.build_path(_write_bundle(tmp_path, receipts, [_agree()]))


def test_supersession_replaces_open_task_with_bounded_results(tmp_path):
    receipts = {
        "old": _receipt([_observation("A")], consumer="old"),
        "new": _receipt([
            _observation("A", state="CLOSED", status="RESOLVED",
                         replacements=["B"]),
            _observation("B", status="OPEN_FINITE_REMAINDER"),
        ], consumer="new"),
    }
    report = B.build_path(_write_bundle(
        tmp_path, receipts, [_supersede()]))
    items = {item["id"]: item for item in report["items"]}

    assert report["open_items"] == ["B"]
    assert items["A"]["status"] == "RESOLVED"
    assert items["A"]["supersedes_receipts"] == ["old"]
    assert items["A"]["replacements"] == ["B"]


def test_supersession_refuses_unproved_status_or_missing_replacement(tmp_path):
    receipts = {
        "old": _receipt([_observation("A")], consumer="old"),
        "new": _receipt([_observation(
            "A", state="CLOSED", status="SOMETHING_ELSE",
            replacements=["B"])], consumer="new"),
    }
    with pytest.raises(B.FrontierBundleError, match="status disagrees"):
        B.build_path(_write_bundle(tmp_path, receipts, [_supersede()]))

    receipts["new"] = _receipt([
        _observation("A", state="CLOSED", status="RESOLVED",
                     replacements=["B"])], consumer="new")
    with pytest.raises(B.FrontierBundleError, match="replacement is absent"):
        B.build_path(_write_bundle(tmp_path, receipts, [_supersede()]))


def test_supersession_refuses_current_as_prior_or_self_replacement(tmp_path):
    receipts = {
        "old": _receipt([_observation("A")], consumer="old"),
        "new": _receipt([
            _observation("A", state="CLOSED", status="RESOLVED",
                         replacements=["B"]),
            _observation("B"),
        ], consumer="new"),
    }
    resolution = _supersede()
    resolution["prior_receipts"].append("new")
    with pytest.raises(B.FrontierBundleError, match="current receipt as prior"):
        B.build_path(_write_bundle(tmp_path, receipts, [resolution]))

    resolution = _supersede()
    resolution["replacements"] = ["A"]
    with pytest.raises(B.FrontierBundleError, match="distinct replacement"):
        B.build_path(_write_bundle(tmp_path, receipts, [resolution]))


def test_receipt_digest_mutation_refuses(tmp_path):
    manifest = _write_bundle(
        tmp_path, {"only": _receipt([_observation("A")])})
    (tmp_path / "only.json").write_text("{}", encoding="utf-8")

    with pytest.raises(B.FrontierBundleError, match="digest changed"):
        B.build_path(manifest)


def test_lf_normalized_digest_survives_crlf_checkout(tmp_path):
    manifest = _write_bundle(
        tmp_path, {"only": _receipt([_observation("A")])})
    path = tmp_path / "only.json"
    lf = path.read_bytes().replace(b"\r\n", b"\n")
    path.write_bytes(lf.replace(b"\n", b"\r\n"))

    assert B.build_path(manifest)["open_items"] == ["A"]


def test_bundle_is_deterministic_and_cli_exposes_same_surface(tmp_path, capsys):
    receipts = {
        "z": _receipt([_observation("Z")], consumer="z"),
        "a": _receipt([_observation("A")], consumer="a"),
    }
    manifest = _write_bundle(tmp_path, receipts)
    first = B.build_path(manifest)
    second = B.build_path(manifest)

    assert B.canonical_json(first) == B.canonical_json(second)
    assert first["open_items"] == ["A", "Z"]
    assert cli.main(["frontier-bundle", str(manifest), "--compact"]) == 0
    assert json.loads(capsys.readouterr().out) == first


def test_atomic_review_emission_matches_derived_surface(tmp_path, capsys):
    manifest = _write_bundle(
        tmp_path, {"only": _receipt([_observation("A")])})
    target = tmp_path / "review.json"

    assert cli.main(["frontier-bundle", str(manifest), "--emit-review",
                     str(target)]) == 0
    result = json.loads(capsys.readouterr().out)
    report = B.build_path(manifest)
    expected = B.review_receipt(report)

    assert json.loads(target.read_text(encoding="utf-8")) == expected
    assert result["sha256_lf_normalized"] == hashlib.sha256(
        target.read_bytes().replace(b"\r\n", b"\n")).hexdigest()


def test_agreement_refuses_closed_observation_or_incomplete_receipts(tmp_path):
    receipts = {
        "old": _receipt([_observation("A")], consumer="old"),
        "new": _receipt([
            _observation("A", state="CLOSED", status="RESOLVED")],
            consumer="new"),
    }
    with pytest.raises(B.FrontierBundleError, match="includes a closed"):
        B.build_path(_write_bundle(tmp_path, receipts, [_agree()]))

    receipts["new"] = _receipt([_observation("A")], consumer="new")
    with pytest.raises(B.FrontierBundleError, match="name every receipt"):
        B.build_path(_write_bundle(
            tmp_path, receipts, [_agree(receipts=("old",))]))


def test_supersession_refuses_incomplete_receipts_or_closed_prior(tmp_path):
    receipts = {
        "old": _receipt([_observation("A")], consumer="old"),
        "middle": _receipt([_observation("A")], consumer="middle"),
        "new": _receipt([
            _observation("A", state="CLOSED", status="RESOLVED",
                         replacements=["B"]),
            _observation("B"),
        ], consumer="new"),
    }
    with pytest.raises(B.FrontierBundleError, match="name every receipt"):
        B.build_path(_write_bundle(tmp_path, receipts, [_supersede()]))

    receipts.pop("middle")
    receipts["old"] = _receipt([
        _observation("A", state="CLOSED", status="OLD_RESOLVED")],
        consumer="old")
    with pytest.raises(B.FrontierBundleError, match="prior state is not OPEN"):
        B.build_path(_write_bundle(tmp_path, receipts, [_supersede()]))


def test_receipt_refuses_open_list_foreign_schema_or_bad_fingerprint(tmp_path):
    receipt = _receipt([_observation("A")])
    receipt["open_items"] = []
    with pytest.raises(B.FrontierBundleError, match="open_items disagrees"):
        B.build_path(_write_bundle(tmp_path, {"only": receipt}))

    receipt = _receipt([_observation("A")])
    receipt.pop("projection_schema")
    with pytest.raises(B.FrontierBundleError, match="not a frontier/v1"):
        B.build_path(_write_bundle(tmp_path, {"only": receipt}))

    receipt = _receipt([_observation("A")])
    receipt["history"]["input_fingerprint"] = "sha256:not-a-digest"
    with pytest.raises(B.FrontierBundleError, match="input_fingerprint"):
        B.build_path(_write_bundle(tmp_path, {"only": receipt}))

    receipt = _receipt([_observation("A")])
    receipt["history"] = []
    with pytest.raises(B.FrontierBundleError, match="history must be an object"):
        B.build_path(_write_bundle(tmp_path, {"only": receipt}))


def test_receipt_refuses_duplicate_normalized_path_or_content(tmp_path):
    receipts = {
        "first": _receipt([_observation("A")]),
        "second": _receipt([_observation("A")]),
    }
    with pytest.raises(B.FrontierBundleError, match="duplicates receipt content"):
        B.build_path(_write_bundle(tmp_path, receipts, [_agree(
            receipts=("first", "second"))]))

    manifest = _write_bundle(tmp_path, {
        "first": _receipt([_observation("A")], consumer="first"),
        "second": _receipt([_observation("B")], consumer="second"),
    })
    value = json.loads(manifest.read_text(encoding="utf-8"))
    value["receipts"][1]["path"] = value["receipts"][0]["path"]
    value["receipts"][1]["sha256"] = value["receipts"][0]["sha256"]
    manifest.write_text(json.dumps(value), encoding="utf-8")
    with pytest.raises(B.FrontierBundleError, match="normalized receipt path"):
        B.build_path(manifest)


def test_supersession_refuses_replacement_provenance_disagreement(tmp_path):
    receipts = {
        "old": _receipt([_observation("A")], consumer="old"),
        "new": _receipt([
            _observation("A", state="CLOSED", status="RESOLVED",
                         replacements=["C"]),
            _observation("B"),
            _observation("C"),
        ], consumer="new"),
    }
    with pytest.raises(B.FrontierBundleError,
                       match="replacement provenance disagrees"):
        B.build_path(_write_bundle(tmp_path, receipts, [_supersede()]))
