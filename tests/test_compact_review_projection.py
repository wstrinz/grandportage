import json

from grandportage import projection


def _large_jsonl(path, mutation=None):
    with path.open("w", encoding="utf-8", newline="\n") as stream:
        for index in range(12000):
            value = {"id": "R%d" % index, "payload": "x" * 120}
            if index == mutation:
                value["payload"] = "y" * 120
            stream.write(json.dumps(value, sort_keys=True) + "\n")


def test_compact_projection_is_bounded_derived_and_digest_bound(tmp_path):
    source = tmp_path / "large.jsonl"
    _large_jsonl(source)
    first = projection.compact_review_projection(source, max_records=1000)
    encoded = projection.canonical_json(first, pretty=False).encode("utf-8")
    assert len(encoded) < 1000000
    assert first["authority"] == "DERIVED_READ_MODEL_ONLY"
    assert first["graph_effect"] == "NONE"
    assert first["selection"]["omitted"] == 11000
    _large_jsonl(source, mutation=6000)
    second = projection.compact_review_projection(source, max_records=1000)
    assert second["source"]["sha256"] != first["source"]["sha256"]
    assert second["projection_sha256"] != first["projection_sha256"]


def test_compact_projection_commits_first_and_last_records(tmp_path):
    source = tmp_path / "small.jsonl"
    _large_jsonl(source)
    value = projection.compact_review_projection(source, max_records=10)
    assert [item["line"] for item in value["records"]] == [
        1, 2, 3, 4, 5, 11996, 11997, 11998, 11999, 12000]
