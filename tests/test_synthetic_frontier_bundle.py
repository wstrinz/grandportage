from pathlib import Path

from grandportage import frontier_bundle as B


MANIFEST = (Path(__file__).resolve().parents[1] / "fixtures" / "frontier" /
            "synthetic" / "bundle.json")


def test_non_jc_consumers_compose_without_widening_authority():
    report = B.build_path(MANIFEST)
    items = {item["id"]: item for item in report["items"]}

    assert report["counts"] == {
        "receipts": 2, "items": 4, "open": 2,
        "resolved": 2, "overlap_resolutions": 2}
    assert report["open_items"] == [
        "SYNTH.CALIBRATION.B", "SYNTH.COVERAGE"]
    assert items["SYNTH.CALIBRATION"]["replacements"] == [
        "SYNTH.CALIBRATION.A", "SYNTH.CALIBRATION.B"]
    assert items["SYNTH.COVERAGE"]["receipts"] == [
        "execution", "planning"]
    assert report["authority"] == "DERIVED_READ_MODEL_ONLY"
    assert report["graph_effect"] == "NONE"
