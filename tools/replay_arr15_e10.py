"""Replay two immutable ARR15 E10 graphs without modifying either source."""

import argparse
import hashlib
import json
from pathlib import Path
import tempfile

from grandportage import check as C
from grandportage import migration as MIG
from grandportage import store as S


EXPECTED = {
    "windows": "ca497fd5db7a75c2eb56b6393c9a90a324b05b57cc5cc5b4f634d1326f703d8d",
    "mac": "3eb5639d383cd2e6933812aa52809cfb4ee1bb5e33b8de2c6d02dd2f15a9d968",
}


def replay(sources):
    results = []
    with tempfile.TemporaryDirectory(prefix="gp-arr15-e10-") as temporary:
        migrated = []
        for lane, source in sources.items():
            raw = Path(source).read_bytes()
            actual = hashlib.sha256(raw).hexdigest()
            if actual != EXPECTED[lane]:
                raise ValueError(
                    "%s source hash %s != preserved %s"
                    % (lane, actual, EXPECTED[lane]))
            destination = Path(temporary) / (lane + ".format-current.jsonl")
            migration = MIG.migrate_kernel_epoch(
                [str(source)], output=str(destination))[0]
            graph = S.load(str(destination))
            findings = C.run(graph)
            migrated.append(str(destination))
            results.append({
                "lane": lane,
                "source_sha256": actual,
                "source_events": migration["events"] + 1,
                "migrated_graph_format": graph.graph_format,
                "migrated_kernel_epoch": graph.kernel_epoch,
                "models": len(graph.models),
                "claims": len(graph.claims),
                "verdicts": len(graph.verdicts),
                "current_verdicts": sum(
                    bool(verdict.get("current"))
                    for verdict in graph.verdicts.values()),
                "findings": [finding.as_dict() for finding in findings],
            })
        _graph, conflicts = S.merge_report(migrated)
        return {
            "schema": "grand-portage-arr15-e10-replay/v1",
            "sources_unchanged": True,
            "lanes": results,
            "merge_conflicts": [{
                "kind": conflict["kind"],
                "id": conflict["id"],
                "fields": conflict["fields"],
            } for conflict in conflicts],
        }


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--windows", required=True,
                        help="preserved Windows/local E10 graph")
    parser.add_argument("--mac", required=True,
                        help="preserved native Mac E10 graph")
    args = parser.parse_args(argv)
    print(json.dumps(replay({"windows": args.windows, "mac": args.mac}),
                     indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
