"""Verbatim local corpus intake. Hash checking is integrity, not authentication."""
import argparse
from collections import Counter
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import shutil

CAMPAIGNS = ("arr15", "cfg23", "cloquet")

def digest(data):
    return hashlib.sha256(data).hexdigest()

def events(data):
    return [json.loads(line) for line in data.decode("utf-8-sig").splitlines()
            if line.strip() and not line.lstrip().startswith("#")]

def fields(value, prefix=""):
    result = set()
    if isinstance(value, dict):
        for key, child in value.items():
            path = prefix + "/" + key.replace("~", "~0").replace("/", "~1")
            result.add(path)
            result.update(fields(child, path))
    elif isinstance(value, list):
        for child in value:
            result.update(fields(child, prefix + "/*"))
    return sorted(result)

def export(source, destination):
    """Explicit byte-copy operation; no fold, migration, verification or repair."""
    source, destination = Path(source).resolve(), Path(destination).resolve()
    if destination.exists() or source == destination or source in destination.parents:
        raise ValueError("export destination must be new and outside source")
    graph = source / "graph.jsonl"
    if not graph.is_file():
        raise ValueError("source must contain graph.jsonl")
    retained = []
    for path in sorted(source.rglob("*")):
        if path.is_symlink():
            raise ValueError("symlink in export source")
        if path.is_file():
            data = path.read_bytes()
            retained.append((path, data))
    destination.mkdir(parents=True)
    manifest = {"schema": "gp-corpus-export/v1", "source": str(source),
                "exported_at": datetime.now(timezone.utc).isoformat(),
                "export_command": "python scripts/corpus_check.py export SOURCE DESTINATION",
                "no_backfill": True, "files": []}
    for path, data in retained:
        relative = path.relative_to(source).as_posix()
        target = destination / relative
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_bytes(data)
        item = {"path": relative, "sha256": digest(data), "bytes": len(data)}
        if relative == "graph.jsonl":
            item["field_paths"] = fields(events(data))
        manifest["files"].append(item)
    # Refuse a concurrent source change; never silently call a torn copy a snapshot.
    if {p.relative_to(source).as_posix() for p in source.rglob("*") if p.is_file()} != {x["path"] for x in manifest["files"]}:
        raise ValueError("source file set changed during export; export incomplete")
    for path, data in retained:
        if path.read_bytes() != data:
            raise ValueError("source changed during export; export incomplete")
    (destination / "export-manifest.json").write_text(json.dumps(manifest, indent=2)+"\n", encoding="utf-8")
    return manifest

def validate_campaign(root):
    root = Path(root).resolve()
    manifest_path = root / "export-manifest.json"
    if not manifest_path.exists():
        return {"status": "BLOCKED-ON-CORPUS", "reasons": ["missing export manifest"]}
    manifest = json.loads(manifest_path.read_text())
    reasons = []
    if manifest.get("schema") != "gp-corpus-export/v1" or manifest.get("no_backfill") is not True:
        reasons.append("invalid no-backfill manifest")
    records = manifest.get("files", [])
    named = [r["path"] for r in records]
    if len(named) != len(set(named)):
        reasons.append("duplicate manifest path")
    actual = {p.relative_to(root).as_posix() for p in root.rglob("*") if p.is_file()}
    if actual != set(named) | {"export-manifest.json"}:
        reasons.append("unmanifested or missing file")
    graph_events = []
    for item in records:
        path = root / item["path"]
        if not path.resolve().is_relative_to(root) or path.is_symlink():
            reasons.append("unsafe manifest path")
            continue
        if not path.is_file():
            continue
        data = path.read_bytes()
        if digest(data) != item.get("sha256") or len(data) != item.get("bytes"):
            reasons.append("SHA mismatch: " + item["path"])
        if item["path"] == "graph.jsonl":
            graph_events = events(data)
            if fields(graph_events) != item.get("field_paths"):
                reasons.append("fields absent from or missing relative to export manifest")
    counts = Counter(e.get("ev") for e in graph_events)
    metas = [e for e in graph_events if e.get("ev") == "meta"]
    if not metas or any(e.get("graph_format") != 8 for e in metas):
        reasons.append("format-8 export required; no migration permitted")
    if not counts["verdict"]:
        reasons.append("retained verdict receipts absent")
    return {"status": "READY" if not reasons else "BLOCKED-ON-CORPUS",
            "reasons": reasons, "event_counts": dict(counts),
            "graph_formats": [e.get("graph_format") for e in metas],
            "export_manifest_sha256": digest(manifest_path.read_bytes()),
            "files": len(records), "bytes": sum(r["bytes"] for r in records),
            "authority_note": "verbatim retention only; load-time authority must be reconstructed and checked"}

def check(root):
    root = Path(root)
    baseline_path = root / "manifest.json"
    baseline = json.loads(baseline_path.read_text(encoding="utf-8")) if baseline_path.exists() else {}
    result = {"schema": "gp-corpus-intake/v1", "no_backfill": True,
              "campaigns": {c: validate_campaign(root/c) for c in CAMPAIGNS}}
    for campaign, report in result["campaigns"].items():
        expected = baseline.get("campaigns", {}).get(campaign, {}).get("export_manifest_sha256")
        observed = report.get("export_manifest_sha256")
        if expected is not None and observed != expected:
            report["status"] = "BLOCKED-ON-CORPUS"
            report["reasons"].append("export manifest changed since intake")
            report["observed_export_manifest_sha256"] = observed
            # A failed check must not silently replace the original pin.
            report["export_manifest_sha256"] = expected
    result["status"] = "READY" if all(c["status"] == "READY" for c in result["campaigns"].values()) else "BLOCKED-ON-CORPUS"
    return result

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest="command", required=True)
    ex = sub.add_parser("export"); ex.add_argument("source", type=Path); ex.add_argument("destination", type=Path)
    ck = sub.add_parser("check"); ck.add_argument("root", type=Path)
    args = parser.parse_args()
    if args.command == "export":
        export(args.source, args.destination)
        return 0
    result = check(args.root)
    args.root.mkdir(parents=True, exist_ok=True)
    (args.root/"manifest.json").write_text(json.dumps(result, indent=2)+"\n", encoding="utf-8")
    print(json.dumps(result, indent=2))
    return 0 if result["status"] == "READY" else 2

if __name__ == "__main__":
    raise SystemExit(main())
