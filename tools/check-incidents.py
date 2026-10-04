"""Validate the finite Phase0b inventory, bindings and private custody."""
import argparse
import hashlib
import json
import subprocess
from collections import Counter
from pathlib import Path

import jsonschema

ROOT = Path(__file__).resolve().parents[1]

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def read(path):
    return json.loads(path.read_text(encoding="utf-8-sig"))

def local(path):
    resolved = (ROOT / path).resolve()
    if not resolved.is_relative_to(ROOT):
        raise ValueError("Inventory path escapes workspace: " + path)
    return resolved

def validate():
    manifest_path = local("corpus/incident-registers/MANIFEST.json")
    manifest = read(manifest_path)
    schema_path = local(manifest["schema"]["path"])
    if sha(schema_path) != manifest["schema"]["sha256"]:
        raise ValueError("Incident schema changed without updated binding")
    validator = jsonschema.Draft202012Validator(read(schema_path), format_checker=jsonschema.FormatChecker())
    records = []
    for binding in manifest["records"]:
        path = local(binding["path"])
        if sha(path) != binding["sha256"] or path.stem != binding["id"]:
            raise ValueError("Incident record binding changed: " + binding["id"])
        record = read(path)
        if record["id"] != binding["id"]:
            raise ValueError("Incident ID differs from bound filename")
        records.append(record)
    separate_path = local(manifest["separate_register"]["path"])
    if sha(separate_path) != manifest["separate_register"]["sha256"]:
        raise ValueError("Separate-register binding changed")
    separate = read(separate_path)
    main = records + separate["main_dispositions"]
    originals = read(local("reports/PHASE-0B-INVENTORY-DRAFT.json"))["rows"]
    supplement = read(local("reports/PHASE-0B-GP-INVENTORY-SUPPLEMENT-DRAFT.json"))
    originals += supplement["operational_entries"] + supplement["named_gp_source_groups"]
    original_ids = {r["id"] for r in originals}
    if len(main) != len({r["id"] for r in main}) or {r["id"] for r in main} != original_ids:
        raise ValueError("Main IDs missing, duplicated or added")
    cache = {}
    pointers = set()
    def resolve_pointer(binding):
        path = local(binding["report"])
        if "sha256" in binding and sha(path) != binding["sha256"]:
            raise ValueError("Referenced report hash changed: " + binding["report"])
        if path not in cache:
            cache[path] = read(path)
        node = cache[path]
        for token in binding["pointer"].lstrip("/").split("/"):
            token = token.replace("~1", "/").replace("~0", "~")
            node = node[int(token)] if isinstance(node, list) else node[token]
        pointers.add((str(path), binding["pointer"]))
        return node
    for record in main:
        validator.validate(record)
        original = resolve_pointer(record["original_pointer"])
        if original["id"] != record["id"]:
            raise ValueError("Record original pointer names another owner")
        for key in ("claimed", "problem", "sources", "class", "origin", "campaign",
                    "scope_or_region", "cost", "shipped", "gp_v037_would_catch",
                    "core_expressible", "core_would_refuse"):
            if record.get(key) != original.get(key):
                raise ValueError("Original evidence field changed: " + record["id"] + "/" + key)
        if record["counting_qualification"]["independent_sample"] is not None:
            raise ValueError("Unestablished independent sample status")
        if "review-source date" not in record["source"]["date_kind"]:
            raise ValueError("Source review date qualification missing")
        for value, note in (("cost", "cost_note"), ("shipped", "shipped_note"),
                            ("gp_v037_would_catch", "gp_v037_would_catch_note")):
            if record[value] is None and not record.get(note):
                raise ValueError("Unknown field lacks explanation")
        if record["core_expressible"] is not None or record["core_would_refuse"] is not None:
            raise ValueError("Premature core verdict")
    for dimension in ("class", "origin", "campaign"):
        if dict(Counter(r[dimension] for r in main)) != manifest["counts"]["all_by_" + dimension]:
            raise ValueError("Descriptive count mismatch")
    group_map = {r["id"]: r for r in main if r["id"].startswith("GP-SRC-")}
    subepisodes = 0
    for original in supplement["named_gp_source_groups"]:
        current = group_map[original["id"]]["subepisodes"]
        if [r["id"] for r in current] != [r["id"] for r in original["subepisodes"]]:
            raise ValueError("Nested episode IDs changed")
        for old, new in zip(original["subepisodes"], current):
            if any(new.get(k) != v for k, v in old.items()):
                raise ValueError("Nested original episode fields changed")
        subepisodes += len(current)
    if subepisodes != 47:
        raise ValueError("Nested episode coverage mismatch")
    if {r["id"] for r in separate["cross_occurrence_ownership"]} != {"DK-B018", "PR-O01", "PR-O02", "PR-T15"}:
        raise ValueError("Cross-occurrence ownership changed")
    auxiliary = read(local("reports/PHASE-0B-INVENTORY-DRAFT.json"))["excluded_or_separate_register"]
    if {r["id"] for r in auxiliary} != {r["id"] for r in separate["auxiliary_index"]}:
        raise ValueError("Auxiliary index coverage mismatch")
    harvest_paths = []
    for path in sorted((ROOT / "reports").glob("PHASE-0B-*-HARVEST-MANIFEST.json")):
        for entry in read(path)["entries"]:
            target = local(entry["harvest"])
            if not target.is_relative_to(local("corpus/harvest")) or sha(target) != entry["sha256"] or target.stat().st_size != entry["bytes"]:
                raise ValueError("Private custody mismatch: " + entry["harvest"])
            harvest_paths.append(entry["harvest"].replace("\\", "/"))
    if len(harvest_paths) != len(set(harvest_paths)) or len(harvest_paths) != 89:
        raise ValueError("Private harvest coverage mismatch")
    ignored = subprocess.check_output(["git", "-C", str(ROOT), "check-ignore", "-z", "--stdin"],
                                     input=("\0".join(harvest_paths) + "\0").encode("utf-8"))
    if {p.decode("utf-8") for p in ignored.split(b"\0") if p} != set(harvest_paths):
        raise ValueError("Private harvest is not fully ignored")
    if manifest["pivot_screen"]["status"] != "indeterminate" or manifest["pivot_screen"]["high_cost_denominator"] is not None:
        raise ValueError("Unsupported statistical screen result")
    return {"status": "passed", "incident_correction_group_records": len(records),
            "separate_main_records": len(separate["main_dispositions"]), "all_main_records": len(main),
            "unique_original_pointers": len(pointers), "nested_gp_subdispositions": subepisodes,
            "auxiliary_index_entries": len(auxiliary), "private_files_hash_size_ignore_checked": 89,
            "pivot_screen": "indeterminate", "fresh_campaign_execution": False}

if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--report", action="store_true")
    args = parser.parse_args()
    result = validate()
    if args.report:
        (ROOT / "reports/PHASE-0B-FINAL-VALIDATION.json").write_text(
            json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(result))
