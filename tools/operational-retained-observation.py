"""Verify retained operational evidence bindings without calling an oracle.

This is a diagnostic reader. Its manifest digest must be pinned by the caller;
otherwise a replaced manifest could simply rebind altered evidence.
"""

import argparse
import hashlib
import json
import re
import sys
from pathlib import Path, PurePosixPath

WORKSPACE = Path(__file__).resolve().parents[1]
MANIFEST = "reports/PHASE-0A-OPERATIONAL-EVIDENCE-BINDINGS.json"
KIND = "gp-operational-retained-observation-bindings/v1"
SOURCE_COMMIT = "ac4155787207e2847d248cffed7be871d5dcd577"
LAYERS = {
    "retained_bounded_diagnostic",
    "offline_direct_bounded_control",
    "accepted_injected_persistence_contrast",
}


class BindingError(Exception):
    """The trusted binding cannot be verified."""


def _digest(data):
    return hashlib.sha256(data).hexdigest()


def _canonical_digest(value):
    data = json.dumps(value, sort_keys=True, separators=(",", ":"),
                      ensure_ascii=False, allow_nan=False).encode("utf-8")
    return _digest(data)


def _required(mapping, key, expected_type):
    if not isinstance(mapping, dict) or key not in mapping:
        raise BindingError("missing binding field: " + key)
    value = mapping[key]
    if not isinstance(value, expected_type):
        raise BindingError("wrong binding field type: " + key)
    return value


def _inside_file(root, relative):
    if not isinstance(relative, str) or not relative or "\\" in relative:
        raise BindingError("invalid relative file path")
    pure = PurePosixPath(relative)
    if pure.is_absolute() or any(part in (".", "..") for part in pure.parts):
        raise BindingError("unsafe relative file path")
    try:
        resolved = (root / Path(*pure.parts)).resolve(strict=True)
    except (OSError, RuntimeError) as exc:
        raise BindingError("bound file missing: " + relative) from exc
    if not resolved.is_relative_to(root) or not resolved.is_file():
        raise BindingError("bound file escapes workspace or is not a file")
    return resolved


def _read_json_file(path, label):
    try:
        raw = path.read_bytes()
        return raw, json.loads(raw.decode("utf-8"))
    except (OSError, UnicodeError, json.JSONDecodeError) as exc:
        raise BindingError("invalid bound JSON: " + label) from exc


def _pointer(document, pointer):
    if not pointer.startswith("#/"):
        raise BindingError("evidence ref must contain a JSON pointer")
    value = document
    for raw in pointer[2:].split("/"):
        if re.search(r"~(?![01])", raw):
            raise BindingError("invalid JSON pointer escape")
        key = raw.replace("~1", "/").replace("~0", "~")
        try:
            if isinstance(value, list):
                if not re.fullmatch(r"0|[1-9][0-9]*", key):
                    raise BindingError("invalid JSON array index")
                value = value[int(key)]
            elif isinstance(value, dict):
                value = value[key]
            else:
                raise BindingError("JSON pointer crosses a scalar")
        except (IndexError, KeyError) as exc:
            raise BindingError("JSON pointer target missing") from exc
    return value


def _candidate_refs(candidate):
    inputs = _required(candidate, "inputs", dict)
    refs = _required(inputs, "retained_evidence_refs", list)
    if "bounded_control_ref" in inputs:
        refs = refs + [_required(inputs, "bounded_control_ref", str)]
    if not refs or any(not isinstance(ref, str) for ref in refs):
        raise BindingError("candidate has no valid evidence refs")
    if len(refs) != len(set(refs)):
        raise BindingError("duplicate candidate evidence ref")
    return refs


def verify(candidate_id, *, workspace=WORKSPACE, manifest=MANIFEST,
           manifest_sha256):
    """Return a null-verdict diagnostic only after all target bindings verify."""
    root = Path(workspace).resolve(strict=True)
    if not re.fullmatch(r"GP-X[0-9]{3}", candidate_id):
        raise BindingError("invalid operational candidate id")
    if not re.fullmatch(r"[0-9a-fA-F]{64}", manifest_sha256):
        raise BindingError("a trusted 64-hex manifest SHA-256 is required")
    manifest_path = _inside_file(root, manifest)
    manifest_raw, bindings = _read_json_file(manifest_path, "manifest")
    if _digest(manifest_raw) != manifest_sha256.lower():
        raise BindingError("binding manifest SHA-256 mismatch")
    if _required(bindings, "binding_kind", str) != KIND:
        raise BindingError("unsupported binding kind")
    if _required(bindings, "frozen_source_commit", str) != SOURCE_COMMIT:
        raise BindingError("frozen source commit mismatch")
    entries = _required(bindings, "candidates", list)
    if len(entries) != _required(bindings, "candidate_count", int):
        raise BindingError("binding candidate count mismatch")
    ids = [_required(entry, "id", str) for entry in entries]
    if len(set(ids)) != len(ids) or ids.count(candidate_id) != 1:
        raise BindingError("target candidate binding missing or duplicated")
    entry = entries[ids.index(candidate_id)]

    expected_path = "reports/operational-case-candidates/" + candidate_id + ".json"
    if _required(entry, "candidate_path", str) != expected_path:
        raise BindingError("candidate path binding mismatch")
    candidate_path = _inside_file(root, expected_path)
    candidate_raw, candidate = _read_json_file(candidate_path, candidate_id)
    if _digest(candidate_raw) != _required(entry, "candidate_file_sha256", str):
        raise BindingError("candidate file SHA-256 mismatch")
    if _canonical_digest(candidate) != _required(entry, "candidate_canonical_sha256", str):
        raise BindingError("candidate canonical SHA-256 mismatch")
    if _required(candidate, "id", str) != candidate_id:
        raise BindingError("candidate identity mismatch")
    inputs = _required(candidate, "inputs", dict)
    if _required(inputs, "incident_row", str) != _required(entry, "incident_row", str):
        raise BindingError("incident row mismatch")
    layer = _required(inputs, "observation_layer", str)
    if layer not in LAYERS or layer != _required(entry, "observation_layer", str):
        raise BindingError("observation layer mismatch")

    source = _required(entry, "primary_source", dict)
    sources = _required(candidate, "sources", list)
    if not sources or not isinstance(sources[0], dict):
        raise BindingError("primary candidate source missing")
    for key in ("repository", "commit", "path", "line", "anchor"):
        if _required(sources[0], key, int if key == "line" else str) != (
                _required(source, key, int if key == "line" else str)):
            raise BindingError("primary source binding mismatch: " + key)
    if source["repository"] != "gp-v037" or source["commit"] != SOURCE_COMMIT:
        raise BindingError("primary source identity mismatch")
    source_path = _inside_file(root, "oracle/checkout/" + source["path"])
    if _digest(source_path.read_bytes()) != _required(source, "file_sha256", str):
        raise BindingError("frozen primary source SHA-256 mismatch")
    lines = source_path.read_text(encoding="utf-8").splitlines()
    line = source["line"]
    if line < 1 or line > len(lines) or lines[line - 1].strip() != source["anchor"]:
        raise BindingError("frozen primary source anchor mismatch")

    refs = _candidate_refs(candidate)
    evidence = _required(entry, "evidence", list)
    if refs != [_required(item, "ref", str) for item in evidence]:
        raise BindingError("candidate evidence binding list mismatch")
    for item in evidence:
        ref = item["ref"]
        if ref.count("#") != 1:
            raise BindingError("invalid evidence ref")
        path_part, pointer = ref.split("#", 1)
        if not path_part.startswith("reports/") or not path_part.endswith(".json"):
            raise BindingError("evidence must be a reports JSON file")
        path = _inside_file(root, path_part)
        raw, document = _read_json_file(path, path_part)
        if _digest(raw) != _required(item, "file_sha256", str):
            raise BindingError("evidence file SHA-256 mismatch: " + path_part)
        if _canonical_digest(_pointer(document, "#" + pointer)) != (
                _required(item, "pointer_canonical_sha256", str)):
            raise BindingError("evidence pointer SHA-256 mismatch: " + ref)

    return {
        "candidate_id": candidate_id,
        "incident_row": entry["incident_row"],
        "observation_layer": layer,
        "diagnostic_status": "RETAINED_DIAGNOSTIC_BINDINGS_VERIFIED",
        "observed_verdict": None,
        "oracle_called": False,
        "agreement": None,
        "evidence_refs_verified": len(evidence),
        "binding_manifest_sha256": "sha256:" + manifest_sha256.lower(),
    }


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--candidate", required=True)
    parser.add_argument("--workspace", default=str(WORKSPACE))
    parser.add_argument("--manifest", default=MANIFEST)
    parser.add_argument("--manifest-sha256", required=True,
                        help="trusted whole-file SHA-256 of the binding manifest")
    args = parser.parse_args(argv)
    try:
        result = verify(args.candidate, workspace=args.workspace,
                        manifest=args.manifest,
                        manifest_sha256=args.manifest_sha256)
        code = 0
    except (BindingError, OSError, UnicodeError, ValueError, TypeError) as exc:
        result = {
            "candidate_id": args.candidate,
            "diagnostic_status": "RETAINED_DIAGNOSTIC_BINDING_FAILED",
            "observed_verdict": None,
            "oracle_called": False,
            "agreement": None,
            "error": str(exc),
        }
        code = 2
    print(json.dumps(result, sort_keys=True))
    return code


if __name__ == "__main__":
    sys.exit(main())
