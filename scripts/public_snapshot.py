#!/usr/bin/env python3
"""Compile a deterministic public Grand Portage snapshot from one Git tree."""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path, PurePosixPath
import subprocess


ROOT = Path(__file__).resolve().parents[1]
DEFAULT_MANIFEST = "public-snapshot-v1.json"
SCHEMA = "grand-portage-public-snapshot/v1"
RECEIPT_SCHEMA = "grand-portage-public-snapshot-receipt/v1"
RECEIPT_PATH = "PUBLIC-SNAPSHOT-RECEIPT.json"
_FIELDS = {
    "schema", "generated_paths", "private_paths", "private_prefixes",
    "public_paths", "public_prefixes", "required_public_paths",
}


class PublicSnapshotError(ValueError):
    """The public/private boundary or requested materialization is unsafe."""


def _require(condition, check_id, message):
    if not condition:
        raise PublicSnapshotError("%s: %s" % (check_id, message))


def canonical_json(value):
    return json.dumps(value, indent=2, sort_keys=True,
                      ensure_ascii=True) + "\n"


def digest_bytes(payload):
    return hashlib.sha256(payload).hexdigest()


def _safe_path(value, where):
    _require(isinstance(value, str) and value and "\\" not in value,
             "PATH1", "%s is not a normalized path" % where)
    path = PurePosixPath(value)
    _require(not path.is_absolute() and ".." not in path.parts and
             value not in {".", ".git"} and not value.startswith(".git/"),
             "PATH2", "%s escapes the snapshot root" % where)
    return value


def _path_list(value, where, prefixes=False):
    _require(isinstance(value, list), "MAN1", "%s must be a list" % where)
    result = []
    for index, item in enumerate(value):
        item = _safe_path(item, "%s[%d]" % (where, index))
        if prefixes:
            _require(item.endswith("/"), "MAN2",
                     "%s entries must end in /" % where)
        result.append(item)
    _require(len(result) == len(set(result)), "MAN3",
             "%s repeats an entry" % where)
    return sorted(result)


def load_manifest_bytes(payload):
    try:
        value = json.loads(payload.decode("utf-8"))
    except (UnicodeDecodeError, json.JSONDecodeError) as exc:
        raise PublicSnapshotError("MAN4: invalid manifest: %s" % exc)
    _require(isinstance(value, dict) and set(value) == _FIELDS, "MAN5",
             "manifest has unknown or missing fields")
    _require(value["schema"] == SCHEMA, "MAN6",
             "unsupported public snapshot schema")
    result = {"schema": SCHEMA}
    for field in ("generated_paths", "private_paths", "public_paths",
                  "required_public_paths"):
        result[field] = _path_list(value[field], field)
    for field in ("private_prefixes", "public_prefixes"):
        result[field] = _path_list(value[field], field, prefixes=True)
    _require(RECEIPT_PATH in result["generated_paths"], "MAN7",
             "the generated receipt path is not declared")
    return result


def load_manifest(path):
    return load_manifest_bytes(Path(path).read_bytes())


def _matches(path, exact, prefixes):
    return path in exact or any(path.startswith(prefix) for prefix in prefixes)


def classify_paths(manifest, paths):
    public = []
    private = []
    generated = []
    unclassified = []
    overlaps = []
    for index, raw_path in enumerate(paths):
        path = _safe_path(raw_path, "tracked_paths[%d]" % index)
        # Exact declarations are deliberate exceptions to broad directory
        # classifications.  This is how two private planning notes can remain
        # under otherwise-public docs/ without becoming ambiguous or public.
        exact_public = path in manifest["public_paths"]
        exact_private = path in manifest["private_paths"]
        is_generated = path in manifest["generated_paths"]
        exact_count = sum((exact_public, exact_private, is_generated))
        if exact_count:
            is_public = exact_public
            is_private = exact_private
        else:
            is_public = any(
                path.startswith(prefix) for prefix in manifest["public_prefixes"])
            is_private = any(
                path.startswith(prefix) for prefix in manifest["private_prefixes"])
        count = sum((is_public, is_private, is_generated))
        if count > 1:
            overlaps.append(path)
        elif is_public:
            public.append(path)
        elif is_private:
            private.append(path)
        elif is_generated:
            generated.append(path)
        else:
            unclassified.append(path)
    _require(not overlaps, "CLS1",
             "paths have multiple classifications: %s" %
             ", ".join(sorted(overlaps)))
    _require(not unclassified, "CLS2",
             "tracked paths are unclassified: %s" %
             ", ".join(sorted(unclassified)))
    missing = sorted(set(manifest["required_public_paths"]) - set(public))
    _require(not missing, "CLS3",
             "required public paths are absent: %s" % ", ".join(missing))
    return {
        "public": sorted(public),
        "private": sorted(private),
        "generated": sorted(generated),
    }


def _git(root, *args):
    command = ["git", "-c", "safe.directory=%s" % root.as_posix(),
               "-C", str(root)] + list(args)
    completed = subprocess.run(
        command, capture_output=True, check=False, timeout=30)
    _require(completed.returncode == 0, "GIT1",
             completed.stderr.decode("utf-8", "replace").strip() or
             "git command failed")
    return completed.stdout


def resolve_revision(root, revision):
    value = _git(root, "rev-parse", "%s^{commit}" % revision)
    commit = value.decode("ascii", "strict").strip()
    _require(len(commit) == 40 and all(c in "0123456789abcdef" for c in commit),
             "GIT2", "revision did not resolve to a full commit id")
    return commit


def revision_paths(root, commit):
    payload = _git(root, "ls-tree", "-r", "--name-only", "-z", commit)
    paths = [item.decode("utf-8") for item in payload.split(b"\0") if item]
    _require(len(paths) == len(set(paths)), "GIT3",
             "revision repeats a tracked path")
    return sorted(paths)


def revision_blob(root, commit, path):
    return _git(root, "show", "%s:%s" % (commit, path))


def build_receipt(commit, manifest_path, manifest_payload, blobs,
                  classifications):
    files = [
        {"path": path, "sha256": digest_bytes(payload)}
        for path, payload in sorted(blobs.items())
    ]
    snapshot_payload = "".join(
        "%s  %s\n" % (item["sha256"], item["path"]) for item in files
    ).encode("utf-8")
    return {
        "schema": RECEIPT_SCHEMA,
        "source_commit": commit,
        "manifest": {
            "path": manifest_path,
            "sha256": digest_bytes(manifest_payload),
        },
        "snapshot_sha256": digest_bytes(snapshot_payload),
        "counts": {
            "public_files": len(files),
            "private_files": len(classifications["private"]),
            "generated_files": 1,
        },
        "private_paths": classifications["private"],
        "files": files,
    }


def compile_snapshot(source_root=ROOT, revision="HEAD",
                     manifest_path=DEFAULT_MANIFEST):
    root = Path(source_root).resolve()
    manifest_path = _safe_path(manifest_path, "manifest_path")
    commit = resolve_revision(root, revision)
    paths = revision_paths(root, commit)
    _require(manifest_path in paths, "GIT4",
             "manifest is absent from the source revision")
    manifest_payload = revision_blob(root, commit, manifest_path)
    manifest = load_manifest_bytes(manifest_payload)
    classifications = classify_paths(manifest, paths)
    blobs = {
        path: revision_blob(root, commit, path)
        for path in classifications["public"]
    }
    receipt = build_receipt(
        commit, manifest_path, manifest_payload, blobs, classifications)
    return blobs, receipt


def materialize(output_dir, blobs, receipt):
    output = Path(output_dir)
    _require(not output.exists(), "OUT1",
             "output directory already exists: %s" % output)
    output.mkdir(parents=True)
    try:
        for relative, payload in sorted(blobs.items()):
            target = output / Path(*PurePosixPath(relative).parts)
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_bytes(payload)
        with (output / RECEIPT_PATH).open(
                "w", encoding="utf-8", newline="\n") as stream:
            stream.write(canonical_json(receipt))
    except Exception:
        # The caller supplied a new exact target, so an incomplete target can
        # be removed without risking unrelated user content.
        for path in sorted(output.rglob("*"), reverse=True):
            if path.is_file() or path.is_symlink():
                path.unlink()
            elif path.is_dir():
                path.rmdir()
        output.rmdir()
        raise
    return receipt


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source-root", type=Path, default=ROOT)
    parser.add_argument("--revision", default="HEAD")
    parser.add_argument("--manifest", default=DEFAULT_MANIFEST)
    parser.add_argument("--output-dir", type=Path)
    args = parser.parse_args(argv)
    try:
        blobs, receipt = compile_snapshot(
            args.source_root, args.revision, args.manifest)
        if args.output_dir is not None:
            materialize(args.output_dir, blobs, receipt)
        print(canonical_json({
            "status": "READY",
            "source_commit": receipt["source_commit"],
            "snapshot_sha256": receipt["snapshot_sha256"],
            "counts": receipt["counts"],
            "output_dir": (str(args.output_dir.resolve())
                           if args.output_dir is not None else None),
        }), end="")
        return 0
    except (OSError, UnicodeError, PublicSnapshotError) as exc:
        print(canonical_json({"status": "REFUSED", "error": str(exc)}),
              end="")
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
