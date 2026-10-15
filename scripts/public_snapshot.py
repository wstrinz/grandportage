#!/usr/bin/env python3
"""Compile a deterministic public Grand Portage snapshot from one Git tree."""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path, PurePosixPath
import re
import subprocess


ROOT = Path(__file__).resolve().parents[1]
DEFAULT_MANIFEST = "public-snapshot-v2.json"
SCHEMA = "grand-portage-public-snapshot/v1"
RECEIPT_SCHEMA = "grand-portage-public-snapshot-receipt/v2"
RECEIPT_PATH = "PUBLIC-SNAPSHOT-RECEIPT.json"
_FIELDS = {
    "schema", "generated_paths", "private_paths", "private_prefixes",
    "public_paths", "public_prefixes", "required_public_paths",
    "campaign_path_allowlist",
}
# Optional: {"path": ..., "sha256": ...} naming a withheld file that lists further private paths, so
# the public manifest need not name them. Declared by hash, so a missing or altered overlay refuses.
OVERLAY_FIELD = "private_overlay"
OVERLAY_SCHEMA = "grand-portage-public-snapshot-private-overlay/v1"


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
    _require(isinstance(value, dict) and set(value) - {OVERLAY_FIELD} == _FIELDS, "MAN5",
             "manifest has unknown or missing fields")
    _require(value["schema"] == SCHEMA, "MAN6",
             "unsupported public snapshot schema")
    result = {"schema": SCHEMA}
    if OVERLAY_FIELD in value:
        overlay = value[OVERLAY_FIELD]
        _require(isinstance(overlay, dict) and set(overlay) == {"path", "sha256"} and
                 isinstance(overlay["sha256"], str) and len(overlay["sha256"]) == 64,
                 "MAN8", "private_overlay must be {path, sha256}")
        result[OVERLAY_FIELD] = {"path": _safe_path(overlay["path"], OVERLAY_FIELD),
                                 "sha256": overlay["sha256"]}
    for field in ("generated_paths", "private_paths", "public_paths",
                  "required_public_paths", "campaign_path_allowlist"):
        result[field] = _path_list(value[field], field)
    for field in ("private_prefixes", "public_prefixes"):
        result[field] = _path_list(value[field], field, prefixes=True)
    _require(RECEIPT_PATH in result["generated_paths"], "MAN7",
             "the generated receipt path is not declared")
    return result


def load_manifest(path):
    return load_manifest_bytes(Path(path).read_bytes())


def apply_private_overlay(manifest, paths, read):
    """The manifest with its declared overlay's paths added to private_paths.

    `read(path)` returns a tracked file's bytes. The overlay may be absent only from a tree with
    no private files (a public snapshot). Otherwise it must be present, match its declared SHA-256
    and be private itself."""
    declared = manifest.get(OVERLAY_FIELD)
    if declared is None:
        return manifest
    path = declared["path"]

    def by_prefix(item):
        return (_longest_prefix(item, manifest["private_prefixes"]) >
                _longest_prefix(item, manifest["public_prefixes"]))

    _require(by_prefix(path) and path not in manifest["public_paths"], "OVL2",
             "the private overlay would itself be public")
    if path not in paths:
        withheld = [item for item in paths
                    if item in manifest["private_paths"] or by_prefix(item)]
        _require(not withheld, "OVL1",
                 "the declared private overlay is absent from a tree with private files")
        return manifest
    payload = read(path)
    _require(digest_bytes(payload) == declared["sha256"], "OVL3",
             "the private overlay does not match its declared SHA-256")
    try:
        value = json.loads(payload.decode("utf-8"))
    except (UnicodeDecodeError, json.JSONDecodeError) as exc:
        raise PublicSnapshotError("OVL4: invalid private overlay: %s" % exc)
    _require(isinstance(value, dict) and "private_paths" in value and
             set(value) <= {"schema", "private_paths", "guarded_names", "audit_terms"} and
             value["schema"] == OVERLAY_SCHEMA, "OVL4", "invalid private overlay")
    extra = _path_list(value["private_paths"], "private_overlay.private_paths")
    guarded = value.get("guarded_names", [])
    _require(isinstance(guarded, list) and all(
        isinstance(g, str) and g and g == g.lower() for g in guarded), "OVL4",
        "guarded_names must be non-empty lowercase strings")
    named = set(manifest["private_paths"]) | set(manifest["public_paths"]) | set(
        manifest["generated_paths"])
    _require(not set(extra) & named, "OVL5", "the private overlay repeats a manifest path")
    result = dict(manifest)
    result["private_paths"] = sorted(manifest["private_paths"] + extra)
    result["guarded_names"] = sorted(guarded)
    terms = value.get("audit_terms", [])
    _require(isinstance(terms, list) and all(isinstance(x, str) and x for x in terms), "OVL4",
             "audit_terms must be non-empty strings")
    result["audit_terms"] = sorted(terms)
    return result


def _matches(path, exact, prefixes):
    return path in exact or any(path.startswith(prefix) for prefix in prefixes)


def _longest_prefix(path, prefixes):
    """Length of the longest prefix in `prefixes` that `path` starts with, or -1."""
    return max((len(prefix) for prefix in prefixes if path.startswith(prefix)),
               default=-1)


def _campaign_domain_path(path):
    lowered = path.lower()
    parts = PurePosixPath(lowered).parts
    markers = ("jc_", "jc-", "arr15")
    return any(part.startswith(markers) or part in {
        "jc2", "gamma_window", "jc_sigma", "jc_publication"
    } for part in parts)


def _guarded_name_path(path, names):
    """A path naming a withheld campaign the private overlay guards (N7). A plain name matches a whole
    token of the path; a name with separators matches as a substring, with - and _ alike."""
    lowered = path.lower()
    tokens = set(re.split(r"[^a-z0-9]+", lowered))
    flat = lowered.replace("_", "-")
    return any((name in tokens) if re.fullmatch(r"[a-z0-9]+", name)
               else name.replace("_", "-") in flat for name in names)


def _withheld_by_prefix(manifest, path):
    """A path a private prefix withholds (and no exact public declaration ships)."""
    return path not in manifest["public_paths"] and (
        _longest_prefix(path, manifest["private_prefixes"]) >
        _longest_prefix(path, manifest["public_prefixes"]))


def refuse_new_campaign_paths(manifest, paths):
    allowlist = manifest["campaign_path_allowlist"]
    guarded = manifest.get("guarded_names", [])
    violations = sorted(path for path in paths
                        if (_campaign_domain_path(path) or
                            (_guarded_name_path(path, guarded) and
                             not _withheld_by_prefix(manifest, path)))
                        and not any(path == allowed or path.startswith(allowed)
                                    for allowed in allowlist))
    _require(not violations, "CAMP1",
             "campaign-domain paths require an explicit custody allowlist: %s"
             % ", ".join(violations))


def classify_paths(manifest, paths):
    refuse_new_campaign_paths(manifest, paths)
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
            # The longest matching prefix decides, so a private directory can
            # hold public subdirectories (and the reverse) without the
            # manifest naming any private subdirectory.  The same prefix
            # declared on both sides stays an overlap.
            public_length = _longest_prefix(path, manifest["public_prefixes"])
            private_length = _longest_prefix(path, manifest["private_prefixes"])
            is_public = public_length >= 0 and public_length >= private_length
            is_private = private_length >= 0 and private_length >= public_length
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


def revision_blobs(root, commit, paths):
    """{path: raw blob bytes} for every path, read through one `git cat-file --batch` process rather than one
    `git show` each (thousands of processes were slow and hit the per-call timeout under load). A path with a
    newline cannot be named in batch input, so it falls back to `git show`."""
    batched = [path for path in paths if "\n" not in path]
    request = "".join("%s:%s\n" % (commit, path) for path in batched).encode("utf-8")
    process = subprocess.run(
        ["git", "-c", "safe.directory=%s" % root.as_posix(), "-C", str(root), "cat-file", "--batch"],
        input=request, capture_output=True, check=False)
    _require(process.returncode == 0, "GIT5",
             process.stderr.decode("utf-8", "replace").strip() or "git cat-file failed")
    out, pos, blobs = process.stdout, 0, {}
    for path in batched:
        end = out.index(b"\n", pos)
        header = out[pos:end].split()
        _require(len(header) == 3 and header[1] == b"blob", "GIT6",
                 "%s:%s is not a blob in the revision" % (commit, path))
        size = int(header[2])
        start = end + 1
        blobs[path] = out[start:start + size]
        _require(out[start + size:start + size + 1] == b"\n", "GIT6", "malformed cat-file output")
        pos = start + size + 1
    _require(pos == len(out), "GIT6", "unexpected trailing cat-file output")
    for path in paths:
        if path not in blobs:
            blobs[path] = revision_blob(root, commit, path)
    return blobs


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
        # v2: a commitment, not the list. Withheld paths can name unpublished work; the workspace
        # recomputes this digest to show which paths were withheld.
        "private_paths_sha256": digest_bytes(
            "".join("%s\n" % path for path in classifications["private"]).encode("utf-8")),
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
    manifest = apply_private_overlay(manifest, paths,
                                     lambda path: revision_blob(root, commit, path))
    classifications = classify_paths(manifest, paths)
    blobs = revision_blobs(root, commit, classifications["public"])
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


# Generic patterns that must never reach the public tree; campaign terms live only in the withheld overlay.
GENERIC_AUDIT = [
    re.compile(r"[A-Za-z]:[\\/]+(?:Users|repos|caches|trials|tools)[\\/]", re.I),  # a local machine path
    re.compile(r"/(?:home|Users)/[a-z][a-z0-9_-]*/", re.I),
    re.compile(r"ghp_[A-Za-z0-9]{20,}|github_pat_[A-Za-z0-9_]{20,}|sk-ant-[A-Za-z0-9_-]{10,}|AKIA[0-9A-Z]{16}"),
    re.compile(r"-----BEGIN [A-Z ]*PRIVATE KEY-----"),
]


def audit_terms_for(source_root, revision, manifest_path=DEFAULT_MANIFEST):
    """The guarded names and private audit terms of a revision's overlay ([] in a public tree)."""
    root = Path(source_root).resolve()
    commit = resolve_revision(root, revision)
    paths = revision_paths(root, commit)
    manifest = load_manifest_bytes(revision_blob(root, commit, manifest_path))
    manifest = apply_private_overlay(manifest, paths, lambda path: revision_blob(root, commit, path))
    return manifest.get("guarded_names", []) + manifest.get("audit_terms", [])


def audit_snapshot(blobs, published_dir, terms):
    """Lines new to the snapshot (absent from the same file in the published tree) that match a generic pattern,
    a guarded name (as a whole token, or a hyphenated name as a substring) or a private audit term
    (case-insensitive substring). Returns [(path, line_number, matched)]; unchanged lines are not re-reported."""
    published = Path(published_dir)
    plain = [n for n in terms if re.fullmatch(r"[a-z0-9]+", n)]
    phrases = [n.lower() for n in terms if n not in plain]
    hits = []
    for path, payload in sorted(blobs.items()):
        try:
            lines = payload.decode("utf-8").splitlines()
        except UnicodeDecodeError:
            continue
        old_file = published / path
        old = set()
        if old_file.is_file():
            old = set(old_file.read_bytes().decode("utf-8", "replace").splitlines())
        for number, line in enumerate(lines, 1):
            if line in old:
                continue
            lowered = line.lower()
            tokens = set(re.split(r"[^a-z0-9]+", lowered))
            found = [pattern.pattern for pattern in GENERIC_AUDIT if pattern.search(line)]
            found += [n for n in plain if n in tokens]
            found += [n for n in phrases if n.replace("_", "-") in lowered.replace("_", "-")]
            if found:
                hits.append((path, number, found[0]))
    return hits


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source-root", type=Path, default=ROOT)
    parser.add_argument("--revision", default="HEAD")
    parser.add_argument("--manifest", default=DEFAULT_MANIFEST)
    parser.add_argument("--output-dir", type=Path)
    parser.add_argument("--audit-against", type=Path,
                        help="the published tree; refuse if a new line leaks a machine path, a secret or a "
                             "withheld name")
    args = parser.parse_args(argv)
    try:
        blobs, receipt = compile_snapshot(
            args.source_root, args.revision, args.manifest)
        if args.audit_against is not None:
            hits = audit_snapshot(blobs, args.audit_against,
                                  audit_terms_for(args.source_root, args.revision, args.manifest))
            # The matched term is not printed: it may itself be a withheld name.
            _require(not hits, "AUD1", "new lines leak a machine path, a secret or a withheld name: %s"
                     % ", ".join("%s:%d" % (path, number) for path, number, _ in hits[:20]))
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
