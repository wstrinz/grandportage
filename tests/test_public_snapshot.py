import importlib.util
import json
from pathlib import Path
import subprocess

import pytest


ROOT = Path(__file__).resolve().parents[1]
SCRIPT = ROOT / "scripts" / "public_snapshot.py"
MANIFEST = ROOT / "public-snapshot-v2.json"


def _load():
    spec = importlib.util.spec_from_file_location(
        "public_snapshot_test", SCRIPT)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def _candidate_paths():
    top = subprocess.run(
        ["git", "rev-parse", "--show-toplevel"], cwd=ROOT,
        capture_output=True, text=True, check=False)
    if top.returncode != 0 or Path(top.stdout.strip()).resolve() != ROOT:
        receipt_path = ROOT / "PUBLIC-SNAPSHOT-RECEIPT.json"
        if not receipt_path.is_file():
            raise AssertionError("snapshot has neither a local Git root nor a receipt")
        receipt = json.loads(receipt_path.read_text(encoding="utf-8"))
        return ([item["path"] for item in receipt["files"]] +
                ["PUBLIC-SNAPSHOT-RECEIPT.json"])
    completed = subprocess.run(
        ["git", "ls-files", "--cached", "--others", "--exclude-standard"],
        cwd=ROOT, capture_output=True, text=True, check=True)
    return [line for line in completed.stdout.splitlines() if line]


def _manifest(module, path=MANIFEST, paths=None):
    """The manifest with its private overlay applied, read from the working tree."""
    return module.apply_private_overlay(
        module.load_manifest(path), _candidate_paths() if paths is None else paths,
        lambda item: (ROOT / item).read_bytes())


def test_every_current_path_has_exactly_one_public_boundary_classification():
    module = _load()
    manifest = _manifest(module)
    result = module.classify_paths(manifest, _candidate_paths())

    assert "README.md" in result["public"]
    receipt_path = ROOT / module.RECEIPT_PATH
    if receipt_path.is_file():
        receipt = json.loads(receipt_path.read_text(encoding="utf-8"))
        assert len(receipt["private_paths_sha256"]) == 64
        assert receipt["counts"]["private_files"] > 0
        assert "private_paths" not in receipt
        assert "uv.lock" in manifest["private_paths"]
        assert not (ROOT / "uv.lock").exists()
        assert result["generated"] == [module.RECEIPT_PATH]
    else:
        assert "HANDOFF.md" in result["private"]
        assert "review/v0.32/SOL-HANDOFF.md" in result["private"]
        assert "uv.lock" in manifest["private_paths"]
        if (ROOT / "uv.lock").exists():
            assert "uv.lock" in result["private"]
        assert not result["generated"]


def test_new_unclassified_path_fails_closed():
    module = _load()
    manifest = _manifest(module)

    with pytest.raises(module.PublicSnapshotError, match="CLS2"):
        module.classify_paths(manifest, _candidate_paths() + ["SECRETS.md"])


def test_new_campaign_domain_path_fails_before_broad_public_prefix():
    module = _load()
    manifest = _manifest(module)
    with pytest.raises(module.PublicSnapshotError, match="CAMP1"):
        module.classify_paths(
            manifest,
            _candidate_paths() + ["experiments/arr15_ranker/adapter.py"],
        )


def test_public_and_private_overlap_is_refused():
    module = _load()
    manifest = _manifest(module)
    manifest["private_paths"].append("README.md")

    with pytest.raises(module.PublicSnapshotError, match="CLS1"):
        module.classify_paths(manifest, _candidate_paths())


def test_required_public_path_cannot_silently_disappear():
    module = _load()
    manifest = _manifest(module)
    paths = [path for path in _candidate_paths() if path != "LICENSE"]

    with pytest.raises(module.PublicSnapshotError, match="CLS3"):
        module.classify_paths(manifest, paths)


def test_receipt_is_deterministic_and_binds_every_public_byte():
    module = _load()
    manifest_payload = MANIFEST.read_bytes()
    classifications = {"public": ["a", "b"], "private": ["secret"],
                       "generated": []}
    blobs = {"b": b"second", "a": b"first"}
    first = module.build_receipt(
        "a" * 40, MANIFEST.name, manifest_payload, blobs, classifications)
    second = module.build_receipt(
        "a" * 40, MANIFEST.name, manifest_payload,
        dict(reversed(list(blobs.items()))), classifications)

    assert first == second
    assert first["counts"] == {
        "public_files": 2, "private_files": 1, "generated_files": 1}
    assert first["files"] == [
        {"path": "a", "sha256": module.digest_bytes(b"first")},
        {"path": "b", "sha256": module.digest_bytes(b"second")},
    ]


def test_materialization_requires_a_new_exact_target(tmp_path):
    module = _load()
    output = tmp_path / "snapshot"
    receipt = {"schema": module.RECEIPT_SCHEMA}
    module.materialize(output, {"nested/file.txt": b"payload"}, receipt)

    assert (output / "nested" / "file.txt").read_bytes() == b"payload"
    assert json.loads((output / module.RECEIPT_PATH).read_text(
        encoding="utf-8")) == receipt
    with pytest.raises(module.PublicSnapshotError, match="OUT1"):
        module.materialize(output, {}, receipt)


def _synthetic_manifest(module, **lists):
    manifest = {"schema": module.SCHEMA,
                "generated_paths": [module.RECEIPT_PATH],
                "campaign_path_allowlist": [], "private_paths": [],
                "private_prefixes": [], "public_paths": [],
                "public_prefixes": [], "required_public_paths": []}
    manifest.update(lists)
    return manifest


def test_longest_matching_prefix_decides():
    module = _load()
    manifest = _synthetic_manifest(
        module,
        private_prefixes=["work/", "work/open/deep/"],
        public_prefixes=["work/open/", "docs/"],
        private_paths=["docs/secret.md"],
        public_paths=["work/notice.md"])
    paths = ["work/x/a.md", "work/open/b.md", "work/open/deep/c.md",
             "work/notice.md", "docs/d.md", "docs/secret.md",
             module.RECEIPT_PATH]
    result = module.classify_paths(manifest, paths)

    assert result["public"] == ["docs/d.md", "work/notice.md", "work/open/b.md"]
    assert result["private"] == ["docs/secret.md", "work/open/deep/c.md",
                                 "work/x/a.md"]
    assert result["generated"] == [module.RECEIPT_PATH]

    # The same prefix declared on both sides is still an overlap, not a choice.
    manifest["public_prefixes"].append("work/")
    with pytest.raises(module.PublicSnapshotError, match="CLS1"):
        module.classify_paths(manifest, ["work/x/a.md"])


def _legacy_classify(manifest, path):
    """The rule before longest-prefix: any matching prefix counts, two kinds overlap."""
    if path in manifest["public_paths"] or path in manifest["private_paths"] \
            or path in manifest["generated_paths"]:
        flags = (path in manifest["public_paths"], path in manifest["private_paths"],
                 path in manifest["generated_paths"])
    else:
        flags = (any(path.startswith(p) for p in manifest["public_prefixes"]),
                 any(path.startswith(p) for p in manifest["private_prefixes"]),
                 False)
    if sum(flags) != 1:
        return "overlap" if sum(flags) else "unclassified"
    return ("public", "private", "generated")[flags.index(True)]


def _named_form(manifest, paths):
    """Rewrite each generic private prefix as the names it stands for on these paths."""
    named = {key: list(value) if isinstance(value, list) else value
             for key, value in manifest.items()}
    exact = set(manifest["public_paths"]) | set(manifest["private_paths"]) \
        | set(manifest["generated_paths"])
    for generic in manifest["private_prefixes"]:
        longer_public = [p for p in manifest["public_prefixes"]
                         if p.startswith(generic)]
        under_public = any(generic.startswith(p)
                           for p in manifest["public_prefixes"])
        if not longer_public and not under_public:
            continue
        named["private_prefixes"].remove(generic)
        for path in paths:
            if not path.startswith(generic) or path in exact or \
                    any(path.startswith(p) for p in longer_public):
                continue
            rest = path[len(generic):]
            if "/" in rest and not under_public:
                prefix = generic + rest.split("/")[0] + "/"
                if prefix not in named["private_prefixes"]:
                    named["private_prefixes"].append(prefix)
            else:
                named["private_paths"].append(path)
    return named


def test_generic_prefixes_classify_every_current_path_as_the_named_form():
    module = _load()
    manifest = module.load_manifest(MANIFEST)
    paths = _candidate_paths()
    current = module.classify_paths(manifest, paths)
    by_path = {path: kind for kind, items in current.items() for path in items}
    named = _named_form(manifest, paths)

    assert {path: _legacy_classify(named, path) for path in paths} == by_path


def test_manifests_name_no_withheld_campaign_rope_or_private_doc():
    module = _load()
    current = module.classify_paths(_manifest(module), _candidate_paths())
    withheld_campaigns = {path.split("/")[1] for path in current["private"]
                          if path.startswith("campaigns/") and path.count("/") >= 2}
    private_docs = {path.rsplit("/", 1)[1] for path in current["private"]
                    if path.startswith("docs/private/")}
    for manifest_path in (ROOT / "public-snapshot-v1.json", MANIFEST):
        text = manifest_path.read_text(encoding="utf-8")
        manifest = module.load_manifest(manifest_path)
        # The overlay's own (generic) name is declared; the paths it withholds are not named.
        private_docs.discard(manifest["private_overlay"]["path"].rsplit("/", 1)[1])
        # A public snapshot has no overlay (it is withheld); this check runs in the workspace.
        if (ROOT / manifest["private_overlay"]["path"]).is_file():
            overlay = _manifest(module, manifest_path)
            for path in set(overlay["private_paths"]) - set(manifest["private_paths"]):
                assert path not in text, (manifest_path.name, path)
        assert {"campaigns/", "ropes/", "docs/private/"} <= set(
            manifest["private_prefixes"])
        for prefix in manifest["private_prefixes"]:
            assert not (prefix.startswith(("campaigns/", "ropes/"))
                        and prefix.count("/") > 1), prefix
        assert not [path for path in manifest["private_paths"]
                    if path.startswith(("campaigns/", "ropes/", "docs/private/"))]
        for name in withheld_campaigns | private_docs:
            assert name not in text, (manifest_path.name, name)


def test_no_exact_private_path_repeats_a_private_prefix():
    module = _load()
    for manifest_path in (ROOT / "public-snapshot-v1.json", MANIFEST):
        manifest = module.load_manifest(manifest_path)
        redundant = [
            path for path in manifest["private_paths"]
            if module._longest_prefix(path, manifest["private_prefixes"]) >
            module._longest_prefix(path, manifest["public_prefixes"])]
        assert redundant == [], (manifest_path.name, redundant)


def test_private_overlay_fails_closed():
    module = _load()
    overlay_path = "private/OVERLAY.json"
    payload = (b'{"schema": "%s", "private_paths": ["docs/packet.md"]}'
               % module.OVERLAY_SCHEMA.encode())
    manifest = _synthetic_manifest(
        module, private_prefixes=["private/"], public_prefixes=["docs/"],
        private_overlay={"path": overlay_path, "sha256": module.digest_bytes(payload)})
    paths = ["docs/a.md", "docs/packet.md", overlay_path, module.RECEIPT_PATH]
    applied = module.apply_private_overlay(manifest, paths, lambda path: payload)
    result = module.classify_paths(applied, paths)
    assert result["private"] == ["docs/packet.md", overlay_path]
    assert result["public"] == ["docs/a.md"]

    # Altered overlay bytes.
    with pytest.raises(module.PublicSnapshotError, match="OVL3"):
        module.apply_private_overlay(manifest, paths, lambda path: payload + b" ")
    # Absent overlay in a tree that has private files: the packet would otherwise go public.
    with pytest.raises(module.PublicSnapshotError, match="OVL1"):
        module.apply_private_overlay(
            manifest, ["docs/a.md", "docs/packet.md", "private/other.md"], lambda path: payload)
    # Absent overlay in a public tree is fine.
    assert module.apply_private_overlay(
        manifest, ["docs/a.md", module.RECEIPT_PATH], lambda path: payload) is manifest
    # An overlay that would itself be published.
    public = dict(manifest, private_overlay={"path": "docs/OVERLAY.json",
                                             "sha256": module.digest_bytes(payload)})
    with pytest.raises(module.PublicSnapshotError, match="OVL2"):
        module.apply_private_overlay(public, paths, lambda path: payload)


def test_overlay_guarded_names_fail_closed():
    # N7: a public path naming a campaign the private overlay guards needs a custody decision, unless
    # a private prefix withholds it. The names live only in the (withheld) overlay.
    module = _load()
    overlay_path = "private/OVERLAY.json"
    payload = (b'{"schema": "%s", "private_paths": [], "guarded_names": ["zebu", "red-fox"]}'
               % module.OVERLAY_SCHEMA.encode())
    manifest = _synthetic_manifest(
        module, private_prefixes=["private/", "campaigns/"], public_prefixes=["docs/", "tools/"],
        private_overlay={"path": overlay_path, "sha256": module.digest_bytes(payload)})
    base = ["docs/a.md", overlay_path, module.RECEIPT_PATH]
    applied = module.apply_private_overlay(manifest, base, lambda path: payload)
    for path in ["docs/zebu-note.md", "tools/ZEBU_probe.py", "docs/red_fox/README.md"]:
        with pytest.raises(module.PublicSnapshotError, match="CAMP1"):
            module.classify_paths(applied, base + [path])
    # Whole tokens only for plain names; withheld paths need no custody entry.
    result = module.classify_paths(applied, base + ["docs/zebus.md", "campaigns/zebu/campaign.json"])
    assert "docs/zebus.md" in result["public"]
    assert "campaigns/zebu/campaign.json" in result["private"]
    with pytest.raises(module.PublicSnapshotError, match="OVL4"):
        bad = payload.replace(b'"zebu"', b'"Zebu"')
        module.apply_private_overlay(dict(manifest, private_overlay={
            "path": overlay_path, "sha256": module.digest_bytes(bad)}), base, lambda path: bad)


def test_workspace_guarded_names_are_live():
    # In the workspace, every name the overlay guards refuses a public path built from it.
    module = _load()
    manifest = module.load_manifest(MANIFEST)
    overlay = ROOT / manifest["private_overlay"]["path"]
    if not overlay.is_file():
        pytest.skip("public snapshot: the overlay is withheld")
    applied = _manifest(module)
    assert applied["guarded_names"], "the overlay guards no names"
    for name in applied["guarded_names"]:
        with pytest.raises(module.PublicSnapshotError, match="CAMP1"):
            module.classify_paths(applied, _candidate_paths() + [f"docs/{name}-note.md"])


def test_audit_flags_new_leaks_only(tmp_path):
    # A new line with a machine path, a guarded name or a private term is flagged; an unchanged line is not.
    module = _load()
    published = tmp_path / "published"
    (published / "docs").mkdir(parents=True)
    (published / "docs" / "a.md").write_bytes(b"old zebu line\n")
    machine = ("F" + ":/repos/x").encode()  # built, so the file itself holds no local path
    blobs = {"docs/a.md": b"old zebu line\nsee " + machine + b" for it\nthe zebu result\nred_fox notes\nfine\n",
             "docs/b.md": b"a zebus plural is fine\n"}
    hits = module.audit_snapshot(blobs, published, ["zebu", "red-fox"])
    assert [(path, line) for path, line, _ in hits] == [("docs/a.md", 2), ("docs/a.md", 3), ("docs/a.md", 4)]


def test_workspace_audit_terms_are_live(tmp_path):
    # In the workspace, every guarded name and private audit term is flagged on a new line.
    module = _load()
    manifest = module.load_manifest(MANIFEST)
    if not (ROOT / manifest["private_overlay"]["path"]).is_file():
        pytest.skip("public snapshot: the overlay is withheld")
    terms = module.audit_terms_for(ROOT, "HEAD")
    assert terms, "the overlay carries no audit terms"
    for term in terms:
        assert module.audit_snapshot({"docs/n.md": ("note: %s here\n" % term).encode()}, tmp_path, terms), term
