"""Exact implementation identity shared by CLI, MCP, graphs, and diagnostics."""

from functools import lru_cache
from pathlib import Path
import subprocess

from . import backend as B


MCP_PROTOCOL_VERSION = "2025-06-18"
IDENTITY_SCHEMA = "grand-portage-implementation/v1"


def _git(root, *args):
    try:
        completed = subprocess.run(
            ["git", "-c", "safe.directory=%s" % root, "-C", str(root)]
            + list(args),
            stdin=subprocess.DEVNULL, capture_output=True, text=True,
            timeout=10)
    except (OSError, subprocess.SubprocessError):
        return None
    if completed.returncode:
        return None
    return completed.stdout.strip()


@lru_cache(maxsize=1)
def source_root():
    """Return the checkout containing this package, if it is a Git tree."""
    candidate = Path(__file__).resolve().parents[1]
    top = _git(candidate, "rev-parse", "--show-toplevel")
    return str(Path(top).resolve()) if top else None


@lru_cache(maxsize=1)
def source_identity():
    """Return the source revision seen by this running process."""
    root = source_root()
    commit = _git(root, "rev-parse", "HEAD") if root else None
    status = _git(root, "status", "--porcelain", "--untracked-files=normal") \
        if root else None
    return commit, None if status is None else bool(status)


def implementation_identity(package_version, graph_format, kernel_epoch):
    """Return a closed, portable identity for the executing implementation."""
    commit, dirty = source_identity()
    return {
        "schema": IDENTITY_SCHEMA,
        "package_version": package_version,
        "source_commit": commit,
        "source_dirty": dirty,
        "graph_format": graph_format,
        "kernel_epoch": kernel_epoch,
        "mcp_protocol": MCP_PROTOCOL_VERSION,
        "backend": {
            "contract": B.SINGULAR_CONTRACT,
            "implementation": B.SINGULAR_IMPLEMENTATION,
            "implementation_version": B.SINGULAR_IMPLEMENTATION_VERSION,
            "protocol_version": B.BACKEND_PROTOCOL_VERSION,
        },
    }


def version_text(identity):
    values = dict(identity)
    values["source_commit"] = identity.get("source_commit") or "unavailable"
    dirty = identity.get("source_dirty")
    dirty_text = "unknown" if dirty is None else str(dirty).lower()
    values["dirty"] = dirty_text
    return (
        "grand-portage {package_version}\n"
        "source {source_commit}\n"
        "dirty {dirty}\n"
        "graph format {graph_format}\n"
        "kernel epoch {kernel_epoch}\n"
        "MCP protocol {mcp_protocol}\n"
        "backend {backend[implementation]} implementation "
        "{backend[implementation_version]} / protocol "
        "{backend[protocol_version]}"
    ).format(**values)
