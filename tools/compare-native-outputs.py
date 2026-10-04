"""Compare a fresh Phase 2 execution with the committed receipts, ignoring only environment metadata.

usage: python tools/compare-native-outputs.py <before-dir> <after-dir>
Each directory holds PHASE-2-*.json receipts with identical names. Native results, verdicts,
snapshots, controls and source contracts must match exactly; build/adapter/test hashes,
timings and aggregator identity fields are excluded because the refactor necessarily changes them.
"""
import json
from pathlib import Path
import sys

# Keys whose values are bound to the build environment or tool bytes, not native behaviour.
VOLATILE = {
    "build", "adapter_sha256", "tests_sha256", "elapsed_seconds", "runner_sha256",
    "reviewed_adapter_sha256", "shared_adapter_sha256", "executables", "runner_source_hashes",
    "harness_sha256", "olean_sha256", "wrapper_sha256", "build_input_hashes", "compile_log_sha256",
    "checker_log_sha256", "lean_path", "execution_reuse", "aggregation_mode",
}
# Keys that bind a receipt to toolchain binaries or to source/olean bytes. A toolchain bump or a
# Kernel refactor changes them by construction; they are reported, but do not fail the comparison.
PROVENANCE = {
    "runtime_command_template", "checker", "runtime", "kernel_source_sha256",
    "compiled_proof_sha256", "executable_sha256", "source_hashes", "identity_inspector_sha256",
}


def strip(value, path="", drop=VOLATILE):
    if isinstance(value, dict):
        return {k: strip(v, path + "." + k, drop) for k, v in value.items()
                if k not in drop and not k.endswith("_report_sha256")
                and not k.endswith("_supplement_sha256")}
    if isinstance(value, list):
        return [strip(v, path, drop) for v in value]
    return value


def diff(a, b, path="", out=None, limit=20):
    out = [] if out is None else out
    if len(out) >= limit:
        return out
    if type(a) is not type(b):
        out.append(f"{path}: type {type(a).__name__} -> {type(b).__name__}")
    elif isinstance(a, dict):
        for k in sorted(set(a) | set(b)):
            if k not in a or k not in b:
                out.append(f"{path}.{k}: {'added' if k not in a else 'removed'}")
            else:
                diff(a[k], b[k], path + "." + k, out, limit)
    elif isinstance(a, list):
        if len(a) != len(b):
            out.append(f"{path}: length {len(a)} -> {len(b)}")
        for i, (x, y) in enumerate(zip(a, b)):
            diff(x, y, f"{path}[{i}]", out, limit)
    elif a != b:
        out.append(f"{path}: {str(a)[:80]!r} -> {str(b)[:80]!r}")
    return out


def compare(before, after):
    results = {}
    for old in sorted(Path(before).glob("PHASE-2-*.json")):
        new = Path(after) / old.name
        if not new.exists():
            continue
        a = json.loads(old.read_text(encoding="utf-8"))
        b = json.loads(new.read_text(encoding="utf-8"))
        behaviour = diff(strip(a, drop=VOLATILE | PROVENANCE), strip(b, drop=VOLATILE | PROVENANCE))
        provenance = diff(strip(a), strip(b))
        results[old.name] = (behaviour, len(provenance))
    return results


if __name__ == "__main__":
    results = compare(sys.argv[1], sys.argv[2])
    for name, (problems, provenance) in results.items():
        label = "DIFFERS   " if problems else ("PROVENANCE" if provenance else "IDENTICAL ")
        print(label + " " + name + (f"  ({provenance} provenance fields)" if provenance and not problems else ""))
        for p in problems:
            print("    " + p)
    raise SystemExit(0 if all(not p for p, _ in results.values()) else 1)
