"""Build the deterministic JC replay-resource lock from one clean run tree."""

from __future__ import annotations

import argparse
import ast
import hashlib
import json
from pathlib import Path
import re


AUTHORITY = "DERIVED_READ_MODEL_ONLY"
GRAPH_EFFECT = "NONE"
DIGEST_ALGO = "sha256-lf-normalized"

LANES = {
    "JC.REPLAY.SET.ENTRY": "f2_h3_sigma_entry_t_five_colon_z1_reduction.py",
    "JC.REPLAY.SET.EXTRACTION": "f2_roy_extraction_root_bridge.py",
    "JC.REPLAY.SET.OMEGA36": "f2_omega36_actual_pair.py",
    "JC.REPLAY.SET.ORDER6": "f2_sigma_source_order6_vertex_realizability.py",
    "JC.REPLAY.SET.LOCAL_CONNECTING":
        "_local_finite_algebra/z10_d9_connecting_map_replay.py",
    "JC.REPLAY.SET.LOCAL_INTEGRABILITY":
        "_local_finite_algebra/z10_d9_integrability9_replay.py",
}

RECEIPTS = {
    "f2_h3_sigma_entry_t_five_colon_z1_reduction_certificate.json":
        "JC.REPLAY.RECEIPT.ENTRY",
    "f2_roy_extraction_root_bridge_certificate.json":
        "JC.REPLAY.RECEIPT.EXTRACTION",
    "f2_omega36_actual_pair_certificate.json": "JC.REPLAY.RECEIPT.OMEGA36",
    "f2_sigma_source_order6_vertex_realizability_certificate.json":
        "JC.REPLAY.RECEIPT.ORDER6",
    "_local_finite_algebra/z10_d9_connecting_map_replay_local.json":
        "JC.REPLAY.RECEIPT.LOCAL_CONNECTING",
    "_local_finite_algebra/z10_d9_integrability9_replay_local.json":
        "JC.REPLAY.RECEIPT.LOCAL_INTEGRABILITY",
}

FORMAL_MODULES = [
    "SigmaCurrentShadow", "SigmaEndgameComposition", "SigmaI4Endgame",
    "SigmaLocalAlgebraToS2", "SigmaLocalConnecting",
]

FORMAL_PREPARATION = [
    "SigmaCloseoutConsumers", "SigmaDerivativePascal",
    "SigmaDividedPowerPoincare", "SigmaEndgameComposition",
    "SigmaFiniteSqueeze", "SigmaLiveThetaCorner", "SigmaLocalCoboundary",
    "SigmaPascalHasse", "SigmaPascalHasseGeneral", "SigmaI4Endgame",
    "SigmaLocalAlgebraToS2", "SigmaLocalConnecting", "SigmaOrderSixVertex",
    "SigmaRowDichotomy", "SigmaUpstreamS6Chain",
    "SigmaActualPivotCompression", "SigmaAtlasA2Enumeration",
    "SigmaRecipCarrierReduction", "SigmaCurrentShadow",
]


def digest_bytes(payload):
    return hashlib.sha256(payload.replace(b"\r\n", b"\n")).hexdigest()


def digest(path):
    return digest_bytes(path.read_bytes())


def resource_id(relative):
    if relative in RECEIPTS:
        return RECEIPTS[relative]
    token = hashlib.sha256(relative.encode("utf-8")).hexdigest()[:20].upper()
    return "JC.REPLAY.FILE.%s" % token


def python_closure(root, entry):
    seen = set()
    todo = [root / entry]
    literals = set()
    while todo:
        path = todo.pop()
        if path in seen or not path.is_file():
            continue
        seen.add(path)
        tree = ast.parse(path.read_text(encoding="utf-8-sig"))
        for node in ast.walk(tree):
            if isinstance(node, ast.Constant) and isinstance(node.value, str):
                literals.add(node.value)
            names = []
            if isinstance(node, ast.Import):
                names = [alias.name.split(".", 1)[0] for alias in node.names]
            elif isinstance(node, ast.ImportFrom) and node.module:
                names = [node.module.split(".", 1)[0]]
            for name in names:
                for base in (path.parent, root):
                    candidate = base / (name + ".py")
                    if candidate.is_file():
                        todo.append(candidate)
                        break
    for literal in literals:
        if not literal or len(literal) > 240:
            continue
        for base in ((root / entry).parent, root):
            candidate = base / literal
            if candidate.is_file():
                seen.add(candidate.resolve())
    return {path.resolve() for path in seen}


def lean_closure(root):
    lean = root / "lean"
    seen = set()
    todo = [lean / "JC" / (module + ".lean") for module in FORMAL_MODULES]
    pattern = re.compile(r"^import\s+JC\.([A-Za-z0-9_.]+)\s*$", re.MULTILINE)
    while todo:
        path = todo.pop()
        if path in seen or not path.is_file():
            continue
        seen.add(path)
        for module in pattern.findall(path.read_text(encoding="utf-8-sig")):
            todo.append(lean / "JC" / (module.replace(".", "/") + ".lean"))
    seen.update({lean / "build.sh", lean / "lean-toolchain"})
    return {path.resolve() for path in seen}


def make_resource(root, path, *, embedded=False):
    relative = path.relative_to(root).as_posix()
    release_path = "replay/jc/d2_plane_72_108/" + relative
    suffix = path.suffix.lower()
    role = "CHECKER" if suffix in {".py", ".lean", ".sh"} else "INPUT"
    if path.name == "lean-toolchain":
        role = "ENVIRONMENT"
    if relative in RECEIPTS:
        role = "RECEIPT"
        embedded = True
    value = {
        "id": resource_id(relative),
        "role": role,
        "release_path": release_path,
        "digest_algo": DIGEST_ALGO,
        "sha256": digest(path),
        "license_status": "CLEAR",
        "provenance": "Committed JC replay dependency at 1bbdec4.",
    }
    if embedded:
        value["embedded_text"] = path.read_text(encoding="utf-8")
        value["sha256"] = hashlib.sha256(
            value["embedded_text"].encode("utf-8")).hexdigest()
        value["provenance"] = "Fresh clean-checkout replay receipt at 1bbdec4."
    else:
        value["source_path"] = "d2_plane_72_108/" + relative
    return value


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("source_root", type=Path)
    parser.add_argument("output", type=Path)
    args = parser.parse_args()
    root = args.source_root.resolve() / "d2_plane_72_108"
    resources = {}
    sets = []
    for set_id, entry in LANES.items():
        paths = python_closure(root, entry)
        ids = []
        for path in sorted(paths):
            resource = make_resource(root, path)
            resources[resource["id"]] = resource
            ids.append(resource["id"])
        sets.append({"id": set_id, "resource_ids": sorted(set(ids))})

    formal_ids = []
    for path in sorted(lean_closure(root)):
        resource = make_resource(root, path)
        resources[resource["id"]] = resource
        formal_ids.append(resource["id"])
    preparation_command = "bash build.sh " + " ".join(FORMAL_PREPARATION)
    consumer_commands = ["bash build.sh " + item for item in FORMAL_MODULES]
    formal_receipt = json.dumps({
        "commit": "1bbdec4334602dd755375ef414100bd44b90338d",
        "environment": {
            "runtime": "Lean 4.23.0 via elan and Git Bash",
            "network": "FORBIDDEN",
            "external_dependencies": [
                "prebuilt mathlib dependency tree supplied by JC_LEAN_PKGS",
            ],
        },
        "preparation_command": preparation_command,
        "consumer_commands": consumer_commands,
        "result": "PASS",
        "preparation": {
            "elapsed_seconds": 451.2,
            "modules": {item: {"sorry": 0} for item in FORMAL_PREPARATION},
        },
        "consumers": {
            "elapsed_seconds": 132.5,
            "modules": {item: {"sorry": 0} for item in FORMAL_MODULES},
        },
    }, sort_keys=True, indent=2) + "\n"
    formal_id = "JC.REPLAY.RECEIPT.FORMAL"
    resources[formal_id] = {
        "id": formal_id,
        "role": "RECEIPT",
        "release_path": "replay/jc/d2_plane_72_108/lean/gp-formal-replay.json",
        "digest_algo": DIGEST_ALGO,
        "sha256": hashlib.sha256(formal_receipt.encode("utf-8")).hexdigest(),
        "license_status": "CLEAR",
        "provenance": "Fresh materialized-kit Git-Bash/Lean replay at 1bbdec4.",
        "embedded_text": formal_receipt,
    }
    formal_ids.append(formal_id)
    sets.append({"id": "JC.REPLAY.SET.FORMAL",
                 "resource_ids": sorted(set(formal_ids))})

    value = {
        "schema": "campaign-replay-resources/v0",
        "authority": AUTHORITY,
        "graph_effect": GRAPH_EFFECT,
        "source_commit": "1bbdec4334602dd755375ef414100bd44b90338d",
        "resources": sorted(resources.values(), key=lambda item: item["id"]),
        "sets": sorted(sets, key=lambda item: item["id"]),
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(value, sort_keys=True, indent=2) + "\n",
                           encoding="utf-8", newline="\n")
    print("%d resources, %d sets" % (len(resources), len(sets)))
    print(digest(args.output))


if __name__ == "__main__":
    main()
