#!/usr/bin/env python3
"""Run the bounded GP replay gate for the landed JC H3 depth-6 lane.

This is a post-receipt integration gate, not a discovery driver.  It checks
the frozen adapters in their mathematical order, records the authority earned
at each seam, and deliberately terminates at the first still-open transition:
the target polynomial pair to normalized Laurent-root presentation.

The default mode is suitable for routine milestone checks. ``--full`` also
rederives the reduced E-system rows and replays all 25 chain substitutions.
``--native-replay`` is a separate opt-in because it executes the sibling JC
verifier and is intentionally not required for normal GP development.
"""

from __future__ import annotations

import argparse
import ctypes
import hashlib
import importlib.util
import json
import os
import subprocess
import sys
import tempfile
import time
from pathlib import Path

from grandportage import evidence as EV
from grandportage import verify as V


ROOT = Path(__file__).resolve().parents[2]
HERE = Path(__file__).resolve().parent
SCHEMA_V1 = "gp-jc-h3-depth6-milestone-replay/v1"
SCHEMA = "gp-jc-h3-depth6-milestone-replay/v2"
OVERALL_VERDICT = "VERIFIED_TO_EXPLICIT_OPEN_OBLIGATION"
FIRST_MISSING = "target_pair_to_normalized_laurent_root"
NATIVE_VERIFIER = (
    ROOT.parent / "math-stuff" / "d2_plane_72_108" /
    "f2_original_pair_to_esystem_verify.py"
)
EXPECTED_BOUNDARY_FIXTURE_SHA256 = (
    "4a0cf6999dedf3334e4e9f0b5918303757cdd857b88090017319ab0c87eff991"
)


class MilestoneReplayError(ValueError):
    """A stage failed, drifted, or attempted to widen its authority."""


def _require(condition, message):
    if not condition:
        raise MilestoneReplayError(message)


def _load(name):
    path = HERE / (name + ".py")
    spec = importlib.util.spec_from_file_location(
        "jc_h3_depth6_gate_" + name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


ORIGINAL = _load("original_pair_seam_adapter")
R1_R7 = _load("r1_r7_seam_adapter")
FACE = _load("face_extraction_adapter")
FULL_TEMPLATE = _load("full_template_campaign")
CHAIN = _load("chain_adapter")
BOUNDARY = _load("adapter")


def migrate_v1_ledger(value):
    """Make the lossy v1-to-v2 boundary explicit for old review ledgers."""
    _require(isinstance(value, dict) and value.get("schema") == SCHEMA_V1,
             "ledger is not a depth-6 aggregate replay v1 artifact")
    migrated = dict(value)
    migrated["schema"] = SCHEMA
    migrated["binding_digest_algo"] = "sha256-mixed-legacy"
    migrated["open_frontier"] = [
        {
            "id": "target_pair_to_normalized_laurent_root",
            "status": "UNMATERIALIZED_OPEN",
            "why_open": "v1 recorded only the parent open seam",
            "premises": [],
            "blocks": list(value.get("first_missing_authority", {}).get(
                "blocks", [])),
        },
    ]
    migrated["superseded_by"] = []
    migrated["migration"] = {
        "from": SCHEMA_V1,
        "status": "LOSSY_EXPLICIT",
        "missing_v1_fields": [
            "R5/R6/R7 typed frontier",
            "LF-normalized source-binding declaration",
            "correction commit provenance",
        ],
    }
    return migrated


def normalize_ledger(value):
    """Accept current ledgers or explicitly migrate checked-in v1 artifacts."""
    if isinstance(value, dict) and value.get("schema") == SCHEMA:
        return value
    if isinstance(value, dict) and value.get("schema") == SCHEMA_V1:
        return migrate_v1_ledger(value)
    raise MilestoneReplayError("unsupported aggregate replay ledger schema")


def _sha256(path):
    payload = Path(path).read_bytes().replace(b"\r\n", b"\n")
    return "sha256:" + hashlib.sha256(payload).hexdigest()


def _stage(stage_id, verdict, seconds, graph_effect, summary, licenses,
           outstanding=(), status="VERIFIED"):
    return {
        "id": stage_id,
        "status": status,
        "verdict": verdict,
        "seconds": round(seconds, 3),
        "graph_effect": graph_effect,
        "summary": summary,
        "licenses": list(licenses),
        "outstanding_premises": list(outstanding),
    }


def _rss_mb():
    """Return current resident memory using only the standard library."""
    try:
        if os.name == "nt":
            class Counters(ctypes.Structure):
                _fields_ = [
                    ("cb", ctypes.c_ulong),
                    ("PageFaultCount", ctypes.c_ulong),
                    ("PeakWorkingSetSize", ctypes.c_size_t),
                    ("WorkingSetSize", ctypes.c_size_t),
                    ("QuotaPeakPagedPoolUsage", ctypes.c_size_t),
                    ("QuotaPagedPoolUsage", ctypes.c_size_t),
                    ("QuotaPeakNonPagedPoolUsage", ctypes.c_size_t),
                    ("QuotaNonPagedPoolUsage", ctypes.c_size_t),
                    ("PagefileUsage", ctypes.c_size_t),
                    ("PeakPagefileUsage", ctypes.c_size_t),
                ]
            counters = Counters()
            counters.cb = ctypes.sizeof(counters)
            get_process = ctypes.windll.kernel32.GetCurrentProcess
            get_process.restype = ctypes.c_void_p
            process = get_process()
            get_memory = ctypes.windll.psapi.GetProcessMemoryInfo
            get_memory.argtypes = [
                ctypes.c_void_p, ctypes.POINTER(Counters), ctypes.c_ulong]
            get_memory.restype = ctypes.c_int
            ok = get_memory(
                process, ctypes.byref(counters), counters.cb)
            if ok:
                return round(counters.WorkingSetSize / (1024 * 1024), 3)
        else:  # ru_maxrss is KiB on Linux and bytes on macOS.
            import resource
            value = resource.getrusage(resource.RUSAGE_SELF).ru_maxrss
            scale = 1024 * 1024 if sys.platform == "darwin" else 1024
            return round(value / scale, 3)
    except (AttributeError, OSError, ValueError):
        pass
    return None


def _append_journal(path, stage):
    """Append one fsynced diagnostic record; never grants authority."""
    path = Path(path)
    path.parent.mkdir(parents=True, exist_ok=True)
    record = {
        "id": stage["id"],
        "status": stage["status"],
        "verdict": stage["verdict"],
        "seconds": stage["seconds"],
        "graph_effect": stage["graph_effect"],
        "rss_mb": _rss_mb(),
        "diagnostic_only": True,
    }
    with path.open("a", encoding="utf-8", newline="\n") as stream:
        stream.write(json.dumps(record, sort_keys=True) + "\n")
        stream.flush()
        os.fsync(stream.fileno())


def _run_preflight(check_native_bindings=False, stage_callback=None):
    """Run tier 0: frozen bindings/digests only, with no chain decoding."""
    started = time.time()
    stages = []

    def record(stage):
        stages.append(stage)
        if stage_callback is not None:
            stage_callback(stage)

    tick = time.time()
    checks = {
        "conditional seam": (
            ORIGINAL.DEFAULT_FIXTURE, ORIGINAL.EXPECTED_FIXTURE_SHA256),
        "R1--R7 seam": (
            R1_R7.DEFAULT_FIXTURE, R1_R7.EXPECTED_FIXTURE_SHA256),
        "graded face": (
            FACE.DEFAULT_FIXTURE, FACE.EXPECTED_FIXTURE_SHA256),
        "boundary": (
            BOUNDARY.DEFAULT_FROZEN, EXPECTED_BOUNDARY_FIXTURE_SHA256),
    }
    for name, (path, expected) in checks.items():
        observed = _sha256(path)[len("sha256:"):]
        _require(observed == expected, name + " fixture digest changed")
    if check_native_bindings:
        ORIGINAL.verify_fixture(check_native_bindings=True)
        value = json.loads(R1_R7.DEFAULT_FIXTURE.read_text(encoding="utf-8"))
        R1_R7.check_native_bindings(value)
    record(_stage(
        "frozen_fixture_bindings", "PREFLIGHT_BINDINGS_ONLY",
        time.time() - tick, EV.GRAPH_EFFECT_NONE,
        "Frozen fixture identities and optional sibling bindings match.",
        ("frozen_inputs_are_the_named_inputs",),
        ("no polynomial or transport authority checked",)))

    tick = time.time()
    chain = CHAIN.preflight_chain()
    _require(chain.get("verdict") == "PREFLIGHT_BINDINGS_ONLY",
             "chain preflight emitted mathematical authority")
    record(_stage(
        "ordered_depth6_chain_bindings", chain["verdict"],
        time.time() - tick, EV.GRAPH_EFFECT_NONE,
        "Chain record digests, ordering fingerprints, and rung welds match.",
        chain["licenses"], chain["refuses"]))

    runtime = round(time.time() - started, 3)
    return {
        "schema": SCHEMA,
        "overall_verdict": "PREFLIGHT_BINDINGS_ONLY",
        "tier": "preflight",
        "mode": "preflight",
        "coverage": "BINDINGS_AND_DIGESTS_ONLY",
        "native_bindings_checked": bool(check_native_bindings),
        "native_replay_executed": False,
        "aggregate_graph_effect": EV.GRAPH_EFFECT_NONE,
        "stages": stages,
        "open_frontier": [],
        "authority_ceiling": "NO_MATHEMATICAL_AUTHORITY",
        "binding_digest_algo": "sha256-lf-normalized",
        "runtime_seconds": runtime,
        "tier_cost_seconds": runtime,
        "bindings": {name: _sha256(path) for name, (path, _expected)
                     in checks.items()},
    }


def _run_native_replay():
    _require(NATIVE_VERIFIER.exists(),
             "sibling JC original-pair seam verifier is absent")
    started = time.time()
    completed = subprocess.run(
        [sys.executable, str(NATIVE_VERIFIER), "--self-test-mutations"],
        cwd=str(NATIVE_VERIFIER.parent), capture_output=True, text=True,
        timeout=600, check=False)
    _require(completed.returncode == 0,
             "native seam replay failed: " + completed.stderr.strip())
    try:
        report = json.loads(completed.stdout)
    except json.JSONDecodeError as exc:
        raise MilestoneReplayError(
            "native seam replay did not emit JSON: %s" % exc)
    _require(report.get("strict_original_source_supported") is False,
             "native replay silently promoted strict original-source support")
    _require(report.get("status") == "CONDITIONAL_EXACT_WITH_OPEN_UPSTREAM",
             "native replay changed its conditional status")
    _require(report.get("original_pair_to_normalized_root") ==
             "UNMATERIALIZED_OPEN",
             "native replay changed the first missing source stage")
    _require(report.get("mutation_refusals") == 9,
             "native replay did not refuse all nine mutations")
    return _stage(
        "native_original_pair_seam_replay", report["status"],
        time.time() - started, EV.GRAPH_EFFECT_NONE,
        "Sibling JC verifier and all nine mutation refusals passed.",
        ("native_conditional_source_seam_replayed",
         "nine_native_mutations_refused"),
        (FIRST_MISSING,))


def run_gate(full=False, check_native_bindings=False, native_replay=False,
             tier=None, stage_callback=None):
    """Return a machine-readable ordered replay ledger.

    Passing all stages does not close the terminal obligation and therefore
    does not grant original-pair membership, H3, coverage, or verdict authority.
    """
    if tier is None:
        tier = "full" if full else "seam"
    _require(tier in {"preflight", "seam", "full"},
             "unknown replay tier: " + str(tier))
    _require(not (full and tier != "full"),
             "legacy full=True conflicts with tier=" + tier)
    if tier == "preflight":
        _require(not native_replay,
                 "native replay is outside the binding-only preflight tier")
        return _run_preflight(check_native_bindings, stage_callback)
    full = tier == "full"
    started = time.time()
    stages = []

    def record(stage):
        stages.append(stage)
        if stage_callback is not None:
            stage_callback(stage)

    def progress(message):
        print("[gp-jc-depth6] " + message, file=sys.stderr, flush=True)

    progress("conditional source seam")
    tick = time.time()
    original = ORIGINAL.verify_fixture(
        check_native_bindings=check_native_bindings)
    _require(original.get("verdict") ==
             "VERIFIED_CONDITIONAL_ESYSTEM_SEAM",
             "conditional source-seam verdict changed")
    _require(original.get("strict_original_source_supported") is False,
             "conditional source seam claimed strict original-source support")
    _require(original.get("missing_stage") == FIRST_MISSING,
             "conditional source seam changed the first missing stage")
    record(_stage(
        "conditional_source_seam", original["verdict"],
        time.time() - tick, EV.GRAPH_EFFECT_NONE,
        "Normalized Laurent-root data replay to the five reduced rows.",
        original["evidence_envelope"]["licenses"],
        original["evidence_envelope"]["outstanding_premises"]))

    progress("corrected R1--R7 source frontier")
    tick = time.time()
    r1_r7 = R1_R7.verify_fixture(check_bindings=check_native_bindings)
    _require(r1_r7.get("verdict") == "VERIFIED_R1_R7_OPEN_FRONTIER",
             "corrected R1--R7 frontier verdict changed")
    _require(r1_r7.get("parent_obligation") == FIRST_MISSING and
             r1_r7.get("parent_status") == "UNMATERIALIZED_OPEN",
             "R1--R7 adapter silently closed or changed the parent seam")
    _require(r1_r7.get("graph_effect") == EV.GRAPH_EFFECT_NONE,
             "R1--R7 adapter widened graph authority")
    _require(r1_r7.get("R6", {}).get("Q_positive_j") == "OPEN",
             "R1--R7 adapter silently forced Q-side relocation")
    record(_stage(
        "r1_r7_source_frontier", r1_r7["verdict"],
        time.time() - tick, EV.GRAPH_EFFECT_NONE,
        "R1--R4 close conditionally; R5, R6, and R7 remain typed open seams.",
        r1_r7["evidence_envelope"]["licenses"],
        r1_r7["evidence_envelope"]["outstanding_premises"]))

    progress("graded face extraction")
    tick = time.time()
    face = FACE.verify_fixture(
        full_source_replay=full,
        check_native_bindings=check_native_bindings)
    expected_face = ("VERIFIED_GRADED_FACE_EXTRACTION_WITH_SOURCE_REPLAY"
                     if full else "VERIFIED_GRADED_FACE_EXTRACTION")
    _require(face.get("verdict") == expected_face,
             "graded face-extraction verdict changed")
    _require(face.get("source_rows") == 5 and face.get("faces") == 25,
             "graded face-extraction cardinality changed")
    record(_stage(
        "graded_face_extraction", face["verdict"],
        time.time() - tick, EV.GRAPH_EFFECT_NONE,
        "Five reduced rows yield the exact selected depth-2..6 faces.",
        face["evidence_envelope"]["licenses"],
        face["evidence_envelope"]["outstanding_premises"]))

    if full:
        progress("complete finite-template graph inclusion")
        tick = time.time()
        campaign = FULL_TEMPLATE.compile_campaign(full_source_replay=False)
        _require(campaign.get("source_generators") == 147 and
                 campaign.get("selected_generators") == 25 and
                 campaign.get("ring_variables") == 78,
                 "complete finite-template dimensions changed")
        graph = FULL_TEMPLATE.graph_from_campaign(campaign)
        containment, reason = V.containment(graph, FULL_TEMPLATE.EDGE)
        _require(containment == V.VERIFIED,
                 "finite-template exact inclusion failed: " + str(reason))
        record(_stage(
            "complete_finite_template", "VERIFIED_EXACT_GENERATOR_INCLUSION",
            time.time() - tick, "POINT_INCLUSION",
            "The selected 25 faces are an exact generator subset of 147 rows.",
            campaign["authority"]["licenses"],
            campaign["authority"]["refuses"]))
    else:
        record(_stage(
            "complete_finite_template", "NOT_RUN_IN_FAST_MODE", 0,
            "NONE", "The 147-row graph inclusion is reserved for --full.",
            (), ("run --full for exact generator-inclusion authority",),
            status="DEFERRED_OPTIONAL"))

    progress("ordered depth-6 chain")
    tick = time.time()
    chain = CHAIN.verify_chain(full_replay=full)
    expected_chain = ("VERIFIED_DEPTH6_CHAIN_FULL_REPLAY" if full else
                      "VERIFIED_DEPTH6_CHAIN_ENVELOPE")
    _require(chain.get("verdict") == expected_chain,
             "ordered depth-6 chain verdict changed")
    _require(chain.get("solved_steps") == 23 and
             chain.get("residuals_welded") == 2,
             "ordered depth-6 chain cardinality changed")
    record(_stage(
        "ordered_depth6_chain", chain["verdict"],
        time.time() - tick, EV.GRAPH_EFFECT_NONE,
        "The 23 ordered solve steps weld the selected faces to two residuals.",
        chain["evidence_envelope"]["licenses"],
        chain["evidence_envelope"]["outstanding_premises"]))

    progress("boundary projection")
    tick = time.time()
    frozen = json.loads(BOUNDARY.DEFAULT_FROZEN.read_text(encoding="utf-8"))
    boundary = BOUNDARY.verify_frozen(frozen)
    _require(boundary.get("verdict") == "VERIFIED_FROZEN_DEPTH6_BOUNDARY",
             "depth-6 boundary verdict changed")
    boundary_licenses = tuple(boundary["evidence_envelope"]["licenses"])
    boundary_outstanding = list(
        boundary["evidence_envelope"]["outstanding_premises"])
    if full:
        progress("boundary graph equivalences")
        boundary_graph = BOUNDARY.graph_from_frozen(frozen)
        for edge_id in (BOUNDARY.GENERIC_EDGE, BOUNDARY.DISCRIMINANT_EDGE):
            verdict, reason = V.ring_iso(boundary_graph, edge_id)
            _require(verdict == V.ISO_VERIFIED,
                     "%s equivalence failed: %s" % (edge_id, reason))
        boundary_verdict = "VERIFIED_BOUNDARY_WITH_TWO_EXACT_EQUIVALENCES"
        boundary_effect = "IDENTITY_TRANSPORT"
        boundary_summary = (
            "Both residuals and the generic/discriminant rewrites verify.")
        boundary_licenses += (
            "generic_affine_rewrite_equivalence",
            "discriminant_collapse_equivalence",
        )
    else:
        boundary_verdict = "VERIFIED_BOUNDARY_PROJECTION_EQUIVALENCES_DEFERRED"
        boundary_effect = EV.GRAPH_EFFECT_NONE
        boundary_summary = (
            "Both residuals verify; graph equivalences are reserved for --full.")
        boundary_outstanding.append(
            "run --full to recompute both exact boundary equivalences")
    record(_stage(
        "boundary_projection_and_strata", boundary_verdict,
        time.time() - tick, boundary_effect, boundary_summary,
        boundary_licenses, boundary_outstanding))

    if native_replay:
        progress("native seam verifier and mutations")
        record(_run_native_replay())

    expected_order = [
        "conditional_source_seam", "r1_r7_source_frontier",
        "graded_face_extraction",
        "complete_finite_template", "ordered_depth6_chain",
        "boundary_projection_and_strata",
    ] + (["native_original_pair_seam_replay"] if native_replay else [])
    _require([stage["id"] for stage in stages] == expected_order,
             "milestone replay stage order changed")

    open_frontier = []
    for item in r1_r7["open_frontier"]:
        frontier_item = dict(item)
        frontier_item["premises"] = (
            list(r1_r7["R6"]["premises"]) if item["id"] == "R6" else [])
        frontier_item["blocks"] = list(r1_r7["refusals"])
        open_frontier.append(frontier_item)
    open_frontier.extend([
        {
            "id": "R6.Q_side_relocation",
            "status": r1_r7["R6"]["Q_positive_j"],
            "why_open": "pair positive-j does not force Q positive-j",
            "premises": list(r1_r7["R6"]["premises"]),
            "blocks": ["Q-side positive-j relocation"],
        },
        {
            "id": FIRST_MISSING,
            "status": r1_r7["parent_status"],
            "why_open": "the target pair has not been materialized as normalized Laurent-root data",
            "premises": [],
            "blocks": list(r1_r7["refusals"]),
        },
    ])
    bindings = {
        "conditional_seam_fixture": _sha256(ORIGINAL.DEFAULT_FIXTURE),
        "r1_r7_seam_fixture": _sha256(R1_R7.DEFAULT_FIXTURE),
        "graded_face_fixture": _sha256(FACE.DEFAULT_FIXTURE),
        "chain_certificate": "sha256:" + CHAIN.EXPECTED_CANONICAL_SHA256,
        "boundary_fixture": _sha256(BOUNDARY.DEFAULT_FROZEN),
    }
    bindings.update({
        "r1_r7_native:" + name: "sha256:" + digest
        for name, digest in r1_r7["source_bindings"].items()
    })

    runtime = round(time.time() - started, 3)
    return {
        "schema": SCHEMA,
        "overall_verdict": OVERALL_VERDICT,
        "tier": tier,
        "mode": "full" if full else "fast",
        "coverage": ("ALL_FROZEN_STAGES_AND_COMPLETE_TEMPLATE" if full else
                     "WELDS_ONLY_GRAPH_AUTHORITIES_DEFERRED"),
        "native_bindings_checked": bool(check_native_bindings),
        "native_replay_executed": bool(native_replay),
        "aggregate_graph_effect": EV.GRAPH_EFFECT_NONE,
        "stages": stages,
        "open_frontier": open_frontier,
        "first_missing_authority": {
            "id": FIRST_MISSING,
            "status": "UNMATERIALIZED_OPEN",
            "blocks": [
                "original polynomial-pair membership",
                "source-image sufficiency or reverse lift",
                "chart or branch coverage",
                "H3 promotion",
                "(75,125) verdict change",
            ],
        },
        "authority_ceiling": (
            "CONDITIONAL_NORMALIZED_ROOT_TO_DEPTH6_BOUNDARY_ONLY"),
        "superseded_by": [
            "math-stuff:d0257f9",
            "math-stuff:fb18749",
        ],
        "binding_digest_algo": "sha256-lf-normalized",
        "runtime_seconds": runtime,
        "tier_cost_seconds": runtime,
        "bindings": bindings,
    }


def _write_report(path, report, force=False):
    path = Path(path)
    if path.exists() and not force:
        raise MilestoneReplayError(
            "output exists; pass --force to replace it: %s" % path)
    path.parent.mkdir(parents=True, exist_ok=True)
    payload = (json.dumps(report, indent=2, sort_keys=True) + "\n").encode()
    handle, temporary = tempfile.mkstemp(
        prefix=path.name + ".", suffix=".tmp", dir=str(path.parent))
    try:
        with os.fdopen(handle, "wb") as stream:
            stream.write(payload)
            stream.flush()
            os.fsync(stream.fileno())
        os.replace(temporary, path)
    except BaseException:
        try:
            os.unlink(temporary)
        except FileNotFoundError:
            pass
        raise


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    tiers = parser.add_mutually_exclusive_group()
    tiers.add_argument("--preflight", action="store_true",
                       help="bindings and digests only; no mathematical verdict")
    tiers.add_argument("--seam", action="store_true",
                       help="exact seam identities (the default tier)")
    tiers.add_argument("--full", action="store_true",
                       help="rederive source rows and replay all substitutions")
    parser.add_argument("--check-native-bindings", action="store_true",
                        help="require the bound sibling JC files to match")
    parser.add_argument("--native-replay", action="store_true",
                        help="execute the sibling JC verifier and mutations")
    parser.add_argument("--output", type=Path,
                        help="atomically write the JSON ledger here")
    parser.add_argument("--journal", type=Path,
                        help="append a diagnostic JSON line after every stage")
    parser.add_argument("--force", action="store_true",
                        help="replace an existing --output report")
    args = parser.parse_args(argv)
    if args.force and args.output is None:
        parser.error("--force requires --output")
    try:
        tier = "preflight" if args.preflight else (
            "full" if args.full else "seam")
        callback = (None if args.journal is None else
                    lambda stage: _append_journal(args.journal, stage))
        report = run_gate(
            full=args.full,
            check_native_bindings=args.check_native_bindings,
            native_replay=args.native_replay,
            tier=tier,
            stage_callback=callback)
        if args.output is not None:
            _write_report(args.output, report, args.force)
        print(json.dumps(report, indent=2, sort_keys=True))
        return 0
    except (MilestoneReplayError, ValueError, OSError, subprocess.SubprocessError) as exc:
        print(json.dumps({
            "schema": SCHEMA,
            "overall_verdict": "REFUSED",
            "error": str(exc),
        }, indent=2, sort_keys=True), file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
