#!/usr/bin/env python3
"""Compile the JC on-wall base obstruction to existing local-EMPTY authority.

The native receipt proves the exact identity

    value_24|Delta = OB - 45*c2_3*t*R*c8_9.

On the constructible piece R=0, OB!=0, the dead-row equation is therefore
inconsistent.  The adapter freezes the two exact sparse polynomials and emits
a localization-membership certificate for

    OB = value_24 + 45*c2_3*t*c8_9*R.

No new evidence schema, claim kind, relation, or kernel authority is needed.
The graph-bound claim concerns the exact dead-row consequence model only; an
edge from a fully materialized nine-body model remains future composition work.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import subprocess
import sys
from pathlib import Path

from grandportage import check as C
from grandportage import evidence as EV
from grandportage import format as F
from grandportage import groebner as G
from grandportage import localization as L
from grandportage import store as S
from grandportage import verify as V


ROOT = Path(__file__).resolve().parents[2]
NATIVE_ROOT = ROOT.parent / "math-stuff" / "d2_plane_72_108"
DEFAULT_FROZEN = ROOT / "fixtures" / "jc_wall_ob_open" / "native_v1.json"
DEFAULT_AUTHORITY = (ROOT / "fixtures" / "jc_wall_ob_open" /
                     "localized_unit_ideal_v1.json")

FROZEN_SCHEMA = "jc_h3_onwall_ob_open_dead_row_v1"
EXPECTED_FROZEN_SHA256 = (
    "a2d1544cf9b7f9a4966c4a197d626fb79bd3fccd0f1672e726cdb0ae746a88b9")
NATIVE_BINDINGS = {
    "f2_h3_onwall_repivot_certificate.json":
        "d19b5bc5d334be88ddcb1cf013ba10e1c9df3523c2388fc2f05e5b538f7805d9",
    "f2_h3_onwall_repivot.py":
        "04118f6efa2650a2bdc93ba317449493be0f4989d389c5fb6fdb7ccc8d35f4a8",
}
NATIVE_POLYNOMIAL_DIGESTS = {
    "value_24_delta":
        "c818a58103641cca7dac3339abdde210221b62aa3c4f35e5f8a0475d3fe15801",
    "OB_ambient":
        "a44bee1d2c271265c01c4166d5024ae6ad031221c48640f89a9ac82af72ce172",
}

MODEL = "JC-H3-S2-WALL-OB-OPEN-DEAD-ROW"
EMPTY_CLAIM = "JC-H3-S2-WALL-OB-OPEN-DEAD-ROW-EMPTY"


class WallObstructionError(ValueError):
    """The frozen dead-row identity or its authority scope drifted."""


def require(condition, check_id, message):
    if not condition:
        raise WallObstructionError("%s: %s" % (check_id, message))


def normalized_sha256(path):
    return hashlib.sha256(
        Path(path).read_bytes().replace(b"\r\n", b"\n")).hexdigest()


def _sha256(data):
    return "sha256:" + hashlib.sha256(data).hexdigest()


def _encoded(value):
    return (json.dumps(value, indent=2, sort_keys=True,
                       ensure_ascii=True) + "\n").encode("utf-8")


def _native_sparse_digest(value):
    canonical = json.dumps(value, sort_keys=True, separators=(",", ":"))
    return hashlib.sha256(canonical.encode("utf-8")).hexdigest()


def _gp_sparse(native):
    symbols = native["symbols"]
    decoded = []
    for support, coefficient in native["terms"]:
        powers = [[symbols[index], exponent] for index, exponent in support]
        power_map = dict((name, exponent) for name, exponent in powers)
        key = tuple(power_map.get(name, 0) for name in symbols)
        decoded.append((key, {
            "coefficient": coefficient,
            "powers": powers,
        }))
    decoded.sort(key=lambda item: item[0], reverse=True)
    return {
        "schema": G.SPARSE_POLYNOMIAL_SCHEMA,
        "terms": [record for _key, record in decoded],
    }


def _validate_native_certificate(certificate):
    require(certificate.get("id") == "f2_h3_onwall_repivot" and
            certificate.get("schema_version") == 1, "N1",
            "native receipt identity or schema changed")
    layer = certificate.get("layer", "")
    require("fiber-emptiness consequence over Z(R) with OB != 0" in layer and
            "EXACT ambient polynomial identities" in layer and
            "P1..P5 and S2" in layer, "N2",
            "dead-row exactness or premise layer changed")
    dead = certificate.get("dead_row_identity", {})
    require("coef(value_24|D, c8_9) = -45*a*t*R exactly" in
            dead.get("statement", "") and
            "129 on-wall terms" in dead.get("obstruction", "") and
            "empty in every field extension" in
            dead.get("obstruction", "").lower(), "N3",
            "native dead-row identity or obstruction consequence changed")
    verdict = certificate.get("verdict", {})
    require(verdict.get("fiber_empty_over_ZR_with_OB_nonzero") ==
            "PROVED (every field extension)" and
            verdict.get("wall_blockage_is_base_obstruction") is True, "N4",
            "native wall obstruction verdict changed")


def _extract_native_polynomials(native_root=NATIVE_ROOT):
    """Explicit producer path; ordinary verification never imports JC code."""
    native_root = Path(native_root)
    sys.path.insert(0, str(native_root))
    try:
        from f2_h3_p_partial_zero_block import (  # type: ignore
            LP_VARS, from_sparse, load_bodies, subs_delta, to_sparse)
        _chain, _receipt, _strata, raw_bodies, _digest = load_bodies()
        value_24 = subs_delta(from_sparse(raw_bodies["value_24"][0]))
        obstruction = {
            monomial: coefficient
            for monomial, coefficient in value_24.items()
            if not any(name in LP_VARS for name, _exponent in monomial)
        }
        return {
            "value_24_delta": to_sparse(value_24),
            "OB_ambient": to_sparse(obstruction),
        }
    finally:
        try:
            sys.path.remove(str(native_root))
        except ValueError:
            pass


def build_frozen(native_root=NATIVE_ROOT):
    root = Path(native_root)
    bindings = {name: normalized_sha256(root / name)
                for name in sorted(NATIVE_BINDINGS)}
    require(bindings == dict(sorted(NATIVE_BINDINGS.items())), "B1",
            "native on-wall inputs drifted before freeze")
    certificate = json.loads((root /
        "f2_h3_onwall_repivot_certificate.json").read_text(encoding="utf-8"))
    _validate_native_certificate(certificate)
    native_polynomials = _extract_native_polynomials(root)
    require({name: _native_sparse_digest(value)
             for name, value in native_polynomials.items()} ==
            NATIVE_POLYNOMIAL_DIGESTS, "B2",
            "native dead-row polynomial extraction changed")
    value = native_polynomials["value_24_delta"]
    obstruction = native_polynomials["OB_ambient"]
    require(len(value["terms"]) == 502 and len(obstruction["terms"]) == 499,
            "B3", "dead-row or obstruction term count changed")
    require("c8_9" in value["symbols"] and
            "c8_9" not in obstruction["symbols"], "B4",
            "OB is not free of the fiber variable")
    return {
        "schema": FROZEN_SCHEMA,
        "binding_digest_algo": "sha256-lf-normalized",
        "source_bindings": bindings,
        "native_certificate": certificate,
        "ring_vars": value["symbols"],
        "polynomials": {
            "pin": "15*t^3+1",
            "R": "c8_12+2*c3_5*c5_7-c2_3*c3_5^2",
            "value_24_delta": _gp_sparse(value),
            "OB_ambient": _gp_sparse(obstruction),
        },
        "scope": {
            "presentation": "Delta-substituted S2 dead-row consequence",
            "constructible_piece": "R=0 and OB!=0",
            "coefficient_domain": "Q with 15*t^3+1 imposed",
            "point_universe": S.ALGEBRAIC_CLOSURE_POINT_UNIVERSE,
            "premises": ["P1..P5", "S2", "p!=0", "c2_3!=0",
                         "c5_7!=0"],
            "not_materialized": (
                "the complete nine-body parent and its necessary-condition "
                "edge to this consequence model"),
        },
        "authority_boundary": (
            "local EMPTY authority belongs only to the exact R=0, OB!=0 "
            "dead-row consequence model; no automatic nine-body, component, "
            "actual-source, H3, or verdict authority"),
    }


def authority_spec(frozen):
    p = frozen["polynomials"]
    return {
        "schema": L.SCHEMA,
        "characteristic": 0,
        "ring_vars": list(frozen["ring_vars"]),
        "generators": [p["pin"], p["R"], p["value_24_delta"]],
        "guards": ["t", "p", "c2_3", "c5_7", p["OB_ambient"]],
        "expression": {
            "numerator": "1",
            "denominator_powers": [0, 0, 0, 0, 0],
        },
        "certificate": {
            "localization_powers": [0, 0, 0, 0, 1],
            "membership_target": p["OB_ambient"],
            "cofactors": ["0", "45*c2_3*t*c8_9", "1"],
        },
    }


def validate_frozen(frozen):
    require(frozen.get("schema") == FROZEN_SCHEMA and
            frozen.get("binding_digest_algo") == "sha256-lf-normalized", "F1",
            "frozen schema or digest algorithm changed")
    require(frozen.get("source_bindings") ==
            dict(sorted(NATIVE_BINDINGS.items())), "F2",
            "frozen native binding changed")
    _validate_native_certificate(frozen.get("native_certificate", {}))
    scope = frozen.get("scope", {})
    require(scope == {
        "presentation": "Delta-substituted S2 dead-row consequence",
        "constructible_piece": "R=0 and OB!=0",
        "coefficient_domain": "Q with 15*t^3+1 imposed",
        "point_universe": S.ALGEBRAIC_CLOSURE_POINT_UNIVERSE,
        "premises": ["P1..P5", "S2", "p!=0", "c2_3!=0", "c5_7!=0"],
        "not_materialized": (
            "the complete nine-body parent and its necessary-condition edge "
            "to this consequence model"),
    }, "M1", "constructible, point, premise, or parent scope changed")
    report = L.verify(authority_spec(frozen))
    require(report["checked"]["generator_count"] == 3 and
            G.parse_polynomial(report["checked"]["target"],
                               frozen["ring_vars"], 0) ==
            G.parse_polynomial(frozen["polynomials"]["OB_ambient"],
                               frozen["ring_vars"], 0), "M2",
            "localized dead-row identity changed")
    return report


def graph_authority_spec(frozen):
    """Compile compact sparse fixture values to the graph/backend format."""
    spec = authority_spec(frozen)
    compiled = dict(spec)
    compiled["generators"] = [G.render_polynomial(G.parse_polynomial(
        value, spec["ring_vars"], 0)) for value in spec["generators"]]
    compiled["guards"] = [G.render_polynomial(G.parse_polynomial(
        value, spec["ring_vars"], 0)) for value in spec["guards"]]
    return compiled


def check_native_bindings(frozen, native_root=NATIVE_ROOT):
    root = Path(native_root)
    require(root.exists(), "B5", "sibling JC checkout is absent")
    for name, expected in frozen["source_bindings"].items():
        require((root / name).exists(), "B6", "native input absent: " + name)
        require(normalized_sha256(root / name) == expected, "B7",
                "native input changed: " + name)


def graph_events(frozen, frozen_bytes):
    spec = graph_authority_spec(frozen)
    # The frozen artifact keeps the compact sparse producer representation.
    # Graph/backend inputs use the exact canonical representation emitted by
    # the trusted checker; the current Singular bridge accepts infix strings.
    checked = L.verify(spec)["normalized"]
    binding = "frozen wall receipt %s; native %s" % (
        _sha256(frozen_bytes),
        "sha256:" + frozen["source_bindings"][
            "f2_h3_onwall_repivot_certificate.json"])
    return [
        {
            "ev": "model", "id": MODEL,
            "what": "exact on-wall dead-row consequence model; " + binding,
            "characteristic": 0,
            "coefficient_domain": "Q",
            "point_universe": S.ALGEBRAIC_CLOSURE_POINT_UNIVERSE,
            "ring_vars": list(checked["ring_vars"]),
            "generators": list(checked["generators"]),
            "open_conditions": list(checked["guards"]),
            "chart": "p-S2-wall-OB-open-dead-row",
            "cite": "sha256:" + frozen["source_bindings"][
                "f2_h3_onwall_repivot_certificate.json"],
        },
        {
            "ev": "claim", "id": EMPTY_CLAIM, "model": MODEL,
            "kind": "EMPTY",
            "statement": (
                "the exact R=0, OB!=0 dead-row consequence model has no points"),
            "certificate": "LOCALIZED_UNIT_IDEAL_CERT",
            "established_by": "RAN",
            "ladder": "exact-checked",
            "cite": "sha256:" + frozen["source_bindings"][
                "f2_h3_onwall_repivot_certificate.json"],
            "caveat": frozen["authority_boundary"],
        },
    ]


def graph_from_frozen(frozen, frozen_bytes):
    graph = S.Graph()
    graph.apply(F.meta_event())
    for event in graph_events(frozen, frozen_bytes):
        graph.apply(event)
    graph.validate()
    return graph


def evidence_envelope(frozen, frozen_bytes, report):
    spec = authority_spec(frozen)
    context = EV.AffineContext(
        characteristic=0,
        coefficient_domain="Q",
        point_universe=S.ALGEBRAIC_CLOSURE_POINT_UNIVERSE,
        ring_vars=tuple(spec["ring_vars"]),
        unit_generators=tuple(spec["guards"]),
        generators=tuple(spec["generators"]),
    )
    return EV.EvidenceEnvelope(
        schema=L.SCHEMA,
        context=context,
        source_bindings=tuple(EV.SourceBinding(name, "sha256:" + digest)
                              for name, digest in sorted(
                                  frozen["source_bindings"].items())),
        checked_proposition=(
            "OB belongs to (R,value_24) and OB is inverted on the exact "
            "on-wall open consequence model"),
        certificate_payload={
            "membership_target": report["checked"]["target"],
            "generator_count": report["checked"]["generator_count"],
            "cofactor_identity": "OB = value_24 + 45*c2_3*t*c8_9*R",
        },
        licenses=tuple(report["licenses"]),
        outstanding_premises=(
            frozen["scope"]["not_materialized"],
            "obtain a current graph-bound localized-unit verifier verdict",
        ),
        graph_effect=EV.GRAPH_EFFECT_NONE,
        authority_boundary=frozen["authority_boundary"],
    ).as_dict()


def write_campaign(root, frozen, frozen_bytes, record):
    graph_path = Path(S.graph_path(str(root)))
    if graph_path.exists():
        raise WallObstructionError("campaign graph already exists: %s" %
                                   graph_path)
    S.append(graph_events(frozen, frozen_bytes), root=str(root))
    results = V.verify_all(root=str(root)) if record else []
    graph = S.load(S.graph_path(str(root)))
    claim = graph.claims[EMPTY_CLAIM]
    if record:
        require(claim.get("certificate_verdict") == V.CERT_VERIFIED, "G1",
                "recorded campaign did not mint local EMPTY authority")
        require(C.effective_certificate(claim) ==
                "LOCALIZED_UNIT_IDEAL_CERT", "G2",
                "current localized-unit authority was not effective")
    return {
        "graph": str(graph_path),
        "local_verdict": claim.get("certificate_verdict"),
        "graph_effect": (EV.GRAPH_EFFECT_LOCAL_EMPTY if record
                         else EV.GRAPH_EFFECT_NONE),
        "verify_results": [list(item[:3]) for item in results],
    }


def native_replay(native_root=NATIVE_ROOT):
    completed = subprocess.run(
        [sys.executable, str(Path(native_root) /
         "f2_h3_onwall_repivot.py"), "--quiet"], cwd=str(native_root),
        capture_output=True, text=True, timeout=180, check=False)
    require(completed.returncode == 0, "N5",
            "native on-wall replay failed: " + completed.stderr.strip())
    require("25/25 pass" in completed.stdout and
            "wall blockage = base obstruction OB" in completed.stdout, "N6",
            "native replay summary changed")
    return {"verdict": "VERIFIED_NATIVE_25_OF_25", "graph_effect": "NONE"}


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--native-root", type=Path, default=NATIVE_ROOT)
    parser.add_argument("--frozen", type=Path, default=DEFAULT_FROZEN)
    parser.add_argument("--authority", type=Path, default=DEFAULT_AUTHORITY)
    parser.add_argument("--write-fixtures", action="store_true")
    parser.add_argument("--check-native-bindings", action="store_true")
    parser.add_argument("--native-replay", action="store_true")
    parser.add_argument("--campaign-root", type=Path)
    parser.add_argument("--record", action="store_true")
    parser.add_argument("--output", type=Path)
    args = parser.parse_args(argv)
    if args.record and args.campaign_root is None:
        parser.error("--record requires --campaign-root")
    try:
        if args.write_fixtures:
            frozen = build_frozen(args.native_root)
            args.frozen.parent.mkdir(parents=True, exist_ok=True)
            args.frozen.write_bytes(_encoded(frozen))
            args.authority.write_bytes(_encoded(authority_spec(frozen)))
        frozen_bytes = args.frozen.read_bytes()
        if EXPECTED_FROZEN_SHA256 is not None:
            require(hashlib.sha256(frozen_bytes).hexdigest() ==
                    EXPECTED_FROZEN_SHA256, "F3",
                    "frozen wall-obstruction fixture digest changed")
        frozen = json.loads(frozen_bytes.decode("utf-8"))
        report = validate_frozen(frozen)
        require(args.authority.read_bytes() ==
                _encoded(authority_spec(frozen)), "F4",
                "checked-in localized authority fixture changed")
        if args.check_native_bindings:
            check_native_bindings(frozen, args.native_root)
        output = {
            "verdict": report["verdict"],
            "checked_target": "OB",
            "native_parent_sha256": frozen["source_bindings"][
                "f2_h3_onwall_repivot_certificate.json"],
            "frozen_receipt_sha256": _sha256(frozen_bytes),
            "standalone_graph_effect": "NONE",
            "compiled_graph_effect": "LOCAL_EMPTY on exact model after a "
                                     "current graph-bound verdict",
            "authority_boundary": frozen["authority_boundary"],
            "evidence_envelope": evidence_envelope(
                frozen, frozen_bytes, report),
        }
        if args.native_replay:
            output["native_replay"] = native_replay(args.native_root)
        if args.campaign_root is not None:
            output["campaign"] = write_campaign(
                args.campaign_root, frozen, frozen_bytes, args.record)
        payload = _encoded(output)
        if args.output is not None:
            require(not args.output.exists(), "O1",
                    "output exists: %s" % args.output)
            args.output.parent.mkdir(parents=True, exist_ok=True)
            args.output.write_bytes(payload)
        else:
            sys.stdout.buffer.write(payload)
        return 0
    except (WallObstructionError, L.LocalizationError, G.CertificateError,
            OSError, ValueError, json.JSONDecodeError) as exc:
        print("REFUSED: %s" % exc, file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
