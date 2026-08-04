#!/usr/bin/env python3
"""Replay the JC b=0 free-plane exceptional-factor receipt.

Fixture construction executes the digest-bound native checker and freezes its
complete 35-object two-column ledger. Routine replay is independent bounded
arithmetic over QQ: it verifies the four nonzero rows, their b/Delta
factorizations, the S2 and b=0 restrictions, and the reversible c9_7 affine
coordinate change. The result is standalone evidence with graph effect NONE.
"""

from __future__ import annotations

import argparse
import contextlib
import copy
import hashlib
import importlib.util
import io
import json
import os
import subprocess
import sys
import tempfile
from fractions import Fraction
from pathlib import Path

from grandportage import groebner as G
from grandportage import evidence as EV


ROOT = Path(__file__).resolve().parents[2]
NATIVE_ROOT = ROOT.parent / "math-stuff" / "d2_plane_72_108"
DEFAULT_FIXTURE = ROOT / "fixtures" / "jc_b0_free_plane" / "v1.json"
DEFAULT_REVIEW = ROOT / "review" / "jc-h3-b0-free-plane-v1.json"
SCHEMA = EV.EXCEPTIONAL_FACTOR_COLUMN_SCHEMA
EXPECTED_FIXTURE_SHA256 = (
    "b0bdca0a0b410d3510dd6b9285f9484c9c4462b42ebf3ff3439925a2326fac58")

NATIVE_BINDINGS = {
    "f2_h3_b0_free_plane_receipt.json":
        "e6c731f984d9c06d84aac014db8bff234bb15962d1ee6fac2ee80df7795e00da",
    "f2_h3_b0_free_plane_receipt.py":
        "0a97339a1c9dc7e3c9d04ce39b76b95f58171f20abb0f4b5a8b836628083edf9",
    "f2_h3_b0_compatibility_module.json":
        "944f95d762e05d3dec4ffa6599b4f0d1d2674e4127e5d168712a62de50291840",
    "f2_h3_p_c6_1_receipt.json":
        "d971325110dcab38b25089c542c4cc5fd79ddb04342124ebf11c5d673ce4ee25",
    "f2_h3_rung_degeneration_sweep.json":
        "aa5088d03fdf484b059103d798b2e2509f8d5f7e88d84d7dfda1f4c23abb0bdf",
    "f2_h3_source_depth6_chain_certificate.json.gz":
        "2280c88410667ce9c8ac5900c61b044f5cd7174540d859485c04bcca3a27eba0",
    "f2_h3_source_depth6_receipt.json":
        "3dde87dd53b07c851ce78c27227b63660a9177860791cc2dca5bff5152db9c0d",
    "f2_h3_source_depth7_receipt.json":
        "2b50fc44669222a335697119c6221588e056cc32dfc1e1590e96162a4d301b86",
}

RING_VARS = ("c2_3", "c3_5", "c4_5", "c5_7", "c8_12", "t")
FREE_COLUMNS = ("c7_4", "c8_5")
LIVE_BODIES = (
    "E321", "VD", "d7rung:row1/c9_7", "d7rung:row4/c5_0",
)


class FreePlaneEvidenceError(ValueError):
    """The frozen column ledger, factorization, or scope drifted."""


def require(condition, check_id, message):
    if not condition:
        raise FreePlaneEvidenceError("%s: %s" % (check_id, message))


def normalized_sha256(path):
    return hashlib.sha256(
        Path(path).read_bytes().replace(b"\r\n", b"\n")).hexdigest()


def encoded(value):
    return (json.dumps(value, indent=2, sort_keys=True,
                       ensure_ascii=True) + "\n").encode("utf-8")


def _canonical_native(value):
    return (json.dumps(value, sort_keys=True, separators=(",", ":"))
            + "\n").encode("utf-8")


def _native_series_to_sparse(value):
    require(isinstance(value, list), "P1", "native polynomial is not a list")
    terms = []
    seen = set()
    for position, entry in enumerate(value):
        require(isinstance(entry, list) and len(entry) == 2, "P2",
                "native term %d is malformed" % position)
        powers, coefficient = entry
        require(isinstance(powers, list) and isinstance(coefficient, str),
                "P3", "native term fields are malformed")
        try:
            rational = Fraction(coefficient)
        except (ValueError, ZeroDivisionError) as exc:
            raise FreePlaneEvidenceError("P4: invalid rational coefficient") from exc
        require(str(rational) == coefficient and rational != 0, "P5",
                "native coefficient is not canonical nonzero rational")
        power_map = {}
        for pair in powers:
            require(isinstance(pair, list) and len(pair) == 2 and
                    pair[0] in RING_VARS and type(pair[1]) is int and
                    pair[1] > 0, "P6", "native variable power is invalid")
            require(pair[0] not in power_map, "P7", "duplicate variable power")
            power_map[pair[0]] = pair[1]
        monomial = tuple(power_map.get(name, 0) for name in RING_VARS)
        require(monomial not in seen, "P8", "duplicate native monomial")
        seen.add(monomial)
        terms.append({
            "coefficient": coefficient,
            "powers": [[name, exponent] for name, exponent in
                       zip(RING_VARS, monomial) if exponent],
        })
    terms.sort(key=lambda term: tuple(dict(term["powers"]).get(name, 0)
                                      for name in RING_VARS), reverse=True)
    return {"schema": G.SPARSE_POLYNOMIAL_SCHEMA, "terms": terms}


def _poly(value):
    return G.parse_polynomial(_native_series_to_sparse(value), RING_VARS)


def _expected_projection():
    return {
        "instance_id": "jc_h3_b0_landed_free_plane_columns",
        "coefficient_domain": "K = QQ[t]/(15*t^3+1)",
        "semantic_layer": "MATERIALIZED_B0_COMPATIBILITY_MODULE",
        "model": {
            "name": "X_b",
            "equations": ["c5_7=0", "R=0", "A=0", "OB=0", "Delta=0"],
            "guards": ["c2_3!=0", "p!=0", "det5!=0"],
            "free_coordinates": ["c7_4", "c8_5"],
        },
        "checked_result": {
            "ambient_exceptional_factors": ["c5_7", "Delta"],
            "S2_exceptional_factors": ["c5_7"],
            "c8_5_column_generator": "15*c5_7*t^2",
            "c7_4_affine_pivot": {
                "solved_coordinate": "c9_7",
                "march_pivot": "10*t",
                "coefficient": "-(3/2)*c2_3",
                "coordinate_change": "c9_7 <-> c9_7+(3/2)*c2_3*c7_4",
                "role": "DETERMINATION_NOT_COMPATIBILITY",
            },
            "downstream_equation_count": 8,
            "downstream_uses_c9_7": False,
        },
        "licenses": [
            "the complete landed free-plane column ledger has exactly four live bodies",
            "apart from one solved-coordinate rung, every live coefficient lies in (c5_7,Delta)",
            "on S2 every non-pivot live coefficient is divisible by c5_7",
            "the c9_7 rung is a reversible affine determination step and not a ninth equation",
            "no landed body constrains c8_5 after restricting to b=0",
        ],
        "does_not_license": [
            "freeness on R=0 with c5_7 unrestricted",
            "ambient freeness before imposing Delta=0",
            "a free-plane component or irreducibility statement",
            "constraints from any refused or unmaterialized depth-eight body",
            "all-orders lifting, source sufficiency, source membership, H8, H3, or (75,125)",
            "any graph claim or transport authority",
        ],
        "first_open_obligation": (
            "the six coefficients of c8_5 and c9_7 in the depth-eight "
            "boundary triple E[2,19], E[3,20], E[4,22] on X_b"),
        "graph_effect": "NONE",
    }


def _validate_native_certificate(certificate):
    require(certificate.get("id") == "f2_h3_b0_free_plane_receipt" and
            certificate.get("schema_version") == 1 and
            certificate.get("verdict") == "EXCEPTIONAL_FACTOR_IDENTIFIED",
            "N1", "native receipt identity, schema, or verdict changed")
    require(certificate.get("bindings") == {
        name: NATIVE_BINDINGS[name] for name in (
            "f2_h3_b0_compatibility_module.json",
            "f2_h3_p_c6_1_receipt.json",
            "f2_h3_rung_degeneration_sweep.json",
            "f2_h3_source_depth6_chain_certificate.json.gz",
            "f2_h3_source_depth6_receipt.json",
            "f2_h3_source_depth7_receipt.json",
        )}, "N2", "native dependency custody changed")
    require(certificate.get("inventory_size") == 35 and
            certificate.get("bodies_touching_the_plane") == list(LIVE_BODIES),
            "N3", "native ledger inventory or live-body set changed")
    require(certificate.get("exceptional_factors") ==
            ["c5_7 (= b)", "Delta = c2_3**2 - 4*c4_5"] and
            certificate.get("exceptional_factors_on_S2") == ["c5_7 (= b)"],
            "N4", "native exceptional factors changed")
    pivot = certificate.get("affine_pivot", {})
    require(pivot.get("solves") == "c9_7" and pivot.get("pivot") == "10*t"
            and pivot.get("coefficient_in_c7_4") == "-(3/2)*c2_3" and
            "NOT a compatibility condition" in pivot.get("reading", "") and
            "none of the eight" in pivot.get("invisible_downstream", ""),
            "N5", "native affine-pivot scope changed")
    require(certificate.get("next_receipt", {}).get("size") ==
            "coefficient-only: three c8_5 coefficients and three c9_7 coefficients, no body materialization",
            "N6", "native first open receipt changed")
    require(any("no source sufficiency" in item for item in
                certificate.get("refusals", [])), "N7",
            "native source/H3 refusal disappeared")


def _capture_native(native_root):
    root = Path(native_root)
    script = root / "f2_h3_b0_free_plane_receipt.py"
    old_argv, old_path = sys.argv[:], sys.path[:]
    captured = {}
    try:
        sys.argv = [str(script), "--quiet"]
        sys.path.insert(0, str(root))
        spec = importlib.util.spec_from_file_location(
            "gp_free_plane_fixture_native", script)
        module = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(module)

        def profile(frame, event, _argument):
            if frame.f_code is module.main.__code__ and event == "return":
                captured.update(frame.f_locals)

        sys.setprofile(profile)
        try:
            with contextlib.redirect_stdout(io.StringIO()):
                returncode = module.main()
        finally:
            sys.setprofile(None)
        require(returncode == 0, "B1", "native free-plane checker failed")
        return module, captured
    finally:
        sys.argv = old_argv
        sys.path[:] = old_path


def build_fixture(native_root=NATIVE_ROOT):
    root = Path(native_root)
    bindings = {name: normalized_sha256(root / name)
                for name in sorted(NATIVE_BINDINGS)}
    require(bindings == dict(sorted(NATIVE_BINDINGS.items())), "B2",
            "native inputs drifted before freeze")
    module, captured = _capture_native(root)
    certificate = json.loads((root / "f2_h3_b0_free_plane_receipt.json")
                             .read_text(encoding="utf-8"))
    _validate_native_certificate(certificate)
    columns = {
        body: {column: module.ser(values[column])
               for column in FREE_COLUMNS}
        for body, values in captured["COEF"].items()
    }
    return {
        "schema": SCHEMA,
        "binding_digest_algo": "sha256-lf-normalized",
        "source_bindings": bindings,
        "native_certificate": certificate,
        "columns": columns,
        "projection": _expected_projection(),
        "authority_boundary": (
            "This verifies a complete finite coefficient ledger and one "
            "coordinate normalization only. It mints no model, component, "
            "source, H3, verdict, or graph authority."),
    }


def _substitute(poly, images):
    encoded_poly = G.encode_sparse_polynomial(poly)
    full = dict((name, name) for name in RING_VARS)
    full.update(images)
    return G.parse_polynomial(
        G.substitute_polynomial(encoded_poly, RING_VARS, full,
                                _preserve_sparse=True), RING_VARS)


def _validate_arithmetic(fixture):
    columns = fixture["columns"]
    require(len(columns) == 35 and set(columns) and
            all(set(value) == set(FREE_COLUMNS) for value in columns.values()),
            "A1", "complete 35-body two-column ledger is absent")
    parsed = {body: {column: _poly(value)
                     for column, value in row.items()}
              for body, row in columns.items()}
    live = sorted(body for body, row in parsed.items()
                  if any(not value.is_zero for value in row.values()))
    require(live == sorted(LIVE_BODIES), "A2",
            "free-plane live-body set changed")

    certificate_hashes = fixture["native_certificate"]["coefficients_sha256"]
    actual_hashes = {
        body: hashlib.sha256(_canonical_native(columns[body])).hexdigest()
        for body in LIVE_BODIES
    }
    require(actual_hashes == certificate_hashes, "A3",
            "frozen exact coefficients do not match native commitments")

    a = G.parse_polynomial("c2_3", RING_VARS)
    c = G.parse_polynomial("c3_5", RING_VARS)
    b = G.parse_polynomial("c5_7", RING_VARS)
    t = G.parse_polynomial("t", RING_VARS)
    delta = G.parse_polynomial("c2_3^2-4*c4_5", RING_VARS)
    wall = G.parse_polynomial(
        "c8_12+2*c3_5*c5_7-c2_3*c3_5^2", RING_VARS)
    require(parsed["E321"]["c7_4"] ==
            G.parse_polynomial("(5/2)*t*(c2_3^2-4*c4_5)", RING_VARS),
            "A4", "E321 c7_4 Delta factorization failed")
    require(parsed["VD"]["c7_4"] == G.parse_polynomial(
        "-30*c5_7*t*(c8_12+3*c3_5*c5_7-c2_3*c3_5^2)"
        "+(15/2)*c2_3*t^2*(c2_3^2-4*c4_5)", RING_VARS),
        "A5", "VD c7_4 exceptional-factor split failed")
    expected_bt2 = G.parse_polynomial("15*c5_7*t^2", RING_VARS)
    require(parsed["VD"]["c8_5"] == expected_bt2 and
            parsed["d7rung:row4/c5_0"]["c7_4"] == expected_bt2,
            "A6", "pure b column generator changed")
    require(parsed["d7rung:row1/c9_7"]["c7_4"] ==
            G.parse_polynomial("-(3/2)*c2_3", RING_VARS), "A7",
            "unit affine-pivot coefficient changed")

    s2_b0 = {"c4_5": "c2_3^2/4", "c5_7": "0",
             "c8_12": "c2_3*c3_5^2"}
    require(all(_substitute(value, s2_b0).is_zero
                for body, row in parsed.items()
                for value in row.values()
                if body != "d7rung:row1/c9_7"), "A8",
            "a non-pivot column survives on X_b")
    require(not _substitute(parsed["VD"]["c8_5"], {
                "c8_12": "c2_3*c3_5^2-2*c3_5*c5_7"}).is_zero,
            "M1", "wall-only mutation no longer revives c8_5")
    require(not parsed["E321"]["c7_4"].is_zero and
            _substitute(parsed["E321"]["c7_4"], {
                "c4_5": "c2_3^2/4"}).is_zero, "M2",
            "ambient/S2 distinction disappeared")
    require(not a.is_zero and not c.is_zero and not b.is_zero and
            not t.is_zero and not delta.is_zero and not wall.is_zero, "A9",
            "declared ambient symbols or factors collapsed")

    translation_vars = ("c2_3", "c7_4", "c9_7")
    forward = G.substitute_polynomial(
        "c9_7", translation_vars,
        {"c2_3": "c2_3", "c7_4": "c7_4",
         "c9_7": "c9_7+(3/2)*c2_3*c7_4"})
    backward = G.substitute_polynomial(
        forward, translation_vars,
        {"c2_3": "c2_3", "c7_4": "c7_4",
         "c9_7": "c9_7-(3/2)*c2_3*c7_4"})
    require(G.canonical_polynomial(backward, translation_vars) == "c9_7",
            "A10", "affine pivot round trip failed")
    return {
        "loaded_bodies": 35,
        "distinct_bodies": 31,
        "live_bodies": live,
        "ambient_factors": ["c5_7", "Delta"],
        "S2_factors": ["c5_7"],
        "affine_round_trip": True,
        "downstream_equations": 8,
    }


def validate_fixture_value(fixture):
    require(set(fixture) == {"schema", "binding_digest_algo",
            "source_bindings", "native_certificate", "columns",
            "projection", "authority_boundary"}, "F1",
            "fixture shape changed")
    require(fixture["schema"] == SCHEMA and
            fixture["binding_digest_algo"] == "sha256-lf-normalized", "F2",
            "fixture schema or binding algorithm changed")
    require(fixture["source_bindings"] ==
            dict(sorted(NATIVE_BINDINGS.items())), "F3",
            "frozen native binding changed")
    require(fixture["projection"] == _expected_projection(), "M3",
            "scope, license, refusal, open obligation, or graph effect changed")
    _validate_native_certificate(fixture["native_certificate"])
    return _validate_arithmetic(fixture)


def check_native_bindings(fixture, native_root=NATIVE_ROOT):
    root = Path(native_root)
    require(root.exists(), "B3", "sibling JC checkout is absent")
    for name, expected in fixture["source_bindings"].items():
        require((root / name).exists(), "B4", "native binding absent: " + name)
        require(normalized_sha256(root / name) == expected, "B5",
                "native binding changed: " + name)


def report_from_checked_fixture(fixture, checked):
    report = copy.deepcopy(fixture["projection"])
    report.update({
        "schema": SCHEMA,
        "verdict": "VERIFIED_EXCEPTIONAL_FACTOR_LEDGER",
        "checked_instance": checked,
        "source_bindings": fixture["source_bindings"],
        "evidence_envelope": {
            "schema": SCHEMA,
            "checked_proposition": (
                "the complete landed b=0 free-plane column ledger has the "
                "declared b/Delta factors and one legal affine pivot"),
            "licenses": fixture["projection"]["licenses"],
            "first_open_obligation": fixture["projection"][
                "first_open_obligation"],
            "graph_effect": "NONE",
            "authority_boundary": fixture["authority_boundary"],
        },
    })
    return report


def verify_fixture(path=DEFAULT_FIXTURE, check_bindings=False,
                   native_root=NATIVE_ROOT):
    raw = Path(path).read_bytes()
    if EXPECTED_FIXTURE_SHA256 is not None:
        require(hashlib.sha256(raw).hexdigest() == EXPECTED_FIXTURE_SHA256,
                "F4", "frozen free-plane fixture digest changed")
    fixture = json.loads(raw.decode("utf-8"))
    checked = validate_fixture_value(fixture)
    if check_bindings:
        check_native_bindings(fixture, native_root)
    return report_from_checked_fixture(fixture, checked)


def native_replay(native_root=NATIVE_ROOT):
    completed = subprocess.run(
        [sys.executable, str(Path(native_root) /
         "f2_h3_b0_free_plane_receipt.py"), "--quiet"],
        cwd=str(native_root), capture_output=True, text=True,
        timeout=120, check=False)
    require(completed.returncode == 0, "N8",
            "native free-plane replay failed: " + completed.stderr.strip())
    require("19/19 checks passed" in completed.stdout and
            "EXCEPTIONAL_FACTOR_IDENTIFIED" in completed.stdout, "N9",
            "native replay summary changed")
    return {"verdict": "VERIFIED_NATIVE_19_OF_19", "graph_effect": "NONE"}


def _atomic_write(path, value, force=False):
    path = Path(path)
    if path.exists() and not force:
        raise FreePlaneEvidenceError(
            "output exists; pass --force to replace it: %s" % path)
    payload = encoded(value)
    path.parent.mkdir(parents=True, exist_ok=True)
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
    return hashlib.sha256(payload).hexdigest()


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--fixture", type=Path, default=DEFAULT_FIXTURE)
    parser.add_argument("--native-root", type=Path, default=NATIVE_ROOT)
    parser.add_argument("--check-native-bindings", action="store_true")
    parser.add_argument("--native-replay", action="store_true")
    parser.add_argument("--write-fixture", action="store_true")
    parser.add_argument("--output", type=Path)
    parser.add_argument("--force", action="store_true")
    args = parser.parse_args(argv)
    if args.force and not (args.write_fixture or args.output):
        parser.error("--force requires --write-fixture or --output")
    try:
        if args.write_fixture:
            digest = _atomic_write(
                args.fixture, build_fixture(args.native_root), args.force)
            print(json.dumps({"fixture": str(args.fixture), "sha256": digest},
                             indent=2, sort_keys=True))
            return 0
        report = verify_fixture(
            args.fixture, args.check_native_bindings, args.native_root)
        if args.native_replay:
            report["native_replay"] = native_replay(args.native_root)
        if args.output:
            _atomic_write(args.output, report, args.force)
        else:
            print(json.dumps(report, indent=2, sort_keys=True))
        return 0
    except (FreePlaneEvidenceError, G.CertificateError, OSError, ValueError,
            json.JSONDecodeError) as exc:
        print("REFUSED: %s" % exc, file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
