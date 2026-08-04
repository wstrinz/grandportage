#!/usr/bin/env python3
"""Materialize the complete finite reduced E-system template as a GP graph.

This is deliberately an assay, not a global checker-limit increase.  The
complete finite root supports produce a 78-variable exact-affine model.  Its
147 nonzero coefficient equations contain the landed 25 depth-2..6 equations
verbatim, so the source-to-selection NECESSARY_CONDITION earns containment by
exact generator inclusion without Groebner search.

The source endpoint is the reduced E-system template, not an original
polynomial pair.  No reverse point lift, chart coverage, H3, or verdict change
is licensed.
"""

from __future__ import annotations

import argparse
import hashlib
import importlib.util
import json
from pathlib import Path

from grandportage import check as C
from grandportage import groebner as G
from grandportage import kernel as K
from grandportage import store as S
from grandportage import verify as V


ROOT = Path(__file__).resolve().parents[2]
FACE_ADAPTER_PATH = Path(__file__).with_name("face_extraction_adapter.py")
SOURCE_MODEL = "JC-H3-REDUCED-ESYSTEM-FINITE-TEMPLATE"
SELECTED_MODEL = "JC-H3-REDUCED-ESYSTEM-DEPTH2-6"
EDGE = "JC-H3-SELECT-DEPTH2-6"


def _load_face_adapter():
    spec = importlib.util.spec_from_file_location(
        "jc_source_depth6_faces_for_full_template", FACE_ADAPTER_PATH)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


FACE = _load_face_adapter()


def _source_rows():
    fixture = json.loads(FACE.DEFAULT_FIXTURE.read_text(encoding="utf-8"))
    return {
        record["row"]: FACE.CHAIN._decode_sparse(
            record["sparse"], "full-template source row")
        for record in fixture["source_rows"]
    }


def _complete_depth(row):
    """Largest possible face depth from the exact finite term supports."""
    maximum = FACE._row_max(row)
    answer = 0
    for monomial in row:
        powers = dict(monomial)
        weight = sum(
            powers.get("z%d" % root, 0) * FACE.ROOT_SUPPORTS[root][-1]
            for root in FACE.ROOTS
        )
        distance = maximum - weight
        FACE._require(distance >= 0 and distance % FACE.DELTA == 0,
                      "source term violates the frozen grading")
        depth = distance // FACE.DELTA + sum(
            powers.get("z%d" % root, 0)
            * (len(FACE.ROOT_SUPPORTS[root]) - 1)
            for root in FACE.ROOTS
        )
        answer = max(answer, depth)
    return answer


def _ring_variables(faces):
    return sorted({
        name
        for polynomial in faces.values()
        for monomial in polynomial
        for name, _ in monomial
    })


def _gp_sparse(polynomial, variables):
    """Encode the native sparse map in GP's canonical sparse-polynomial IR."""
    order = {name: index for index, name in enumerate(variables)}

    def monomial_key(monomial):
        powers = dict(monomial)
        return tuple(powers.get(name, 0) for name in variables)

    terms = []
    for monomial, coefficient in sorted(
            polynomial.items(), key=lambda item: monomial_key(item[0]),
            reverse=True):
        powers = sorted(monomial, key=lambda factor: order[factor[0]])
        terms.append({
            "coefficient": str(coefficient),
            "powers": [[name, exponent] for name, exponent in powers],
        })
    encoded = {"schema": G.SPARSE_POLYNOMIAL_SCHEMA, "terms": terms}
    # Encoding is part of the producer boundary; immediately reparse it with
    # the independent bounded checker before it can enter a graph.
    G.parse_polynomial(encoded, variables, 0)
    return encoded


def compile_campaign(full_source_replay=False):
    # Reuse the selected-face gate as an upstream weld: it checks the fixture
    # digest, source-row digests, formula/support manifests, and all 25 landed
    # chain commitments before the larger model is materialized.
    FACE.verify_fixture(full_source_replay=full_source_replay)
    rows = _source_rows()

    row_depths = {row: _complete_depth(value)
                  for row, value in sorted(rows.items())}
    maximum_depth = max(row_depths.values())
    faces, row_maxima, products = FACE._build_faces(
        rows, depth=maximum_depth)
    for (row, depth), polynomial in faces.items():
        if depth > row_depths[row]:
            FACE._require(not polynomial,
                          "a coefficient survived above its complete bound")

    nonzero = {key: value for key, value in faces.items() if value}
    variables = _ring_variables(nonzero)
    FACE._require(len(variables) == 78,
                  "the complete reduced template no longer has 78 variables")
    FACE._require(len(nonzero) == 147,
                  "the complete reduced template no longer has 147 rows")

    encoded = {
        key: _gp_sparse(polynomial, variables)
        for key, polynomial in sorted(nonzero.items())
    }
    selected_keys = [(row, depth) for row in range(1, 6)
                     for depth in range(2, 7)]
    FACE._require(all(key in encoded for key in selected_keys),
                  "a selected landed face vanished from the complete model")
    source_generators = list(encoded.values())
    selected_generators = [encoded[key] for key in selected_keys]
    payload = json.dumps(
        source_generators, sort_keys=True, separators=(",", ":"),
        ensure_ascii=True).encode("utf-8")
    digest = hashlib.sha256(payload).hexdigest()

    common = {
        "characteristic": 0,
        "coefficient_domain": "Q",
        "point_universe": S.ALGEBRAIC_CLOSURE_POINT_UNIVERSE,
        "ring_vars": variables,
        "cite": "sha256:" + FACE.EXPECTED_FIXTURE_SHA256,
    }
    source = dict(common, **{
        "ev": "model",
        "id": SOURCE_MODEL,
        "what": (
            "all nonzero coefficient equations of the five reduced E-system "
            "rows under the complete declared finite root supports"),
        "generators": source_generators,
    })
    selected = dict(common, **{
        "ev": "model",
        "id": SELECTED_MODEL,
        "what": (
            "the exact 25 depth-2..6 coefficient equations selected from "
            "the complete reduced E-system template"),
        "generators": selected_generators,
    })
    edge = {
        "ev": "edge",
        "id": EDGE,
        "src": SOURCE_MODEL,
        "dst": SELECTED_MODEL,
        "type": K.NECESSARY_CONDITION,
        "map_kind": K.IDENTITY_MAP,
        "why": (
            "retain depths 2 through 6 and drop the other 122 nonzero "
            "coefficient equations in the same 78-coordinate ring"),
        "drops": ["all coefficient rows outside depths 2 through 6"],
        "support": ["sha256:" + digest],
    }
    return {
        "events": [source, selected, edge],
        "source_generators": 147,
        "selected_generators": 25,
        "dropped_generators": 122,
        "ring_variables": 78,
        "row_complete_depths": row_depths,
        "sparse_terms": sum(len(value) for value in nonzero.values()),
        "sparse_products": products,
        "generator_bundle_sha256": digest,
        "full_source_replay": full_source_replay,
        "selected_face_weld_verified": True,
        "authority": {
            "licenses": [
                "reduced_esystem_nonempty_implies_selected_faces_nonempty",
                "selected_faces_empty_implies_reduced_esystem_empty",
            ],
            "refuses": [
                "selected_faces_nonempty_implies_reduced_esystem_nonempty",
                "original polynomial-pair membership",
                "chart coverage",
                "H3 promotion",
                "(75,125) verdict change",
            ],
        },
    }


def graph_from_campaign(campaign):
    graph = S.Graph()
    graph.apply_all([(event, "full-template", index)
                     for index, event in enumerate(campaign["events"])])
    graph.validate()
    return graph


def write_campaign(root, campaign, record=False):
    graph_path = Path(S.graph_path(str(root)))
    if graph_path.exists():
        raise ValueError("campaign graph already exists: %s" % graph_path)
    S.append(campaign["events"], root=str(root))
    results = V.verify_all(root=str(root)) if record else []
    graph = S.load(S.graph_path(str(root)))
    findings = C.run(graph)
    if record and graph.edges[EDGE].get("containment") != V.VERIFIED:
        raise AssertionError("the exact selected-face containment was not earned")
    return {
        "graph": str(graph_path),
        "graph_bytes": graph_path.stat().st_size,
        "containment": graph.edges[EDGE].get("containment"),
        "findings": [finding.as_dict() for finding in findings],
        "verify_results": [list(item[:3]) for item in results],
    }


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--full-source-replay", action="store_true")
    parser.add_argument("--campaign-root", type=Path)
    parser.add_argument("--record", action="store_true")
    args = parser.parse_args(argv)
    if args.record and args.campaign_root is None:
        parser.error("--record requires --campaign-root")
    campaign = compile_campaign(args.full_source_replay)
    output = {key: value for key, value in campaign.items()
              if key != "events"}
    if args.campaign_root is not None:
        output["campaign"] = write_campaign(
            args.campaign_root, campaign, record=args.record)
    print(json.dumps(output, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
