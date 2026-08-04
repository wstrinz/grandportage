"""Bind the frozen JC p-axis receipt to existing GP local-EMPTY authority.

The native JC producer remains responsible for extracting the axis equations.
This adapter freezes the selected receipt, independently checks the resulting
localized-unit cofactor identity, and can build a disposable or review campaign.
It introduces no claim kind, edge type, graph field, or verifier authority.
"""

import argparse
import hashlib
import json
from pathlib import Path

from grandportage import check as C
from grandportage import evidence as EV
from grandportage import format as F
from grandportage import kernel as K
from grandportage import localization as L
from grandportage import store as S
from grandportage import verify as V


ROOT = Path(__file__).resolve().parents[2]
DEFAULT_SOURCE = (ROOT.parent / "math-stuff" / "d2_plane_72_108" /
                  "f2_h3_p_window_certificate.json")
DEFAULT_FROZEN = (ROOT / "fixtures" / "jc_p_axis" /
                  "native_axis_slice_v1.json")
DEFAULT_AUTHORITY = (ROOT / "fixtures" / "jc_p_axis" /
                     "localized_unit_ideal_v1.json")

EXPECTED_NATIVE_SHA256 = (
    "sha256:77a110c9d5fc0ab47c67f86509f3d777"
    "d8d9602bad08a992244d3fd98d1b4dde"
)
NATIVE_SCHEMA = "jc-f2-h3-window-elimination/v1"
FROZEN_SCHEMA = "jc-f2-h3-p-axis-slice/v1"
FACTOR_ID = "p-axis-c9_11-square"
AXIS_MODEL = "JC-P-C9-AXIS"
PARENT_MODEL = "JC-P-C9-AXIS-AMBIENT"
EMPTY_CLAIM = "JC-P-C9-AXIS-EMPTY"
PARENT_EDGE = "JC-P-C9-AXIS-IN-AMBIENT"


def _sha256(data):
    return "sha256:" + hashlib.sha256(data).hexdigest()


def _encoded(value):
    return (json.dumps(value, indent=2, sort_keys=True,
                       ensure_ascii=True) + "\n").encode("utf-8")


def freeze_native(native, source_bytes):
    source_sha = _sha256(source_bytes)
    if source_sha != EXPECTED_NATIVE_SHA256:
        raise ValueError(
            "native p-window receipt changed: expected %s, got %s"
            % (EXPECTED_NATIVE_SHA256, source_sha))
    if native.get("schema") != NATIVE_SCHEMA:
        raise ValueError("unexpected native receipt schema")
    if native.get("chart") != "p":
        raise ValueError("native receipt is not the p chart")
    if native.get("pin") != "15*t^3+1=0":
        raise ValueError("native receipt changed the scalar pin")
    if native.get("declared_units") != ["p", "t"]:
        raise ValueError("native receipt changed the declared units")
    ring = native.get("ring") or {}
    if ring.get("domain") is not True:
        raise ValueError("native receipt no longer records its domain premise")
    if ring.get("declared_units") != ["p", "t"]:
        raise ValueError("native ring and receipt disagree about units")

    receipts = dict((item.get("id"), item)
                    for item in native.get("factor_certificates") or [])
    if FACTOR_ID not in receipts:
        raise ValueError("native receipt lacks %s" % FACTOR_ID)
    factor = receipts[FACTOR_ID]
    consequences = factor.get("consequences") or []
    if len(consequences) != 1:
        raise ValueError("selected factor receipt needs one affine consequence")
    consequence = consequences[0]
    if factor.get("equation") != [3, 22]:
        raise ValueError("selected factor equation id changed")
    if consequence.get("equation") != [1, 22]:
        raise ValueError("selected affine consequence id changed")
    if factor.get("base") != "c9_11 + p*t" or factor.get("exponent") != 2:
        raise ValueError("selected factor shape changed")
    if factor.get("scalar") != "5":
        raise ValueError("selected factor scalar changed")
    if factor.get("substitution") != {"c9_11": "-p*t"}:
        raise ValueError("selected affine substitution changed")
    if consequence.get("post_substitution") != "5*p*t**2":
        raise ValueError("selected affine residual changed")
    if consequence.get("unit") is not True:
        raise ValueError("native receipt no longer grades the residual a unit")
    axis = factor.get("slice") or {}
    zeroed = axis.get("zeroed")
    if axis.get("axis") != "c9_11" or not isinstance(zeroed, list):
        raise ValueError("selected axis slice changed")
    if len(zeroed) != 70 or "c9_11" in zeroed:
        raise ValueError("selected axis zero-list changed")

    return {
        "schema": FROZEN_SCHEMA,
        "native_parent": {
            "schema": native["schema"],
            "sha256": source_sha,
            "model_digest": native["model_digest"],
            "equation_order_digest": native["equation_order_digest"],
            "variable_order_digest": native["variable_order_digest"],
        },
        "scope": native["scope"],
        "chart": "p",
        "coefficient_domain": "Q",
        "point_universe": S.ALGEBRAIC_CLOSURE_POINT_UNIVERSE,
        "pin": "15*t^3+1",
        "fixed_scalars": list(native["fixed_scalars"]),
        "ring_vars": ["p", "t", "c9_11", "I4"],
        "guards": ["p", "t"],
        "axis": {
            "kept": ["p", "t", "c9_11", "I4"],
            "zeroed": list(zeroed),
        },
        "factor": {
            "id": FACTOR_ID,
            "equation_id": "E[3,22]",
            "equation": factor["equation_polynomial"],
            "scalar": factor["scalar"],
            "base": factor["base"],
            "exponent": factor["exponent"],
            "substitution": dict(factor["substitution"]),
        },
        "consequence": {
            "equation_id": "E[1,22]",
            "equation": consequence["equation_polynomial"],
            "post_substitution": consequence["post_substitution"],
        },
        "authority_boundary": (
            "exact c9_11 p-axis stratum only; no full p-chart, "
            "actual-source-membership, infinite-lift, or H3 authority"
        ),
    }


def authority_spec(frozen):
    if frozen.get("schema") != FROZEN_SCHEMA:
        raise ValueError("unexpected frozen p-axis schema")
    return {
        "schema": L.SCHEMA,
        "characteristic": 0,
        "ring_vars": list(frozen["ring_vars"]),
        "generators": [
            frozen["pin"],
            frozen["consequence"]["equation"],
            frozen["factor"]["equation"],
        ],
        "guards": list(frozen["guards"]),
        "expression": {
            "numerator": "1",
            "denominator_powers": [0, 0],
        },
        "certificate": {
            "localization_powers": [2, 4],
            "membership_target": "p^2*t^4",
            "cofactors": [
                "0",
                "-2/5*t*c9_11-1/5*p*t^2",
                "4/5*t^2",
            ],
        },
    }


def evidence_envelope(frozen, frozen_bytes, report):
    context = EV.AffineContext(
        characteristic=0,
        coefficient_domain=frozen["coefficient_domain"],
        point_universe=frozen["point_universe"],
        ring_vars=tuple(frozen["ring_vars"]),
        unit_generators=tuple(frozen["guards"]),
        generators=tuple(authority_spec(frozen)["generators"]),
    )
    return EV.EvidenceEnvelope(
        schema=L.SCHEMA,
        context=context,
        source_bindings=(
            EV.SourceBinding(
                "frozen-jc-p-axis", _sha256(frozen_bytes)),
            EV.SourceBinding(
                "native-jc-p-window",
                frozen["native_parent"]["sha256"]),
        ),
        checked_proposition=(
            "p^2*t^4 belongs to the exact pinned p-axis ideal"
        ),
        certificate_payload={
            "membership_target": report["checked"]["target"],
            "generator_count": report["checked"]["generator_count"],
        },
        licenses=tuple(report["licenses"]),
        outstanding_premises=(
            "bind this exact context to the graph claim and model",
            "obtain a current localized-unit verifier verdict",
        ),
        graph_effect=EV.GRAPH_EFFECT_NONE,
        authority_boundary=frozen["authority_boundary"],
    ).as_dict()


def source_binding(frozen, frozen_bytes):
    return (
        "frozen JC p-axis receipt %s; native parent %s; model digest "
        "sha256:%s"
        % (_sha256(frozen_bytes), frozen["native_parent"]["sha256"],
           frozen["native_parent"]["model_digest"])
    )


def graph_events(frozen, frozen_bytes):
    spec = authority_spec(frozen)
    binding = source_binding(frozen, frozen_bytes)
    common = {
        "characteristic": 0,
        "coefficient_domain": "Q",
        "point_universe": S.ALGEBRAIC_CLOSURE_POINT_UNIVERSE,
        "ring_vars": list(spec["ring_vars"]),
        "open_conditions": list(spec["guards"]),
        "chart": "p",
        "cite": frozen["native_parent"]["sha256"],
    }
    parent = {
        "ev": "model", "id": PARENT_MODEL,
        "what": (
            "same pinned localized axis coordinate ring before the two "
            "selected window equations; " + binding),
        "generators": [frozen["pin"]],
    }
    parent.update(common)
    axis = {
        "ev": "model", "id": AXIS_MODEL,
        "what": "exact JC c9_11 p-axis stratum; " + binding,
        "generators": list(spec["generators"]),
    }
    axis.update(common)
    return [
        parent,
        axis,
        {
            "ev": "edge", "id": PARENT_EDGE,
            "src": AXIS_MODEL, "dst": PARENT_MODEL,
            "type": K.NECESSARY_CONDITION,
            "map_kind": K.IDENTITY_MAP,
            "why": (
                "forgetting E[1,22] and E[3,22] widens the exact axis "
                "system; one empty restricted stratum cannot empty its parent"
            ),
            "drops": ["E[1,22]", "E[3,22]"],
        },
        {
            "ev": "claim", "id": EMPTY_CLAIM, "model": AXIS_MODEL,
            "kind": K.EMPTY,
            "statement": (
                "the exact localized JC c9_11 p-axis stratum has no points"
            ),
            "certificate": "LOCALIZED_UNIT_IDEAL_CERT",
            "established_by": "RAN",
            "ladder": "exact-checked",
            "cite": frozen["native_parent"]["sha256"],
            "caveat": frozen["authority_boundary"],
        },
    ]


def parent_refusal(graph):
    """Exercise the illicit widening in memory without dirtying the campaign."""
    graph.apply({
        "ev": "inference", "id": "JC-P-C9-ILLICIT-PARENT-EMPTY",
        "claim": EMPTY_CLAIM,
        "path": [[PARENT_EDGE, K.ALONG]],
        "concludes_kind": K.EMPTY,
        "asserted": (
            "control only: local axis emptiness would empty its ambient"
        ),
    })
    graph.validate()
    return C.audit_inference(graph, "JC-P-C9-ILLICIT-PARENT-EMPTY")


def graph_from_frozen(frozen, frozen_bytes):
    graph = S.Graph()
    graph.apply(F.meta_event())
    for event in graph_events(frozen, frozen_bytes):
        graph.apply(event)
    graph.validate()
    return graph


def write_campaign(root, frozen, frozen_bytes, record):
    graph_path = Path(S.graph_path(str(root)))
    if graph_path.exists():
        raise ValueError("campaign graph already exists: %s" % graph_path)
    S.append(graph_events(frozen, frozen_bytes), root=str(root))
    results = []
    if record:
        results = V.verify_all(root=str(root))
    graph = S.load(S.graph_path(str(root)))
    local = graph.claims[EMPTY_CLAIM]
    licensed, trace = parent_refusal(graph)
    if licensed:
        raise AssertionError("local p-axis EMPTY escaped to its parent")
    if record and local.get("certificate_verdict") != V.CERT_VERIFIED:
        raise AssertionError("recorded campaign did not mint local EMPTY")
    return {
        "graph": str(graph_path),
        "local_verdict": local.get("certificate_verdict"),
        "parent_empty_licensed": licensed,
        "parent_refusal": trace[0][3],
        "verify_results": [list(item[:3]) for item in results],
    }


def main(argv=None):
    parser = argparse.ArgumentParser()
    parser.add_argument("--source", type=Path, default=DEFAULT_SOURCE)
    parser.add_argument("--frozen", type=Path, default=DEFAULT_FROZEN)
    parser.add_argument("--authority", type=Path, default=DEFAULT_AUTHORITY)
    parser.add_argument("--write-fixtures", action="store_true")
    parser.add_argument("--campaign-root", type=Path)
    parser.add_argument(
        "--record", action="store_true",
        help="run production Singular and persist the local EMPTY verdict")
    args = parser.parse_args(argv)
    if args.record and args.campaign_root is None:
        parser.error("--record requires --campaign-root")

    source_bytes = args.source.read_bytes()
    native = json.loads(source_bytes.decode("utf-8"))
    frozen = freeze_native(native, source_bytes)
    frozen_encoded = _encoded(frozen)
    spec = authority_spec(frozen)
    authority_encoded = _encoded(spec)
    report = L.verify(spec)

    if args.write_fixtures:
        args.frozen.parent.mkdir(parents=True, exist_ok=True)
        args.frozen.write_bytes(frozen_encoded)
        args.authority.write_bytes(authority_encoded)
    else:
        if args.frozen.read_bytes() != frozen_encoded:
            raise SystemExit(
                "frozen axis receipt differs from native adapter output")
        if args.authority.read_bytes() != authority_encoded:
            raise SystemExit(
                "localized authority fixture differs from adapter output")

    output = {
        "verdict": report["verdict"],
        "checked_target": report["checked"]["target"],
        "frozen_receipt_sha256": _sha256(frozen_encoded),
        "native_parent_sha256": frozen["native_parent"]["sha256"],
        "authority_boundary": frozen["authority_boundary"],
        "evidence_envelope": evidence_envelope(
            frozen, frozen_encoded, report),
    }
    if args.campaign_root is not None:
        output["campaign"] = write_campaign(
            args.campaign_root, frozen, frozen_encoded, args.record)
    print(json.dumps(output, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
