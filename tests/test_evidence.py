"""Shared evidence envelope and authority-manifest checks."""

import json
from pathlib import Path

from grandportage import cli
from grandportage import coefficient_expansion as CE
from grandportage import evidence as EV
from grandportage import factor_power as FP
from grandportage import factor_power_contradiction as FPC
from grandportage import laurent_coefficient_pipeline as LCP
from grandportage import laurent_lowering as LL
from grandportage import localization as LOC
from grandportage import product_split as PS
from grandportage import triangular as TRI


ROOT = Path(__file__).parents[1]


def test_affine_context_is_canonical_and_fingerprintable():
    context = EV.AffineContext(
        characteristic=0,
        coefficient_domain="Q",
        point_universe="ALGEBRAIC_CLOSURE",
        ring_vars=("p", "t", "c"),
        unit_generators=("p", "t"),
        generators=("15*t^3+1", "c+p*t"),
    )

    assert context.as_dict() == {
        "characteristic": 0,
        "coefficient_domain": "Q",
        "point_universe": "ALGEBRAIC_CLOSURE",
        "ring_vars": ["p", "t", "c"],
        "unit_generators": ["p", "t"],
        "generators": ["15*t^3+1", "c+p*t"],
    }
    assert context.fingerprint() == EV.fingerprint(context.as_dict())


def test_triangular_state_fingerprint_uses_the_shared_context_projection():
    payload = {
        "characteristic": 0,
        "coefficient_domain": "Q",
        "point_universe": "ALGEBRAIC_CLOSURE",
        "ring_vars": ["t", "x"],
        "unit_generators": ["t"],
        "generators": ["t+x"],
    }

    assert TRI.state_fingerprint(
        0, "Q", "ALGEBRAIC_CLOSURE",
        ["t", "x"], ["t"], ["x+t"],
    ) == EV.fingerprint(payload)


def test_evidence_envelope_keeps_proposition_evidence_and_authority_separate():
    envelope = EV.EvidenceEnvelope(
        schema=LOC.SCHEMA,
        context=EV.AffineContext(
            0, "Q", "ALGEBRAIC_CLOSURE", ("p", "t"), ("p", "t"),
            ("p*t",)),
        source_bindings=(
            EV.SourceBinding("native", "sha256:" + "1" * 64),
        ),
        checked_proposition="p*t belongs to the ideal",
        certificate_payload={"target": "p*t"},
        licenses=("identity_in_declared_localization_only",),
        outstanding_premises=("bind the exact graph model",),
        graph_effect=EV.GRAPH_EFFECT_NONE,
        authority_boundary="standalone only",
    ).as_dict()

    assert envelope["checked_proposition"] == "p*t belongs to the ideal"
    assert envelope["licenses"] == [
        "identity_in_declared_localization_only"]
    assert envelope["graph_effect"] == "NONE"
    assert envelope["outstanding_premises"] == [
        "bind the exact graph model"]


def test_manifest_covers_every_stable_or_experimental_affine_schema():
    expected = {
        EV.AFFINE_FIBER_BLOCK_SCHEMA,
        EV.EXCEPTIONAL_FACTOR_COLUMN_SCHEMA,
        CE.SCHEMA,
        FP.SCHEMA,
        FPC.SCHEMA,
        "graded_face_extraction_v1",
        LCP.SCHEMA,
        LL.SCHEMA,
        LOC.SCHEMA,
        PS.SCHEMA,
        TRI.SCHEMA,
        TRI.SCHEMA_V2,
    }
    actual = {contract.schema for contract in EV.EVIDENCE_CONTRACTS}

    assert actual == expected
    assert len(actual) == len(EV.EVIDENCE_CONTRACTS)
    assert all(contract.standalone_graph_effect == EV.GRAPH_EFFECT_NONE
               for contract in EV.EVIDENCE_CONTRACTS)


def test_manifest_names_current_graph_authority_effects():
    assert len(EV.AUTHORITY_CONTRACTS) == 3
    contracts = {
        contract.verifier: contract for contract in EV.AUTHORITY_CONTRACTS
    }

    containment = contracts["verify.containment"]
    assert containment.representation.startswith("ideal_containment_v3")
    assert containment.graph_effect == EV.GRAPH_EFFECT_POINT_INCLUSION
    assert "failed ideal membership does not refute" in containment.containment
    assert "no reverse" in containment.containment

    localized = contracts["verify.localized_unit_ideal"]
    assert localized.representation == "localized_unit_ideal_v1"
    assert localized.graph_effect == EV.GRAPH_EFFECT_LOCAL_EMPTY
    assert "no parent" in localized.containment

    ring_iso = contracts["verify.ring_iso"]
    assert ring_iso.representation.startswith("mapped_ring_iso_v1")
    assert ring_iso.graph_effect == EV.GRAPH_EFFECT_IDENTITY_TRANSPORT
    assert "optional cofactor proof" in ring_iso.binds
    assert "exact endpoint quotient rings" in ring_iso.containment
    assert "no unencoded localization" in ring_iso.containment


def test_factor_affine_contract_compiles_to_existing_localization_schema():
    contract = EV.evidence_contract(FPC.SCHEMA)

    assert LOC.SCHEMA in contract.compilation_target
    assert contract.standalone_graph_effect == EV.GRAPH_EFFECT_NONE


def test_cli_evidence_text_and_json_share_the_manifest(capsys):
    assert cli.main(["evidence"]) == 0
    text = capsys.readouterr().out
    assert FPC.SCHEMA in text
    assert "effect=NONE" in text
    assert "verify.localized_unit_ideal" in text
    assert "effect=LOCAL_EMPTY" in text

    assert cli.main(["evidence", "--json"]) == 0
    payload = json.loads(capsys.readouterr().out)
    assert payload == EV.manifest()


def test_two_consumer_promotion_rule_is_documented():
    architecture = (ROOT / "ARCHITECTURE.md").read_text(encoding="utf-8")

    assert "two genuinely independent consumers" in architecture
    assert "end-to-end" in architecture
    assert "kernel-epoch review" in architecture
