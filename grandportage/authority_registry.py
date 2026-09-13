"""Printable declarations for transport, verifier authority, and custody.

The registry is descriptive and kernel-adjacent.  It does not implement a
verifier and does not grant authority.  Drift tests compare these declarations
with the kernel table, CLI surface, and evidence schemas that actually run.
"""

from dataclasses import asdict, dataclass

from . import evidence
from . import kernel


CORE = "CORE"
GENERAL_CONTRIB = "GENERAL-CONTRIB"
CAMPAIGN = "CAMPAIGN"
CLASSIFICATIONS = (CORE, GENERAL_CONTRIB, CAMPAIGN)


# The Lean shadow deliberately does not import this table. These names make
# the comparison explicit and mechanically total without making Lean runtime
# authority. These decisions model the HISTORICAL Boolean scope interface,
# not epoch-12 effective reach. In particular orderedSosDecision only refutes
# arbitrary extension stability; it does not classify ORDERED as one field.
# Atlas.lean and scripts/check_atlas_parity.py cover current instantiation.
# ``lean_derived_scope`` is the historical result; FIELD_RELATIVE means the
# exact declared field atom within that older two-level vocabulary.
CERTIFICATE_STABILITY = {
    "UNIT_IDEAL_CERT": {
        "lean_decision": "unitIdealDecision",
        "lean_derived_scope": "SCHEME",
    },
    "LOCALIZED_UNIT_IDEAL_CERT": {
        "lean_decision": "localizedUnitIdealDecision",
        "lean_derived_scope": "SCHEME",
    },
    "NONZERO_RESULTANT": {
        "lean_decision": "nonzeroResultantDecision",
        "lean_derived_scope": "SCHEME",
    },
    "EXACT_VALUATION_COLLISION": {
        "lean_decision": "exactValuationCollisionDecision",
        "lean_derived_scope": "SCHEME",
    },
    "DEGREE_COUNT": {
        "lean_decision": "degreeCountDecision",
        "lean_derived_scope": "SCHEME",
    },
    "NONSQUARE_CLASS": {
        "lean_decision": "nonsquareClassDecision",
        "lean_derived_scope": "FIELD_RELATIVE",
    },
    "NO_RATIONAL_POINT_SEARCH": {
        "lean_decision": "noRationalPointSearchDecision",
        "lean_derived_scope": "FIELD_RELATIVE",
    },
    "ORDERED_SOS_CERT": {
        "lean_decision": "orderedSosDecision",
        "lean_derived_scope": "FIELD_RELATIVE",
    },
    "CITED_PROOF": {
        "lean_decision": "citedProofDecision",
        "lean_derived_scope": "FIELD_RELATIVE",
    },
}


@dataclass(frozen=True)
class VerifierDeclaration:
    verifier: str
    command: str
    graph_effect: str
    authority_ceiling: str
    consumes: tuple
    mints: tuple
    classification: str
    why: str

    def as_dict(self):
        value = asdict(self)
        value["consumes"] = list(self.consumes)
        value["mints"] = list(self.mints)
        return value


def _v(verifier, command, effect, ceiling, consumes=(), mints=(),
       classification=CORE, why="domain-general graph verification"):
    return VerifierDeclaration(
        verifier, command, effect, ceiling, tuple(consumes), tuple(mints),
        classification, why)


VERIFIER_DECLARATIONS = (
    _v("verify.containment", "verify", "POINT_INCLUSION",
       "the declared directed endpoint relation", ("endpoint ideals",),
       ("ideal_containment_v3",)),
    _v("verify.identity", "verify", "LOCAL_IDENTITY",
       "the exact claim at its declared model", ("identity claim",),
       ("ideal_membership",)),
    _v("verify.unit_ideal", "verify", "LOCAL_EMPTY",
       "the exact affine model only", ("UNIT_IDEAL_CERT",),
       ("unit_ideal_v1",)),
    _v("verify.localized_unit_ideal", "verify", "LOCAL_EMPTY",
       "the exact localized model only", ("localized_guard_reduction_chain_v2",),
       ("LOCALIZED_UNIT_IDEAL_CERT",)),
    _v("verify.ordered_sos", "verify", "ORDERED_EMPTY",
       "all ordered fields through exact rational identity replay",
       ("rational_sos_cofactor_v1",), ("ORDERED",)),
    _v("verify.ring_iso", "verify", "IDENTITY_TRANSPORT",
       "the exact endpoint quotient rings", ("mapped polynomial maps",),
       ("mapped_ring_iso_v1",)),
    _v("verify.point_witness", "verify", "LOCAL_NONEMPTY",
       "the exact model only", ("witness_point",), ("point_witness_v1",)),
    _v("verify.predicate_condition", "verify", "LOCAL_PREDICATE",
       "the exact structured predicate at its model", ("ZERO/NONZERO atoms",),
       ("predicate_condition_v1",)),
    _v("verify.partition_exhaustiveness", "verify", "PARTITION_COVER",
       "the declared parent and complete branch family", ("partition",),
       ("partition_exhaustiveness_v2",)),
    _v("verify.operation_output", "verify", "POINT_INCLUSION",
       "the exact constructor output edge", ("operation contract",),
       ("operation_output_v2",)),
    _v("verify.elimination_section", "verify-elimination",
       "EXACT_CONTRACTION", "the declared elimination edge",
       ("polynomial section",), ("elimination_section_v1",)),
    _v("verify.elimination_point_lift", "verify-elimination-point-lift",
       "POINT_SURJECTIVITY", "the declared elimination edge",
       ("finite chart lift cover",), ("elimination_point_lift_v1",)),
    _v("verify.elimination_groebner", "verify-elimination-groebner",
       "EXACT_CONTRACTION", "the declared elimination edge",
       ("Groebner elimination certificate",),
       ("groebner_elimination_v1",)),
    _v("evidence.coefficient_expansion", "verify-coefficient-expansion",
       "NONE", "standalone translation validation",
       ("coefficient_expansion_v1",), (), GENERAL_CONTRIB,
       "domain-general operation motivated by JC coefficient lifting"),
    _v("evidence.laurent_lowering", "verify-laurent-lowering", "NONE",
       "standalone translation validation", ("laurent_lowering_v1",), (),
       GENERAL_CONTRIB, "general Laurent arithmetic first demanded by JC"),
    _v("evidence.laurent_pipeline", "verify-laurent-coefficient-pipeline",
       "NONE", "standalone translation validation",
       ("laurent_coefficient_pipeline_v1",), (), GENERAL_CONTRIB,
       "general compiler composition first demanded by JC"),
    _v("evidence.factor_power", "verify-factor-power", "NONE",
       "standalone exact identity", ("factor_power_v1",), (),
       GENERAL_CONTRIB, "general factor identity first demanded by JC"),
    _v("evidence.factor_power_contradiction",
       "verify-factor-power-contradiction", "NONE",
       "standalone exact contradiction",
       ("factor_power_affine_contradiction_v1",), (), GENERAL_CONTRIB,
       "general certificate composition first demanded by JC"),
    _v("evidence.product_split", "verify-product-split", "NONE",
       "standalone factorization", ("product_split_v1",), (),
       GENERAL_CONTRIB, "general partition premise first demanded by JC"),
    _v("evidence.localization_membership", "verify-localization-membership",
       "NONE", "identity in the declared localization only",
       ("localization_membership_v1",), (), CORE,
       "domain-general exact checker primitive"),
    _v("evidence.localized_triangular_chain",
       "verify-localized-triangular-chain", "NONE",
       "standalone ordered substitution validation",
       ("localized_triangular_solve_chain_v1",
        "localized_triangular_solve_chain_v2"), (), GENERAL_CONTRIB,
       "general solve-chain contract first demanded by JC"),
)


EVIDENCE_CLASSIFICATIONS = {
    "affine_fiber_block_v1": (GENERAL_CONTRIB,
        "general affine-fiber contract extracted from a JC assay"),
    "exceptional_factor_column_v1": (GENERAL_CONTRIB,
        "general exact column format extracted from a JC assay"),
    "coefficient_expansion_v1": (GENERAL_CONTRIB,
        "general bounded-coefficient lowering first demanded by JC"),
    "factor_power_v1": (GENERAL_CONTRIB,
        "general factor identity first demanded by JC"),
    "factor_power_affine_contradiction_v1": (GENERAL_CONTRIB,
        "general certificate composition first demanded by JC"),
    "graded_face_extraction_v1": (GENERAL_CONTRIB,
        "general one-way extraction contract first demanded by JC"),
    "laurent_lowering_v1": (GENERAL_CONTRIB,
        "general Laurent compiler pass first demanded by JC"),
    "laurent_coefficient_pipeline_v1": (GENERAL_CONTRIB,
        "general compiler composition first demanded by JC"),
    "localization_membership_v1": (CORE,
        "domain-general exact localization membership primitive"),
    "product_split_v1": (GENERAL_CONTRIB,
        "general partition premise first demanded by JC"),
    "localized_triangular_solve_chain_v1": (GENERAL_CONTRIB,
        "general ordered solve contract first demanded by JC"),
    "localized_triangular_solve_chain_v2": (GENERAL_CONTRIB,
        "general normalized solve contract first demanded by JC"),
}


def transport_rows():
    return [
        {"edge_type": edge_type, "direction": direction,
         "claim_kind": claim_kind,
         "rule": kernel.TRANSPORT[edge_type][direction][claim_kind]}
        for edge_type in kernel.DECLARABLE_TYPES
        for direction in kernel.DIRECTIONS
        for claim_kind in kernel.CLAIM_KINDS
    ]


def classification_rows():
    rows = [{
        "surface": declaration.verifier,
        "kind": "verifier",
        "classification": declaration.classification,
        "why": declaration.why,
    } for declaration in VERIFIER_DECLARATIONS]
    rows.extend({
        "surface": schema, "kind": "evidence_schema",
        "classification": classification, "why": why,
    } for schema, (classification, why) in
                sorted(EVIDENCE_CLASSIFICATIONS.items()))
    return rows


def manifest():
    return {
        "transport": {
            "rows": transport_rows(),
            "type_meanings": dict(kernel.TYPE_MEANS),
            "certificate_reach_policy": dict(
                kernel.BUILTIN_CERTIFICATE_REACH_POLICY),
            "legacy_certificate_base_change": dict(
                kernel.BUILTIN_CERTIFICATES),
            "certificate_stability": dict(CERTIFICATE_STABILITY),
            "certificate_stability_role": "LEGACY_BOOLEAN_SCOPE_SHADOW",
        },
        "evidence_contracts": [
            contract.as_dict() for contract in evidence.EVIDENCE_CONTRACTS
        ],
        "authority_contracts": [
            contract.as_dict() for contract in evidence.AUTHORITY_CONTRACTS
        ],
        "verifier_declarations": [
            declaration.as_dict() for declaration in VERIFIER_DECLARATIONS
        ],
        "classification": classification_rows(),
    }
