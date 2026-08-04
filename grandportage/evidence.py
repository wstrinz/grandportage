"""Shared evidence context and authority metadata.

This module is descriptive infrastructure, not a theorem-plugin system. Existing
versioned evidence schemas remain authoritative for their own payloads. The
records here provide one canonical context projection, a read-only envelope,
and a manifest from which user-facing authority descriptions can be generated.
"""

from dataclasses import dataclass, field
import hashlib
import json
from typing import Any, Dict, Optional, Tuple


GRAPH_EFFECT_NONE = "NONE"
GRAPH_EFFECT_LOCAL_EMPTY = "LOCAL_EMPTY"
GRAPH_EFFECT_IDENTITY_TRANSPORT = "IDENTITY_TRANSPORT"
EXCEPTIONAL_FACTOR_COLUMN_SCHEMA = "exceptional_factor_column_v1"
AFFINE_FIBER_BLOCK_SCHEMA = "affine_fiber_block_v1"
GRAPH_EFFECT_POINT_INCLUSION = "POINT_INCLUSION"


def fingerprint(value):
    """Canonical SHA-256 for shared evidence metadata."""
    encoded = json.dumps(
        value, sort_keys=True, separators=(",", ":"), ensure_ascii=True
    ).encode("utf-8")
    return "sha256:" + hashlib.sha256(encoded).hexdigest()


@dataclass(frozen=True)
class SourceBinding:
    """One immutable producer or native-receipt binding."""

    identifier: str
    sha256: str

    def as_dict(self):
        return {"id": self.identifier, "sha256": self.sha256}


@dataclass(frozen=True)
class AffineContext:
    """Canonical projection of the context repeated across affine evidence."""

    characteristic: int
    coefficient_domain: Optional[str]
    point_universe: Optional[str]
    ring_vars: Tuple[str, ...]
    unit_generators: Tuple[str, ...] = ()
    generators: Tuple[Any, ...] = ()

    def as_dict(self):
        value = {
            "characteristic": self.characteristic,
            "coefficient_domain": self.coefficient_domain,
            "point_universe": self.point_universe,
            "ring_vars": list(self.ring_vars),
            "unit_generators": list(self.unit_generators),
            "generators": list(self.generators),
        }
        return value

    def fingerprint(self):
        return fingerprint(self.as_dict())


@dataclass(frozen=True)
class EvidenceEnvelope:
    """Read-only common view over one specialized evidence report."""

    schema: str
    context: AffineContext
    source_bindings: Tuple[SourceBinding, ...]
    checked_proposition: str
    licenses: Tuple[str, ...]
    outstanding_premises: Tuple[str, ...]
    graph_effect: str
    authority_boundary: str
    certificate_payload: Dict[str, Any] = field(default_factory=dict)

    def as_dict(self):
        return {
            "schema": self.schema,
            "context": self.context.as_dict(),
            "source_bindings": [
                binding.as_dict() for binding in self.source_bindings
            ],
            "checked_proposition": self.checked_proposition,
            "certificate_payload": dict(self.certificate_payload),
            "licenses": list(self.licenses),
            "outstanding_premises": list(self.outstanding_premises),
            "graph_effect": self.graph_effect,
            "authority_boundary": self.authority_boundary,
        }


@dataclass(frozen=True)
class EvidenceContract:
    schema: str
    description: str
    maturity: str
    standalone_graph_effect: str
    compilation_target: str

    def as_dict(self):
        return {
            "schema": self.schema,
            "description": self.description,
            "maturity": self.maturity,
            "standalone_graph_effect": self.standalone_graph_effect,
            "compilation_target": self.compilation_target,
        }


@dataclass(frozen=True)
class AuthorityContract:
    verifier: str
    representation: str
    binds: Tuple[str, ...]
    graph_effect: str
    containment: str

    def as_dict(self):
        return {
            "verifier": self.verifier,
            "representation": self.representation,
            "binds": list(self.binds),
            "graph_effect": self.graph_effect,
            "containment": self.containment,
        }


EVIDENCE_CONTRACTS = (
    EvidenceContract(
        AFFINE_FIBER_BLOCK_SCHEMA,
        "exact affine coefficient blocks with determined coordinates and residual compatibility",
        "experimental",
        GRAPH_EFFECT_NONE,
        "a graph-bound necessary-condition model after residual materialization",
    ),
    EvidenceContract(
        EXCEPTIONAL_FACTOR_COLUMN_SCHEMA,
        "finite exact coefficient columns and exceptional-factor decompositions",
        "experimental",
        GRAPH_EFFECT_NONE,
        "operation-specific restriction or affine-coordinate binding remains required",
    ),
    EvidenceContract(
        "coefficient_expansion_v1",
        "bounded exact coefficient images",
        "stable",
        GRAPH_EFFECT_NONE,
        "operation-specific graph binding remains required",
    ),
    EvidenceContract(
        "factor_power_v1",
        "unit-times-positive-power polynomial identities",
        "experimental",
        GRAPH_EFFECT_NONE,
        "semantic domain and unit premises, or a smaller exact certificate",
    ),
    EvidenceContract(
        "factor_power_affine_contradiction_v1",
        "factor contraction plus an affine declared-unit residual",
        "experimental",
        GRAPH_EFFECT_NONE,
        "localization_membership_v1 when an exact cofactor can be emitted",
    ),
    EvidenceContract(
        "graded_face_extraction_v1",
        "bounded weighted coefficient faces from a finite algebraic template",
        "experimental",
        GRAPH_EFFECT_NONE,
        "NECESSARY_CONDITION after complete source-model materialization",
    ),
    EvidenceContract(
        "laurent_lowering_v1",
        "finite Laurent straight-line equalities and support-cleared exports",
        "experimental",
        GRAPH_EFFECT_NONE,
        "coefficient_expansion_v1 after an exact export binding",
    ),
    EvidenceContract(
        "laurent_coefficient_pipeline_v1",
        "bound Laurent lowering and coefficient-image replay",
        "experimental",
        GRAPH_EFFECT_NONE,
        "operation-specific graph binding remains required",
    ),
    EvidenceContract(
        "localization_membership_v1",
        "exact cofactor membership in a declared principal-open localization",
        "stable",
        GRAPH_EFFECT_NONE,
        "LOCALIZED_UNIT_IDEAL_CERT on an exact graph-bound model",
    ),
    EvidenceContract(
        "product_split_v1",
        "exact product factorizations with declared-unit scalars",
        "experimental",
        GRAPH_EFFECT_NONE,
        "ProductSplit constructor plus independently verified partition",
    ),
    EvidenceContract(
        "localized_triangular_solve_chain_v1",
        "ordered localized affine substitutions",
        "experimental",
        GRAPH_EFFECT_NONE,
        "mapped-equivalence authority after exact state and map binding",
    ),
    EvidenceContract(
        "localized_triangular_solve_chain_v2",
        "ordered substitutions modulo explicit normalization generators",
        "experimental",
        GRAPH_EFFECT_NONE,
        "mapped-equivalence authority after exact state and map binding",
    ),
)


AUTHORITY_CONTRACTS = (
    AuthorityContract(
        "verify.containment",
        "ideal_containment_v3 (exact generator inclusion or backend reduction)",
        (
            "edge", "endpoint models", "coefficient domains",
            "point universes", "ring orders", "generator ideals",
            "verifier epoch",
        ),
        GRAPH_EFFECT_POINT_INCLUSION,
        "the exact directed endpoint relation only; failed ideal membership "
        "does not refute point containment, and no reverse, source-extraction, "
        "parent, or coverage authority is implied",
    ),
    AuthorityContract(
        "verify.localized_unit_ideal",
        "localized_unit_ideal_v1",
        (
            "claim", "model", "coefficient domain", "point universe",
            "ring order", "generators", "guards", "proof", "verifier epoch",
        ),
        GRAPH_EFFECT_LOCAL_EMPTY,
        "the exact localized model only; no parent or cover authority",
    ),
    AuthorityContract(
        "verify.ring_iso",
        "mapped_ring_iso_v1 or solver-checked polynomial maps",
        (
            "edge", "endpoint models", "coefficient domains",
            "point universes", "ring orders", "generator ideals",
            "forward map", "inverse map", "optional cofactor proof",
            "verifier epoch",
        ),
        GRAPH_EFFECT_IDENTITY_TRANSPORT,
        "the exact endpoint quotient rings only; no unencoded localization, "
        "source-extraction, parent, or coverage authority",
    ),
)


def evidence_contract(schema):
    for contract in EVIDENCE_CONTRACTS:
        if contract.schema == schema:
            return contract
    return None


def manifest():
    """Stable machine-readable authority manifest."""
    return {
        "evidence_contracts": [
            contract.as_dict() for contract in EVIDENCE_CONTRACTS
        ],
        "authority_contracts": [
            contract.as_dict() for contract in AUTHORITY_CONTRACTS
        ],
    }
