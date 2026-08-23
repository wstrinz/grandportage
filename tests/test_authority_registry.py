"""Drift gate for the unified authority and classification registry."""

import argparse
from pathlib import Path

import pytest

from grandportage import authority_registry as registry
from grandportage import cli
from grandportage import evidence
from grandportage import kernel


def _commands():
    parser = cli.build_parser()
    action = next(action for action in parser._actions
                  if isinstance(action, argparse._SubParsersAction))
    return set(action.choices)


def test_registry_transport_rows_match_every_kernel_cell():
    rows = registry.transport_rows()
    expected = len(kernel.DECLARABLE_TYPES) * len(kernel.DIRECTIONS) * \
        len(kernel.CLAIM_KINDS)
    assert len(rows) == expected
    keys = set()
    for row in rows:
        key = (row["edge_type"], row["direction"], row["claim_kind"])
        assert key not in keys
        keys.add(key)
        assert row["rule"] == kernel.TRANSPORT[key[0]][key[1]][key[2]]


def test_every_verify_command_has_a_complete_declaration():
    commands = {declaration.command
                for declaration in registry.VERIFIER_DECLARATIONS}
    assert {name for name in _commands() if name == "verify" or
            name.startswith("verify-")} == commands
    for declaration in registry.VERIFIER_DECLARATIONS:
        assert declaration.graph_effect
        assert declaration.authority_ceiling
        assert declaration.classification in registry.CLASSIFICATIONS
        assert declaration.why


def test_every_evidence_schema_is_classified_once():
    schemas = {contract.schema for contract in evidence.EVIDENCE_CONTRACTS}
    assert schemas == set(registry.EVIDENCE_CLASSIFICATIONS)
    assert all(value[0] in registry.CLASSIFICATIONS
               for value in registry.EVIDENCE_CLASSIFICATIONS.values())


def test_graph_authority_contracts_are_named_by_verifier_registry():
    declared = {item.verifier for item in registry.VERIFIER_DECLARATIONS}
    assert {item.verifier for item in evidence.AUTHORITY_CONTRACTS} <= declared


def test_classification_has_zero_unclassified_rows():
    rows = registry.classification_rows()
    assert rows
    assert all(row["classification"] in registry.CLASSIFICATIONS for row in rows)
    assert not [row for row in rows if "UNCLASSIFIED" in row.values()]


def test_every_builtin_certificate_names_a_lean_stability_decision():
    rows = registry.CERTIFICATE_STABILITY
    assert set(rows) == set(kernel.BUILTIN_CERTIFICATES)

    lean = (Path(__file__).parents[1] / "lean" / "GrandPortage" /
            "CertificateScope.lean").read_text(encoding="utf-8")
    for certificate, row in rows.items():
        assert "def %s " % row["lean_decision"] in lean, certificate


def test_runtime_certificate_scopes_match_the_named_lean_derivations():
    for certificate, base_changes in kernel.BUILTIN_CERTIFICATES.items():
        row = registry.CERTIFICATE_STABILITY[certificate]
        if row["lean_derived_scope"] == "SCHEME":
            assert base_changes is True
            assert kernel.derive_scope(
                kernel.EMPTY, certificate, None) == kernel.SCHEME
        else:
            assert row["lean_derived_scope"] == "FIELD_RELATIVE"
            assert base_changes is False
            assert kernel.derive_scope(
                kernel.EMPTY, certificate, "Q") == "Q"
            with pytest.raises(kernel.ScopeError):
                kernel.derive_scope(
                    kernel.EMPTY, certificate, kernel.SCHEME)


def test_table_and_evidence_commands_share_the_registry(capsys):
    assert cli.main(["table"]) == 0
    table = capsys.readouterr().out
    assert registry.transport_rows()[0]["edge_type"] in table
    assert cli.main(["evidence"]) == 0
    evidence_text = capsys.readouterr().out
    assert "COMPLETE VERIFIER DECLARATIONS" in evidence_text
    assert "CLASSIFICATION" in evidence_text
