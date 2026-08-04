"""The v0.5 compatibility epoch is a trust boundary, not a file header."""

import hashlib
import json
import os

import pytest

from grandportage import check as C
from grandportage import cli
from grandportage import format as F
from grandportage import kernel as K
from grandportage import migration as MIG
from grandportage import operations as O
from grandportage import store as S


def _write(path, events):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(
        "".join(json.dumps(event, sort_keys=True) + "\n" for event in events),
        encoding="utf-8")
    return str(path)


def test_init_starts_with_epoch_metadata(tmp_path):
    assert cli.main(["--root", str(tmp_path), "init"]) == 0
    path = S.graph_path(str(tmp_path))
    events = list(S.load_events(path))
    assert events[0][0] == {
        "created_with": "grandportage/0.23.0",
        "ev": "meta",
        "graph_format": 4,
        "kernel_epoch": F.KERNEL_EPOCH,
    }
    graph = S.load(path)
    assert graph.graph_format == 4
    assert graph.kernel_epoch == F.KERNEL_EPOCH
    assert graph.compatibility_mode is False


@pytest.mark.parametrize("kind,field", [
    ("claim", "integral"),
    ("claim", "coefficients_in_base"),
    ("claim", "zariski_closed"),
    ("claim", "existential"),
    ("edge", "refinement"),
    ("edge", "ring_iso"),
])
def test_native_licensing_flags_are_json_booleans(kind, field):
    event = ({"ev": "edge", "id": "E", "src": "A", "dst": "B",
              "type": "NECESSARY_CONDITION", "why": "w",
              "map_kind": "POLYNOMIAL"}
             if kind == "edge" else
             {"ev": "claim", "id": "C", "model": "M",
              "kind": "PREDICATE", "statement": "s"})
    event[field] = "false"
    with pytest.raises(S.GraphError, match="must be true or false"):
        F.validate_native_event(event, "test:1", S.GraphError)


def test_native_format2_inference_retract_accepts_required_why():
    events = [
        F.meta_event(),
        {"ev": "model", "id": "M", "what": "one model"},
        {"ev": "claim", "id": "C", "model": "M",
         "kind": K.PREDICATE, "statement": "P holds"},
        {"ev": "inference", "id": "I", "claim": "C", "path": [],
         "concludes_kind": K.PREDICATE, "asserted": "therefore P"},
        {"ev": "inference", "id": "R-I", "supersedes": "I",
         "discharge_kind": K.RETRACT,
         "why": "the probe argument should license no conclusion"},
    ]

    graph = S.Graph().apply_all([
        (event, "native-format2", index + 1)
        for index, event in enumerate(events)
    ]).validate()

    assert graph.inferences["I"]["retracted_by"] == "R-I"
    assert "R-I" not in graph.inferences
    assert graph.retractions[("inference", "R-I")]["why"] == (
        "the probe argument should license no conclusion"
    )


def test_native_edges_require_map_kind_and_reject_unknown_or_deprecated_fields():
    edge = {"ev": "edge", "id": "E", "src": "A", "dst": "B",
            "type": "NECESSARY_CONDITION", "why": "w"}
    with pytest.raises(S.GraphError, match="map_kind"):
        F.validate_native_event(edge, "test:1", S.GraphError)
    edge["map_kind"] = "POLYNOMIAL"
    for field in ("typo", "witness", "zariski_dense"):
        bad = dict(edge, **{field: "legacy"})
        with pytest.raises(S.GraphError, match="unknown field"):
            F.validate_native_event(bad, "test:1", S.GraphError)


def test_native_ring_iso_certificate_must_be_an_object():
    edge = {
        "ev": "edge", "id": "E", "src": "A", "dst": "B",
        "type": K.EQUIVALENCE, "why": "mapped",
        "map_kind": K.POLYNOMIAL,
        "ring_iso_certificate": "not a proof object",
    }
    with pytest.raises(S.GraphError, match="must be an object"):
        F.validate_native_event(edge, "test:1", S.GraphError)

def test_native_verdict_requires_versioned_provenance():
    verdict = {"ev": "verdict", "id": "V", "subject": "claim", "of": "C",
               "verdict": "VERIFIED_AMBIENT", "why": "reduced"}
    with pytest.raises(S.GraphError, match="needs"):
        F.validate_native_event(verdict, "test:1", S.GraphError)


def test_epoch0_import_is_conservative_and_read_only(tmp_path):
    path = _write(tmp_path / "legacy.jsonl", [
        {"ev": "model", "id": "A", "desc": "a"},
        {"ev": "model", "id": "B", "desc": "b"},
        {"ev": "edge", "id": "E", "src": "A", "dst": "B",
         "type": "NECESSARY_CONDITION", "why": "drops",
         "ring_iso": "false", "refinement": "false", "witness": "counterpoint",
         "zariski_dense": True},
        {"ev": "claim", "id": "C", "model": "A", "kind": "PREDICATE",
         "statement": "p", "integral": "false",
         "coefficients_in_base": "false", "zariski_closed": "false",
         "existential": "false"},
    ])
    graph = S.load(path)
    assert graph.compatibility_mode is True
    assert graph.edges["E"]["map_kind"] == "RATIONAL"
    assert graph.edges["E"]["ring_iso"] is False
    assert graph.edges["E"]["refinement"] is False
    assert graph.edges["E"]["strictness_witness"] == "counterpoint"
    assert "witness" not in graph.edges["E"]
    assert "zariski_dense" not in graph.edges["E"]
    for field in ("integral", "coefficients_in_base", "zariski_closed",
                  "existential"):
        assert graph.claims["C"][field] is False

    root = tmp_path / "campaign"
    legacy = root / ".portage" / "graph.jsonl"
    _write(legacy, [{"ev": "model", "id": "M", "desc": "m"}])
    before = legacy.read_bytes()
    with pytest.raises(S.GraphError, match="REFUSING TO APPEND"):
        S.append([{"ev": "model", "id": "N", "desc": "n"}], str(root))
    assert legacy.read_bytes() == before


def test_direct_fold_cannot_upgrade_legacy_records_with_late_meta():
    graph = S.Graph()
    graph.apply({"ev": "model", "id": "M", "desc": "legacy",
                 "unknown_legacy_field": "would bypass the closed schema"})
    with pytest.raises(S.GraphError, match="only legal as the first"):
        graph.apply(F.meta_event())

    native = S.Graph()
    native.apply(F.meta_event())
    with pytest.raises(S.GraphError, match="only legal as the first"):
        native.apply(F.meta_event())

    batched = S.Graph()
    batched.apply({"ev": "model", "id": "L", "desc": "legacy",
                   "legacy_truthy": "false"})
    with pytest.raises(S.GraphError, match="already contains events"):
        batched.apply_all([(F.meta_event(), "late", 2)])


@pytest.mark.parametrize("field,value", [
    ("graph_format", True), ("graph_format", 1.0),
    ("graph_format", "1"), ("kernel_epoch", True),
    ("kernel_epoch", 1.0), ("kernel_epoch", "1"),
])
def test_meta_versions_are_strict_integers(field, value):
    event = F.meta_event()
    event[field] = value
    with pytest.raises(S.GraphError, match="must be an integer"):
        F.validate_meta(event, "test:1", S.GraphError)


@pytest.mark.parametrize("value", [None, True, -1, 1, 4, 9, 25])
def test_field_characteristic_rejects_nonfields(value):
    graph = S.Graph()
    graph.apply(F.meta_event())
    with pytest.raises(S.GraphError, match="0 or a prime"):
        graph.apply({"ev": "model", "id": "M", "desc": "bad field",
                     "characteristic": value})


@pytest.mark.parametrize("value", [0, 2, 3, 23])
def test_field_characteristic_accepts_zero_or_prime(value):
    graph = S.Graph()
    graph.apply(F.meta_event())
    graph.apply({"ev": "model", "id": "M", "desc": "a field",
                 "characteristic": value})
    assert graph.models["M"]["characteristic"] == value


def test_model_separates_coefficient_domain_from_point_universe():
    graph = S.Graph()
    graph.apply(F.meta_event())
    graph.apply({
        "ev": "model", "id": "M", "desc": "geometric Q-model",
        "characteristic": 0,
        "coefficient_domain": "Q",
        "point_universe": S.ALGEBRAIC_CLOSURE_POINT_UNIVERSE,
    })
    model = graph.models["M"]
    assert S.declared_coefficient_domain(model) == "Q"
    assert S.declared_point_universe(model) == "ALGEBRAIC_CLOSURE"
    assert S.point_scope(model) == ("Q", "ALGEBRAIC_CLOSURE")


@pytest.mark.parametrize("fields, message", [
    ({"characteristic": 0, "coefficient_domain": "F_2"},
     "supported exact domain is Q"),
    ({"characteristic": 0, "coefficient_domain": "Q",
      "point_universe": "COMPLEX_NUMBERS"},
     "supported values"),
    ({"characteristic": 0, "point_universe": "BASE"},
     "without the structured `coefficient_domain`"),
    ({"characteristic": 0, "coefficient_domain": "Q", "field": "Q"},
     "competing sources of truth"),
    ({"characteristic": 0, "coefficient_domain": "Q",
      "point_universe": "BASE", "universe": "Q-points"},
     "Keep only `point_universe`"),
])
def test_structured_point_scope_rejects_ambiguous_or_unsupported_models(
        fields, message):
    graph = S.Graph()
    graph.apply(F.meta_event())
    event = {"ev": "model", "id": "M", "desc": "bad scope"}
    event.update(fields)
    with pytest.raises(S.GraphError, match=message):
        graph.apply(event)


def test_prime_field_scope_is_canonical():
    graph = S.Graph()
    graph.apply(F.meta_event())
    graph.apply({
        "ev": "model", "id": "M", "desc": "geometric F_5-model",
        "characteristic": 5, "coefficient_domain": "F_5",
        "point_universe": "BASE",
    })
    assert S.point_scope(graph.models["M"]) == ("F_5", "BASE")


def test_cas_program_rejects_composite_characteristic():
    from grandportage import cas

    with pytest.raises(ValueError, match="0 or a prime"):
        cas.CASProgram(
            cas.SINGULAR, ring="R", ring_vars=["x"],
            decls=[], body=[], outputs=[], characteristic=4)


def test_misplaced_meta_and_mixed_epoch_folds_are_refused(tmp_path):
    legacy = _write(tmp_path / "legacy.jsonl", [
        {"ev": "model", "id": "M", "desc": "m"},
        F.meta_event(),
    ])
    with pytest.raises(S.GraphError, match="misplaced `meta`"):
        S.load(legacy)

    native = _write(tmp_path / "native.jsonl", [
        F.meta_event(), {"ev": "model", "id": "N", "desc": "n"},
    ])
    plain = _write(tmp_path / "plain.jsonl", [
        {"ev": "model", "id": "P", "desc": "p"},
    ])
    with pytest.raises(S.GraphError, match="cannot merge epoch-0 and epoch-1"):
        S.load(native, plain)


def test_epoch1_migration_is_beside_original_audited_and_strict(tmp_path):
    source_path = tmp_path / "graph.jsonl"
    source = _write(source_path, [
        {"ev": "model", "id": "A", "desc": "a", "legacy_note": "drop me"},
        {"ev": "model", "id": "B", "desc": "b"},
        {"ev": "edge", "id": "E", "src": "A", "dst": "B",
         "type": "EQUIVALENCE", "why": "same points",
         "ring_isomorphism": True, "refinement": "false",
         "witness": "a target point outside the source",
         "zariski_dense": True},
    ])
    original = source_path.read_bytes()
    assert cli.main(["--graph", source, "migrate", "--to-epoch1"]) == 0

    destination = tmp_path / "graph.epoch1.jsonl"
    audit_path = tmp_path / "graph.epoch1.jsonl.audit.json"
    assert source_path.read_bytes() == original
    assert destination.exists() and audit_path.exists()
    graph = S.load(str(destination))
    assert graph.compatibility_mode is False
    assert graph.edges["E"]["map_kind"] == "RATIONAL"
    assert graph.edges["E"]["ring_iso"] is False
    assert graph.edges["E"]["refinement"] is False
    assert graph.edges["E"]["strictness_witness"]
    assert "legacy_note" not in graph.models["A"]

    audit = json.loads(audit_path.read_text(encoding="utf-8"))
    expected = "sha256:" + hashlib.sha256(original).hexdigest()
    assert audit["source_sha256"] == expected
    changed = json.dumps(audit["changes"])
    for field in ("legacy_note", "ring_isomorphism", "witness",
                  "zariski_dense", "refinement"):
        assert field in changed


def test_constructor_events_fit_epoch1_and_carry_characteristic():
    def facstd(prog, timeout):
        return {"aborted": False, "returncode": 0, "stderr": "",
                "stdout": ("@@GP_L:\n[1]:\n_[1]=x\n[2]:\n_[1]=y\n"
                           + prog.completion_marker + "\n")}

    operations = [
        O.localize("M", "x", "L", ["x", "y"], ["x*y"],
                   characteristic=7),
        O.saturate_closure("M", "x", "S", ["x", "y"], ["x*y"],
                           characteristic=7),
        O.eliminate("M", ["y"], "E", ["x", "y"], ["x*y"],
                    characteristic=7),
        O.decompose("M", ["x", "y"], ["x*y"], characteristic=7,
                    _runner=facstd),
    ]
    for operation in operations:
        minted = [event for event in operation.events
                  if event["ev"] == "model"]
        assert minted and all(event["characteristic"] == 7
                              for event in minted)
        for index, event in enumerate(operation.events):
            F.validate_native_event(
                event, "%s:%d" % (operation.kind, index), S.GraphError)


def test_append_refuses_caller_supplied_meta_without_writing(tmp_path):
    path = S.graph_path(str(tmp_path))
    with pytest.raises(S.GraphError, match="callers cannot append `meta`"):
        S.append([F.meta_event()], str(tmp_path))
    assert not os.path.exists(path)

    S.append([{"ev": "model", "id": "M", "desc": "m"}], str(tmp_path))
    before = open(path, "rb").read()
    with pytest.raises(S.GraphError, match="callers cannot append `meta`"):
        S.append([F.meta_event()], str(tmp_path))
    assert open(path, "rb").read() == before
    S.load(path)


def test_first_append_creates_a_native_graph(tmp_path):
    S.append([{"ev": "model", "id": "M", "desc": "m"}], str(tmp_path))
    path = S.graph_path(str(tmp_path))
    first = next(iter(S.load_native_events(path)))[0]
    assert first["ev"] == "meta"


def test_kernel_epoch1_migration_is_non_destructive_and_reaudits_transport(
        tmp_path):
    source = tmp_path / "epoch1.jsonl"
    destination = tmp_path / "current-kernel.jsonl"
    events = [
        {"ev": "meta", "graph_format": 1, "kernel_epoch": 1,
         "created_with": "grandportage/0.5.0"},
        {"ev": "model", "id": "SOURCE", "what": "source",
         "characteristic": 0, "ring_vars": ["x", "y"],
         "generators": ["x"]},
        {"ev": "model", "id": "BUILT", "what": "elimination target",
         "characteristic": 0, "ring_vars": ["x"], "generators": [],
         "eliminated": ["y"]},
        {"ev": "edge", "id": "E", "src": "SOURCE", "dst": "BUILT",
         "type": K.IMAGE_CLOSURE, "map_kind": K.POLYNOMIAL,
         "why": "eliminate y", "built_by_operation": "Eliminate"},
        {"ev": "claim", "id": "C", "model": "SOURCE",
         "kind": K.IDENTITY, "statement": "x vanishes", "lhs": "x",
         "rhs": "0", "ring_vars": ["x"],
         "identity_origin": K.DERIVED},
        {"ev": "inference", "id": "I", "claim": "C",
         "path": [["E", K.ALONG]], "concludes_kind": K.IDENTITY,
         "asserted": "x vanishes on the target"},
    ]
    _write(source, events)
    before = source.read_bytes()

    assert cli.main([
        "--graph", str(source), "migrate", "--to-current-kernel",
        "--kernel-output", str(destination),
    ]) == 0

    assert source.read_bytes() == before
    graph = S.load(str(destination))
    assert graph.kernel_epoch == F.KERNEL_EPOCH == 10
    finding = [item for item in C.run(graph) if item.rule == C.R_TRANSPORT]
    assert len(finding) == 1
    assert "completeness" in finding[0].detail
    audit = json.loads((tmp_path / "current-kernel.jsonl.audit.json").read_text())
    assert audit["from_kernel_epoch"] == 1
    assert audit["kernel_epoch"] == 10


def test_older_epochs_migrate_non_destructively_to_format4_epoch10(tmp_path):
    source = tmp_path / "format1-epoch4.jsonl"
    destination = tmp_path / "format4-epoch10.jsonl"
    _write(source, [{
        "ev": "meta", "graph_format": 1, "kernel_epoch": 4,
        "created_with": "grandportage/0.8.0",
    }])
    before = source.read_bytes()

    reports = MIG.migrate_kernel_epoch(
        [str(source)], output=str(destination))

    assert source.read_bytes() == before
    assert reports[0]["from_graph_format"] == 1
    assert reports[0]["from_kernel_epoch"] == 4
    assert reports[0]["graph_format"] == F.GRAPH_FORMAT == 4
    assert reports[0]["kernel_epoch"] == F.KERNEL_EPOCH == 10
    assert S.load(str(destination)).graph_format == 4
    assert S.load(str(destination)).kernel_epoch == 10

    epoch5 = tmp_path / "format2-epoch5.jsonl"
    epoch8_from_epoch5 = tmp_path / "format2-epoch8-from-epoch5.jsonl"
    _write(epoch5, [{
        "ev": "meta", "graph_format": 2, "kernel_epoch": 5,
        "created_with": "grandportage/0.10.0",
    }])
    epoch5_before = epoch5.read_bytes()
    epoch5_reports = MIG.migrate_kernel_epoch(
        [str(epoch5)], output=str(epoch8_from_epoch5))
    assert epoch5.read_bytes() == epoch5_before
    assert epoch5_reports[0]["from_graph_format"] == 2
    assert epoch5_reports[0]["from_kernel_epoch"] == 5
    assert epoch5_reports[0]["graph_format"] == 4
    assert epoch5_reports[0]["kernel_epoch"] == 10
    assert S.load(str(epoch8_from_epoch5)).kernel_epoch == 10

    epoch6 = tmp_path / "format2-epoch6.jsonl"
    epoch8 = tmp_path / "format2-epoch8-from-epoch6.jsonl"
    _write(epoch6, [{
        "ev": "meta", "graph_format": 2, "kernel_epoch": 6,
        "created_with": "grandportage/0.11.0",
    }])
    epoch6_before = epoch6.read_bytes()
    epoch6_reports = MIG.migrate_kernel_epoch(
        [str(epoch6)], output=str(epoch8))
    assert epoch6.read_bytes() == epoch6_before
    assert epoch6_reports[0]["from_graph_format"] == 2
    assert epoch6_reports[0]["from_kernel_epoch"] == 6
    assert epoch6_reports[0]["graph_format"] == 4
    assert epoch6_reports[0]["kernel_epoch"] == 10
    assert S.load(str(epoch8)).kernel_epoch == 10

    epoch7 = tmp_path / "format2-epoch7.jsonl"
    epoch8_from_epoch7 = tmp_path / "format2-epoch8-from-epoch7.jsonl"
    _write(epoch7, [{
        "ev": "meta", "graph_format": 2, "kernel_epoch": 7,
        "created_with": "grandportage/0.12.0",
    }])
    epoch7_before = epoch7.read_bytes()
    epoch7_reports = MIG.migrate_kernel_epoch(
        [str(epoch7)], output=str(epoch8_from_epoch7))
    assert epoch7.read_bytes() == epoch7_before
    assert epoch7_reports[0]["from_graph_format"] == 2
    assert epoch7_reports[0]["from_kernel_epoch"] == 7
    assert epoch7_reports[0]["graph_format"] == 4
    assert epoch7_reports[0]["kernel_epoch"] == 10
    assert S.load(str(epoch8_from_epoch7)).kernel_epoch == 10
    future = tmp_path / "format1-future-epoch.jsonl"
    _write(future, [{
        "ev": "meta", "graph_format": 1, "kernel_epoch": 11,
        "created_with": "grandportage/future",
    }])
    with pytest.raises(S.GraphError, match="cannot migrate forward"):
        MIG.migrate_kernel_epoch([str(future)])


def test_partition_receipt_binding_fields_are_native_schema():
    event = {
        "ev": "partition",
        "id": "P",
        "parent": "M",
        "branches": ["L", "R"],
        "exhaustive": "C",
        "why": "a checked binary-product cover",
        "receipt_schema": "product_split_v1",
        "receipt_id": "E_2_0_bottom_split",
        "receipt_fingerprint": "sha256:" + "a" * 64,
    }

    F.validate_native_event(event, "test:1", S.GraphError)


def test_partition_receipt_binding_is_all_or_none_and_typed():
    base = {
        "ev": "partition",
        "id": "P",
        "parent": "M",
        "branches": ["L", "R"],
        "exhaustive": "C",
        "why": "cover",
    }
    with pytest.raises(S.GraphError, match="must provide"):
        F.validate_native_event(
            dict(base, receipt_schema="product_split_v1"),
            "test:1", S.GraphError)

    complete = dict(
        base,
        receipt_schema="product_split_v1",
        receipt_id="E",
        receipt_fingerprint="sha256:" + "a" * 64,
    )
    for field, value, message in (
        ("receipt_schema", "", "non-empty string"),
        ("receipt_id", None, "non-empty string"),
        ("receipt_fingerprint", "sha256:ABC", "64 lowercase hex"),
    ):
        with pytest.raises(S.GraphError, match=message):
            F.validate_native_event(
                dict(complete, **{field: value}), "test:1", S.GraphError)
