"""M2 backend contract and semantic golden corpus."""

import pytest

from grandportage import artifacts as A
from grandportage import backend as B
from grandportage import cas
from grandportage import groebner as G
from grandportage import kernel as K
from grandportage import provenance as P
from grandportage import store as S
from grandportage import verify as V


def _raw(stdout, *, returncode=0, aborted=False, stderr=""):
    return {
        "returncode": returncode,
        "stdout": stdout,
        "stderr": stderr,
        "aborted": aborted,
        "abort_reason": "timeout" if aborted else None,
        "argv": ["Singular-test-double"],
    }


def _finished(program, stdout):
    separator = "" if stdout.endswith("\n") else "\n"
    return stdout + separator + program.completion_marker + "\n"


def _program(characteristic=0, outputs=None):
    outputs = outputs or ["GP_G"]
    return cas.CASProgram(
        cas.SINGULAR,
        ring="GP_R",
        ring_vars=["x"],
        decls=[("GP_G", "ideal", "std(ideal(x))")],
        body=[],
        outputs=outputs,
        characteristic=characteristic,
    )


def test_execution_artifact_snapshots_program_backend_raw_and_parsed_output():
    program = _program()
    backend = cas.SingularBackend(
        runner=lambda program, _timeout: _raw(_finished(
            program, "@@GP_G:\nGP_G[1]=x\n"
        )),
        binary_version="Singular 9.9-test",
    )

    result = backend.execute(
        program,
        semantic_input={"operation": "basis", "generators": ["x"]},
    )
    values = cas._parse_result(result, program.outputs)
    artifact = result.artifact

    assert result["program"] is program
    assert artifact.backend.binary_version == "Singular 9.9-test"
    assert artifact.backend.implementation == "grandportage.cas.SingularBackend"
    assert artifact.program_text == program.execution_text(
        artifact.completion_nonce
    )
    assert artifact.program_text != program.text
    assert artifact.program_fingerprint == B.text_fingerprint(
        artifact.program_text
    )
    assert artifact.semantic_input_fingerprint.startswith("sha256:")
    assert artifact.stdout.startswith("@@GP_G:\nGP_G[1]=x\n")
    assert artifact.stdout.rstrip().endswith(
        "@@GP-END:%s" % artifact.completion_nonce
    )
    assert artifact.stdout_fingerprint == B.text_fingerprint(artifact.stdout)
    assert artifact.stderr_fingerprint == B.text_fingerprint(artifact.stderr)
    assert artifact.parsed_output is not None
    assert values == {"GP_G": "GP_G[1]=x"}

    result["stdout"] = "mutated legacy dictionary"
    program.body.append("// mutated after execution")
    assert artifact.stdout.startswith("@@GP_G:\nGP_G[1]=x\n")
    assert "// mutated" not in artifact.program_text


def test_parse_uses_the_frozen_stdout_not_a_mutated_legacy_field():
    program = _program()
    backend = cas.SingularBackend(
        runner=lambda program, _timeout: _raw(_finished(
            program, "@@GP_G:\nGP_G[1]=x\n"
        )),
        binary_version="test",
    )
    result = backend.execute(program)
    result["stdout"] = "@@GP_G:\nGP_G[1]=not_the_run\n"

    values = cas._parse_result(result, program.outputs)

    assert values == {"GP_G": "GP_G[1]=x"}
    assert "not_the_run" not in result.artifact.parsed_output


@pytest.mark.parametrize("transcript", [
    "missing",
    "wrong",
    "duplicate",
    "trailing-data",
])
def test_transcript_envelope_refuses_partial_stale_or_concatenated_output(
        transcript):
    program = _program()

    def runner(invocation, _timeout):
        prefix = "@@GP_G:\nGP_G[1]=x\n"
        if transcript == "missing":
            stdout = prefix
        elif transcript == "wrong":
            stdout = prefix + "@@GP-END:%s\n" % ("0" * 32)
        elif transcript == "duplicate":
            stdout = (_finished(invocation, prefix)
                      + invocation.completion_marker + "\n")
        else:
            stdout = _finished(invocation, prefix) + "a second transcript\n"
        return _raw(stdout)

    result = cas.SingularBackend(
        runner=runner, binary_version="test"
    ).execute(program)

    with pytest.raises(cas.CASError, match="terminal marker|different invocation"):
        cas._parse_result(result, program.outputs)

    assert result.artifact.parsed_output is None


def test_each_execution_gets_a_fresh_nonce_and_stdout_cannot_be_replayed():
    program = _program()
    first_stdout = []

    def runner(invocation, _timeout):
        if not first_stdout:
            stdout = _finished(invocation, "@@GP_G:\nGP_G[1]=x\n")
            first_stdout.append(stdout)
        else:
            stdout = first_stdout[0]
        return _raw(stdout)

    backend = cas.SingularBackend(runner=runner, binary_version="test")
    first = backend.execute(program)
    assert cas._parse_result(first, program.outputs) == {
        "GP_G": "GP_G[1]=x"
    }
    second = backend.execute(program)

    assert first.artifact.completion_nonce != second.artifact.completion_nonce
    assert first.artifact.program_fingerprint != second.artifact.program_fingerprint
    assert first.artifact.semantic_input_fingerprint == (
        second.artifact.semantic_input_fingerprint
    )
    with pytest.raises(cas.CASError, match="different invocation"):
        cas._parse_result(second, program.outputs)


def test_a_runner_cannot_smuggle_in_a_foreign_execution_artifact():
    program = _program()
    first = cas.SingularBackend(
        runner=lambda program, _timeout: _raw(_finished(
            program, "@@GP_G:\nGP_G[1]=x\n"
        )),
        binary_version="first",
    ).execute(program)
    second = cas.SingularBackend(
        runner=lambda _program, _timeout: first,
        binary_version="second",
    )

    with pytest.raises(TypeError, match="pre-wrapped BackendExecution"):
        second.execute(_program(characteristic=2))

    assert second.executions == []


def test_verify_all_uses_semantic_backend_methods_not_cas_programs(tmp_path):
    S.append([
        {
            "ev": "model", "id": "M", "what": "the origin",
            "characteristic": 0, "ring_vars": ["x"], "generators": ["x"],
        },
        {
            "ev": "claim", "id": "C", "model": "M", "kind": K.IDENTITY,
            "statement": "x vanishes", "lhs": "x", "rhs": "0",
            "ring_vars": ["x"], "identity_origin": K.DERIVED,
            "established_by": "RAN", "ladder": "exact-checked",
        },
    ], str(tmp_path))

    class SemanticOnly(cas.SingularBackend):
        def __init__(self):
            super().__init__(runner=lambda *_args: None,
                             binary_version="test-double")
            self.calls = []

        def execute(self, *_args, **_kwargs):
            raise AssertionError("semantic verifier passed a CASProgram")

        def classify_identity(self, *_args, **_kwargs):
            self.calls.append("classify_identity")
            return K.DERIVED, {"difference": "x", "reduced_modulo_ideal": "0"}

        def membership(self, *_args, **_kwargs):
            self.calls.append("membership")
            return {"is_member": True, "cofactors": ["1"], "reduced": "0"}

        def check_membership(self, *_args, **_kwargs):
            self.calls.append("check_membership")
            return True, "0"

    backend = SemanticOnly()
    assert backend.identity.implementation.endswith(".<locals>.SemanticOnly")
    assert backend.can_record_verdicts is False
    with pytest.raises(ValueError, match="record=True requires"):
        V.verify_all(root=str(tmp_path), backend=backend, record=True)
    results = V.verify_all(root=str(tmp_path), backend=backend, record=False)

    assert backend.calls == [
        "classify_identity", "membership", "check_membership"
    ]
    assert [(subject, oid, verdict) for subject, oid, verdict, _ in results] == [
        ("claim", "C", V.DERIVED)
    ]
    assert not (tmp_path / ".portage" / "artifacts").exists()


def test_derived_identity_without_a_replayable_representation_is_unverified():
    graph = S.Graph()
    graph.models["M"] = {
        "id": "M", "characteristic": 0, "ring_vars": ["x"],
        "generators": ["x"],
    }
    graph.claims["C"] = {
        "id": "C", "model": "M", "kind": K.IDENTITY,
        "lhs": "x", "rhs": "0", "ring_vars": ["x"],
    }

    class NoRepresentation(cas.SingularBackend):
        def classify_identity(self, *_args, **_kwargs):
            return K.DERIVED, {"reduced_modulo_ideal": "0"}

        def membership(self, *_args, **_kwargs):
            return {"is_member": True, "cofactors": None, "reduced": "0"}

    verdict, why = V.identity(
        graph, "C", _backend=NoRepresentation(
            runner=lambda *_args: None, binary_version="test"))

    assert verdict == V.UNVERIFIED
    assert "NO REPRESENTATION" in why


def test_verify_all_refuses_to_record_an_injected_runner(tmp_path):
    S.append([
        {
            "ev": "model", "id": "M", "what": "the origin",
            "characteristic": 0, "ring_vars": ["x"], "generators": ["x"],
        },
        {
            "ev": "claim", "id": "C", "model": "M", "kind": K.IDENTITY,
            "statement": "x vanishes", "lhs": "x", "rhs": "0",
            "ring_vars": ["x"], "identity_origin": K.DERIVED,
            "established_by": "RAN", "ladder": "exact-checked",
        },
    ], str(tmp_path))

    def runner(program, _timeout):
        stdout = "".join("@@%s:\n0\n" % output.upper()
                         for output in program.outputs)
        return _raw(stdout)

    with pytest.raises(ValueError, match="injected runners"):
        V.verify_all(root=str(tmp_path), _runner=runner, record=True)
    assert S.load(S.graph_path(str(tmp_path))).verdicts == {}


@pytest.mark.live
def test_verify_all_records_the_real_backend_trace_that_answered(tmp_path):
    S.append([
        {
            "ev": "model", "id": "M", "what": "the origin",
            "characteristic": 0, "ring_vars": ["x"], "generators": ["x"],
        },
        {
            "ev": "claim", "id": "C", "model": "M", "kind": K.IDENTITY,
            "statement": "x vanishes", "lhs": "x", "rhs": "0",
            "ring_vars": ["x"], "identity_origin": K.DERIVED,
            "established_by": "RAN", "ladder": "exact-checked",
        },
    ], str(tmp_path))

    V.verify_all(root=str(tmp_path), record=True, timeout=120)
    verdict = next(iter(S.load(S.graph_path(str(tmp_path))).verdicts.values()))
    manifest = P.backend_provenance(verdict["backend"])

    assert verdict["current"] is True
    assert manifest["contract"] == "singular"
    assert manifest["binary_version"] != "test-double"
    assert manifest["implementation"] == B.SINGULAR_IMPLEMENTATION
    assert manifest["executions"]
    assert all(B.valid_execution_trace_entry(entry)
               for entry in manifest["executions"])
    assert A.audit_manifest(str(tmp_path), manifest) == []
    assert all(A.load(str(tmp_path), entry["artifact_fingerprint"])
               for entry in manifest["executions"])


def test_characteristic_is_part_of_the_semantic_program_fingerprint():
    assert (
        _program(characteristic=0).semantic_fingerprint
        != _program(characteristic=2).semantic_fingerprint
    )


def test_multi_output_parse_is_atomic_on_an_empty_second_marker():
    program = _program(outputs=["GP_G", "GP_M"])
    backend = cas.SingularBackend(
        runner=lambda program, _timeout: _raw(_finished(
            program, "@@GP_G:\nGP_G[1]=1\n@@GP_M:\n"
        )),
        binary_version="test",
    )
    result = backend.execute(program)

    with pytest.raises(cas.CASError):
        cas._parse_result(result, program.outputs)

    assert result.artifact.parsed_output is None
    assert "parsed_values" not in result


def test_truncated_facstd_component_is_not_an_empty_ideal():
    backend = cas.SingularBackend(
        runner=lambda program, _timeout: _raw(_finished(
            program, "@@GP_L:\n[1]:\n_[1]=x\n[2]:\n"
        )),
        binary_version="test",
    )

    with pytest.raises(cas.CASError, match="truncated facstd output"):
        backend.factorizing_decomposition(["x"], ["x"])


def test_named_saturation_and_elimination_keep_the_exact_executed_program():
    seen = []

    def runner(program, _timeout):
        seen.append(program)
        return _raw(_finished(program, "@@GP_OUT:\nGP_OUT[1]=y\n"))

    backend = cas.SingularBackend(runner=runner, binary_version="test")
    saturated = backend.saturate(["x", "y"], ["x^9*y"], "x")
    eliminated = backend.eliminate(
        ["x", "y", "z"], ["z", "x*(y-x^2)"], ["z"]
    )

    assert saturated["generators"] == ["y"]
    assert eliminated["ring_vars"] == ["x", "y"]
    assert eliminated["generators"] == ["y"]
    assert saturated["execution"].execution_program is seen[0]
    assert eliminated["execution"].execution_program is seen[1]
    assert saturated["execution"]["program"] is saturated["program"]
    assert eliminated["execution"]["program"] is eliminated["program"]
    assert saturated["execution"].artifact.program_text == seen[0].text
    assert eliminated["execution"].artifact.program_text == seen[1].text


def _assert_member(backend, ring, target, generators, characteristic=0):
    answer = backend.membership(
        ring, target, generators, characteristic=characteristic, timeout=120
    )
    assert answer["is_member"], answer
    ok, expanded = backend.check_membership(
        ring, target, generators, answer["cofactors"],
        characteristic=characteristic, timeout=120,
    )
    assert ok, expanded


def test_membership_boundary_compiles_sparse_polynomials_before_singular():
    sparse = {
        "schema": G.SPARSE_POLYNOMIAL_SCHEMA,
        "terms": [{"coefficient": "1", "powers": [["x", 2]]}],
    }
    seen = []

    def runner(program, _timeout):
        seen.append(program.text)
        assert "{'schema'" not in program.text
        assert '"schema"' not in program.text
        return _raw(_finished(program, "@@GP_RED:\nGP_RED[1]=0\n"))

    # The first probe is sufficient to exercise sparse target and generator
    # compilation. It then attempts `lift`; stop there with a typed CAS error.
    with pytest.raises(cas.CASError):
        cas.membership_representation(
            ["x"], sparse, [sparse], _runner=runner)
    assert seen and "x^2" in seen[0]


def test_membership_checker_compiles_sparse_target_generator_and_cofactor():
    sparse_x = {
        "schema": G.SPARSE_POLYNOMIAL_SCHEMA,
        "terms": [{"coefficient": "1", "powers": [["x", 1]]}],
    }

    def runner(program, _timeout):
        assert "{'schema'" not in program.text
        assert '"schema"' not in program.text
        assert "x" in program.text
        return _raw(_finished(program, "@@GP_DIFF:\nGP_DIFF[1]=0\n"))

    valid, difference = cas.check_membership_representation(
        ["x"], sparse_x, [sparse_x], ["1"], _runner=runner)
    assert valid and difference == "0"


@pytest.mark.live
def test_real_singular_prints_the_matching_terminal_marker_last():
    backend = cas.SingularBackend()
    answer = backend.membership(
        ["x"], "1", ["x"], characteristic=0, timeout=120
    )

    assert answer["is_member"] is False
    artifact = backend.executions[-1].artifact
    expected = "@@GP-END:%s" % artifact.completion_nonce
    assert [line for line in artifact.stdout.splitlines() if line.strip()][-1] == expected
    assert ('"%s";' % expected) in artifact.program_text
    assert artifact.program_text.rstrip().endswith("quit;")


@pytest.mark.live
def test_golden_characteristic_dependent_membership():
    backend = cas.SingularBackend()

    over_q = backend.membership(
        ["x"], "x^2+1", ["x+1"], characteristic=0, timeout=120
    )
    over_f2 = backend.membership(
        ["x"], "x^2+1", ["x+1"], characteristic=2, timeout=120
    )

    assert over_q["is_member"] is False
    assert over_q["reduced"] == "2"
    assert over_f2["is_member"] is True
    assert backend.executions[-1].artifact.certificate is not None
    _assert_member(
        backend, ["x"], "x^2+1", ["x+1"], characteristic=2
    )

    for generators in (
        ["x+y", "x-y"],
        ["y-x", "-(x+y)"],
    ):
        answer = backend.membership(
            ["x", "y"], "3*x+y", generators, timeout=120
        )
        assert answer["is_member"], answer
        ok, expanded = backend.check_membership(
            ["x", "y"], "3*x+y", generators, answer["cofactors"],
            timeout=120,
        )
        assert ok, expanded
        wrong, _ = backend.check_membership(
            ["x", "y"], "3*x+y", generators,
            list(reversed(answer["cofactors"])), timeout=120,
        )
        assert wrong is False


@pytest.mark.live
def test_golden_saturation_beyond_the_old_witness_bound():
    backend = cas.SingularBackend()
    answer = backend.saturate(
        ["x", "y"], ["x^9*y"], "x", characteristic=0, timeout=120
    )

    _assert_member(backend, ["x", "y"], "y", answer["generators"])
    for generator in answer["generators"]:
        _assert_member(backend, ["x", "y"], generator, ["y"])

    for exponent in range(9):
        probe = backend.membership(
            ["x", "y"], "x^%d*y" % exponent, ["x^9*y"], timeout=120
        )
        assert probe["is_member"] is False
    _assert_member(backend, ["x", "y"], "x^9*y", ["x^9*y"])


@pytest.mark.live
def test_golden_non_involution_pullback_and_compact_elimination():
    backend = cas.SingularBackend()

    reduced, zero = backend.pullback_reduce(
        ["x"], "x-1", {"x": "x+1"}, generators=["x"], timeout=120
    )
    assert zero, reduced
    reduced, zero = backend.pullback_reduce(
        ["x"], "x", {"x": "x-1"}, generators=["x-1"], timeout=120
    )
    assert zero, reduced

    eliminated = backend.eliminate(
        ["x", "y", "z"], ["z", "x*(y-x^2)"], ["z"], timeout=120
    )
    assert all("z" not in generator for generator in eliminated["generators"])
    _assert_member(
        backend, ["x", "y"], "x^3-x*y", eliminated["generators"]
    )
    for generator in eliminated["generators"]:
        _assert_member(
            backend, ["x", "y"], generator, ["x^3-x*y"]
        )


@pytest.mark.live
def test_golden_geometric_hole_and_overlapping_decomposition():
    backend = cas.SingularBackend()

    covered, evidence = backend.partition_cover(
        ["x"], ["x^2+1"], [["x^2+1", "x"], ["x^2+1", "x-1"]],
        timeout=120,
    )
    assert covered is False
    assert evidence["uncovered"]
    _assert_member(backend, ["x"], "1", evidence["uncovered"])
    for generator in evidence["uncovered"]:
        _assert_member(backend, ["x"], generator, ["1"])

    pieces = backend.factorizing_decomposition(
        ["x", "y"], ["x*y*(x-y)"], timeout=120
    )
    assert len(pieces) == 3
    for piece in pieces:
        _assert_member(backend, ["x", "y"], "x*y*(x-y)", piece)
        is_origin, evidence = backend.evaluate_point(
            ["x", "y"], piece, {"x": 0, "y": 0}, timeout=120
        )
        assert is_origin, evidence
    covered, evidence = backend.partition_cover(
        ["x", "y"], ["x*y*(x-y)"], pieces, timeout=120
    )
    assert covered, evidence

    one_piece = backend.factorizing_decomposition(
        ["x", "y"], ["x^2+y", "y^2+x"], timeout=120
    )
    assert len(one_piece) == 1
    input_ideal = ["x^2+y", "y^2+x"]
    returned_ideal = one_piece[0]
    for generator in input_ideal:
        _assert_member(backend, ["x", "y"], generator, returned_ideal)
    for generator in returned_ideal:
        _assert_member(backend, ["x", "y"], generator, input_ideal)
    _assert_member(
        backend, ["x", "y"], "y*(y^3+1)", returned_ideal
    )
    assert backend.membership(
        ["x", "y"], "y", returned_ideal, timeout=120
    )["is_member"] is False
    assert backend.membership(
        ["x", "y"], "y^3+1", returned_ideal, timeout=120
    )["is_member"] is False

@pytest.mark.live
def test_real_singular_polynomial_section_persists_exact_contraction(tmp_path):
    """The first exact-elimination authority runs end to end on real CAS.

    The section y -> x^2 sends (y*x-1, y^2-x) into (x^3-1). The ordinary
    output verifier independently proves the other inclusion, and every raw
    execution is persisted before either verdict reaches the graph.
    """
    from grandportage import check as C

    root = str(tmp_path)
    S.append([
        {"ev": "model", "id": "PRE", "what": "translated source",
         "characteristic": 0, "ring_vars": ["y", "x"],
         "generators": ["y*(x+1)-1", "y^2-(x+1)"]},
        {"ev": "model", "id": "SOURCE", "what": "source",
         "characteristic": 0, "ring_vars": ["y", "x"],
         "generators": ["y*x-1", "y^2-x"]},
        {"ev": "model", "id": "LOOSE", "what": "ambient open-condition model",
         "characteristic": 0, "ring_vars": ["y", "x"],
         "generators": ["y*x-1", "y^2-x"]},
        {"ev": "model", "id": "TARGET", "what": "target",
         "characteristic": 0, "ring_vars": ["x"],
         "generators": ["x^3-1"], "eliminated": ["y"]},
        {"ev": "edge", "id": "EQ", "src": "PRE", "dst": "SOURCE",
         "type": K.EQUIVALENCE, "map_kind": K.POLYNOMIAL,
         "why": "translate x by one", "ring_iso": True,
         "forward": {"y": "y", "x": "x+1"},
         "inverse": {"y": "y", "x": "x-1"}},
        {"ev": "edge", "id": "R", "src": "SOURCE", "dst": "LOOSE",
         "type": K.RESTRICTION, "map_kind": K.IDENTITY_MAP,
         "why": "forget an open side condition"},
        {"ev": "edge", "id": "E", "src": "SOURCE", "dst": "TARGET",
         "type": K.IMAGE_CLOSURE, "map_kind": K.POLYNOMIAL,
         "why": "eliminate y", "built_by_operation": "Eliminate"},
    ], root)

    V.verify_all(root=root, timeout=120, record=True)
    verdict, why, certificate = V.verify_elimination_section(
        root, "E", {"y": "x^2"}, timeout=120, record=True)

    assert verdict == V.SECTION_VERIFIED, why
    assert certificate["rows"][1]["cofactors"] == ["x"]

    # Consume the live certificates through the mapped claim transformer. The
    # retained predicate crosses; closedness cannot rescue a condition whose
    # expression still names the eliminated coordinate.
    S.append([
        {"ev": "claim", "id": "P-LOOSE", "model": "LOOSE",
         "kind": K.PREDICATE, "statement": "x is nonzero",
         "condition": {"all": [
             {"relation": "NONZERO", "expression": "x"},
         ]}},
        {"ev": "inference", "id": "I-LOOSE", "claim": "P-LOOSE",
         "path": [["R", K.AGAINST], ["E", K.ALONG]],
         "concludes_kind": K.PREDICATE,
         "asserted": "the ambient condition holds on the elimination target"},
        {"ev": "claim", "id": "P-TARGET", "model": "TARGET",
         "kind": K.PREDICATE, "statement": "x is nonzero",
         "condition": {"all": [
             {"relation": "NONZERO", "expression": "x"},
         ]}},
        {"ev": "inference", "id": "I-PROJECTION", "claim": "P-TARGET",
         "path": [["E", K.AGAINST], ["E", K.ALONG]],
         "concludes_kind": K.PREDICATE,
         "asserted": "the projection pullback composes with the checked lift"},
        {"ev": "claim", "id": "P-PRE", "model": "PRE",
         "kind": K.PREDICATE, "statement": "x+1 is nonzero",
         "condition": {"all": [
             {"relation": "NONZERO", "expression": "x+1"},
         ]}},
        {"ev": "inference", "id": "I-PRE", "claim": "P-PRE",
         "path": [["EQ", K.ALONG], ["E", K.ALONG]],
         "concludes_kind": K.PREDICATE,
         "asserted": "the rewritten x coordinate is nonzero on the target"},
        {"ev": "claim", "id": "P-X", "model": "SOURCE",
         "kind": K.PREDICATE, "statement": "x is nonzero",
         "condition": {"all": [
             {"relation": "NONZERO", "expression": "x"},
         ]}},
        {"ev": "inference", "id": "I-X", "claim": "P-X",
         "path": [["E", K.ALONG]], "concludes_kind": K.PREDICATE,
         "asserted": "x is nonzero on the target"},
        {"ev": "claim", "id": "P-Y", "model": "SOURCE",
         "kind": K.PREDICATE, "statement": "y vanishes",
         "condition": {"all": [
             {"relation": "ZERO", "expression": "y"},
         ]}},
        {"ev": "inference", "id": "I-Y", "claim": "P-Y",
         "path": [["E", K.ALONG]], "concludes_kind": K.PREDICATE,
         "asserted": "y vanishes on the target"},
    ], root)

    graph = S.load(S.graph_path(root))
    mapped = graph.edges["EQ"]
    edge = graph.edges["E"]
    assert mapped["ring_iso_verdict"] == V.ISO_VERIFIED
    assert edge["output_verdict"] == V.OP_SOUND
    assert edge["contraction_verdict"] == V.SECTION_VERIFIED
    assert C.effective_exact_contraction(edge)
    assert C.effective_geometric_closure(edge)
    assert C.effective_point_surjective(edge)
    restricted_ok, restricted_trace = C.audit_inference(graph, "I-LOOSE")
    assert restricted_ok
    assert "literal identity point map" in restricted_trace[0][3]
    projected_ok, projected_trace = C.audit_inference(graph, "I-PROJECTION")
    assert projected_ok
    assert "checked retained-coordinate projection" in projected_trace[0][3]
    mapped_ok, mapped_trace = C.audit_inference(graph, "I-PRE")
    assert mapped_ok
    assert "inverse point-map substitution" in mapped_trace[0][3]
    assert "closedness is not required" in mapped_trace[1][3]
    assert C.audit_inference(graph, "I-X")[0]
    refused, trace = C.audit_inference(graph, "I-Y")
    assert not refused
    assert "no structured target-expressibility proof" in trace[0][3]
    assert A.audit_graph(root, graph) == []


@pytest.mark.live
def test_real_singular_hyperbola_has_no_false_polynomial_section():
    """Exact elimination can exist without this deliberately narrow proof."""
    graph = S.Graph().apply_all([
        ({"ev": "model", "id": "SOURCE", "what": "hyperbola",
          "characteristic": 0, "ring_vars": ["y", "x"],
          "generators": ["x*y-1"]}, "test", 0),
        ({"ev": "model", "id": "TARGET", "what": "dense image closure",
          "characteristic": 0, "ring_vars": ["x"],
          "generators": [], "eliminated": ["y"]}, "test", 1),
        ({"ev": "edge", "id": "E", "src": "SOURCE", "dst": "TARGET",
          "type": K.IMAGE_CLOSURE, "map_kind": K.POLYNOMIAL,
          "why": "eliminate y", "built_by_operation": "Eliminate"},
         "test", 2),
    ]).validate()

    verdict, why, certificate = V.elimination_section(
        graph, "E", {"y": "0"}, timeout=120)
    assert verdict == V.SECTION_REJECTED
    assert "not to zero" in why
    assert certificate is None
def test_section_wrapper_persists_verdict_and_every_answering_artifact(
        tmp_path, monkeypatch):
    root = str(tmp_path)
    S.append([
        {"ev": "model", "id": "SOURCE", "what": "source",
         "characteristic": 0, "ring_vars": ["y", "x"],
         "generators": ["y*x-1", "y^2-x"]},
        {"ev": "model", "id": "TARGET", "what": "target",
         "characteristic": 0, "ring_vars": ["x"],
         "generators": ["x^3-1"], "eliminated": ["y"]},
        {"ev": "edge", "id": "E", "src": "SOURCE", "dst": "TARGET",
         "type": K.IMAGE_CLOSURE, "map_kind": K.POLYNOMIAL,
         "why": "eliminate y", "built_by_operation": "Eliminate"},
    ], root)

    def runner(program, _timeout):
        declarations = dict((name, value) for name, _kind, value in program.decls)
        if program.outputs == ["GP_E"]:
            value = {"y*x-1": "x^3-1", "y^2-x": "x^4-x"}[
                declarations["GP_P"]]
            output = "@@GP_E:\n%s\n" % value
        elif program.outputs == ["GP_RED"]:
            output = "@@GP_RED:\n0\n"
        elif program.outputs == ["GP_M"]:
            coefficient = "x" if "x^4-x" in declarations["GP_T"] else "1"
            output = "@@GP_M:\nGP_M[1,1]=%s\n" % coefficient
        elif program.outputs == ["GP_DIFF"]:
            output = "@@GP_DIFF:\n0\n"
        else:
            pytest.fail("unexpected section program outputs %r" % program.outputs)
        return _raw(_finished(program, output))

    backend = cas.SingularBackend(
        runner=runner, binary_version="Singular 4.4.1")
    monkeypatch.setattr(
        cas.SingularBackend, "can_record_verdicts",
        property(lambda _self: True))

    verdict, why, representation = V.verify_elimination_section(
        root, "E", {"y": "x^2"}, backend=backend, record=True)

    assert verdict == V.SECTION_VERIFIED, why
    assert len(backend.executions) == 8
    assert representation["rows"][1]["cofactors"] == ["x"]
    graph = S.load(S.graph_path(root))
    assert graph.edges["E"]["contraction_verdict"] == V.SECTION_VERIFIED
    assert A.audit_graph(root, graph) == []
