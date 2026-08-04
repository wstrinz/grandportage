"""The three structured operations, and the distinction that motivated two.

Experiment B narrowed this layer from sixteen constructors to three, and the
reasoning is in EXPERIMENT-B.md: hand declarations are 88% accurate, so
correctness alone does not pay for constructors. What these three earn is that
`Localize` and `SaturateClosure` derive DIFFERENT edge types from the same
intuition -- "the part where f is nonzero" -- and a live campaign typed both as
NECESSARY_CONDITION, getting one right by accident.
"""

import pytest

from grandportage import artifacts as A
from grandportage import check as C
from grandportage import cli
from grandportage import kernel as K
from grandportage import operations as O
from grandportage import store as S

RING = ["x", "y"]
HYP = ["x*y-1"]


def _completed(program, stdout):
    separator = "" if stdout.endswith("\n") else "\n"
    return stdout + separator + program.completion_marker + "\n"


def _fold(events):
    g = S.Graph().apply_all([(e, "t", i) for i, e in enumerate(events)])
    g.validate()
    return g


def test_localize_and_saturate_derive_different_types():
    """THE WHOLE REASON THESE TWO EXIST, and the error the corpus contains.

    Both answer "the part of V(I) where f is nonzero", and they are different
    objects:

        Localize          the OPEN locus. THE SAME IDEAL, with a condition on
                          POINTS. Returning to the ambient model drops an
                          INEQUALITY and no equation -> RESTRICTION
        SaturateClosure   its CLOSURE, back in the ambient space. I : f^oo
                          contains I, so returning drops EQUATIONS
                          -> NECESSARY_CONDITION

    A live campaign typed a localisation (`E_LAUR`, K[x,y] -> K[x,y,y^-1]) as
    NECESSARY_CONDITION and a saturation (`E-G3_ELIM_NO_A5`, dropping the
    Rabinowitsch generator 1-w*a whose content is a != 0) the same way. One of
    those was right.
    """
    loc = O.localize("M", "y", "M_LOC", RING, HYP)
    sat = O.saturate_closure("M", "y", "M_SAT", RING, HYP)

    assert loc.events[1]["type"] == K.RESTRICTION
    assert sat.events[1]["type"] == K.NECESSARY_CONDITION
    assert loc.events[1]["type"] != sat.events[1]["type"], (
        "if these ever agree, the constructors have stopped distinguishing "
        "the two objects and the layer buys nothing")

    # A localisation changes no coordinates, so there is no substitution that
    # could introduce a denominator.
    assert loc.events[1]["map_kind"] == K.IDENTITY_MAP


def test_the_derived_type_is_inspectable():
    """The claim of this module is that the type is DERIVED. A reader must be
    able to check that without reading the code that acts on it."""
    for kind, (etype, why) in O.DERIVES.items():
        assert etype in K.ALL_TYPES, "%s derives an unknown type" % kind
        assert len(why) > 40, (
            "%s derives %s with no argument for it; a table entry that only "
            "names a type is the honour system with a lookup" % (kind, etype))


def test_eliminate_emits_the_closure_and_refuses_the_witness():
    """THE HYPERBOLA, which is the ten-minute demonstration of the whole idea.

    Eliminating `y` from `xy = 1` gives the ZERO ideal, so the closure of the
    image is all of A^1 -- while `x = 0` has no preimage at all. The CAS is
    right and the unsupported step is reading the closure as the image.

    So the constructor emits IMAGE_CLOSURE, whose AGAINST/NONEMPTY cell refuses
    an exhibited witness. The point is that the caller never chose that type:
    they said `eliminate(y)`, and the refusal followed.
    """
    op = O.eliminate("M_HYP", ["y"], "M_IMG", RING, HYP)
    assert op.events[1]["type"] == K.IMAGE_CLOSURE
    assert op.events[0]["ring_vars"] == ["x"], (
        "the target lives in the ring the eliminated variables left behind")

    g = _fold(
        [{"ev": "model", "id": "M_HYP", "what": "the hyperbola xy=1",
          "ring_vars": RING, "generators": HYP}]
        + op.events
        + [{"ev": "claim", "id": "C", "model": "M_IMG", "kind": K.NONEMPTY,
            "statement": "x=0 is a point of the closure",
            "witness_kind": "EXHIBITED", "established_by": "RAN",
            "ladder": "exact-checked"},
           {"ev": "inference", "id": "I", "claim": "C",
            "path": [["E-M_IMG", K.AGAINST]], "concludes_kind": K.NONEMPTY,
            "asserted": "so the hyperbola has a point with x = 0"}])

    refused = [f for f in C.run(g) if f.rule == C.R_TRANSPORT]
    assert refused, (
        "a closure point read as a source witness is Chevalley, and the "
        "edge the constructor chose exists to refuse it")


def test_eliminating_everything_is_refused():
    """A projection onto no variables has no target model, and returning one
    would be a confident answer about nothing."""
    with pytest.raises(ValueError) as exc:
        O.eliminate("M", ["x", "y"], "M2", RING, HYP)
    assert "no variables" in str(exc.value)


@pytest.mark.parametrize("make", [
    lambda: O.localize("M", "y", "M2", RING, HYP),
    lambda: O.saturate_closure("M", "y", "M2", RING, HYP),
    lambda: O.eliminate("M", ["y"], "M2", RING, HYP),
])
def test_every_constructor_emits_a_foldable_graph(make):
    """The events go through the ORDINARY write path, where every existing
    guard still applies. A constructor that emitted something the store
    refuses would be a second, weaker door into the graph."""
    op = make()
    g = _fold([{"ev": "model", "id": "M", "what": "the source",
                "ring_vars": RING, "generators": HYP}] + op.events)
    assert "M2" in g.models
    assert len(g.edges) == 1
    assert op.program.text.startswith("ring GP_R")
    assert op.verify_hint


# ===========================================================================
# A COMPUTED IDEAL, BEFORE IT HAS BEEN COMPUTED.
#
# `saturate_closure` and `eliminate` mint a model whose ideal only the CAS
# knows.  Both used to put a PLACEHOLDER STRING in `generators` -- literally
# `<saturation of M at f>` -- and every layer above believed it: `gp check`
# reported "both models carry ideals, so the containment is CHECKABLE", and
# `gp verify` handed the placeholder to Singular and relayed `expected
# ideal-expression`.  Two layers agreed the graph was fine and the third
# failed to parse.
#
# Found by running the constructor through its own documented flow.  No test
# had ever done that: this file asserted on `program.text` and stopped.
# ===========================================================================
def _pending_graph(op, src_generators=("x*y",)):
    return _fold([
        {"ev": "model", "id": "M_A", "what": "the source",
         "ring_vars": RING, "generators": list(src_generators)},
    ] + op.events + [
        {"ev": "claim", "id": "CL", "model": op.events[0]["id"],
         "kind": "IDENTITY", "statement": "y = 0 there",
         "lhs": "y", "rhs": "0", "ring_vars": RING,
         "identity_origin": "DERIVED"},
    ])


def test_constructors_emit_no_generator_that_is_not_a_polynomial():
    """The placeholder went to the solver verbatim.  It must not exist."""
    for op in (O.saturate_closure("M_A", "x", "M_S", RING, ["x*y"]),
               O.eliminate("M_A", ["y"], "M_E", RING, ["x*y"])):
        model = op.events[0]
        assert "generators" not in model, (
            "%s still declares generators it cannot know" % op.kind)
        assert model["ideal_pending"], (
            "%s drops the ideal without saying what will fill it" % op.kind)


def test_execute_materializes_a_pending_ideal_without_writing():
    op = O.saturate_closure("M_A", "x", "M_S", RING, ["x*y"])

    def fake(program, timeout):
        assert program.outputs == ["GP_OUT"]
        return {"aborted": False, "returncode": 0, "stderr": "",
                "stdout": _completed(
                    program, "@@GP_OUT:\nGP_OUT[1]=y\nGP_OUT[2]=x+1\n"
                )}

    done = O.execute(op, timeout=17, _runner=fake)
    assert op.events[0].get("ideal_pending"), (
        "execution mutated the plain constructor value in place")
    assert "ideal_pending" not in done.events[0]
    assert done.events[0]["generators"] == ["y", "x+1"]
    assert "gp verify" in done.verify_hint
    assert len(done.artifacts) == 1
    artifact = done.artifacts[0]
    assert artifact.program_text == op.program.execution_text(
        artifact.completion_nonce
    )

    graph = _fold([
        {"ev": "model", "id": "M_A", "what": "source",
         "ring_vars": RING, "generators": ["x*y"]},
    ] + done.events)
    assert graph.models["M_S"]["generators"] == ["y", "x+1"]


def test_elimination_output_is_round_trippable_through_the_verifier():
    """W8: Singular compact printing changed mathematics at the boundary.

    Default ``short=1`` printed x^3-x*y as ``x3-xy``. The constructor stored
    that string, then the verifier correctly parsed x3 and xy as identifiers
    and incorrectly declared a sound elimination unsound. This fake runner
    behaves like Singular on both sides of the setting, so removing short=0
    recreates the live failure instead of merely asserting on program text.
    """
    from grandportage import verify as V

    op = O.eliminate("M_A", ["z"], "M_E", ["x", "y", "z"],
                     ["z", "x*(y-x^2)"])

    def singular_like(program, timeout):
        rendered = "x^3-x*y" if "short=0;" in program.text else "x3-xy"
        return {"aborted": False, "returncode": 0, "stderr": "",
                "stdout": _completed(
                    program, "@@GP_OUT:\nGP_OUT[1]=%s\n" % rendered
                )}

    done = O.execute(op, _runner=singular_like)
    assert done.events[0]["generators"] == ["x^3-x*y"]
    done.events[0]["characteristic"] = 0

    graph = _fold([
        {"ev": "model", "id": "M_A", "what": "source",
         "characteristic": 0, "ring_vars": ["x", "y", "z"],
         "generators": ["z", "x*(y-x^2)"]},
    ] + done.events)

    def membership(program, timeout):
        if program.outputs == ["GP_RED"]:
            stdout = "@@GP_RED:\n0\n"
        else:
            assert program.outputs == ["GP_M"]
            stdout = "@@GP_M:\nGP_M[1,1]=0\nGP_M[2,1]=-1\n"
        return {"aborted": False, "returncode": 0, "stderr": "",
                "stdout": _completed(program, stdout)}

    verdict, why, certificate = V.operation_output(
        graph, "E-M_E", _runner=membership)
    assert verdict == V.OP_SOUND, why
    assert certificate["targets"] == ["x^3-x*y"]


def test_execute_treats_the_zero_ideal_as_no_generators():
    op = O.eliminate("M_A", ["y"], "M_E", RING, ["x*y"])

    def fake(program, timeout):
        return {"aborted": False, "returncode": 0, "stderr": "",
                "stdout": _completed(program, "@@GP_OUT:\nGP_OUT[1]=0\n")}

    assert O.execute(op, _runner=fake).events[0]["generators"] == []


def test_operations_reject_an_artifact_attached_to_a_different_program():
    from grandportage import cas

    def fake(program, _timeout):
        return {"aborted": False, "returncode": 0, "stderr": "",
                "stdout": _completed(program, "@@GP_OUT:\nGP_OUT[1]=y\n")}

    backend = cas.SingularBackend(runner=fake, binary_version="test")
    op = O.saturate_closure("M_A", "x", "M_S", RING, ["x*y"])
    honest_saturate = backend.saturate

    def mismatched_saturate(*args, **kwargs):
        answer = honest_saturate(*args, **kwargs)
        answer["program"] = O.localize(
            "M_A", "x", "M_OPEN", RING, ["x*y"]).program
        return answer

    backend.saturate = mismatched_saturate
    with pytest.raises(ValueError, match="different program"):
        O.execute(op, backend=backend)

    backend = cas.SingularBackend(runner=fake, binary_version="test")
    executed_program = op.program
    reported_program = O.localize(
        "M_A", "x", "M_OPEN", RING, ["x*y"]).program

    def mismatched_decomposition(*_args, **_kwargs):
        execution = backend.execute(executed_program)
        return {"pieces": [["x"], ["y"]], "program": reported_program,
                "execution": execution}

    backend.factorizing_decomposition = mismatched_decomposition
    with pytest.raises(ValueError, match="different program"):
        O.decompose("M_A", RING, ["x*y"], backend=backend)


def test_pending_ideal_is_not_the_ambient_space():
    """THE FIX THAT WOULD HAVE BEEN WORSE THAN THE BUG.

    Just dropping `generators` looks like the obvious repair, and it is a FALSE
    LICENCE.  An absent ideal already MEANS something to `verify.identity`: the
    SOS Gram case, "the model imposes no equations", where the reduction is
    read in the polynomial ring and can come back VERIFIED_AMBIENT.  A model
    waiting on a saturation would then have licensed an AMBIENT origin -- the
    strongest origin there is, the one that transports everywhere -- computed
    against an ideal nobody had ever computed.

    So this asserts the verdict is UNVERIFIED and that THE SOLVER IS NEVER
    CALLED: the question is refused before it is asked, not answered wrongly.
    """
    from grandportage import verify as V

    def never(prog, timeout):
        raise AssertionError("the CAS was called for a model with no ideal")

    g = _pending_graph(O.saturate_closure("M_A", "x", "M_S", RING, ["x*y"]))
    verdict, why = V.identity(g, "CL", _runner=never)
    assert verdict == V.UNVERIFIED, verdict
    assert "waiting on" in why and "saturation" in why


def test_check_does_not_say_a_pending_model_carries_an_ideal():
    """CONTAINMENT's sentence was false, and its DISCHARGE was a dead end.

    It read the placeholder as an ideal, said so, and sent the author to
    `gp verify` to reduce modulo something that did not exist.
    """
    g = _pending_graph(O.saturate_closure("M_A", "x", "M_S", RING, ["x*y"]))
    findings = C.run(g)
    rules = {f.rule for f in findings}
    assert C.R_PENDING_IDEAL in rules
    assert C.R_CONTAINMENT not in rules, (
        "containment still claims a pending model carries an ideal")
    pending = [f for f in findings if f.rule == C.R_PENDING_IDEAL][0]
    assert "M_S" in pending.detail and "saturation" in pending.detail
    # The blocked objects are named, so the reader knows what is waiting.
    assert "CL" in pending.detail and "E-M_S" in pending.detail
    assert "RELICENSE" in pending.discharge
    assert "AMEND" not in pending.discharge
    assert "--run --declare" in pending.discharge



def test_untested_identity_stops_promising_one_solver_call():
    """Same class of false sentence, one rule over.

    "the answer is one solver call away" is true of the common case and was
    asserted unconditionally.
    """
    g = _pending_graph(O.saturate_closure("M_A", "x", "M_S", RING, ["x*y"]))
    untested = [f for f in C.run(g)
                if f.rule == C.R_IDENTITY and "untested" in f.fid]
    assert untested, "the identity stopped being reported at all"
    assert "HAS NOT BEEN COMPUTED YET" in untested[0].detail
    assert "the answer is one solver call away" not in untested[0].detail


def test_store_refuses_an_ideal_that_is_both_known_and_waiting():
    """Two contradictory states, refused rather than resolved by precedence."""
    with pytest.raises(S.GraphError) as e:
        _fold([{"ev": "model", "id": "M", "what": "m", "ring_vars": RING,
                "generators": ["x"], "ideal_pending": "a saturation"}])
    assert "contradictory" in str(e.value)


def test_store_refuses_a_pending_marker_that_says_nothing():
    """"Something is missing" without "what" is not a record of anything."""
    with pytest.raises(S.GraphError) as e:
        _fold([{"ev": "model", "id": "M", "what": "m", "ring_vars": RING,
                "ideal_pending": "   "}])
    assert "WHAT WILL FILL IT" in str(e.value)


@pytest.mark.live
def test_an_operations_program_actually_runs(tmp_path):
    """NO TEST HAD EVER RUN ONE, and that is how the placeholder survived.

    Everything above this line asserts on `program.text` -- that it starts with
    `ring GP_R` -- which is satisfied by a program that cannot execute.  The
    same gap hid a worse one before it: `saturate_closure` first emitted
    `sat(GP_I,GP_F)[1]`, whose symbol lives in `elim.lib`, and `LIB` is in the
    dialect's FORBIDDEN set.  That constructor could never have run at all, and
    a live campaign found it by trying to use it rather than a test by
    exercising it.

    So run it, on the case with a known answer.  Saturating (xy) at x removes
    the component inside V(x) and leaves (y).

    ALSO PINS THE IDENTITY THE PROGRAM RESTS ON, since `sat` is unavailable:

        I : f^oo  =  (I + (1 - t*f)) inter R,  eliminating t
    """
    from grandportage import cas

    op = O.saturate_closure("M_A", "x", "M_SAT", RING, ["x*y"])
    e = op.events[1]
    out = cas.run_cas(
        op.program,
        edge={"src": e["src"], "type": e["type"], "map_kind": e["map_kind"],
              "why": e["why"]},
        produces="M_SAT", describes="the closure of the locus where x != 0",
        root=str(tmp_path), timeout=120)

    assert out["verdict"] == "OK", out.get("stderr") or out.get("stdout")
    assert out["values"]["GP_OUT"].strip() == "GP_OUT[1]=y", (
        "saturating (xy) at x must give (y); got %r"
        % out["values"]["GP_OUT"])


@pytest.mark.live
def test_real_singular_elimination_output_round_trips_through_verifier():
    """The exact W8 compact-polynomial failure, against the real CAS."""
    from grandportage import verify as V

    op = O.eliminate("M_A", ["z"], "M_E", ["x", "y", "z"],
                     ["z", "x*(y-x^2)"])
    done = O.execute(op, timeout=120)
    assert done.events[0]["generators"] == ["x^3-x*y"]
    graph = _fold([
        {"ev": "model", "id": "M_A", "what": "source",
         "characteristic": 0, "ring_vars": ["x", "y", "z"],
         "generators": ["z", "x*(y-x^2)"]},
    ] + done.events)
    verdict, why, certificate = V.operation_output(
        graph, "E-M_E", timeout=120)
    assert verdict == V.OP_SOUND, why
    assert certificate["targets"] == ["x^3-x*y"]


# ===========================================================================
# DECOMPOSE: a cover that carries its own completeness proof.
#
# `facstd` is a KERNEL BUILTIN and reachable; `primdecGTZ`, `minAssGTZ` and
# `radical` are not -- all three live in primdec.lib, the same wall `sat` hit.
# That had to be settled by PROBING before any vocabulary was designed around a
# decomposition, and it is the reason this constructor exists at all.
#
# What comes back is a COVER: V(I) = union V(I_j), each I_j containing I. That
# is exactly a partition, and exactly what verify.partition_exhaustiveness
# decides -- so the constructor gets its own proof for free.
# ===========================================================================
def test_decompose_is_a_partition_whose_branches_were_minted():
    """No new edge type. Every piece is `parent AND more equations`, which is
    NECESSARY_CONDITION -- the same relation an author would have typed by hand,
    derived instead."""
    op = O.decompose("M", RING, ["x*y*(x-1)"], _runner=_facstd_runner())
    kinds = [e["ev"] for e in op.events]
    assert kinds.count("model") == 3
    assert kinds.count("edge") == 3
    assert kinds.count("partition") == 1
    assert all(e["type"] == K.NECESSARY_CONDITION
               for e in op.events if e["ev"] == "edge")


def test_decompose_reports_the_exact_program_that_was_run():
    """The operation artifact and CAS execution share one provenance object."""
    seen = []

    def runner(prog, timeout):
        seen.append(prog)
        stdout = ("@@GP_L:\n[1]:\n   _[1]=y\n"
                  "[2]:\n   _[1]=x\n")
        return {"aborted": False, "returncode": 0, "stderr": "",
                "stdout": _completed(prog, stdout)}

    op = O.decompose("M", RING, ["x*y"], _runner=runner)
    assert len(seen) == 1
    assert op.program is not seen[0]
    assert len(op.artifacts) == 1
    assert op.artifacts[0].program_text == seen[0].text
    assert op.artifacts[0].program_text == op.program.execution_text(
        op.artifacts[0].completion_nonce
    )


def test_every_minted_component_carries_its_own_ideal():
    """THE #37 DESIGN, in the one place it can be enforced without a migration:
    anything a constructor mints carries its algebra by construction, so the
    checkable fraction of a graph rises over time instead of needing a
    backfill."""
    op = O.decompose("M", RING, ["x*y*(x-1)"], _runner=_facstd_runner())
    for e in op.events:
        if e["ev"] == "model":
            assert e["generators"], "%s was minted without an ideal" % e["id"]
            assert e["component_of"] == "M"


def test_the_completeness_premise_is_minted_as_a_decidable_claim():
    """A partition needs an `exhaustive` claim or the graph will not fold, and
    until `verify.partition_exhaustiveness` existed that claim was prose. This
    one is RAN, and a verifier re-decides it from the recorded ideals rather
    than trusting the tool that produced them."""
    op = O.decompose("M", RING, ["x*y*(x-1)"], _runner=_facstd_runner())
    claim = [e for e in op.events if e["ev"] == "claim"][0]
    part = [e for e in op.events if e["ev"] == "partition"][0]
    assert part["exhaustive"] == claim["id"]
    assert claim["established_by"] == "RAN"
    assert set(part["branches"]) == {
        e["id"] for e in op.events if e["ev"] == "model"}


def test_an_ideal_that_does_not_factor_emits_nothing():
    """"A split into one piece is just the parent" -- the store's own words,
    refusing a one-branch partition. So this returns NO EVENTS rather than a
    degenerate one, and says so.

    It is NOT a proof of irreducibility. `facstd` gives a cover and nothing
    inside this boundary decides primality.
    """
    op = O.decompose("M", RING, ["y^2-x^3-x^2"],
                     _runner=_facstd_runner(["[1]:", "   _[1]=x3+x2-y2"]))
    assert op.events == []
    assert "did not factor" in op.derivation
    assert "NOT a proof" in op.derivation


def _facstd_runner(rows=None):
    rows = rows or ["[1]:", "   _[1]=y", "[2]:", "   _[1]=x-1",
                    "[3]:", "   _[1]=x"]
    def run(prog, timeout):
        stdout = "@@GP_L:\n%s\n" % "\n".join(rows)
        return {"aborted": False, "returncode": 0, "stderr": "",
                "stdout": _completed(prog, stdout)}
    return run


@pytest.mark.live
def test_a_minted_cover_verifies_exhaustive(tmp_path):
    """THE CLAIM UNDER TEST is one written into a docstring: that a cover minted
    by `facstd` verifies exhaustive BY CONSTRUCTION. That is a justification,
    and this project's recurring defect is justifications that generalize one
    case too far -- so it gets run rather than asserted.

    Three lines and a circle, so the pieces differ in degree and the answer is
    not an artifact of a uniform split.
    """
    from grandportage import verify as V
    gens = ["x*y*(x-1)*(x^2+y^2-1)"]
    op = O.decompose("M", RING, gens, timeout=120)
    g = _fold([{"ev": "model", "id": "M", "what": "three lines and a circle",
                "characteristic": 0, "ring_vars": RING,
                "generators": gens}] + op.events)
    assert len(g.models) == 5
    verdict, why = V.partition_exhaustiveness(g, "P-M", timeout=120)
    assert verdict == V.COVERS, why
    for eid in g.edges:
        assert V.containment(g, eid, timeout=120)[0] == V.VERIFIED, eid


def test_elimination_rejects_duplicate_variables_before_execution():
    with pytest.raises(ValueError, match="must be unique"):
        O.eliminate("M0", ["y", "y"], "M1", ["x", "y"], ["x+y"])

def test_declared_computed_operation_publishes_auditable_raw_artifact(
        tmp_path, monkeypatch, capsys):
    root = str(tmp_path)
    S.append([{
        "coefficient_domain": "Q",
        "point_universe": S.ALGEBRAIC_CLOSURE_POINT_UNIVERSE,
        "ev": "model", "id": "M", "what": "source",
        "characteristic": 0, "ring_vars": ["x", "y"],
        "generators": ["x*y"],
    }], root)
    real_execute = O.execute

    def fake_runner(program, _timeout):
        return {
            "aborted": False, "returncode": 0, "stderr": "",
            "stdout": _completed(program, "@@GP_OUT:\nGP_OUT[1]=x\n"),
        }

    def execute_with_fake(op, timeout=300):
        return real_execute(op, timeout=timeout, _runner=fake_runner)

    monkeypatch.setattr(O, "execute", execute_with_fake)
    assert cli.main([
        "--root", root, "construct", "eliminate", "--src", "M",
        "--vars", "y", "--produces", "IMG", "--run", "--declare",
    ]) == 0

    graph = S.load(S.graph_path(root))
    assert graph.models["IMG"]["coefficient_domain"] == "Q"
    assert graph.models["IMG"]["point_universe"] == "ALGEBRAIC_CLOSURE"

    references = [
        A.note_reference(note.get("source")) for note in graph.notes
        if A.note_reference(note.get("source")) is not None
    ]
    assert len(references) == 1
    stored = A.load(root, references[0]["artifact_fingerprint"])
    assert stored["program_fingerprint"] == references[0]["program_fingerprint"]
    assert A.audit_graph(root, graph) == []

    capsys.readouterr()
    assert cli.main([
        "--graph", S.graph_path(root), "artifacts", "check",
    ]) == 0
    assert "1 execution reference checked" in capsys.readouterr().out
