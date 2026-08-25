"""GP030: field-relative EMPTY scope must name a field, not any string.

Two independent CFG23 scratch assays found that a field-relative EMPTY claim
(a certificate that does not base-change: NONSQUARE_CLASS, CITED_PROOF, ...)
accepted an arbitrary `scope` string -- "ALL_FIELDS", "banana" -- with no
structural refusal.  `derive_scope` (grandportage/kernel.py) checked only
that the value was neither `None` nor `SCHEME`; anything else was folded
straight into the graph as though it named a field.

The repair adds `K.valid_field_scope`, a closed grammar (atomic Q/R/C, a
finite field F_p for prime p, or a simple extension Q(...)/R(...)) consulted
at the one place a field-relative EMPTY claim's scope is derived.  Because
`derive_scope` runs inside `Graph._apply_claim`, and every declaration, every
persisted-graph read (native or legacy epoch-0), and every migration folds
through that same method, this single check closes all three surfaces at
once -- see `test_malformed_historical_graph_scope_is_refused_on_read` and
`test_migration_cannot_launder_a_malformed_scope` below.

`scope` on NONEMPTY, and on any other claim kind, is deliberately left as it
was: NONEMPTY's scope is prose no transport rule consults, and `scope` is
tracked generically as one of `LICENSING_FIELDS` for supersession-staleness
grading regardless of claim kind (see test_adversarial.py's
`test_a_superseded_premise_is_graded_by_what_actually_changed`, which
declares `scope` on a PREDICATE claim on purpose).  Restricting scope to only
EMPTY/NONEMPTY was tried while building this fix and broke that legitimate,
pre-existing use; it is not repeated here as a lesson to future readers.
"""

import json
import os

import pytest

from grandportage import format as F
from grandportage import kernel as K
from grandportage import migration as MIG
from grandportage import store as S

import helpers as H


MODEL_A = {"ev": "model", "id": "A", "desc": "a"}


def _empty_claim(scope, claim_id="CL", certificate="NONSQUARE_CLASS"):
    return {"ev": "claim", "id": claim_id, "model": "A", "kind": K.EMPTY,
            "statement": "no rational point", "certificate": certificate,
            "scope": scope}


# -- 1. every currently-accepted value keeps working -------------------------

@pytest.mark.parametrize("scope", ["Q", "R", "C", "F_2", "F_3", "F_101",
                                    "Q(sqrt 17)", "Q(sqrt(-3))", "R(sqrt 2)"])
def test_every_currently_documented_empty_scope_is_still_accepted(scope):
    assert K.derive_scope(K.EMPTY, "NONSQUARE_CLASS", scope) == scope


@pytest.mark.parametrize("scope", ["R", "C", "F_2", "Q(sqrt(-3))",
                                    "combinatorial", "banana"])
def test_nonemptiness_scope_remains_undevalidated_prose(scope):
    """NONEMPTY's scope is not consulted by any transport rule (only
    (BASE_EXTENSION, ALONG, EMPTY) reads `scope`), so it stays exactly the
    free-form label it always was -- including `combinatorial`, live in the
    matroid fixture on `CM-NP-ORIENTABLE`, which names no field at all."""
    assert K.derive_scope(K.NONEMPTY, None, scope) == scope


def test_full_fold_accepts_every_field_relative_scope_shape_in_live_fixtures():
    for scope in ("Q", "R", "F_2", "Q(sqrt 17)"):
        g = H.fold([MODEL_A, _empty_claim(scope)])
        assert g.claims["CL"]["scope"] == scope


# -- 2. unknown strings are refused, at the same boundary as SCHEME/None -----

@pytest.mark.parametrize("scope", [
    "banana", "ALL_FIELDS", "over Q", "everywhere", "Qbar",
    "F_4", "F_1", "F_0", "F_-2", "F_", "F_02", "F_4294967311",
    "F_" + "9" * 5000,
    "Q()", "R( )", "Qsqrt17", "(Q)",
    "Q(" + "x" * 256 + ")",
])
def test_unrecognized_scope_string_is_refused(scope):
    with pytest.raises(K.ScopeError, match="does not recognize"):
        K.derive_scope(K.EMPTY, "NONSQUARE_CLASS", scope)


def test_unrecognized_scope_is_refused_at_full_fold_time_too():
    with pytest.raises(K.ScopeError, match="does not recognize"):
        H.fold([MODEL_A, _empty_claim("banana")])


# -- 3. missing / null scope on a field-relative certificate ------------------

def test_missing_scope_on_field_relative_certificate_is_refused():
    with pytest.raises(K.ScopeError):
        K.derive_scope(K.EMPTY, "NONSQUARE_CLASS", None)


def test_null_scope_at_full_fold_is_refused():
    events = [MODEL_A,
              {"ev": "claim", "id": "CL", "model": "A", "kind": K.EMPTY,
               "statement": "empty", "certificate": "NONSQUARE_CLASS",
               "scope": None}]
    with pytest.raises(K.ScopeError):
        H.fold(events)


# -- 4. case drift -------------------------------------------------------------

@pytest.mark.parametrize("scope", ["q", "r", "c", "scheme", "SCHEME ",
                                    " SCHEME", "f_2", "q(sqrt 17)"])
def test_case_or_whitespace_drift_is_refused(scope):
    with pytest.raises(K.ScopeError):
        K.derive_scope(K.EMPTY, "NONSQUARE_CLASS", scope)


# -- 5. scope on an inapplicable claim kind is unaffected, on purpose ---------

def test_scope_on_a_predicate_claim_remains_legal_generic_bookkeeping():
    """`scope` plays no role in PREDICATE/IDENTITY/COUNT transport, but it is
    tracked generically as a LICENSING_FIELD for supersession grading -- see
    test_adversarial.py's staleness tests, which declare it on a PREDICATE
    claim.  This defect's repair must not foreclose that: only the
    field-relative EMPTY branch gained a grammar check."""
    events = [MODEL_A,
              {"ev": "claim", "id": "CL", "model": "A", "kind": K.PREDICATE,
               "statement": "P holds", "scope": "Q(sqrt 17)"}]
    g = H.fold(events)
    assert g.claims["CL"]["scope"] == "Q(sqrt 17)"
    # Even a scope value this kernel could never accept for EMPTY is legal
    # bookkeeping prose on a claim kind the field-relative check never sees.
    events2 = [MODEL_A,
               {"ev": "claim", "id": "CL2", "model": "A", "kind": K.PREDICATE,
                "statement": "P holds", "scope": "banana"}]
    g2 = H.fold(events2)
    assert g2.claims["CL2"]["scope"] == "banana"


# -- 6. malformed historical graph: the compat (epoch-0) read path -----------

def test_malformed_historical_graph_scope_is_refused_on_read(tmp_path):
    """An unversioned (epoch-0) log with no `meta` event goes through the
    conservative compatibility importer, not the author path -- but it still
    folds through `_apply_claim`, so a malformed scope cannot be read back
    out of old history just because nobody is declaring it today."""
    path = tmp_path / "legacy.jsonl"
    events = [MODEL_A, _empty_claim("banana")]
    with open(path, "w", encoding="utf-8") as fh:
        for ev in events:
            fh.write(json.dumps(ev) + "\n")
    assert S.is_native_graph(str(path)) is False
    with pytest.raises(K.ScopeError, match="does not recognize"):
        S.load(str(path))


def test_honest_historical_graph_still_reads_clean(tmp_path):
    path = tmp_path / "legacy.jsonl"
    events = [MODEL_A, _empty_claim("Q(sqrt 17)")]
    with open(path, "w", encoding="utf-8") as fh:
        for ev in events:
            fh.write(json.dumps(ev) + "\n")
    g = S.load(str(path))
    assert g.claims["CL"]["scope"] == "Q(sqrt 17)"


# -- 7. migration cannot launder a malformed scope ----------------------------

def _old_epoch_meta():
    meta = F.meta_event()
    meta["kernel_epoch"] = F.KERNEL_EPOCH - 1
    meta["implementation"]["kernel_epoch"] = F.KERNEL_EPOCH - 1
    return meta


def test_migration_cannot_launder_a_malformed_scope(tmp_path):
    """`gp migrate --kernel-epoch` copies an older native graph forward by
    folding it through `Graph.apply_all(...).validate()` -- the same
    boundary as a fresh declaration.  A malformed scope must refuse the
    migration, not ride along into the new-epoch file."""
    source = tmp_path / "old.jsonl"
    events = [_old_epoch_meta(), MODEL_A, _empty_claim("ALL_FIELDS")]
    with open(source, "w", encoding="utf-8") as fh:
        for ev in events:
            fh.write(json.dumps(ev) + "\n")
    destination = tmp_path / "old.epoch11.jsonl"
    with pytest.raises(K.ScopeError, match="does not recognize"):
        MIG.migrate_kernel_epoch([str(source)], output=str(destination))
    assert not destination.exists(), (
        "a refused migration must not leave a laundered destination file")


def test_migration_of_an_honest_scope_still_succeeds(tmp_path):
    source = tmp_path / "old.jsonl"
    events = [_old_epoch_meta(), MODEL_A, _empty_claim("F_2")]
    with open(source, "w", encoding="utf-8") as fh:
        for ev in events:
            fh.write(json.dumps(ev) + "\n")
    destination = tmp_path / "old.epoch11.jsonl"
    report = MIG.migrate_kernel_epoch([str(source)], output=str(destination))
    assert os.path.exists(destination)
    g = S.load(str(destination))
    assert g.claims["CL"]["scope"] == "F_2"


# -- 8. a valid selected-embedding witness composes with a named field scope -

def test_valid_field_scope_composes_with_a_selected_embedding_model():
    """Field-relative scope (kernel.py's `derive_scope`) and selected-embedding
    identity (kernel.py's `_SELECTED_EMBEDDING_IDENTITY`, store.py's
    `embedding`/`point_universe`) are independent dimensions that both use the
    word "field" in prose -- exactly the conflation GP030 was asked to avoid.
    A model may select a REAL embedding over ALGEBRAIC_CLOSURE and still
    carry an EMPTY claim whose scope names an unrelated number field; neither
    validation interferes with the other."""
    events = [
        {"ev": "model", "id": "A", "desc": "a",
         "characteristic": 0, "coefficient_domain": "Q",
         "point_universe": "REAL_CLOSURE", "ring_vars": ["t"],
         "generators": ["t^2-2"],
         "embedding": {"var": "t", "kind": "REAL",
                       "isolating_interval": {"lo": "1", "hi": "2"}}},
        _empty_claim("Q(sqrt 17)"),
    ]
    g = H.fold(events)
    assert g.claims["CL"]["scope"] == "Q(sqrt 17)"
    assert g.models["A"]["point_universe"] == "REAL_CLOSURE"
    r = K.transport(K.BASE_EXTENSION, K.ALONG, K.EMPTY,
                     scope=g.claims["CL"]["scope"], certificate="NONSQUARE_CLASS")
    assert not r.licensed, (
        "a field-relative EMPTY claim must still be refused across "
        "BASE_EXTENSION regardless of the model's selected embedding")
