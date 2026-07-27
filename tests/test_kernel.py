"""Properties of the transport table itself, independent of any domain.

These are the checks that would fail if someone "simplified" the table.  They
are written to be non-vacuous: several assert that a cell is FALSE, which is
the direction a lazily-written test never covers.
"""

import itertools

import pytest

from grandportage import kernel as K


def test_table_is_total():
    """Every (type, direction, kind) has a rule.  No silent KeyError path."""
    for t, d, k in itertools.product(K.DECLARABLE_TYPES, K.DIRECTIONS,
                                     K.CLAIM_KINDS):
        assert k in K.TRANSPORT[t][d], (t, d, k)


def test_equivalence_forbids_nothing_about_points():
    """If it forbade anything about POINTS it would not be an equivalence.

    IDENTITY is deliberately excluded, and the exclusion is the point.  The
    evidence that earns an EQUIVALENCE is a converse -- a construction
    recovering a point of the source from a point of the target -- which is a
    statement about points.  An identity is a statement about functions, and a
    bijection on points is not an isomorphism of coordinate rings.  So IDENTITY
    is conditional on `ring_iso` while every point-level cell stays
    unconditional.
    """
    for d, k in itertools.product(K.DIRECTIONS, K.CLAIM_KINDS):
        if k == K.IDENTITY:
            continue
        assert K.TRANSPORT[K.EQUIVALENCE][d][k] is True


def test_equivalence_licenses_identity_only_across_a_ring_isomorphism():
    """COUNTEREXAMPLE, and it is reachable rather than exotic.

    V(x^2) and V(x) have exactly the same solutions -- the single point 0 --
    so any converse you like exists.  But `x = 0` is a valid rewriting in
    k[x]/(x) and FALSE in k[x]/(x^2), where x is not zero; that is the whole
    content of a double root.  Saturation and radicalization are precisely this
    step, and `sat(I, nz)` is in this repository's own CAS helper, so "the
    solutions are unchanged" is a natural and honest EQUIVALENCE declaration
    that does not preserve the ring.

    Verified against Singular in test_live_front.py: classifying `x = 0` gives
    DERIVED at V(x) and FALSE_AT_MODEL at V(x^2).
    """
    for d in K.DIRECTIONS:
        assert not K.transport(K.EQUIVALENCE, d, K.IDENTITY,
                               identity_origin=K.AMBIENT).licensed
        assert K.transport(K.EQUIVALENCE, d, K.IDENTITY,
                           ring_iso=True).licensed


def test_every_lossy_type_forbids_something_outright():
    """A type that forbids nothing unconditionally is EQUIVALENCE in disguise."""
    for t in K.LOSSY_TYPES:
        cells = [K.TRANSPORT[t][d][k]
                 for d, k in itertools.product(K.DIRECTIONS, K.CLAIM_KINDS)]
        assert any(c is False for c in cells), t


def test_all_types_have_distinct_signatures():
    """No type is another wearing a different name."""
    seen = {}
    for t in K.ALL_TYPES:
        sig = K.signature(t)
        assert sig not in seen, "%s and %s have the same table" % (t, seen[sig])
        seen[sig] = t


def test_base_extension_reverses_the_asymmetry():
    """The cell that made the shipped erratum possible.

    NECESSARY_CONDITION carries EMPTY freely AGAINST and refuses NONEMPTY.
    BASE_EXTENSION does the OPPOSITE along its arrow: NONEMPTY travels freely
    (a k-point IS a K-point) and EMPTY needs a certificate.  Anyone who
    internalised "emptiness always transports" was primed to get this backwards.
    """
    nc = K.TRANSPORT[K.NECESSARY_CONDITION]
    be = K.TRANSPORT[K.BASE_EXTENSION]
    assert nc[K.AGAINST][K.EMPTY] is True
    assert nc[K.AGAINST][K.NONEMPTY] is False
    assert be[K.ALONG][K.NONEMPTY] is True
    assert be[K.ALONG][K.EMPTY] is not True      # conditional, not free


def test_specialization_is_maximally_lossy():
    """MATROID_TRANSFER.md sec.3 pins this signature with four counterexamples:
    Fano is EMPTY over Q and NONEMPTY over F_2; non-Fano is the reverse.  So
    all four existence cells are falsified and the type must carry nothing."""
    sp = K.TRANSPORT[K.SPECIALIZATION]
    for d, k in itertools.product(K.DIRECTIONS, (K.EMPTY, K.NONEMPTY)):
        assert sp[d][k] is False, (d, k)


def test_no_inherited_type_could_have_carried_the_characteristic_change():
    """The argument that forced the fifth type, re-run as a test.

    Every type that predates SPECIALIZATION licenses NONEMPTY unconditionally
    in at least one direction, and the characteristic change licenses it in
    neither.  So the step was untyped (silent) or mistyped (unsound), and both
    are coverage failures.
    """
    inherited = (K.EQUIVALENCE, K.NECESSARY_CONDITION, K.BASE_EXTENSION,
                 K.IMAGE_CLOSURE)
    for t in inherited:
        assert any(K.TRANSPORT[t][d][K.NONEMPTY] is True
                   for d in K.DIRECTIONS), t
    assert all(K.TRANSPORT[K.SPECIALIZATION][d][K.NONEMPTY] is False
               for d in K.DIRECTIONS)


def test_untyped_licenses_nothing():
    for d, k in itertools.product(K.DIRECTIONS, K.CLAIM_KINDS):
        r = K.transport(K.UNTYPED, d, k, scope=K.SCHEME,
                        map_kind=K.POLYNOMIAL, zariski_closed=True)
        assert not r.licensed


# -- scope derivation -------------------------------------------------------

def test_scope_derivation_exercises_both_branches():
    assert K.derive_scope(K.EMPTY, "UNIT_IDEAL_CERT", None) == K.SCHEME
    assert K.derive_scope(K.EMPTY, "NONSQUARE_CLASS", "R") == "R"


def test_field_relative_certificate_cannot_declare_scheme_scope():
    """Making the safe path the ONLY path: this is an error, not a finding.

    A claim asserting field-independence on the strength of a field-relative
    certificate is a malformed claim.  Letting it into the graph and flagging
    it later would mean the graph itself records something false.
    """
    with pytest.raises(K.ScopeError):
        K.derive_scope(K.EMPTY, "NONSQUARE_CLASS", K.SCHEME)
    with pytest.raises(K.ScopeError):
        K.derive_scope(K.EMPTY, "NONSQUARE_CLASS", None)


def test_emptiness_without_a_certificate_is_refused():
    with pytest.raises(K.ScopeError):
        K.derive_scope(K.EMPTY, None, "Q")


def test_unknown_certificate_is_refused():
    with pytest.raises(K.ScopeError):
        K.derive_scope(K.EMPTY, "VIBES", "Q")


def test_nonemptiness_keeps_its_declared_scope():
    assert K.derive_scope(K.NONEMPTY, None, "R") == "R"


# -- the robustness property WHETSTONE_DAG.md sec.6 item 3 ------------------

def test_field_relative_emptiness_refused_under_every_lossy_typing():
    """The detection survives MIS-typing the edge.

    A field-relative emptiness pushed ALONG is refused whether the step is
    typed NECESSARY_CONDITION, BASE_EXTENSION, IMAGE_CLOSURE or SPECIALIZATION.
    It only requires the step to be typed lossy at all.
    """
    for t in K.LOSSY_TYPES:
        r = K.transport(t, K.ALONG, K.EMPTY, scope="Q(sqrt 17)",
                        certificate="NONSQUARE_CLASS")
        assert not r.licensed, t


def test_the_refusal_is_not_unconditional():
    """...and the same probe on a certificate-backed emptiness IS licensed
    across BASE_EXTENSION.  Without this, the test above proves only that the
    kernel refuses everything."""
    r = K.transport(K.BASE_EXTENSION, K.ALONG, K.EMPTY, scope=K.SCHEME,
                    certificate="UNIT_IDEAL_CERT")
    assert r.licensed


def test_identity_transport_turns_on_the_map_AND_where_the_identity_CAME_FROM():
    """This test used to be called `..._turns_on_the_map_and_nothing_else`, and
    that name was the bug.  It asserted the unsound cell as its oracle.

    Denominator-freeness is a property of the MAP -- whether substituting
    produces fractions.  Whether an identity SURVIVES is a property of where the
    identity came from, and the two are independent.  The old rule licensed
    `x = 0` escaping from V(x) to the whole affine line, because the inclusion
    map is perfectly denominator-free.

    Both conditions are needed, so both are exercised here.
    """
    ok = K.transport(K.NECESSARY_CONDITION, K.ALONG, K.IDENTITY,
                     map_kind=K.POLYNOMIAL, identity_origin=K.AMBIENT)
    rat = K.transport(K.NECESSARY_CONDITION, K.ALONG, K.IDENTITY,
                      map_kind=K.RATIONAL, identity_origin=K.AMBIENT)
    derived = K.transport(K.NECESSARY_CONDITION, K.ALONG, K.IDENTITY,
                          map_kind=K.POLYNOMIAL, identity_origin=K.DERIVED)
    unknown = K.transport(K.NECESSARY_CONDITION, K.ALONG, K.IDENTITY,
                          map_kind=K.POLYNOMIAL, identity_origin=K.UNKNOWN)
    assert ok.licensed
    assert not rat.licensed, "a rational map still blocks the rewriting"
    assert not derived.licensed, (
        "x = 0 is valid in k[x]/(x) and false in k[x]; a DERIVED identity must "
        "not push forward across a step that drops equations")
    assert not unknown.licensed, (
        "UNKNOWN licenses only what BOTH origins license, so it must be at "
        "least as strict as DERIVED")


def test_identity_pulls_back_regardless_of_origin():
    """AGAINST is the direction the ring map actually points.

    Points travel tighter -> looser; functions travel looser -> tighter.  So a
    rewriting valid in the looser model restricts to the tighter one whatever
    its origin, and this cell needs no origin condition at all.
    """
    for origin in K.IDENTITY_ORIGINS:
        assert K.transport(K.NECESSARY_CONDITION, K.AGAINST, K.IDENTITY,
                           map_kind=K.POLYNOMIAL,
                           identity_origin=origin).licensed, origin


def test_closure_predicate_transport_turns_on_zariski_closed():
    closed = K.transport(K.IMAGE_CLOSURE, K.ALONG, K.PREDICATE,
                         zariski_closed=True)
    open_ = K.transport(K.IMAGE_CLOSURE, K.ALONG, K.PREDICATE,
                        zariski_closed=False)
    assert closed.licensed and not open_.licensed


def test_known_conservatism_is_recorded_not_hidden():
    """Cells refused more strictly than the mathematics requires are DATA.

    Removing one must be a deliberate act, and "we refuse this soundly" must
    never be confused with "we refuse this out of caution".
    """
    from grandportage.discharge import KNOWN_CONSERVATISM
    assert KNOWN_CONSERVATISM
    for entry in KNOWN_CONSERVATISM:
        t, d, k = entry["cell"]
        assert K.TRANSPORT[t][d][k] is entry["kernel_says"]
        assert entry["why_kept"]


def test_an_unjustified_equivalence_is_reported():
    """EQUIVALENCE is the only type that forbids nothing, so one mistyped row
    licenses every transport across that step in both directions.  An
    EQUIVALENCE resting on neither a witness nor a citation is a claim resting
    on the author's confidence."""
    from grandportage import check as C
    import helpers as H
    bare = H.mutate("jc2", H.set_field("edge", "E3", cite="", witness=""))
    ids = {f.fid for f in C.run(bare)}
    assert "UNJUSTIFIED-EQUIVALENCE:E3" in ids


def test_a_documented_equivalence_is_not_reported():
    """Both real fixtures type a step EQUIVALENCE and both cite where the
    converse is proved.  Flagging those would make the rule noise."""
    from grandportage import check as C
    import helpers as H
    for domain in H.DOMAINS:
        rules = {f.rule for f in C.run(H.load(domain))}
        assert "UNJUSTIFIED-EQUIVALENCE" not in rules, domain
