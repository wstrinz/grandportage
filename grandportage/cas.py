"""The CAS boundary: declare the transport, or no process is spawned.

This module is where the discipline becomes unavoidable.  Everything above it
can be ignored by an agent that simply does not run `gp check`; this cannot,
because it sits between the agent and the solver.

Three guards, each earned by a specific recorded defect rather than designed
from first principles:

1. THE TRANSPORT DECLARATION IS REQUIRED.  `run_cas` takes `edge` as a
   keyword-only argument with no default.  Omit it and you get a TypeError
   before any subprocess exists.  A computation that produces a new model
   without saying how that model relates to its source is exactly the untyped
   step the whole system exists to prevent, and the cheapest place to prevent
   it is the moment of spend.

   `{"type": "UNTYPED", "debt_why": "..."}` is a LEGAL declaration -- an
   explicitly recorded debt the checker reports.  What is not legal is silence.

2. THE IDENTIFIER ASSERT IS NON-BYPASSABLE.  `CASProgram` is the only object
   `run_cas` accepts, and its constructor validates emitted identifiers against
   the ring variables and the dialect's reserved words BEFORE the program text
   exists.  There is no string path to a solver.

   Earned by: `build_singular_program` emitting `poly g{i}` indexed by
   generator while the ansatz named its tail coefficients `g0..gz`.  The
   emitted program redefined the ring variable `g0`, so `nz` became a product
   of ideal members and `sat(I, nz)` collapsed the ideal to (1).  Result: a
   confident false EMPTY in 0.3 s at every prime, propagating to 17 rows across
   two documents and to the top-priority recommendation of one.  Contained only
   by a standing social rule that mod p is reconnaissance.

3. AN ERRORED CAS IS NOT A CAS THAT ANSWERED.  Singular reports an error, KEEPS
   GOING, prints the output markers with nothing behind them, and exits 0.  So
   exit status is not evidence, and neither is the presence of a marker.  A
   verdict is read only from a run with no `? error` line, exactly one
   parseable value per declared output, and a per-execution nonce marker as
   the final non-whitespace line.  Parseable output from a truncated or replayed
   transcript is not an answer to this invocation.

   Earned by: an `_ASSAY_` identifier prefix that was illegal because Singular
   identifiers must begin with a letter.  Reviewing the emitter would never
   have caught it; only running it did.
"""

import json
import os
import re
import secrets
import signal
import subprocess
import threading

from . import artifacts as A
from . import backend as B
from . import groebner as G
from . import kernel as K
from . import store as S


class IdentifierCollision(ValueError):
    """An emitted identifier would shadow or duplicate something."""


class CASError(RuntimeError):
    """The CAS did not answer.  Never a verdict."""


class TransportNotDeclared(TypeError):
    """A computation tried to produce a model without typing the step."""


# ---------------------------------------------------------------------------
# Dialects
# ---------------------------------------------------------------------------
SINGULAR = "singular"

DIALECTS = {
    SINGULAR: {
        # Singular identifiers must BEGIN WITH A LETTER.  This one line is the
        # whole of guard 3's prevention half.
        "identifier": re.compile(r"^[A-Za-z][A-Za-z0-9_]*$"),
        "reserved": frozenset("""
            ideal poly ring matrix module vector int intvec intmat number
            list string map proc if else while for return def qring resolution
            std groebner sat quotient reduce lift syz res kbase dim vdim
            factorize gcd lcm resultant subst size nrows ncols leadcoef
            option short printlevel basering
        """.split()),
        # The keywords that INTRODUCE a name.  A body statement beginning with
        # one of these declares an identifier that the collision check never
        # saw, which is the whole defect guard 2 claims to prevent.
        "declares": frozenset("""
            ideal poly ring matrix module vector int intvec intmat number
            list string map proc def qring resolution
        """.split()),
        # Statements that can introduce or destroy a name by other means, or
        # reach outside the process.  `execute` is the important one: it runs a
        # string as Singular source, so permitting it would reopen every path
        # this module closes.
        "forbidden": frozenset("""
            execute kill setring read write system link close open dump
            getdump load LIB quit exit
        """.split()),
        "comment": "//",
    },
}


def assert_no_identifier_collision(dialect, ring_vars, decls):
    """Validate emitted identifiers BEFORE the program text exists.

    `decls` is a list of (identifier, type, expression) TRIPLES.  Keeping the
    identifier a separate field from the text is not tidiness: it is what makes
    the check and the emitted program derive from the same data, so they cannot
    drift.  A format where the identifier must be parsed back out of a
    declaration string would reintroduce exactly the gap this guards.

    Four failure modes, and the discrimination matters: a check that rejects
    everything is worse than none, so legal programs must pass.
    """
    spec = DIALECTS[dialect]
    ring_set = set(ring_vars)
    seen = set()
    for name, _type, _expr in decls:
        if not spec["identifier"].match(name):
            raise IdentifierCollision(
                "emitted identifier %r is not valid in %s (must match %s).  "
                "An illegal identifier does not stop the run: the CAS reports "
                "an error, keeps going, prints the output markers with nothing "
                "behind them, and exits 0."
                % (name, dialect, spec["identifier"].pattern))
        if name in ring_set:
            raise IdentifierCollision(
                "emitted identifier %r SHADOWS the ring variable %r.  The "
                "declaration would redefine the variable, and any ideal "
                "operation naming it afterwards silently means something else "
                "-- this is the `poly g0 = ...` defect that manufactured false "
                "UNIT verdicts at every prime." % (name, name))
        if name in spec["reserved"]:
            raise IdentifierCollision(
                "emitted identifier %r is a %s reserved word" % (name, dialect))
        if name in seen:
            raise IdentifierCollision("identifier %r declared twice" % name)
        seen.add(name)
    return True


_FIRST_TOKEN = re.compile(r"^\s*([A-Za-z_][A-Za-z0-9_]*)")

# Types a declaration may have.  A WHITELIST, because the `type` half of a
# decl triple is interpolated into the program text exactly like the expression
# half, and it was never validated: `('GP_I', 'poly g0 = 1; ideal', 'g0')`
# emits `poly g0 = 1; ideal GP_I = g0;` and shadows the ring variable g0.
DECL_TYPES = {
    SINGULAR: frozenset("""
        ideal poly matrix module vector int intvec intmat number list string
        map def resolution
    """.split()),
}


def _strip_comments(text, dialect):
    """Remove comment tails before any statement analysis.

    `_FIRST_TOKEN` anchors at the start and fails OPEN when it does not match,
    so a leading `// anything` made every statement rule vacuous:

        body=["// harmless\\npoly g0 = 1;"]     -> accepted, shadows g0
        body=['// c\\nexecute("int GP_Z=1")']   -> accepted, and it RAN

    Stripping first is not cosmetic; it is what makes the rules apply at all.
    """
    marker = DIALECTS[dialect]["comment"]
    out = []
    for line in str(text).splitlines():
        idx = line.find(marker)
        out.append(line if idx < 0 else line[:idx])
    return "\n".join(out)


def assert_is_identifier(dialect, name, field):
    """A bare identifier, and nothing else, in a slot that is interpolated raw.

    `ring` and every entry of `ring_vars` land directly in
    `ring %s = %d,(%s),dp;` and neither was checked.  One crafted ring variable
    closes the declaration and appends arbitrary statements:

        ring_vars=['g0', 'x),dp; poly g0 = 1; int Z=1;//']

    emits a complete, valid, hostile ring line.  This reached the solver through
    the MCP tool, since `cas_ideal_is_unit` passes `ring_vars` through verbatim.
    """
    spec = DIALECTS[dialect]
    if not spec["identifier"].match(str(name)):
        raise IdentifierCollision(
            "%s must be a bare identifier matching %s, got %r.  This value is "
            "interpolated into the program text with no quoting, so anything "
            "else can close the statement it sits in and append its own."
            % (field, spec["identifier"].pattern, name))
    if str(name) in spec["reserved"]:
        raise IdentifierCollision(
            "%s is the %s reserved word %r" % (field, dialect, name))
    return True


def assert_declares_nothing(dialect, statements, field):
    """No statement outside `decls` may introduce or destroy an identifier.

    THIS IS THE HALF OF GUARD 2 THAT WAS MISSING, and its absence made the
    module's own headline claim -- "there is no string path to a solver" --
    false.  `assert_no_identifier_collision` validated `decls` and `outputs`
    while `body` and the EXPRESSION half of each declaration went to Singular
    untouched, so the exact defect the guard exists to prevent could be rebuilt
    through either:

        CASProgram(..., ring_vars=['g0','x'],
                   decls=[('I','ideal','g0*x')],
                   body=['poly g0 = 1;'])          # shadows the ring variable

        decls=[('I','ideal','g0*x; poly g0 = 1')]  # two statements, one field

    Both emit `poly g0 = 1;` into a ring that has `g0` as a variable, which is
    the `poly g0 = ...` defect that manufactured false UNIT verdicts at every
    prime.  Guard 2 caught it in the identifier field and waved it through in
    the text field beside it.

    Two rules, both exact rather than heuristic:

      ONE STATEMENT PER ENTRY.  A `;` inside a declaration expression, or more
      than a trailing one in a body statement, means the field carries a
      statement LIST, and a list is where the second statement hides.

      NOTHING DECLARES.  A statement whose leading token is a type keyword
      introduces a name the collision check never saw.  A statement whose
      leading token is `execute`, `kill` or `setring` reaches around the check
      by other means.

    HONEST LIMIT, recorded rather than papered over: this is a denylist over a
    language with a real grammar, so it is sound against the defects on record
    and is not a proof.  The complete fix is a typed statement AST with no free
    strings anywhere, which is a v0.3 change; until then this closes the known
    holes and `body` is empty in every program this repository emits.
    """
    spec = DIALECTS[dialect]
    for stmt in statements:
        text = str(stmt)
        # Comments first, or every rule below is bypassable with `// x\n`.
        core = _strip_comments(text, dialect).strip()
        if not core:
            continue
        if core.endswith(";"):
            core = core[:-1]
        # A multi-line entry is a statement LIST even without a semicolon
        # between the lines, because Singular reads newline as whitespace and
        # `poly g0 = 1` on its own line is still a declaration.
        if "\n" in core.strip():
            raise IdentifierCollision(
                "%s spans several lines (%r).  One statement per entry: a "
                "newline is whitespace to the CAS, so a second declaration on "
                "a second line is not a second entry and is not checked as "
                "one." % (field, text))
        if ";" in core:
            raise IdentifierCollision(
                "%s carries more than one statement (%r).  One statement per "
                "entry: a statement list in a single field is where a second, "
                "unvalidated declaration hides -- "
                "`decls=[('I','ideal','g0*x; poly g0 = 1')]` emits a "
                "declaration the collision check never saw." % (field, text))
        m = _FIRST_TOKEN.match(core)
        if not m:
            continue
        head = m.group(1)
        if head in spec["declares"]:
            raise IdentifierCollision(
                "%s DECLARES an identifier (%r), and only `decls` may do that. "
                "The collision check runs over `decls` before the program text "
                "exists; a declaration smuggled in here is never checked "
                "against the ring variables, which is exactly the `poly g0 = "
                "...` defect that produced false UNIT verdicts at every prime."
                % (field, text))
        if head in spec["forbidden"]:
            raise IdentifierCollision(
                "%s uses %r, which is not permitted in a %s program.  It can "
                "introduce or destroy a name, change the base ring, or run a "
                "string as source -- any of which reaches around the "
                "identifier check rather than through it." % (field, head, dialect))
    return True


class CASProgram(object):
    """The ONLY thing `run_cas` accepts.  There is no string path to a solver.

    The collision check and the program text are derived from the SAME
    (identifier, definition) pairs, so they cannot drift apart.
    """

    def __init__(self, dialect, ring, ring_vars, decls, body, outputs,
                 characteristic=0, generators=None, ordering="dp"):
        if dialect not in DIALECTS:
            raise ValueError("unknown CAS dialect %r" % (dialect,))
        self.dialect = dialect
        self.ring = ring
        self.ring_vars = list(ring_vars)
        # THE GENERATORS, kept because the model minted from this run should
        # record what it IS and not only what it was called.  They are already
        # inside `decls` as one comma-joined string; a caller that has them as a
        # list should not have to parse them back out, and `store` should not
        # have to guess which decl was the ideal.
        self.generators = list(generators) if generators is not None else None
        self.decls = [(str(n), str(t), str(e)) for n, t, e in decls]
        self.body = list(body)
        self.outputs = list(outputs)
        if not S.valid_characteristic(characteristic):
            raise ValueError(
                "characteristic must be 0 or a prime, not %r"
                % characteristic)
        self.characteristic = characteristic
        if ordering not in ("dp", "lp"):
            raise ValueError(
                "ordering must be the closed Singular order `dp` or `lp`, "
                "not %r" % ordering
            )
        self.ordering = ordering
        # EVERY field that reaches the program text, not a subset of them.
        # v0.2 validated the identifier half of `decls` and the expression half
        # and `body`, and left `ring`, `ring_vars` and the TYPE half of each
        # decl entirely unchecked -- which is the same mistake, one layer out,
        # as the original guard validating the identifier and waving through
        # the declaration text beside it.
        assert_is_identifier(dialect, self.ring, "the ring name")
        for v in self.ring_vars:
            assert_is_identifier(dialect, v, "ring variable %r" % (v,))
        for name, typ, _expr in self.decls:
            if typ not in DECL_TYPES[dialect]:
                raise IdentifierCollision(
                    "declaration %r has type %r, which is not a %s type "
                    "(known: %s).  The type is interpolated into the program "
                    "exactly like the expression, so an unvalidated one can "
                    "carry a whole extra declaration."
                    % (name, typ, dialect,
                       ", ".join(sorted(DECL_TYPES[dialect]))))
        assert_no_identifier_collision(
            dialect, [self.ring] + self.ring_vars, self.decls
        )
        assert_no_identifier_collision(dialect, self.ring_vars,
                                       [(o, "", "") for o in self.outputs])
        assert_declares_nothing(dialect, [e for _n, _t, e in self.decls],
                                "a declaration expression")
        assert_declares_nothing(dialect, self.body, "a body statement")

    @property
    def text(self):
        return self.execution_text()

    def execution_text(self, completion_nonce=None):
        """Render this reusable template, optionally bound to one run."""
        if self.dialect != SINGULAR:
            raise NotImplementedError(self.dialect)
        lines = ["ring %s = %d,(%s),%s;"
                 % (self.ring, self.characteristic,
                    ",".join(self.ring_vars), self.ordering)]
        # SINGULAR'S DEFAULT PRINTER IS NOT ROUND-TRIPPABLE. With `short=1`
        # it prints x^3-x*y as `x3-xy`; a consumer that accepts identifiers
        # containing digits must then read x3 and xy as new variables. W8 hit
        # exactly that boundary: Eliminate computed the right polynomial, the
        # constructor stored its compact printout, and operation_output issued
        # a mathematically wrong NOT_THE_STATED_OUTPUT verdict. `short=0`
        # makes Singular print explicit powers and products (`x^3-x*y`). The
        # model and every later verifier now consume a representation that can
        # be sent back to the same CAS without guessing its grammar.
        #
        # This belongs at the emitter, not in a heuristic output parser: ring
        # variables may themselves contain digits, so compact notation is
        # genuinely ambiguous after the ring declaration has been discarded.
        lines.append("short=0;")
        for name, typ, expr in self.decls:
            lines.append("%s %s = %s;" % (typ, name, expr))
        lines.extend(self.body)
        for out in self.outputs:
            lines.append('"@@%s:";' % out.upper())
            lines.append("%s;" % out)
        if completion_nonce is not None:
            if not re.fullmatch(r"[0-9a-f]{32}", completion_nonce):
                raise ValueError(
                    "completion nonce must be 32 lowercase hex digits"
                )
            lines.append('"@@GP-END:%s";' % completion_nonce)
        lines.append("quit;")
        return "\n".join(lines) + "\n"

    @property
    def semantic_fingerprint(self):
        """Address the validated template independently of its run nonce."""
        return B.semantic_fingerprint(
            "cas_program",
            {
                "dialect": self.dialect,
                "ring": B.RingSpec(
                    tuple(self.ring_vars), self.characteristic, self.ordering
                ).payload(),
                "program_text": self.text,
                "outputs": list(self.outputs),
            },
        )


class _BoundCASInvocation(object):
    """One nonce-bound execution of an otherwise reusable CASProgram."""

    def __init__(self, program, completion_nonce):
        self._program = program
        self.completion_nonce = completion_nonce

    def __getattr__(self, name):
        return getattr(self._program, name)

    @property
    def completion_marker(self):
        return "@@GP-END:%s" % self.completion_nonce

    @property
    def text(self):
        return self._program.execution_text(self.completion_nonce)


# ---------------------------------------------------------------------------
# The transport declaration
# ---------------------------------------------------------------------------
class Transport(object):
    """How the model this computation produces relates to its source.

    Constructing one is the act the MCP tool signature makes mandatory.  It
    validates eagerly so that a malformed declaration fails before the solver
    runs rather than after, when the cost has already been paid.
    """

    def __init__(self, src, type, why, map_kind=K.IDENTITY_MAP, drops=(),
                 witness="", debt_why="", cite="",
                 strictness_witness="", converse_witness="", ring_iso=None,
                 forward=None, inverse=None):
        if type not in K.DECLARABLE_TYPES:
            raise TransportNotDeclared(
                "transport type %r is not declarable.  Name what this step "
                "LOSES:\n"
                "  nothing (and you can exhibit the converse) -> EQUIVALENCE\n"
                "  equations                                  -> %s\n"
                "  a larger coefficient field                 -> %s\n"
                "  an elimination or a projection             -> %s\n"
                "  a change of characteristic                 -> %s\n"
                "  not yet known                              -> UNTYPED, with "
                "debt_why"
                % (type, K.NECESSARY_CONDITION, K.BASE_EXTENSION,
                   K.IMAGE_CLOSURE, K.SPECIALIZATION))
        if not why:
            raise TransportNotDeclared(
                "transport declaration needs `why`: what does this step lose?")
        if type == K.UNTYPED and not debt_why:
            raise TransportNotDeclared(
                "an UNTYPED edge is a recorded modelling debt and needs "
                "`debt_why`.  Say what is not yet known about this step.")
        if map_kind not in K.MAP_KINDS:
            raise TransportNotDeclared("unknown map_kind %r" % (map_kind,))
        self.src = src
        self.type = type
        self.why = why
        self.map_kind = map_kind
        self.drops = list(drops)
        self.debt_why = debt_why
        self.cite = cite
        # Two fields with OPPOSITE polarity, previously collapsed into one name
        # called `witness` -- so evidence that a step was lossy could be, and
        # was, accepted as documentation that it was lossless.  Legacy `witness`
        # means STRICTNESS, which is what every existing use of it in this
        # repository intends.
        self.strictness_witness = strictness_witness or witness
        self.converse_witness = converse_witness
        if converse_witness and type != K.EQUIVALENCE:
            raise TransportNotDeclared(
                "a `converse_witness` exhibits the construction that recovers a "
                "point of the source from a point of the target, which is what "
                "makes a step an EQUIVALENCE.  This edge is typed %s.  If the "
                "converse really is exhibitable the type is wrong; if it is "
                "not, the field is." % type)
        self.witness = self.strictness_witness   # back-compatible read
        # `ring_iso` is what lets an IDENTITY cross an EQUIVALENCE.  v0.2 taught
        # the kernel to read it and never gave anyone a way to WRITE it: it was
        # absent from the MCP schema and hard-rejected here as an unknown field,
        # so an honest ring isomorphism could not be declared through the
        # supported path at all, while a raw `portage_declare` could assert it
        # unaudited.  A gate that is unreachable from the front door and wide
        # open at the back is not a gate.
        if ring_iso is not None and not isinstance(ring_iso, bool):
            raise TransportNotDeclared(
                "`ring_iso` must be true or false, not %r" % ring_iso)
        if ring_iso is not None and type != K.EQUIVALENCE:
            raise TransportNotDeclared(
                "`ring_iso` says an EQUIVALENCE is an isomorphism of coordinate "
                "rings and not merely a bijection on solutions.  It is "
                "meaningless on a %s edge, which is lossy by construction."
                % type)
        self.ring_iso = ring_iso
        if (forward is None) != (inverse is None):
            raise TransportNotDeclared(
                "a mapped EQUIVALENCE needs both `forward` and `inverse`; one "
                "map cannot establish an invertible coordinate change")
        if forward is not None:
            if type != K.EQUIVALENCE:
                raise TransportNotDeclared(
                    "`forward`/`inverse` substitutions describe a mapped "
                    "EQUIVALENCE, not a lossy %s edge" % type)
            if (not isinstance(forward, dict) or not forward
                    or not isinstance(inverse, dict) or not inverse):
                raise TransportNotDeclared(
                    "`forward` and `inverse` must be non-empty substitution "
                    "objects: "
                    "one polynomial expression per ring variable")
            if not all(isinstance(k, str) and isinstance(v, str)
                       for maps in (forward, inverse)
                       for k, v in maps.items()):
                raise TransportNotDeclared(
                    "substitution names and polynomial expressions must be strings")
            if not all(k.strip() and v.strip()
                       for maps in (forward, inverse)
                       for k, v in maps.items()):
                raise TransportNotDeclared(
                    "substitution names and expressions must be non-blank")
        self.forward = forward
        self.inverse = inverse

    @classmethod
    def from_dict(cls, d):
        if d is None:
            raise TransportNotDeclared(
                "no transport declared.  A computation that produces a new "
                "model must say how that model relates to its source; an "
                "untyped step is where the errors live.  Pass "
                "edge={'src': ..., 'type': ..., 'why': ...}.")
        if not isinstance(d, dict):
            raise TransportNotDeclared("edge must be an object, got %r"
                                       % type(d).__name__)
        unknown = set(d) - {"src", "type", "why", "map_kind", "drops",
                            "witness", "debt_why", "cite",
                            "strictness_witness", "converse_witness",
                            "ring_iso", "forward", "inverse"}
        if unknown:
            raise TransportNotDeclared("unknown edge fields: %s"
                                       % ", ".join(sorted(unknown)))
        if "ring_iso" in d and not isinstance(d["ring_iso"], bool):
            raise TransportNotDeclared("`ring_iso` must be true or false")
        fwd_present, inv_present = "forward" in d, "inverse" in d
        if fwd_present != inv_present:
            raise TransportNotDeclared(
                "a mapped EQUIVALENCE needs both `forward` and `inverse`; one "
                "map cannot establish an invertible coordinate change")
        if fwd_present and (d["forward"] is None or d["inverse"] is None):
            raise TransportNotDeclared(
                "`forward` and `inverse` must be non-empty substitution objects")
        return cls(**d)

    def events(self, eid, dst, dst_desc, dst_field=None, dst_chart=None,
               ring_vars=None, generators=None, characteristic=None):
        """The graph events this computation contributes.

        THE MODEL KEEPS THE ALGEBRA IT WAS BUILT FROM.

        Every CAS entry point is HANDED `ring_vars` and `generators` -- the
        ideal -- runs a computation with them, mints a model, and threw all of
        it away.  What survived was `desc`: a sentence somebody wrote.  So the
        graph recorded what a model was CALLED and never what it IS, and
        `KNOWN_CONSERVATISM` has carried the consequence since v0.2 -- "models
        are currently descriptions, not objects".

        That single gap is upstream of four separate documented ones:

          * `V(src) subset V(dst)` -- the assertion the ENTIRE ontology rests
            on -- is checkable by ideal containment and is instead taken on the
            author's word.  A live lane put it plainly: a mis-typed flop
            produces no signal, and nothing in the tool would have stopped it;
          * the exact condition for an IDENTITY to cross a NECESSARY_CONDITION
            is `LHS - RHS` lying in the target's ideal.  The kernel uses
            AMBIENT origin instead, which the register records as SUFFICIENT
            BUT NOT NECESSARY;
          * `integral` and `coefficients_in_base` are one question asked twice
            and cannot be unified while the kernel cannot compare fields;
          * `BASE_EXTENSION` must be declared where it could be detected.

        Retaining it costs nothing -- the caller already passed it -- and it is
        the prerequisite for all four.  Nothing in this commit CONSUMES the
        ideal; storing it is deliberately its own step.
        """
        model = {"ev": S.EV_MODEL, "id": dst, "desc": dst_desc,
                 "cite": self.cite}
        if ring_vars:
            model["ring_vars"] = list(ring_vars)
        if generators is not None:
            model["generators"] = list(generators)
        if characteristic is not None:
            model["characteristic"] = characteristic
        if dst_field:
            model["field"] = dst_field
        if dst_chart:
            model["chart"] = dst_chart
        edge = {"ev": S.EV_EDGE, "id": eid, "src": self.src, "dst": dst,
                "type": self.type, "why": self.why, "map_kind": self.map_kind,
                "cite": self.cite}
        if self.drops:
            edge["drops"] = self.drops
        if self.strictness_witness:
            edge["strictness_witness"] = self.strictness_witness
        if self.converse_witness:
            edge["converse_witness"] = self.converse_witness
        if self.ring_iso is not None:
            edge["ring_iso"] = self.ring_iso
        if self.forward is not None:
            edge["forward"] = dict(self.forward)
            edge["inverse"] = dict(self.inverse)
        if self.debt_why:
            edge["debt_why"] = self.debt_why
        return [model, edge]


# ---------------------------------------------------------------------------
# Running
# ---------------------------------------------------------------------------
ABORT_CODES = {
    124: "timeout", 125: "output limit", 137: "SIGKILL", 139: "SIGSEGV"
}
_MAX_STDOUT_BYTES = 16 * 1024 * 1024
_MAX_STDERR_BYTES = 4 * 1024 * 1024

# Windows dev boxes reach Singular through WSL; ASSAY.md recorded the same
# arrangement.  Overridable so a Linux/Mac checkout needs no edit.
SINGULAR_ARGV = os.environ.get("GP_SINGULAR_ARGV")


def _argv():
    if SINGULAR_ARGV:
        return SINGULAR_ARGV.split()
    if os.name == "nt":
        return ["wsl.exe", "--", "Singular", "-q"]
    return ["Singular", "-q"]


def _parse_outputs(stdout, outputs):
    """Read exactly one value BLOCK per declared output, or refuse.

    Not a lenient regex, deliberately.  A laxer parser would have read a
    verdict out of a program that never ran.

    THE WHOLE BLOCK, NOT THE FIRST LINE.  Singular prints an ideal one
    generator per line as `NAME[i]=...`.  The first version captured a single
    line, so a two-generator basis was reported as `GP_G[1]=f6` -- which a
    reader can easily take for "the ideal is (f6)".  It is not; it is the first
    element of a basis whose length was never shown.  Silently under-reporting
    the size of a Groebner basis is exactly the kind of quiet mis-description
    between a computation and its consumer that this project exists to refuse,
    and it reached a user before it was caught.

    Returns a list when the block has several lines, a string when it has one,
    so single-value outputs stay ergonomic.
    """
    values = {}
    for out in outputs:
        marker = "@@%s:" % out.upper()
        starts = [m.end() for m in
                  re.finditer(r"^%s[ \t]*$" % re.escape(marker), stdout,
                              re.MULTILINE)]
        if len(starts) != 1:
            raise CASError(
                "expected exactly one value block for output %r, found %d.  A "
                "CAS that errored is not a CAS that answered."
                % (out, len(starts)))
        lines = []
        for line in stdout[starts[0]:].lstrip("\n").splitlines():
            if not line.strip() or line.startswith("@@"):
                break
            lines.append(line.rstrip())
        if not lines:
            raise CASError(
                "output marker %r was printed with nothing behind it.  "
                "Singular reports an error, keeps going, prints the markers "
                "empty, and exits 0 -- so this is a failed run, not an empty "
                "answer." % out)
        values[out] = lines if len(lines) > 1 else lines[0]
    return values


def run_cas(program, *, edge, produces, describes, root=".", timeout=300,
            record=True, dst_field=None, dst_chart=None, cite="",
            edge_id=None, _runner=None):
    """Run a CAS program and record the typed edge it produced.

    `edge` is KEYWORD-ONLY WITH NO DEFAULT.  Omitting it is a TypeError raised
    by Python's own argument binding, before this function body runs and
    therefore before any subprocess exists.  That is the forcing function, and
    it is deliberately not enforced by a check inside the body -- a check can
    be reordered or short-circuited by a later edit; a missing required
    argument cannot.
    """
    if not isinstance(program, CASProgram):
        raise TypeError(
            "run_cas accepts only a CASProgram, not %r.  There is no string "
            "path to a solver: the identifier collision assert runs in the "
            "CASProgram constructor, before the program text exists, and a raw "
            "string would bypass it." % type(program).__name__)
    transport = Transport.from_dict(edge) if isinstance(edge, dict) else edge
    if not isinstance(transport, Transport):
        raise TransportNotDeclared("edge must be a Transport or a dict")

    result = _execute(program, timeout, _runner)

    if result["aborted"]:
        result["verdict"] = "ABORTED"
        result["values"] = None
    elif "? error" in result["stdout"] or "? error" in result["stderr"]:
        raise CASError(
            "the CAS reported an error and cannot be read for a verdict.  "
            "Note the exit code was %s: Singular reports an error, keeps "
            "going, prints the output markers with nothing behind them, and "
            "exits 0, so exit status is not evidence.\n%s"
            % (result["returncode"], result["stdout"][-2000:]))
    elif result["returncode"] != 0:
        # Exit status is not SUFFICIENT evidence of success -- that is guard 3,
        # and it is why the `? error` scan above exists.  It is still NECESSARY.
        # Only three codes were recognised as aborts, so any other nonzero exit
        # fell through to the OK branch and was read for a verdict as long as
        # the output happened to parse.  A run that did not exit cleanly is a
        # run that did not answer.
        raise CASError(
            "the CAS exited %s.  A nonzero exit is not a verdict, whatever the "
            "output parses to; only the codes %s were previously treated as "
            "aborts and every other nonzero exit was read as OK.\n%s"
            % (result["returncode"],
               ", ".join(str(c) for c in sorted(ABORT_CODES)),
               result["stdout"][-2000:]))
    else:
        result["values"] = _parse_result(result, program.outputs)
        result["verdict"] = "OK"

    result["transport"] = {"src": transport.src, "type": transport.type,
                           "dst": produces}
    if record:
        eid = edge_id or ("E-%s" % produces)
        artifact = B.validate_execution_artifact(result, program)
        artifact_fingerprint = A.persist(root, artifact)
        result["artifact_fingerprint"] = artifact_fingerprint
        artifact_fields = A.reference_fields(
            artifact, artifact_fingerprint)
        if result["verdict"] != "OK":
            # AN UNFINISHED RUN MINTS NO MODEL.  Appending the model and the
            # semantic edge regardless of verdict put a node in the graph
            # asserting that a model EXISTS and relates to its source in a
            # stated way, on the strength of a computation that never returned.
            # Every downstream claim would then attach to an object nothing
            # computed.  The attempt is still worth recording, so it goes in as
            # a note -- which carries provenance and asserts no mathematics.
            result["events"] = [{
                "ev": S.EV_NOTE, "kind": "cas-abort",
                "attempted_model": produces, "src": transport.src,
                "verdict": result["verdict"],
                "abort_reason": result.get("abort_reason"),
                "text": ("an attempt to produce %s from %s ended %s, so NO "
                         "model and NO edge were recorded.  An unfinished run "
                         "is not evidence of anything."
                         % (produces, transport.src, result["verdict"]))}]
            result["events"][0].update(artifact_fields)
        else:
            events = transport.events(
                eid, produces, describes,
                dst_field=dst_field, dst_chart=dst_chart,
                ring_vars=getattr(program, "ring_vars", None),
                generators=getattr(program, "generators", None),
                characteristic=getattr(program, "characteristic", None))
            events[0]["cite"] = events[1]["cite"] = cite or transport.cite
            events.append(dict({
                "ev": S.EV_NOTE,
                "kind": "cas-execution",
                "source": eid,
                "text": (
                    "the exact backend execution that produced model %s; "
                    "this note records provenance and licenses no conclusion"
                    % produces),
            }, **artifact_fields))
            result["events"] = events
        S.append(result["events"], root=root)
    return result


def _limited_argv(argv, timeout):
    """Put the actual WSL child, not only its launcher, under a deadline."""
    if (os.name == "nt" and len(argv) >= 3
            and os.path.basename(argv[0]).lower() == "wsl.exe"
            and argv[1] == "--"):
        return [
            argv[0], "--", "timeout", "--signal=KILL", "--kill-after=2s",
            "%ss" % max(1, int(timeout)),
        ] + list(argv[2:])
    return list(argv)


def _kill_process_tree(proc):
    """Terminate exactly the spawned process group/tree, best effort."""
    if proc.poll() is not None:
        return
    if os.name == "nt":
        try:
            killed = subprocess.run(
                ["taskkill", "/PID", str(proc.pid), "/T", "/F"],
                stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL,
                timeout=2,
            )
            if killed.returncode == 0:
                return
        except (OSError, subprocess.SubprocessError):
            pass
    try:
        if os.name == "nt":
            proc.kill()
        else:
            os.killpg(proc.pid, signal.SIGKILL)
    except OSError:
        pass


def _run_subprocess(program, timeout):
    """Run one CAS with bounded output and whole-tree timeout containment."""
    base_argv = _argv()
    argv = _limited_argv(base_argv, timeout)
    outer_timeout = timeout + 5 if argv != list(base_argv) else timeout
    limits = {
        "stdout": _MAX_STDOUT_BYTES, "stderr": _MAX_STDERR_BYTES,
    }
    buffers = {"stdout": bytearray(), "stderr": bytearray()}
    overflow = threading.Event()
    overflow_stream = []
    popen_kwargs = {}
    if os.name == "nt":
        popen_kwargs["creationflags"] = getattr(
            subprocess, "CREATE_NEW_PROCESS_GROUP", 0
        )
    else:
        popen_kwargs["start_new_session"] = True
    try:
        proc = subprocess.Popen(
            argv, stdin=subprocess.PIPE, stdout=subprocess.PIPE,
            stderr=subprocess.PIPE, **popen_kwargs
        )
    except FileNotFoundError as exc:
        raise CASError("cannot reach the CAS via %s: %s" % (argv, exc))

    def drain(stream_name, pipe):
        while True:
            chunk = pipe.read(65536)
            if not chunk:
                return
            remaining = limits[stream_name] - len(buffers[stream_name])
            if remaining > 0:
                buffers[stream_name].extend(chunk[:remaining])
            if len(chunk) > remaining:
                if not overflow.is_set():
                    overflow_stream.append(stream_name)
                    overflow.set()
                    _kill_process_tree(proc)
                return

    readers = [
        threading.Thread(
            target=drain, args=(name, pipe), daemon=True,
            name="gp-cas-%s" % name,
        )
        for name, pipe in (("stdout", proc.stdout), ("stderr", proc.stderr))
    ]

    def feed_input():
        try:
            proc.stdin.write(program.text.encode("utf-8"))
            proc.stdin.close()
        except (BrokenPipeError, OSError):
            pass

    writer = threading.Thread(
        target=feed_input, daemon=True, name="gp-cas-stdin"
    )
    for reader in readers:
        reader.start()
    writer.start()
    try:
        try:
            rc = proc.wait(timeout=max(0.001, outer_timeout))
        except subprocess.TimeoutExpired:
            _kill_process_tree(proc)
            try:
                proc.wait(timeout=10)
            except subprocess.TimeoutExpired:
                proc.kill()
                proc.wait()
            rc = 124
    finally:
        writer.join(timeout=10)
        for reader in readers:
            reader.join(timeout=10)
        for pipe in (proc.stdin, proc.stdout, proc.stderr):
            try:
                pipe.close()
            except OSError:
                pass
    if overflow.is_set():
        rc = 125
        reason = "%s exceeded its byte limit" % (
            overflow_stream[0] if overflow_stream else "CAS output"
        )
        diagnostic = ("\n" + reason).encode("utf-8")
        remaining = _MAX_STDERR_BYTES - len(buffers["stderr"])
        if remaining > 0:
            buffers["stderr"].extend(diagnostic[:remaining])
    stdout = bytes(buffers["stdout"]).decode("utf-8", errors="ignore")
    stderr = bytes(buffers["stderr"]).decode("utf-8", errors="ignore")
    if rc == 124 and not stderr:
        stderr = "timeout after %ss" % timeout
    return {
        "returncode": rc,
        "stdout": stdout,
        "stderr": stderr,
        "aborted": rc in ABORT_CODES,
        "abort_reason": ABORT_CODES.get(rc),
        "argv": argv,
    }


_BINARY_VERSION_CACHE = {}


def _singular_binary_version(timeout=30):
    """Return the exact Singular version string used by the configured argv."""
    argv = tuple(_argv())
    if argv in _BINARY_VERSION_CACHE:
        return _BINARY_VERSION_CACHE[argv]
    try:
        proc = subprocess.run(
            list(argv) + ["--version"], capture_output=True, text=True,
            timeout=timeout,
        )
    except (OSError, subprocess.TimeoutExpired) as exc:
        version = "unavailable: %s" % type(exc).__name__
    else:
        text = "\n".join(
            line.strip()
            for line in (proc.stdout + "\n" + proc.stderr).splitlines()
            if line.strip()
        )
        version = text[:1000] if text else "unreported"
    _BINARY_VERSION_CACHE[argv] = version
    return version


class SingularBackend(B.Backend):
    """The reference semantic backend, with the old runner as a test adapter."""

    IMPLEMENTATION_VERSION = B.SINGULAR_IMPLEMENTATION_VERSION

    def __init__(self, runner=None, binary_version=None):
        self._runner = runner
        self._binary_version = binary_version
        self.executions = []

    @property
    def identity(self):
        version = self._binary_version
        if version is None:
            version = (
                "test-double" if self._runner is not None
                else _singular_binary_version()
            )
        implementation = (
            B.SINGULAR_IMPLEMENTATION
            if type(self) is SingularBackend
            else "%s.%s" % (type(self).__module__, type(self).__qualname__)
        )
        return B.BackendIdentity(
            contract=B.SINGULAR_CONTRACT,
            implementation=implementation,
            implementation_version=self.IMPLEMENTATION_VERSION,
            binary_version=version,
        )

    @property
    def can_record_verdicts(self):
        return (type(self) is SingularBackend
                and self._runner is None
                and self._binary_version is None)

    @property
    def execution_count(self):
        return len(self.executions)

    def execute(self, program, timeout=300, semantic_input=None):
        if not isinstance(program, CASProgram):
            raise TypeError(
                "SingularBackend accepts only CASProgram, not %r"
                % type(program).__name__
            )
        completion_nonce = secrets.token_hex(16)
        invocation = _BoundCASInvocation(program, completion_nonce)
        runner = self._runner or _run_subprocess
        raw = runner(invocation, timeout)
        if isinstance(raw, B.BackendExecution):
            raise TypeError(
                "a backend runner must return raw process fields, not a "
                "pre-wrapped BackendExecution. Accepting one could attach a "
                "different program, backend, or semantic request to this run."
            )
        fingerprint = (
            B.semantic_fingerprint("backend_request", semantic_input)
            if semantic_input is not None
            else program.semantic_fingerprint
        )
        execution = B.BackendExecution(
            raw, backend=self.identity, program=program,
            execution_program=invocation, completion_nonce=completion_nonce,
            semantic_input_fingerprint=fingerprint,
        )
        self.executions.append(execution)
        return execution

    def provenance(self, start=0):
        """Aggregate the exact executions used for one verifier verdict."""
        if type(start) is not int or start < 0 or start > self.execution_count:
            raise ValueError("backend provenance cursor is out of range")
        identity = self.identity
        artifacts = [
            B.validate_execution_artifact(run)
            for run in self.executions[start:]
        ]
        trace = [B.execution_trace_entry(artifact) for artifact in artifacts]
        return {
            "schema": 2,
            "contract": identity.contract,
            "implementation": identity.implementation,
            "implementation_version": identity.implementation_version,
            "protocol_version": B.BACKEND_PROTOCOL_VERSION,
            "binary_version": identity.binary_version,
            "executions": trace,
            "trace_fingerprint": B.semantic_fingerprint(
                "backend_execution_trace", trace
            ),
        }

    def execution_artifacts(self, start=0):
        """Return validated frozen executions since an opaque cursor."""
        if type(start) is not int or start < 0 or start > self.execution_count:
            raise ValueError("backend provenance cursor is out of range")
        return tuple(
            B.validate_execution_artifact(run)
            for run in self.executions[start:]
        )

    def classify_identity(self, ring_vars, lhs, rhs, generators=(),
                          characteristic=0, timeout=300):
        return classify_identity(
            ring_vars, lhs, rhs, generators=generators,
            characteristic=characteristic, timeout=timeout,
            _runner=self.execute,
        )

    def membership(self, ring_vars, target, generators, characteristic=0,
                   timeout=300):
        return membership_representation(
            ring_vars, target, generators, characteristic=characteristic,
            timeout=timeout, _runner=self.execute,
        )

    def check_membership(self, ring_vars, target, generators, cofactors,
                         characteristic=0, timeout=300):
        return check_membership_representation(
            ring_vars, target, generators, cofactors,
            characteristic=characteristic, timeout=timeout,
            _runner=self.execute,
        )

    def pullback_reduce(self, ring_vars, expr, images, generators=(),
                        characteristic=0, timeout=300):
        return substitute_and_reduce(
            ring_vars, expr, images, generators,
            characteristic=characteristic, timeout=timeout,
            _runner=self.execute,
        )

    def evaluate_point(self, ring_vars, generators, point, characteristic=0,
                       timeout=300):
        return check_witness(
            ring_vars, generators, point, characteristic=characteristic,
            timeout=timeout, _runner=self.execute,
        )

    def compile_saturation(self, ring_vars, generators, at,
                           characteristic=0):
        tvar = "GP_T"
        return CASProgram(
            SINGULAR, ring="GP_R", ring_vars=[tvar] + list(ring_vars),
            decls=[
                ("GP_I", "ideal", ",".join(
                    list(generators) + ["1-%s*(%s)" % (tvar, at)]
                ) or "0"),
                ("GP_E", "ideal", "eliminate(GP_I,%s)" % tvar),
                ("GP_OUT", "ideal", "std(GP_E)"),
            ], body=[], outputs=["GP_OUT"], characteristic=characteristic)

    def compile_elimination(self, ring_vars, generators, variables,
                            characteristic=0):
        variables = list(variables)
        if not variables:
            raise ValueError("elimination needs at least one variable")
        if len(variables) != len(set(variables)):
            raise ValueError("elimination variables must be unique")
        if not set(variables).issubset(set(ring_vars)):
            raise ValueError("cannot eliminate variables outside the ring")
        remaining = [v for v in ring_vars if v not in set(variables)]
        if not remaining:
            raise ValueError("elimination cannot remove every ring variable")
        program = CASProgram(
            SINGULAR, ring="GP_R", ring_vars=list(ring_vars),
            decls=[
                ("GP_I", "ideal", ",".join(generators) or "0"),
                ("GP_E", "ideal", "eliminate(GP_I,%s)"
                 % "*".join(variables)),
                ("GP_OUT", "ideal", "std(GP_E)"),
            ], body=[], outputs=["GP_OUT"], characteristic=characteristic)
        return remaining, program

    def saturate(self, ring_vars, generators, at, characteristic=0,
                 timeout=300):
        return _backend_saturate(
            self, ring_vars, generators, at,
            characteristic=characteristic, timeout=timeout,
        )

    def eliminate(self, ring_vars, generators, variables, characteristic=0,
                  timeout=300):
        return _backend_eliminate(
            self, ring_vars, generators, variables,
            characteristic=characteristic, timeout=timeout,
        )

    def partition_cover(self, ring_vars, parent_generators, branches,
                        characteristic=0, timeout=300):
        return partition_covers(
            ring_vars, parent_generators, branches,
            characteristic=characteristic, timeout=timeout,
            _runner=self.execute,
        )

    def factorizing_decomposition(self, ring_vars, generators,
                                  characteristic=0, timeout=300,
                                  return_program=False):
        start = self.execution_count
        pieces, program = factorizing_decomposition(
            ring_vars, generators, characteristic=characteristic,
            timeout=timeout, _runner=self.execute,
            _return_program=True,
        )
        executions = self.executions[start:]
        if len(executions) != 1:
            raise CASError(
                "factorizing_decomposition must retain exactly one execution "
                "artifact, found %d" % len(executions))
        answer = {
            "pieces": pieces,
            "program": program,
            "execution": executions[0],
        }
        return answer if return_program else pieces

    def unit_ideal(self, ring_vars, generators, characteristic=0,
                   timeout=300):
        return unit_ideal_representation(
            ring_vars, generators, characteristic=characteristic,
            timeout=timeout, _runner=self.execute,
        )

    def check_unit_ideal(self, ring_vars, generators, cofactors,
                         characteristic=0, timeout=300):
        return check_unit_ideal_representation(
            ring_vars, generators, cofactors,
            characteristic=characteristic, timeout=timeout,
            _runner=self.execute,
        )


def _execute(program, timeout, runner=None, semantic_input=None):
    """Compatibility adapter from the old runner seam to a backend execution."""
    owner = getattr(runner, "__self__", None)
    if isinstance(owner, B.Backend):
        return owner.execute(
            program, timeout=timeout, semantic_input=semantic_input
        )
    return SingularBackend(runner=runner).execute(
        program, timeout=timeout, semantic_input=semantic_input
    )


def _parse_result(result, outputs, certificate=None):
    """Parse only a complete transcript from the frozen output snapshot."""
    if not isinstance(result, B.BackendExecution):
        raise CASError(
            "backend output has no retained execution envelope; mathematical "
            "output cannot be parsed without a nonce-bound terminal marker"
        )
    B.validate_execution_artifact(result, result.program)
    stdout = result.artifact.stdout
    expected = "@@GP-END:%s" % result.artifact.completion_nonce
    ends = list(re.finditer(
        r"^@@GP-END:[^\r\n]*[ \t]*$", stdout, re.MULTILINE
    ))
    if len(ends) != 1:
        raise CASError(
            "expected exactly one nonce-bound terminal marker, found %d; "
            "parseable output from an unfinished or concatenated transcript "
            "is not a CAS answer" % len(ends)
        )
    terminal = ends[0]
    if terminal.group(0).strip() != expected:
        raise CASError(
            "the CAS terminal marker belongs to a different invocation; "
            "stale or replayed stdout is not an answer to this program"
        )
    if stdout[terminal.end():].strip():
        raise CASError(
            "non-whitespace follows the CAS terminal marker; the transcript "
            "is concatenated or the marker was not terminal"
        )
    stdout = stdout[:terminal.start()]
    values = _parse_outputs(stdout, outputs)
    if isinstance(result, B.BackendExecution):
        result.attach_parsed(values, certificate=certificate)
    return values


def _require_success(result, action):
    if isinstance(result, B.BackendExecution):
        aborted = result.artifact.aborted
        abort_reason = result.artifact.abort_reason
        returncode = result.artifact.returncode
        stdout = result.artifact.stdout
        stderr = result.artifact.stderr
    else:
        aborted = result["aborted"]
        abort_reason = result.get("abort_reason")
        returncode = result["returncode"]
        stdout = result["stdout"]
        stderr = result["stderr"]
    if aborted:
        raise CASError(
            "%s aborted (%s); an unfinished run answered nothing"
            % (action, abort_reason or "unknown")
        )
    if "? error" in stdout + stderr:
        raise CASError("%s reported a CAS error:\n%s"
                       % (action, stdout[-1500:]))
    if returncode != 0:
        raise CASError("%s exited %s" % (action, returncode))

def _ideal_generators(values, output):
    raw = values[output]
    rows = raw if isinstance(raw, list) else [raw]
    generators = [str(row).split("=", 1)[-1].strip() for row in rows]
    return [g for g in generators if g and g != "0"]


def _backend_saturate(backend, ring_vars, generators, at,
                      characteristic=0, timeout=300):
    program = backend.compile_saturation(
        ring_vars, generators, at, characteristic=characteristic)
    semantic_input = {
        "operation": "saturate", "ring_vars": list(ring_vars),
        "characteristic": characteristic, "generators": list(generators),
        "at": at,
    }
    result = backend.execute(
        program, timeout=timeout, semantic_input=semantic_input
    )
    _require_success(result, "saturation")
    values = _parse_result(result, program.outputs)
    return {
        "generators": _ideal_generators(values, "GP_OUT"),
        "program": program, "execution": result,
    }


def _backend_eliminate(backend, ring_vars, generators, variables,
                       characteristic=0, timeout=300):
    variables = list(variables)
    remaining, program = backend.compile_elimination(
        ring_vars, generators, variables, characteristic=characteristic)
    semantic_input = {
        "operation": "eliminate", "ring_vars": list(ring_vars),
        "characteristic": characteristic, "generators": list(generators),
        "variables": variables,
    }
    result = backend.execute(
        program, timeout=timeout, semantic_input=semantic_input
    )
    _require_success(result, "elimination")
    values = _parse_result(result, program.outputs)
    return {
        "ring_vars": remaining,
        "generators": _ideal_generators(values, "GP_OUT"),
        "program": program, "execution": result,
    }


FALSE_AT_MODEL = "FALSE_AT_MODEL"


def classify_identity(ring_vars, lhs, rhs, generators=(), characteristic=0,
                      timeout=300, _runner=None):
    """DECIDE an identity's origin by computation instead of asking for it.

    Returns (origin, evidence) where origin is one of K.AMBIENT, K.DERIVED or
    FALSE_AT_MODEL, and evidence carries the two normal forms behind the answer.

    Let d = lhs - rhs.  Then:

        d == 0 in the polynomial ring       -> AMBIENT
        d != 0 but d reduces to 0 mod I     -> DERIVED
        neither                             -> FALSE_AT_MODEL

    The middle test is exactly membership d in I, which is what "valid in this
    model's coordinate ring" means: the coordinate ring is R/I, so a relation
    holds there precisely when its difference lies in I.  That is also why the
    non-radical case matters and why a point-level equivalence is not enough --
    x lies in (x) and not in (x^2), which is the whole V(x) versus V(x^2) story.

    THIS TOUCHES THE GRAPH NOT AT ALL, and that is deliberate.  It is a
    measuring instrument, like `cas_health`: it answers a question so the answer
    can be declared with a computation behind it.  Recording is a separate act,
    because a tool that both decides a field and writes it leaves nobody
    holding the claim.

    The third outcome is the one worth building this for.  Neither origin is a
    refusal to transport -- both are legal answers -- but FALSE_AT_MODEL says
    the rewriting does not hold where it was claimed at all, which no amount of
    correct transport typing would ever have surfaced.
    """
    diff = "(%s)-(%s)" % (lhs, rhs)
    decls = [("GP_D", "poly", diff)]
    outputs = ["GP_D", "GP_RED"]
    if generators:
        decls.append(("GP_I", "ideal", ",".join(generators)))
        decls.append(("GP_S", "ideal", "std(GP_I)"))
        decls.append(("GP_RED", "poly", "reduce(GP_D,GP_S)"))
    else:
        # No ideal supplied: the model imposes nothing, so "modulo I" is the
        # same question as "in the ambient ring" and the two agree by
        # construction rather than by accident.
        decls.append(("GP_RED", "poly", "GP_D"))
    prog = CASProgram(SINGULAR, ring="GP_R", ring_vars=ring_vars, decls=decls,
                      body=[], outputs=outputs,
                      characteristic=characteristic)
    result = _execute(prog, timeout, _runner)
    if result["aborted"]:
        raise CASError("classification aborted (%s); an unfinished run "
                       "classifies nothing" % result.get("abort_reason"))
    if "? error" in result["stdout"] + result["stderr"]:
        raise CASError("the CAS reported an error:\n%s"
                       % result["stdout"][-2000:])
    if result["returncode"] != 0:
        raise CASError("the CAS exited %s" % result["returncode"])
    values = _parse_result(result, outputs)

    def _zero(v):
        return str(v if not isinstance(v, list) else " ".join(v)).strip() == "0"

    ambient_zero, mod_zero = _zero(values["GP_D"]), _zero(values["GP_RED"])
    if ambient_zero:
        origin = K.AMBIENT
    elif mod_zero:
        origin = K.DERIVED
    else:
        origin = FALSE_AT_MODEL
    return origin, {"difference": values["GP_D"],
                    "reduced_modulo_ideal": values["GP_RED"],
                    "ambient_zero": ambient_zero, "modulo_zero": mod_zero,
                    "generators": list(generators)}


def check_witness(ring_vars, generators, point, characteristic=0, timeout=300,
                  _runner=None):
    """Substitute a point into the generators and report what each evaluates to.

    Returns (is_solution, evidence).  `point` maps ring variables to values.

    THE CHEAPEST CHECK IN THE SYSTEM, and it did not exist.  An EMPTY claim had
    to name a certificate kind or the graph would not fold; a NONEMPTY claim --
    where the author is holding the object -- carried nothing, so a fabricated
    witness typed identically to a real one.

    Evaluating a point is arithmetic.  There is no interpretation to argue
    about, no ordering assumption, no field subtlety: either every generator
    vanishes or one of them does not, and the one that does not is named.

    Touches the graph not at all.  Like `cas_classify_identity`, it answers a
    question so the answer can be declared with a computation behind it -- a
    tool that both decides a field and writes it leaves nobody holding the
    claim.
    """
    missing = [v for v in ring_vars if v not in point]
    if missing:
        raise CASError(
            "the witness does not give a value for every ring variable; "
            "missing %s.  A partial point is not a point." % ", ".join(missing))
    # THE NESTED `subst` BELOW IS SEQUENTIAL, AND SEQUENTIAL IS NOT
    # SIMULTANEOUS.  `substitute_and_reduce`, forty lines down, exists because
    # getting that wrong is silent: swapping two variables one at a time sends
    # `x*y - 1` to `x*x - 1`, and it was caught only by testing a case meant to
    # PASS.
    #
    # Here it is safe for one reason and one reason only -- a point's values
    # are CONSTANTS, so after substituting `x` no `x` remains for a later
    # substitution to disturb.  That is a precondition, not a property of the
    # code, and nothing enforced it.  A "point" whose value named a ring
    # variable would be evaluated in an order-dependent way and reported with
    # the same confidence as a real one.
    #
    # So require it.  A point whose coordinates depend on the coordinates is
    # not a point.
    used = set()
    for w in point:
        used.update(_SYMBOL.findall(str(point[w])))
    named = sorted(set(ring_vars) & used)
    if named:
        raise CASError(
            "the witness gives a coordinate in terms of the ring variable(s) "
            "%s.  A point's coordinates are constants -- one that refers to "
            "another coordinate is a parametrisation, and substituting it "
            "would depend on the order the variables happened to be in."
            % ", ".join(named))
    # Nested `subst`, one variable at a time, so each generator becomes exactly
    # ONE declaration -- which is what the boundary check requires and why this
    # is built as an expression rather than a statement sequence.
    decls, outs = [], []
    for n, gen in enumerate(generators):
        expr = gen
        for v in ring_vars:
            expr = "subst(%s,%s,%s)" % (expr, v, point[v])
        decls.append(("GP_V%d" % n, "poly", expr))
        outs.append("GP_V%d" % n)
    prog = CASProgram(SINGULAR, ring="GP_R", ring_vars=ring_vars,
                      decls=decls, body=[], outputs=outs,
                      characteristic=characteristic)
    result = _execute(prog, timeout, _runner)
    if result["aborted"] or "? error" in result["stdout"] + result["stderr"] \
            or result["returncode"] != 0:
        raise CASError("the CAS did not evaluate the witness:\n%s"
                       % result["stdout"][-1500:])
    values = _parse_result(result, outs)
    per_gen = []
    for n, gen in enumerate(generators):
        v = values["GP_V%d" % n]
        v = v if not isinstance(v, list) else " ".join(v)
        v = str(v).split("=", 1)[-1].strip()
        per_gen.append({"generator": gen, "value": v, "vanishes": v == "0"})
    ok = all(g["vanishes"] for g in per_gen)
    return ok, {"point": dict(point), "generators": per_gen,
                "failed": [g["generator"] for g in per_gen
                           if not g["vanishes"]]}


def substitute_and_reduce(ring_vars, expr, images, generators=(),
                          characteristic=0, timeout=300, _runner=None):
    """Apply a SIMULTANEOUS substitution, then reduce modulo an ideal.

    NESTED `subst` IS NOT SIMULTANEOUS, and getting that wrong is silent.
    Swapping two variables by substituting one at a time sends `x*y - 1` to
    `x*x - 1`: the first substitution puts `y` everywhere, and the second
    rewrites the lot.  The bug reports the map as failing to carry an ideal it
    carries perfectly well.

    Singular's `map` does the whole substitution at once, which is what a
    change of coordinates means.  Returns (reduced_form, reduces_to_zero).
    """
    if set(images) != set(ring_vars):
        raise CASError(
            "a substitution must give an image for every ring variable; got "
            "%s for %s.  A partial map is not a change of coordinates."
            % (", ".join(sorted(images)), ", ".join(ring_vars)))
    # THE POLYNOMIAL MUST BE NAMED FIRST.  Singular's map application takes a
    # named object, not an inline expression -- `GP_F(x*y-1)` is a syntax
    # error, and the error it gives ("GP_F(<name>) expected") arrives three
    # declarations later as "GP_R2 is undefined".
    decls = [("GP_P", "poly", expr),
             ("GP_F", "map",
              "GP_R," + ",".join(images[v] for v in ring_vars)),
             ("GP_E", "poly", "GP_F(GP_P)")]
    outs = ["GP_E"]
    if generators:
        decls.append(("GP_I", "ideal", ",".join(generators)))
        decls.append(("GP_S", "ideal", "std(GP_I)"))
        decls.append(("GP_R2", "poly", "reduce(GP_E,GP_S)"))
        outs.append("GP_R2")
    prog = CASProgram(SINGULAR, ring="GP_R", ring_vars=list(ring_vars),
                      decls=decls, body=[], outputs=outs,
                      characteristic=characteristic)
    result = _execute(prog, timeout, _runner)
    if (result["aborted"] or result["returncode"] != 0
            or "? error" in result["stdout"] + result["stderr"]):
        raise CASError("the CAS did not apply the substitution:\n%s"
                       % result["stdout"][-1500:])
    vals = _parse_result(result, outs)
    key = "GP_R2" if generators else "GP_E"
    got = vals[key]
    got = " ".join(got) if isinstance(got, list) else str(got)
    got = got.split("=", 1)[-1].strip()
    return got, got == "0"


_FRACTION = re.compile(r"(?<![A-Za-z0-9_])(\d+)\s*/\s*(\d+)")


def non_integral_denominators(prime, *exprs):
    """Denominators in `exprs` that `prime` divides.

    WHAT `integral` IS ACTUALLY ASKING.  That flag gates reducing an IDENTITY
    into characteristic p, and it was declared and never computed.  The
    kernel's own instance is `d2 = h_2 - (3/8)h_1^2`, which travels a perfectly
    polynomial map and does not reduce mod 2 because 8 = 2^3.

    A shadow formalisation put it in a different class from the others.
    `ring_iso` is a property of a map and `identity_origin` is a property of the
    claim, but this is neither: reduction mod p is a PARTIAL map, undefined on
    anything with p in its denominator, and `integral` asks whether it is
    defined here at all.  Modelled that way the transport theorem gains a
    definedness hypothesis and nothing else changes.

    Undefined is not false.  With no image there is nothing to state, which is
    the same shape as `coefficients_in_base`: not a false claim, not a claim.

    Syntactic and conservative, like `foreign_symbols`.  It reads literal
    fractions and cannot evaluate `1/(x-x+2)`; it REPORTS so a declaration has
    something to answer to.
    """
    if not prime or prime < 2:
        return []
    bad = []
    for e in exprs:
        for _num, den in _FRACTION.findall(str(e or "")):
            d = int(den)
            if d and d % prime == 0 and den not in bad:
                bad.append(den)
    return bad


_SYMBOL = re.compile(r"[A-Za-z_][A-Za-z0-9_]*")


def foreign_symbols(ring_vars, *exprs):
    """Symbols in `exprs` that are neither ring variables nor numbers.

    WHAT `coefficients_in_base` IS ACTUALLY ASKING, and it was never asked.

    That flag gates descent across a BASE_EXTENSION, and the kernel's own
    counterexample says why: `x^2 + 1 = (x + i)(x - i)` is valid in Q(i)[x],
    and transported to the Q-model `i` is "not merely unproved -- it is NOT
    EXPRESSIBLE there.  The descended statement is not a false claim, it is
    not a claim."

    A shadow formalisation made the shape precise.  Descent does not fail
    because reflection fails -- for a field extension `I^e cap k[x] = I` holds
    automatically.  It fails because the claim cannot be WRITTEN in the smaller
    ring.  And in a typed setting that condition vanishes into the type: state
    the theorem with `f g : R` and expressibility is free, which is exactly why
    the Lean version could not see the gate.

    SO THE GATE IS A TYPING ARTIFACT.  It exists because a claim here is a
    STRING, and a string carries no evidence about which ring it lives in.
    That makes it decidable rather than declarable: collect the symbols and see
    whether any is foreign to the declared ring.

    Deliberately syntactic and deliberately conservative.  It cannot know that
    `sqrt2` denotes an element of the base if somebody defined it that way, so
    it REPORTS rather than refuses -- the caller still declares, and now has
    something to declare against.
    """
    known = set(ring_vars)
    found = []
    for e in exprs:
        for sym in _SYMBOL.findall(str(e or "")):
            if sym not in known and sym not in found:
                found.append(sym)
    return found


def unit_ideal_representation(ring_vars, generators, characteristic=0,
                              timeout=300, _runner=None):
    """The COFACTORS witnessing `1 = sum a_i f_i`, not just "the basis was 1".

    THE DIFFERENCE BETWEEN EVIDENCE AND A CERTIFICATE ANYBODY CAN RECHECK.
    `ideal_is_unit` returns a Groebner basis, and a caller who sees `1` then
    DECLARES `certificate: UNIT_IDEAL_CERT` -- so the scope of every emptiness
    resting on it derives from a string somebody typed after reading some
    output. Nothing relates the label to the computation.

    A representation fixes that, because it can be checked by ARITHMETIC. Given
    the cofactors, confirming `sum a_i f_i = 1` is one expansion: no Buchberger,
    no monomial order, no trust in the search that found it. That is the
    certifying-algorithms shape -- an answer plus a witness a simpler checker
    can validate -- and it is also the clean bridge to a proof assistant, which
    can check a polynomial identity and should never have to run a Groebner
    engine.

    Returns the raw run. The cofactors come back in `GP_M`, in generator order.
    """
    # TWO CALLS, BECAUSE `lift` FAILS WHEN THERE IS NOTHING TO LIFT.
    #
    # Found by testing the negative case: on `(x, y)` -- a perfectly ordinary
    # non-unit ideal -- `lift(I, ideal(1))` errors, because 1 is not a member
    # and there is no representation to return. Asking for both in one program
    # turned "this ideal is not the unit ideal", which is a fine and common
    # answer, into a CAS error.
    #
    # So: ask whether it is a unit first, and pay for the representation only
    # when there is one.
    basis_prog = CASProgram(
        SINGULAR, ring="GP_R", ring_vars=ring_vars, generators=generators,
        decls=[("GP_I", "ideal", ",".join(generators)),
               ("GP_G", "ideal", "std(GP_I)")],
        body=[], outputs=["GP_G"], characteristic=characteristic)
    basis_res = _execute(basis_prog, timeout, _runner)
    if (basis_res["aborted"] or basis_res["returncode"] != 0
            or "? error" in basis_res["stdout"] + basis_res["stderr"]):
        raise CASError("the CAS did not compute a basis:\n%s"
                       % basis_res["stdout"][-1500:])
    basis = _parse_result(basis_res, ["GP_G"])["GP_G"]
    basis = basis if isinstance(basis, list) else [basis]
    basis = [b.split("=", 1)[-1].strip() for b in basis]
    if basis != ["1"]:
        return {"is_unit": False, "cofactors": None, "basis": basis}

    prog = CASProgram(
        SINGULAR, ring="GP_R", ring_vars=ring_vars, generators=generators,
        decls=[("GP_I", "ideal", ",".join(generators)),
               ("GP_G", "ideal", "std(GP_I)"),
               ("GP_M", "matrix", "lift(GP_I,ideal(1))")],
        body=[], outputs=["GP_G", "GP_M"], characteristic=characteristic)
    # A MEASURING INSTRUMENT, so it bypasses the transport forcing function --
    # the same reason `classify_identity` does. `run_cas` demands an edge
    # because it MINTS A MODEL; this mints nothing and touches no graph. It
    # answers a question so the answer can be recorded with a computation
    # behind it, and recording is a separate, deliberate act.
    result = _execute(prog, timeout, _runner)
    if (result["aborted"] or result["returncode"] != 0
            or "? error" in result["stdout"] + result["stderr"]):
        raise CASError("the CAS did not produce a representation:\n%s"
                       % result["stdout"][-1500:])
    out = _parse_result(result, ["GP_G", "GP_M"])
    # `GP_M[i,1]=...`, one row per generator and IN GENERATOR ORDER, which is
    # the only thing that makes the check below meaningful -- a permuted list
    # would verify a different identity and report it as this one.
    rows = out["GP_M"]
    rows = rows if isinstance(rows, list) else [rows]
    cofactors = []
    for i in range(len(generators)):
        want = "GP_M[%d,1]=" % (i + 1)
        hit = [r for r in rows if r.replace(" ", "").startswith(want)]
        cofactors.append(hit[0].split("=", 1)[-1].strip() if hit else "0")
    result.attach_parsed(out, certificate={
        "kind": "unit_ideal_membership", "target": "1",
        "generators": list(generators), "cofactors": list(cofactors),
    })
    return {"is_unit": True, "cofactors": cofactors, "basis": basis}


def check_unit_ideal_representation(ring_vars, generators, cofactors,
                                    characteristic=0, timeout=300,
                                    _runner=None):
    """Expand `sum a_i f_i` and see whether it is 1.  NO GROEBNER BASIS.

    This is the whole point.  The expensive, subtle computation found the
    cofactors; this one multiplies and adds.  A checker that shares no code
    path with the search is worth more than a second run of the search, and it
    is the only part of the chain a reader has to trust.

    Refuses a length mismatch rather than padding, because a cofactor list
    shorter than the generator list would silently verify a DIFFERENT identity
    -- one about a sub-ideal -- and report it as this one.
    """
    if len(cofactors) != len(generators):
        raise CASError(
            "%d cofactors for %d generators. A representation must give one "
            "coefficient per generator, in the same order; a shorter list "
            "would verify an identity about a different ideal and report it "
            "as this one." % (len(cofactors), len(generators)))
    terms = " + ".join("(%s)*(%s)" % (a, f)
                       for a, f in zip(cofactors, generators))
    prog = CASProgram(
        SINGULAR, ring="GP_R", ring_vars=ring_vars, generators=generators,
        decls=[("GP_SUM", "poly", terms)],
        body=[], outputs=["GP_SUM"], characteristic=characteristic)
    result = _execute(prog, timeout, _runner)
    if (result["aborted"] or result["returncode"] != 0
            or "? error" in result["stdout"] + result["stderr"]):
        raise CASError("the CAS did not expand the representation:\n%s"
                       % result["stdout"][-1500:])
    got = _parse_result(result, ["GP_SUM"])["GP_SUM"]
    got = " ".join(got) if isinstance(got, list) else str(got)
    got = got.split("=", 1)[-1].strip()
    result.attach_parsed(result["parsed_values"], certificate={
        "kind": "unit_ideal_membership", "target": "1",
        "generators": list(generators), "cofactors": list(cofactors),
        "valid": got == "1", "expanded": got,
    })
    return got == "1", got


def membership_representation(ring_vars, target, generators, characteristic=0,
                              timeout=300, _runner=None):
    """The COFACTORS witnessing `g = sum b_i f_i`, generalising the unit case.

    `unit_ideal_representation` is this with `g = 1`, and it exists because a
    Groebner basis reducing to 1 is EVIDENCE while a representation is a
    CERTIFICATE: given the cofactors, confirming the identity is one expansion
    -- no Buchberger, no monomial order, no trust in the search that found
    them.

    THE REASON TO GENERALISE IT IS THAT MEMBERSHIP IS WHERE MOST OF THIS
    SYSTEM'S WEIGHT SITS.  Emptiness is the dramatic case and the rare one.
    Every IDENTITY is `lhs - rhs in I`; every containment is one membership per
    generator.  Those were decided by REDUCTION, which is a decision procedure
    and leaves nothing behind: "it reduced to 0" is a claim about a run that
    nobody can recheck without doing the run again.

    Returns {"is_member", "cofactors", "reduced"}.  `reduced` is the normal
    form, which is the useful thing to print when the answer is no.
    """
    # The exact checker accepts both infix strings and bounded sparse objects.
    # Singular accepts text only. Compile every accepted representation here,
    # at the backend boundary, rather than letting Python dict syntax leak into
    # a program (first exposed by a 499-term localized guard).
    try:
        target = G.render_polynomial(G.parse_polynomial(
            target, ring_vars, characteristic))
        generators = [G.render_polynomial(G.parse_polynomial(
            value, ring_vars, characteristic)) for value in generators]
    except G.CertificateError as exc:
        raise CASError("invalid exact membership polynomial: %s" % exc)

    # TWO CALLS, for the reason the unit version documents: `lift` errors when
    # there is nothing to lift, so asking for membership and a representation
    # in one program turns "not a member" -- a fine and common answer -- into a
    # CAS error.
    probe = CASProgram(
        SINGULAR, ring="GP_R", ring_vars=ring_vars, generators=generators,
        decls=[("GP_I", "ideal", ",".join(generators)),
               ("GP_S", "ideal", "std(GP_I)"),
               ("GP_T", "poly", target),
               ("GP_RED", "poly", "reduce(GP_T,GP_S)")],
        body=[], outputs=["GP_RED"], characteristic=characteristic)
    res = _execute(probe, timeout, _runner)
    if (res["aborted"] or res["returncode"] != 0
            or "? error" in res["stdout"] + res["stderr"]):
        raise CASError("the CAS did not reduce the target:\n%s"
                       % res["stdout"][-1500:])
    reduced = _parse_result(res, ["GP_RED"])["GP_RED"]
    reduced = " ".join(reduced) if isinstance(reduced, list) else str(reduced)
    reduced = reduced.split("=", 1)[-1].strip()
    if reduced != "0":
        return {"is_member": False, "cofactors": None, "reduced": reduced}

    prog = CASProgram(
        SINGULAR, ring="GP_R", ring_vars=ring_vars, generators=generators,
        decls=[("GP_I", "ideal", ",".join(generators)),
               ("GP_T", "poly", target),
               ("GP_M", "matrix", "lift(GP_I,ideal(GP_T))")],
        body=[], outputs=["GP_M"], characteristic=characteristic)
    result = _execute(prog, timeout, _runner)
    if (result["aborted"] or result["returncode"] != 0
            or "? error" in result["stdout"] + result["stderr"]):
        raise CASError("the CAS did not produce a representation:\n%s"
                       % result["stdout"][-1500:])
    rows = _parse_result(result, ["GP_M"])["GP_M"]
    rows = rows if isinstance(rows, list) else [rows]
    # `GP_M[i,1]=...`, one row per generator IN GENERATOR ORDER, which is the
    # only thing that makes the checker meaningful: a permuted list verifies a
    # different identity and reports it as this one.
    cofactors = []
    for i in range(len(generators)):
        want = "GP_M[%d,1]=" % (i + 1)
        hit = [r for r in rows if r.replace(" ", "").startswith(want)]
        cofactors.append(hit[0].split("=", 1)[-1].strip() if hit else "0")
    result.attach_parsed(result["parsed_values"], certificate={
        "kind": "ideal_membership", "target": target,
        "generators": list(generators), "cofactors": list(cofactors),
    })
    return {"is_member": True, "cofactors": cofactors, "reduced": "0"}


def check_membership_representation(ring_vars, target, generators, cofactors,
                                    characteristic=0, timeout=300,
                                    _runner=None):
    """Expand `sum b_i f_i - g` and see whether it is 0.  NO GROEBNER BASIS.

    The whole point, and the same argument `check_unit_ideal_representation`
    makes: the expensive subtle computation found the cofactors, this one
    multiplies and adds.  A checker sharing no code path with the search is
    worth more than a second run of the search, and it is the only part of the
    chain a reader has to trust.

    It is also the bridge to a proof assistant.  Lean can check a polynomial
    identity; it should never have to run a Groebner engine.
    """
    if len(cofactors) != len(generators):
        raise CASError(
            "%d cofactors for %d generators. A representation must give one "
            "coefficient per generator, in the same order; a shorter list "
            "would verify an identity about a different ideal and report it "
            "as this one." % (len(cofactors), len(generators)))
    try:
        target = G.render_polynomial(G.parse_polynomial(
            target, ring_vars, characteristic))
        generators = [G.render_polynomial(G.parse_polynomial(
            value, ring_vars, characteristic)) for value in generators]
        cofactors = [G.render_polynomial(G.parse_polynomial(
            value, ring_vars, characteristic)) for value in cofactors]
    except G.CertificateError as exc:
        raise CASError("invalid exact membership representation: %s" % exc)

    terms = " + ".join("(%s)*(%s)" % (b, f)
                       for b, f in zip(cofactors, generators))
    prog = CASProgram(
        SINGULAR, ring="GP_R", ring_vars=ring_vars, generators=generators,
        decls=[("GP_DIFF", "poly", "(%s) - (%s)" % (terms, target))],
        body=[], outputs=["GP_DIFF"], characteristic=characteristic)
    result = _execute(prog, timeout, _runner)
    if (result["aborted"] or result["returncode"] != 0
            or "? error" in result["stdout"] + result["stderr"]):
        raise CASError("the CAS did not expand the representation:\n%s"
                       % result["stdout"][-1500:])
    got = _parse_result(result, ["GP_DIFF"])["GP_DIFF"]
    got = " ".join(got) if isinstance(got, list) else str(got)
    got = got.split("=", 1)[-1].strip()
    result.attach_parsed(result["parsed_values"], certificate={
        "kind": "ideal_membership", "target": target,
        "generators": list(generators), "cofactors": list(cofactors),
        "valid": got == "0", "expanded_difference": got,
    })
    return got == "0", got


def factorizing_decomposition(ring_vars, generators, characteristic=0,
                              timeout=300, _runner=None,
                              _return_program=False,
                              _return_execution=False):
    """Split an ideal into a COVER of simpler pieces.  Returns a list of them.

    `facstd` IS A KERNEL BUILTIN, and that is the whole reason this exists.
    `primdecGTZ`, `minAssGTZ` and `radical` all live in `primdec.lib`, which
    the boundary will not load -- the same wall `sat` hit.  So the question
    "can a decomposition be computed inside this dialect at all" had to be
    settled before any vocabulary was designed around one.  It can, by probing
    rather than by assuming either way.

        facstd((xy))              ->  [(y), (x)]
        facstd((y^2-x^3-x^2))     ->  [(cubic)]     irreducible over Q
        facstd((x^2-y^2, xy))     ->  [(x, y)]      the origin

    WHAT COMES BACK IS A COVER, NOT THE PRIMARY DECOMPOSITION, and saying so is
    not a caveat to bury.  The pieces need not be prime and may overlap.  What
    IS guaranteed is `V(I) = union V(I_j)` with every `I_j` containing `I` --
    which is exactly a partition of the model, and exactly what
    `verify.partition_exhaustiveness` decides.  So a decomposition minted here
    carries its own exhaustiveness proof.

    It cannot answer "is this component irreducible".  Nothing available inside
    this boundary can.
    """
    prog = CASProgram(
        SINGULAR, ring="GP_R", ring_vars=ring_vars,
        decls=[("GP_I", "ideal", ",".join(generators) or "0"),
               ("GP_L", "list", "facstd(GP_I)")],
        body=[], outputs=["GP_L"], characteristic=characteristic)
    res = _execute(prog, timeout, _runner)
    if (res["aborted"] or res["returncode"] != 0
            or "? error" in res["stdout"] + res["stderr"]):
        raise CASError("the CAS did not decompose the ideal:\n%s"
                       % res["stdout"][-1500:])
    rows = _parse_result(res, ["GP_L"])["GP_L"]
    rows = rows if isinstance(rows, list) else [rows]
    # `[n]:` opens a piece, `_[m]=expr` is one of its generators.  Parsed
    # positionally rather than by index arithmetic, because a piece with no
    # generators would silently shift everything after it.
    pieces, current = [], None
    for raw in rows:
        line = raw.strip()
        if not line:
            continue
        if line.startswith("[") and line.endswith(":"):
            current = []
            pieces.append(current)
        elif "=" in line and current is not None:
            current.append(line.split("=", 1)[1].strip())
    if not pieces:
        raise CASError(
            "the CAS returned no components for an ideal it accepted. A "
            "decomposition with no pieces covers nothing, and reporting one "
            "would assert a partition of the model into nothing.")
    if any(not piece for piece in pieces):
        raise CASError(
            "the CAS opened a decomposition component but printed no "
            "generator for it. An empty final component is indistinguishable "
            "from truncated facstd output; treating it as the zero ideal would "
            "mint an ambient branch and could falsely certify a cover.")
    if _return_program and _return_execution:
        return pieces, prog, res
    if _return_program:
        return pieces, prog
    if _return_execution:
        return pieces, res
    return pieces


def partition_covers(ring_vars, parent_generators, branches,
                     characteristic=0, timeout=300, _runner=None):
    """Do the branches COVER the parent?  Returns (covered, evidence).

    THE STORE SAID THIS WAS NOT CHECKABLE: "The checker cannot verify that
    gamma in {2,3,4} really matches three branches -- that is mathematics."
    It is mathematics, and it is decidable when the models carry their ideals.

        exhaustive  <=>  V(parent) subset union of V(branch_i)
                    <=>  intersect(I(B_1), .., I(B_k)) subset radical(I(parent))

    Each branch is `parent AND condition`, so every I(B_i) already contains
    I(parent) and the reverse inclusion is automatic.  All the content is in
    the direction above.

    WHY IT MATTERS MORE THAN THE OTHER CHECKS.  A false exhaustiveness does not
    produce a wrong answer at one model.  It produces a COMPLETE-LOOKING CASE
    ANALYSIS WITH A HOLE, and every conclusion drawn from "these are all the
    cases" inherits it -- while each branch remains individually correct, which
    is what makes it invisible by construction.

    RADICAL MEMBERSHIP WITHOUT `radical`, by Rabinowitsch:

        g in radical(I)   <=>   1 in I + (1 - t*g)

    the same identity `saturate_closure` uses, and for the same reason: both
    `radical` and `sat` live in libraries the CAS boundary will not load.
    """
    if not branches:
        raise CASError("a partition with no branches covers nothing")
    # ONE CALL FOR THE INTERSECTION.  `intersect` needs at least two arguments.
    # The store already refuses a one-branch partition ("a split into one piece
    # is just the parent"), so that case cannot arrive through the graph -- but
    # this function is callable directly and should not emit `intersect(I)`.
    decls = [("GP_P", "ideal", ",".join(parent_generators) or "0")]
    names = []
    for i, gens in enumerate(branches):
        names.append("GP_B%d" % i)
        decls.append((names[-1], "ideal", ",".join(gens) or "0"))
    decls.append(("GP_J", "ideal",
                  names[0] if len(names) == 1
                  else "intersect(%s)" % ",".join(names)))
    decls.append(("GP_OUT", "ideal", "std(GP_J)"))
    prog = CASProgram(SINGULAR, ring="GP_R", ring_vars=ring_vars,
                      decls=decls, body=[], outputs=["GP_OUT"],
                      characteristic=characteristic)
    res = _execute(prog, timeout, _runner)
    if (res["aborted"] or res["returncode"] != 0
            or "? error" in res["stdout"] + res["stderr"]):
        raise CASError("the CAS did not intersect the branches:\n%s"
                       % res["stdout"][-1500:])
    rows = _parse_result(res, ["GP_OUT"])["GP_OUT"]
    rows = rows if isinstance(rows, list) else [rows]
    common = [r.split("=", 1)[-1].strip() for r in rows]
    common = [g for g in common if g and g != "0"]
    if not common:
        # The branches share only 0, so their union is everything and the
        # parent is inside it whatever the parent is.
        return True, {"common": [], "uncovered": [],
                      "why": "the branch ideals intersect in (0)"}

    # ONE CALL FOR EVERY RADICAL-MEMBERSHIP QUESTION AT ONCE.  The extra
    # variable goes FIRST so it is the one eliminated by the ordering, matching
    # what `saturate_closure` does with the same trick.
    tvar = "GP_T"
    decls = [("GP_P", "ideal", ",".join(parent_generators) or "0")]
    outs = []
    for j, g in enumerate(common):
        decls.append(("GP_C%d" % j, "ideal",
                      "GP_P, 1-%s*(%s)" % (tvar, g)))
        decls.append(("GP_S%d" % j, "ideal", "std(GP_C%d)" % j))
        outs.append("GP_S%d" % j)
    prog = CASProgram(SINGULAR, ring="GP_R", ring_vars=[tvar] + list(ring_vars),
                      decls=decls, body=[], outputs=outs,
                      characteristic=characteristic)
    res = _execute(prog, timeout, _runner)
    if (res["aborted"] or res["returncode"] != 0
            or "? error" in res["stdout"] + res["stderr"]):
        raise CASError("the CAS did not decide radical membership:\n%s"
                       % res["stdout"][-1500:])
    values = _parse_result(res, outs)
    uncovered = []
    for j, g in enumerate(common):
        v = values["GP_S%d" % j]
        v = v if isinstance(v, list) else [v]
        v = [str(x).split("=", 1)[-1].strip() for x in v]
        if v != ["1"]:
            uncovered.append(g)
    return not uncovered, {"common": common, "uncovered": uncovered,
                           "why": ""}


def ideal_is_unit(ring_vars, generators, characteristic=0, name="GP_I",
                  **kw):
    """Convenience: does the ideal reduce to (1)?

    Returns the raw CAS result.  It deliberately does NOT return a verdict
    object, and the reason is the whole point of the surrounding system: a
    Groebner basis reducing to 1 is EVIDENCE of emptiness, and what makes it a
    KILL is the certificate you attach and the scope that certificate derives.
    Turning `std(I) == 1` straight into "this cell is dead" over an unstated
    field is the shape of the error that shipped.
    """
    prog = CASProgram(
        SINGULAR, ring="GP_R", ring_vars=ring_vars, generators=generators,
        decls=[(name, "ideal", ",".join(generators)),
               ("GP_G", "ideal", "std(%s)" % name)],
        body=[], outputs=["GP_G"], characteristic=characteristic)
    return run_cas(prog, **kw)
