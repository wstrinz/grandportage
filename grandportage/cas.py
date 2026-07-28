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
   verdict is read only from a run with no `? error` line and exactly one
   parseable value per declared output.

   Earned by: an `_ASSAY_` identifier prefix that was illegal because Singular
   identifiers must begin with a letter.  Reviewing the emitter would never
   have caught it; only running it did.
"""

import json
import os
import re
import subprocess

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
                 characteristic=0, generators=None):
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
        self.characteristic = characteristic
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
        assert_no_identifier_collision(dialect, self.ring_vars, self.decls)
        assert_no_identifier_collision(dialect, self.ring_vars,
                                       [(o, "", "") for o in self.outputs])
        assert_declares_nothing(dialect, [e for _n, _t, e in self.decls],
                                "a declaration expression")
        assert_declares_nothing(dialect, self.body, "a body statement")

    @property
    def text(self):
        if self.dialect != SINGULAR:
            raise NotImplementedError(self.dialect)
        lines = ["ring %s = %d,(%s),dp;"
                 % (self.ring, self.characteristic, ",".join(self.ring_vars))]
        for name, typ, expr in self.decls:
            lines.append("%s %s = %s;" % (typ, name, expr))
        lines.extend(self.body)
        for out in self.outputs:
            lines.append('"@@%s:";' % out.upper())
            lines.append("%s;" % out)
        lines.append("quit;")
        return "\n".join(lines) + "\n"


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
                 strictness_witness="", converse_witness="", ring_iso=None):
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
        if ring_iso is not None and type != K.EQUIVALENCE:
            raise TransportNotDeclared(
                "`ring_iso` says an EQUIVALENCE is an isomorphism of coordinate "
                "rings and not merely a bijection on solutions.  It is "
                "meaningless on a %s edge, which is lossy by construction."
                % type)
        self.ring_iso = ring_iso

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
                            "ring_iso"}
        if unknown:
            raise TransportNotDeclared("unknown edge fields: %s"
                                       % ", ".join(sorted(unknown)))
        return cls(**d)

    def events(self, eid, dst, dst_desc, dst_field=None, dst_chart=None,
               ring_vars=None, generators=None):
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
        if self.debt_why:
            edge["debt_why"] = self.debt_why
        return [model, edge]


# ---------------------------------------------------------------------------
# Running
# ---------------------------------------------------------------------------
ABORT_CODES = {124: "timeout", 137: "SIGKILL", 139: "SIGSEGV"}

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

    runner = _runner or _run_subprocess
    result = runner(program, timeout)

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
        result["values"] = _parse_outputs(result["stdout"], program.outputs)
        result["verdict"] = "OK"

    result["transport"] = {"src": transport.src, "type": transport.type,
                           "dst": produces}
    if record:
        eid = edge_id or ("E-%s" % produces)
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
        else:
            events = transport.events(
                eid, produces, describes,
                dst_field=dst_field, dst_chart=dst_chart,
                ring_vars=getattr(program, "ring_vars", None),
                generators=getattr(program, "generators", None))
            events[0]["cite"] = events[1]["cite"] = cite or transport.cite
            result["events"] = events
        S.append(result["events"], root=root)
    return result


def _run_subprocess(program, timeout):
    argv = _argv()
    try:
        proc = subprocess.run(argv, input=program.text, capture_output=True,
                              text=True, timeout=timeout)
        rc, stdout, stderr = proc.returncode, proc.stdout, proc.stderr
    except subprocess.TimeoutExpired:
        rc, stdout, stderr = 124, "", "timeout after %ss" % timeout
    except FileNotFoundError as exc:
        raise CASError("cannot reach the CAS via %s: %s" % (argv, exc))
    return {"returncode": rc, "stdout": stdout, "stderr": stderr,
            "aborted": rc in ABORT_CODES,
            "abort_reason": ABORT_CODES.get(rc), "argv": argv}


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
    runner = _runner or _run_subprocess
    result = runner(prog, timeout)
    if result["aborted"]:
        raise CASError("classification aborted (%s); an unfinished run "
                       "classifies nothing" % result.get("abort_reason"))
    if "? error" in result["stdout"] + result["stderr"]:
        raise CASError("the CAS reported an error:\n%s"
                       % result["stdout"][-2000:])
    if result["returncode"] != 0:
        raise CASError("the CAS exited %s" % result["returncode"])
    values = _parse_outputs(result["stdout"], outputs)

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
    runner = _runner or _run_subprocess
    result = runner(prog, timeout)
    if result["aborted"] or "? error" in result["stdout"] + result["stderr"] \
            or result["returncode"] != 0:
        raise CASError("the CAS did not evaluate the witness:\n%s"
                       % result["stdout"][-1500:])
    values = _parse_outputs(result["stdout"], outs)
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
