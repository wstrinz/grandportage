"""MCP server: the CAS, wrapped so that every call emits a typed edge.

Zero dependencies -- JSON-RPC 2.0 over stdio, written out rather than pulled in.
That is a deliberate choice and not stubbornness: the MCP specification is
moving toward statelessness at the transport layer, and a transport GRAPH is
stateful.  Owning the ~150 lines that speak the protocol means the state can
live where it belongs -- `.portage/graph.jsonl` -- instead of in a session that
the protocol may stop guaranteeing.  Nothing in this server holds state between
calls; restart it mid-campaign and the next call folds the same graph.

THE FORCING FUNCTION.  `edge` is `required` in the JSON Schema of every tool
that produces a model, AND the handler validates it, AND `run_cas` takes it as
a keyword-only argument with no default.  Three layers saying the same thing,
because each protects against a different failure: the schema tells the model
what to send, the handler catches a malformed send, and the signature makes it
impossible for a future refactor to introduce a path that skips both.

Register in `.mcp.json`:

    {"mcpServers": {"grand-portage": {
        "command": "python", "args": ["-m", "grandportage.mcp"]}}}
"""

import json
import os
import sys
import traceback

from . import artifacts as A
from . import cas
from . import check as C
from . import format as F
from . import hook as HK
from . import kernel as K
from . import store as S

PROTOCOL_VERSION = "2025-06-18"
SUPPORTED_PROTOCOLS = ("2024-11-05", "2025-03-26", "2025-06-18")

ROOT = os.environ.get("GP_ROOT", ".")

# Reported in `serverInfo`, which is where a client looks to know what it is
# talking to.  It said 0.1.0 for four minor releases -- the same drift the
# check-count spans exist to prevent, in the one field a machine reads.
from . import __version__ as VERSION  # one source of truth


# ---------------------------------------------------------------------------
# The transport declaration, as a schema fragment.
#
# The description text matters more than usual here.  This is the one place a
# model is asked to make a modelling judgement, and the enum alone does not
# tell it how to choose.  So the description is a decision procedure, phrased
# as "what does this step LOSE?" rather than "what kind of step is this?" --
# the second question invites a guess, the first has an answer the caller knows.
# ---------------------------------------------------------------------------
EDGE_SCHEMA = {
    "type": "object",
    "description": (
        "REQUIRED. How the model this computation produces relates to the one "
        "it came from. There is no default and no inference: a step whose "
        "relaxation type is not named is exactly where unsound conclusions "
        "come from."),
    "properties": {
        "src": {"type": "string",
                "description": "id of the model this computation starts from"},
        "type": {
            "type": "string",
            "enum": list(K.DECLARABLE_TYPES),
            "description": (
                "Ask what the step LOSES.\n"
                "  EQUIVALENCE - nothing, and you can exhibit the converse. "
                "Do not use this because a step 'should be' reversible.\n"
                "  NECESSARY_CONDITION - equations. The target is a strict "
                "relaxation: every point of the source is a point of the "
                "target, not conversely.\n"
                "  BASE_EXTENSION - the coefficient field grows. Note the "
                "reversed asymmetry: witnesses travel along the arrow freely, "
                "emptiness only with a certificate that base-changes.\n"
                "  IMAGE_CLOSURE - an elimination or a projection. What you "
                "get back is the Zariski CLOSURE of the image, and a point of "
                "the closure need not lift.\n"
                "  SPECIALIZATION - the characteristic changes. Carries no "
                "existence statement in either direction.\n"
                "  RESTRICTION - INEQUALITIES, not equations. src is a "
                "semialgebraic subset of dst cut out by strict inequalities -- "
                "a positivity cone, an open region, a nondegeneracy condition "
                "-- in the SAME coordinates, with nothing added to the ideal. "
                "Reach for this whenever you are about to write "
                "NECESSARY_CONDITION for a step that dropped no equation: the "
                "point-transports are identical, so the wrong label licenses "
                "nothing false and hides whether a result is global or only "
                "generic. An IDENTITY crosses ALONG unconditionally, because a "
                "restriction shares its ideal -- but only things that really "
                "ARE identities: a relation observed to vanish at every point "
                "of the region is a PREDICATE, and that does not cross.\n"
                "  UNTYPED - not yet known. Legal, but requires debt_why, and "
                "no conclusion will cross this edge until it is typed.")},
        "why": {"type": "string",
                "description": "REQUIRED. What information does this step lose?"},
        "map_kind": {"type": "string", "enum": list(K.MAP_KINDS),
                     "description": (
                         "POLYNOMIAL / IDENTITY_MAP if the coordinate change "
                         "is denominator-free, RATIONAL otherwise. This single "
                         "attribute decides whether a dictionary may be "
                         "rewritten across the edge.")},
        "drops": {"type": "array", "items": {"type": "string"},
                  "description": "the specific conditions this step discards"},
        "strictness_witness": {
            "type": "string",
            "description": (
                "explicit evidence that the step IS lossy -- e.g. a point of "
                "the target that is not in the source. This REFUTES an "
                "equivalence; it never documents one.")},
        "converse_witness": {
            "type": "string",
            "description": (
                "only for EQUIVALENCE: the construction that recovers a point "
                "of the source from a point of the target. 'This step should "
                "be reversible' is a feeling; this field is the converse. If "
                "you cannot fill it, the step is a NECESSARY_CONDITION.")},
        "witness": {"type": "string",
                    "description": (
                        "DEPRECATED, read as strictness_witness. Use the two "
                        "fields above -- they have opposite polarity and one "
                        "name for both meant evidence against an equivalence "
                        "could document one.")},
        "forward": {
            "type": "object",
            "additionalProperties": {"type": "string"},
            "description": (
                "EQUIVALENCE only. The point-forward map from source to target, "
                "written as a simultaneous polynomial substitution with one "
                "expression for every ring variable. Polynomial pullback runs "
                "contravariantly. The current verifier requires both endpoints "
                "to use the same ring-variable names. Supplying forward and "
                "inverse declares a MAPPED equivalence, not literal containment "
                "of the two solution sets as written. Structured maps license "
                "IDENTITY transport only after `VERIFIED`.")},
        "inverse": {
            "type": "object",
            "additionalProperties": {"type": "string"},
            "description": (
                "EQUIVALENCE only. The point-inverse map from target to source, "
                "paired with forward. `gp verify` checks both ideal pullbacks "
                "and both inverse compositions. The field names are exactly "
                "`forward` and `inverse`, not `maps` or `inverse_maps`.")},
        "ring_iso": {
            "type": "boolean",
            "description": (
                "EQUIVALENCE only. True if the step is an ISOMORPHISM OF "
                "COORDINATE RINGS, not merely a bijection on solutions. "
                "Required before a rewriting (an IDENTITY claim) may cross: "
                "V(x^2) and V(x) have the same single solution, yet x = 0 "
                "holds in one coordinate ring and is false in the other. "
                "Saturation and radicalization are exactly that step, so "
                "'the solutions are unchanged' is NOT sufficient here.")},
        "discharge_hint": {
            "type": "string",
            "description": (
                "optional: what would actually close a refusal across THIS "
                "edge. The checker knows the requirement a cell imposes and "
                "cannot know your remedy -- it will offer an illustration from "
                "another domain if you do not say. One sentence naming the "
                "computation or construction that would settle it.")},
        "zariski_dense": {
            "type": "boolean",
            "description": (
                "RETRACTED, and consulted by no cell. It used to gate "
                "RESTRICTION/ALONG/IDENTITY on the target being irreducible "
                "with Zariski-dense real points. That condition is NOT "
                "SUFFICIENT -- the nodal cubic y^2 = x^2(x-1) satisfies every "
                "word of it, and the region cut by x^2+y^2 < 1/2 is the "
                "ISOLATED real point (0,0), where `x = 0` holds and on the "
                "curve it does not. It was also beside the point: a "
                "restriction shares its ideal, so an IDENTITY is the same "
                "statement at both ends and there was nothing to gate. The "
                "field is kept only so graphs that declared it keep folding. "
                "Do not declare it on anything new.")},
        "debt_why": {"type": "string",
                     "description": "required when type is UNTYPED"},
        "cite": {"type": "string"},
    },
    "required": ["src", "type", "why"],
}
for _legacy_edge_field in ("witness", "zariski_dense"):
    EDGE_SCHEMA["properties"].pop(_legacy_edge_field, None)
EDGE_SCHEMA["required"].append("map_kind")
EDGE_SCHEMA["additionalProperties"] = False


CONDITION_SCHEMA = {
    "type": "object",
    "description": (
        "A conjunction of exact-affine point conditions. ZERO means the "
        "polynomial vanishes; NONZERO means it does not. Every expression is "
        "parsed against the claim model's exact polynomial ring. Verified mapped "
        "equivalences rewrite it contravariantly. Matching identity-coordinate "
        "maps and checked Eliminate projections preserve it under AGAINST before "
        "a polynomial-section elimination checks target expressibility."),
    "properties": {
        "all": {
            "type": "array",
            "minItems": 1,
            "items": {
                "type": "object",
                "properties": {
                    "relation": {"type": "string",
                                 "enum": list(K.CONDITION_RELATIONS)},
                    "expression": {"type": "string", "minLength": 1},
                },
                "required": ["relation", "expression"],
                "additionalProperties": False,
            },
        },
    },
    "required": ["all"],
    "additionalProperties": False,
}


def _event_schema(kind):
    properties = {field: {} for field in sorted(F.EVENT_FIELDS[kind])}
    if kind == "claim":
        properties["condition"] = CONDITION_SCHEMA
    properties["ev"] = {"type": "string", "enum": [kind]}
    if kind == "model":
        properties["coefficient_domain"] = {
            "type": "string",
            "pattern": "^(Q|F_[0-9]+)$",
            "description": (
                "exact certificate domain; must match characteristic"),
        }
        properties["point_universe"] = {
            "type": "string",
            "enum": list(S.POINT_UNIVERSES),
            "description": "BASE or algebraic closure of coefficient_domain",
        }
    return {
        "type": "object",
        "properties": properties,
        "required": sorted(F.REQUIRED_FIELDS.get(kind, {"ev"})),
        "additionalProperties": False,
    }


DECLARABLE_EVENT_SCHEMA = {
    "description": (
        "A native graph event. Event schemas are closed: misspelled or "
        "unowned fields are rejected rather than retained as inert metadata."),
    "oneOf": [
        _event_schema(kind) for kind in sorted(F.EVENT_FIELDS)
        if kind not in ("meta", "verdict")
    ],
}


def _tool(name, description, properties, required):
    return {"name": name, "description": description,
            "inputSchema": {"type": "object", "properties": properties,
                            "required": required,
                            "additionalProperties": False}}


TOOLS = [
    _tool(
        "cas_ideal_is_unit",
        "Run a Groebner basis computation to see whether an ideal reduces to "
        "(1), and record the typed edge to the model it produces. Returns "
        "EVIDENCE, not a verdict: std(I)==1 becomes a kill only once you "
        "attach a certificate kind and the scope that certificate derives. "
        "Requires `edge` -- no CAS process is spawned without it.",
        {"ring_vars": {"type": "array", "items": {"type": "string"},
                       "description": "ring variables, in order"},
         "generators": {"type": "array", "items": {"type": "string"},
                        "description": "ideal generators as CAS expressions"},
         "characteristic": {"type": "integer", "default": 0,
                            "description": (
                                "0 for char 0. A nonzero value is "
                                "RECONNAISSANCE: a mod-p result may direct "
                                "effort and may never close a case, and the "
                                "step to char 0 is a SPECIALIZATION edge that "
                                "carries nothing.")},
         "produces": {"type": "string",
                      "description": "id for the model this run produces"},
         "describes": {"type": "string",
                       "description": "one line: what that model IS"},
         "edge": EDGE_SCHEMA},
        ["ring_vars", "generators", "produces", "describes", "edge"]),

    _tool(
        "portage_declare",
        "Append events to the graph without running a CAS: models, claims, "
        "inferences, certificate kinds, provenance. This is how a conclusion "
        "gets recorded, and recording it is what submits it to the checker. "
        "The write is transactional against the fold -- if the events do not "
        "produce a well-formed graph, nothing is written.",
        {"events": {"type": "array", "items": DECLARABLE_EVENT_SCHEMA,
                    "description": (
                        "graph events. Each needs `ev`: one of certificate, "
                        "model, edge, claim, inference, built_by, note. An "
                        "EMPTY claim must carry a `certificate` kind, and its "
                        "scope is DERIVED from that certificate rather than "
                        "from what you declare. A PREDICATE may carry a closed-schema "
                        "structured `condition`: {all: [{relation: ZERO or "
                        "NONZERO, expression: polynomial}, ...]}. Expressions "
                        "must parse in the claim model. Verified equivalences "
                        "rewrite them contravariantly; matching identity maps "
                        "and checked Eliminate projections preserve them under "
                        "AGAINST. A later section-certified elimination checks "
                        "the resulting expressions in its retained target. "
                        "An inference may rest on SEVERAL premises: use "
                        "`premises: [{claim, path}, ...]` instead of "
                        "`claim`+`path` when the argument combines facts. "
                        "Every premise must transport to the SAME model -- if "
                        "yours do not meet, they are separate statements with "
                        "a conjunction written between them, which is the "
                        "commonest way a wrong join gets recorded. Put the "
                        "side conditions in as premises rather than in a note: "
                        "a note is carried and never typed, so an argument "
                        "whose load-bearing premise lives there is reported "
                        "clean while the thing making it valid is invisible. "
                        "An IDENTITY claim must carry `identity_origin`, "
                        "because it decides which way the rewriting travels. "
                        "Ask: is this rewriting true BEFORE this model's "
                        "equations are imposed? A definition, a substitution "
                        "or a change of variables is AMBIENT and travels both "
                        "ways. Something that follows FROM the model's "
                        "equations is DERIVED: it restricts to tighter models "
                        "but dies when those equations are dropped. If you "
                        "have not established which, say UNKNOWN -- it is a "
                        "legal answer, it licenses only what both do, and "
                        "`cas_classify_identity` settles it by computation. "
                        "BETTER STILL, RECORD THE REWRITING ITSELF: an "
                        "IDENTITY may carry `lhs`, `rhs` and `ring_vars`, and "
                        "when it does the claim stops being prose and becomes "
                        "decidable. An IDENTITY asserts that lhs - rhs lies in "
                        "the model's ideal, reduction modulo a Groebner basis "
                        "DECIDES that, and `portage_verify` will run it and "
                        "record the answer -- including REFUTED, which means "
                        "the rewriting is false at the model it was claimed "
                        "at, something no amount of correct transport typing "
                        "would ever surface. Give all three or none; half an "
                        "identity is not a weaker identity. You may NOT "
                        "declare `identity_verdict` -- it is what a verifier "
                        "found, and its whole value is that a computation "
                        "stands behind it. "
                        "A claim's optional `ladder` is its EVIDENCE GRADE and "
                        "is ORTHOGONAL to transport -- it never licenses a "
                        "step and the type system never grades evidence. "
                        "Values, weakest first: open, claimed, exact-checked, "
                        "independently-audited, certified. Use `claimed` for "
                        "an assertion you have not verified (including a "
                        "published one stated without proof), `exact-checked` "
                        "for something a gated checker verifies, and "
                        "`independently-audited` only when a SECOND "
                        "implementation agrees. One gated checker is "
                        "exact-checking, not audit. "
                        "The top three grades ASSERT THAT SOMETHING HAPPENED, "
                        "so each requires `established_by`: RAN (executed "
                        "here), READ (read a source or file, not executed), "
                        "CITED (relying on a paper or authority) or "
                        "NOT_REACHED. Most of those are then refused against "
                        "those grades, which is the point -- if no run backs "
                        "the claim, its grade is `claimed`. Leaving both "
                        "fields off is fine; an ungraded claim is merely "
                        "ungraded. What is refused is half a grade. "
                        "TO REPLACE A RECORD YOU HAVE ALREADY MADE, do not "
                        "mint an unrelated id and leave the old one sitting "
                        "there: declare the new one with `supersedes` and "
                        "`discharge_kind`. "
                        "THERE ARE TWO DISCHARGE VOCABULARIES AND THEY DO NOT "
                        "MIX. Which one you are choosing from is settled "
                        "before you think about the change at all, by WHAT "
                        "you are replacing: an EDGE takes one list, a CLAIM "
                        "or an INFERENCE takes the other. There is no "
                        "combined list, because the two lists answer "
                        "different questions -- and borrowing across them "
                        "fails in two different ways, neither of which helps: "
                        "a supersession kind from the edge list is REFUSED on "
                        "a claim, and one from the claim list is a word no "
                        "obligation has ever admitted, so on an edge it "
                        "discharges nothing.\n"
                        "REPLACING AN EDGE -- DERIVE, RETYPE, ACCEPT, WITHDRAW. "
                        "An edge "
                        "is what a transport refusal is recorded AGAINST, so "
                        "replacing one asks: WHAT HAPPENED TO THE OBLIGATION "
                        "the old edge was carrying? Supersession INHERITS "
                        "those obligations rather than clearing them, and a "
                        "baseline entry may pin `admits`, in which case the "
                        "only exit is the one the obligation asked for.\n"
                        "  DERIVE - the mathematics the refusal was waiting "
                        "for now exists. The refusal goes away because the "
                        "thing it wanted is there.\n"
                        "  RETYPE - the relation was mis-stated and the true "
                        "one licenses the step. Legitimate, and the move most "
                        "reached for when the mathematics is hard, which is "
                        "why an obligation recorded as admitting only DERIVE "
                        "refuses it.\n"
                        "  ACCEPT - carry it deliberately, in the open, with "
                        "a reason.\n"
                        "  WITHDRAW - this was not an edge at all. Nothing "
                        "replaces it, and any live inference crossing it must "
                        "be retracted or rerouted over a real path.\n"
                        "  DERIVE is a discharge kind and is NOT the "
                        "identity_origin value DERIVED described above. One "
                        "is a move that closes an obligation; the other says "
                        "where a rewriting is valid. They share six letters "
                        "and nothing else.\n"
                        "REPLACING A CLAIM OR AN INFERENCE -- AMEND, "
                        "RELICENSE, RESTATE, RETRACT. These records carry no "
                        "obligation; they carry CONTENT. So the question is "
                        "not what was discharged but WHAT CHANGED ABOUT THE "
                        "RECORD, and the answer is checked against the two "
                        "versions rather than taken on your word.\n"
                        "  AMEND - nothing that licenses a transport changed: "
                        "a citation, a caveat, an evidence grade.\n"
                        "  RELICENSE - an attribute that DECIDES transport "
                        "moved (certificate, scope, identity_origin, "
                        "coefficients_in_base, witness_kind). The quiet one: "
                        "the sentence is unchanged and what stands behind it "
                        "is not.\n"
                        "  RESTATE - the statement, kind or model itself "
                        "changed.\n"
                        "  RETRACT - withdrawn, and nothing replaces it.\n"
                        "The tool DIFFS the two records and "
                        "refuses a kind that understates what moved, so "
                        "'I only added an attribute' will not get a licensing "
                        "field past unexamined. Superseding does NOT repoint "
                        "the inferences that used the old claim -- they are "
                        "reported, at a severity that depends on whether "
                        "anything they relied on actually changed.")},
         "root": {"type": "string",
                  "description": (
                      "the campaign directory to read or write -- the one "
                      "holding `.portage/`. Omit and the server uses its own "
                      "working directory, which is the SESSION root and not "
                      "necessarily the campaign you are in. Name it whenever "
                      "you are working in a subdirectory.")}},
        ["events"]),

    _tool(
        "cas_classify_identity",
        "DECIDE whether a rewriting is AMBIENT or DERIVED, by computing it "
        "rather than judging it. An IDENTITY claim must say where its "
        "rewriting is valid, because that decides which way it can travel: an "
        "AMBIENT rewriting holds in the coordinate ring before this model's "
        "equations are imposed and so survives dropping them, while a DERIVED "
        "one does not. This reduces LHS - RHS and answers from the normal "
        "form. It can also report FALSE_AT_MODEL -- the rewriting does not "
        "hold where it was claimed -- which no transport typing would catch. "
        "Touches NOTHING in the graph; declare the answer yourself.",
        {"ring_vars": {"type": "array", "items": {"type": "string"},
                       "description": "ring variables, in order"},
         "lhs": {"type": "string", "description": "left side of the rewriting"},
         "rhs": {"type": "string", "description": "right side"},
         "generators": {
             "type": "array", "items": {"type": "string"},
             "description": (
                 "generators of the model's ideal. Omit if the model imposes "
                 "no equations -- then AMBIENT and DERIVED coincide.")},
         "characteristic": {"type": "integer", "default": 0}},
        ["ring_vars", "lhs", "rhs"]),

    _tool(
        "portage_check",
        "Type-check the accumulated graph. Returns findings with their "
        "discharge moves, and the list of inferences that came back clean.",
        {"floor": {"type": "string", "enum": list(C.SEVERITY_ORDER),
                   "description": "lowest severity to report as failing"},
         "full": {"type": "boolean", "default": False,
                  "description": (
                      "also print the detail of findings already accepted "
                      "into the baseline. Off by default: once a campaign has "
                      "a real graph, re-printing every carried obligation is "
                      "noise on every call.")},
         "root": {"type": "string",
                  "description": (
                      "the campaign directory to read or write -- the one "
                      "holding `.portage/`. Omit and the server uses its own "
                      "working directory, which is the SESSION root and not "
                      "necessarily the campaign you are in. Name it whenever "
                      "you are working in a subdirectory.")}},
        []),

    _tool(
        "portage_verify",
        "Spend CAS time to SETTLE what the graph currently takes on the "
        "author's word, and record the answers. Two things get checked: every "
        "IDENTITY claim carrying `lhs`/`rhs` is reduced (is lhs - rhs in the "
        "model's ideal?), and every edge whose endpoints carry generators has "
        "its central assertion V(src) subset V(dst) tested. `portage_check` "
        "reports which objects are missing the data this needs. A REFUTED "
        "identity means the rewriting is FALSE where it was claimed -- the one "
        "error class transport typing can never surface, because every route "
        "from a false premise is unsound no matter how it is typed.",
        {"timeout": {"type": "integer", "default": 300},
         "dry_run": {"type": "boolean", "default": False,
                     "description": (
                         "report the verdicts without recording them. Off by "
                         "default: a verification that lives in a scrollback "
                         "is one nobody can act on next week.")},
         "root": {"type": "string",
                  "description": (
                      "the campaign directory to read or write -- the one "
                      "holding `.portage/`. Omit and the server uses its own "
                      "working directory, which is the SESSION root and not "
                      "necessarily the campaign you are in. Name it whenever "
                      "you are working in a subdirectory.")}},
        []),

    _tool(
        "portage_verify_elimination",
        "Certify exact coordinate-ring contraction for one constructor-built "
        "Eliminate edge using a polynomial section. The section fixes retained "
        "variables and maps every eliminated variable to a polynomial in them. "
        "It also supplies explicit polynomial point lifts; constructed image "
        "authority requires the independent no-invention verdict as well.",
        {"edge": {"type": "string"},
         "section": {
             "type": "object",
             "additionalProperties": {"type": "string"},
             "description": (
                 "map each eliminated variable to its polynomial image in the "
                 "retained variables")},
         "timeout": {"type": "integer", "default": 300},
         "dry_run": {"type": "boolean", "default": False},
         "root": {"type": "string",
                  "description": "campaign directory holding .portage/"}},
        ["edge", "section"]),
    _tool(
        "portage_verify_elimination_point_lift",
        "Check a finite cover of a constructor-built Eliminate target by "
        "principal-open rational lift charts plus one all-guards-zero "
        "polynomial fallback. Exact membership identities are replayed before "
        "point-surjective authority is recorded; contraction exactness remains "
        "a separate obligation.",
        {"edge": {"type": "string"},
         "certificate": {
             "type": "object",
             "description": (
                 "{charts:[{guard, lift:{variable:{numerator,"
                 "denominator_power}}}], fallback:{lift:{variable:poly}}}")},
         "timeout": {"type": "integer", "default": 300},
         "dry_run": {"type": "boolean", "default": False},
         "root": {"type": "string",
                  "description": "campaign directory holding .portage/"}},
        ["edge", "certificate"]),
    _tool(
        "portage_verify_elimination_groebner",
        "Produce a bounded pure-lex Groebner certificate for one constructor-"
        "built Eliminate edge, check it without trusting Singular, persist "
        "the proof and producer artifacts, and license exact contraction only "
        "when the separate no-invention verdict is also current. This grants "
        "no geometric point-image authority.",
        {"edge": {"type": "string"},
         "timeout": {"type": "integer", "default": 300},
         "dry_run": {"type": "boolean", "default": False},
         "root": {"type": "string",
                  "description": "campaign directory holding .portage/"}},
        ["edge"]),
    _tool(
        "cas_health",
        "Check that the CAS is reachable and answers correctly, WITHOUT "
        "touching the graph. Runs a trivial ideal with a known answer. Use "
        "this first on a new machine -- every other CAS tool requires "
        "`produces` and `edge`, so the cheapest plumbing probe would otherwise "
        "permanently add a model and an edge to the campaign.",
        {}, []),

    _tool(
        "portage_show",
        "Print the current graph: models, edges, claims, inferences. Read this "
        "before adding to a campaign you did not start -- the graph is the "
        "state, so it is the handoff.",
        {"root": {"type": "string",
                  "description": (
                      "the campaign directory to read -- the one holding "
                      "`.portage/`. Omit and the server uses its own working "
                      "directory, which is the SESSION root.")}}, []),

    _tool(
        "portage_transport_table",
        "The transport table and the certificate registry, printed from the "
        "kernel. Read this when deciding an edge type or a certificate kind.",
        {}, []),
]


# ---------------------------------------------------------------------------
# Handlers
# ---------------------------------------------------------------------------
def _text(s):
    return {"content": [{"type": "text", "text": s}]}


def _err(s):
    return {"content": [{"type": "text", "text": s}], "isError": True}


def h_cas_ideal_is_unit(args, root):
    edge = args.get("edge")
    if edge is None:
        # Belt and braces: the schema says required, but a client that ignores
        # its own schema must not reach the solver either.
        return _err(str(cas.TransportNotDeclared(
            "no transport declared. A computation that produces a new model "
            "must say how that model relates to its source. Pass edge with "
            "src, type and why; see portage_transport_table for the types.")))
    result = cas.ideal_is_unit(
        args["ring_vars"], args["generators"],
        characteristic=args.get("characteristic", 0),
        edge=edge, produces=args["produces"], describes=args["describes"],
        root=root, dst_field=args.get("field"), cite=args.get("cite", ""))
    lines = ["run: %s" % result["verdict"],
             "recorded: model %s, edge %s (%s from %s)"
             % (args["produces"], "E-" + args["produces"],
                edge.get("type"), edge.get("src"))]
    if result["values"]:
        for k, v in sorted(result["values"].items()):
            # Say how many generators there are.  Printing only the first line
            # of a basis lets `GP_G[1]=f6` be read as "the ideal is (f6)".
            if isinstance(v, list):
                lines.append("%s: Groebner basis, %d generators" % (k, len(v)))
                lines.extend("    " + row for row in v)
            else:
                lines.append("%s: Groebner basis, 1 generator" % k)
                lines.append("    " + v)
        gb = result["values"].get("GP_G")
        gb_is_unit = (not isinstance(gb, list)
                      and str(gb).replace(" ", "").endswith("=1"))
        if gb_is_unit:
            lines.append("")
            lines.append(
                "The ideal reduced to (1). That is EVIDENCE of emptiness and "
                "not yet a kill: record it as an EMPTY claim with a "
                "`certificate` kind, and the scope will be derived. If the "
                "certificate is field-relative the emptiness will NOT "
                "base-change, and reading it as geometric is the exact error "
                "this system exists to refuse.")
    if result["verdict"] == "ABORTED":
        lines.append("An unfinished run is not evidence of anything.")
    return _text("\n".join(lines))


def h_cas_health(args, root):
    """Prove the CAS answers, without writing anything.

    Wanted by the first real user: every other path requires `produces` and
    `edge`, so the cheapest possible "does Singular actually work from here"
    probe permanently added a model and an edge.  That pushed them toward
    composing the real call first and discovering plumbing failures inside it,
    which is the opposite of what you want on a first run.
    """
    prog = cas.CASProgram(
        cas.SINGULAR, ring="GP_HEALTH", ring_vars=["x", "y"],
        decls=[("GPH_I", "ideal", "x-1,y-2"),
               ("GPH_G", "ideal", "std(GPH_I)")],
        body=[], outputs=["GPH_G"])
    try:
        result = cas._execute(prog, 60)
    except cas.CASError as exc:
        return _err("CAS UNREACHABLE via %s\n%s" % (cas._argv(), exc))
    if result["aborted"]:
        return _err("CAS aborted (%s) via %s"
                    % (result["abort_reason"], result["argv"]))
    if "? error" in result["stdout"] + result["stderr"]:
        return _err("CAS reported an error:\n%s" % result["stdout"][-800:])
    try:
        values = cas._parse_result(result, prog.outputs)
    except cas.CASError as exc:
        return _err("CAS output unparseable: %s" % exc)
    gb = values["GPH_G"]
    gb = gb if isinstance(gb, list) else [gb]
    joined = "".join(gb).replace(" ", "")
    ok = "y-2" in joined and "x-1" in joined
    return _text(
        "CAS reachable via %s\n"
        "probe ideal (x-1, y-2) -> %d generator(s):\n%s\n%s\n"
        "NOTHING was written to the graph."
        % (" ".join(result["argv"]), len(gb),
           "\n".join("    " + g for g in gb),
           "answer is correct."
           if ok else
           "UNEXPECTED answer -- the CAS ran but did not return the known "
           "basis. Do not trust verdicts from it until this is understood."))


def h_portage_declare(args, root):
    events = args.get("events") or []
    if not isinstance(events, list):
        return _err("`events` must be a list of graph events")
    # NAME THE GRAPH BEING WRITTEN, ALWAYS.
    #
    # `GP_ROOT` defaults to "." and "." is the SERVER PROCESS's cwd, which is
    # the session root -- not the directory the `.mcp.json` declaring it sits
    # in.  A campaign whose `.mcp.json` says `GP_ROOT: "."` therefore writes to
    # a DIFFERENT graph than `gp check` run inside that campaign reads, and
    # nothing said so.
    #
    # A live lane hit this in the worst available way: the root graph happened
    # to be in a refused state from an unrelated session, `declare` is
    # transactional against the fold, and so the author's FIRST declaration came
    # back rejected citing a claim id they had never seen, in a campaign they
    # had just created.  They diagnosed it by diffing four copies of a fixture.
    #
    # Resolving the root differently is not available here -- the server does
    # not know where its config lives.  Saying which graph it wrote is, costs
    # one line, and turns a mystery into a fact on the first call.
    where = os.path.abspath(S.graph_path(root))
    try:
        S.append(events, root=root)
    except Exception as exc:
        # The exception TYPE is part of the message on purpose -- a caller
        # distinguishes a ScopeError from a GraphError by name, and an existing
        # test pins it. The first version of this wrapper dropped it.
        return _err("%s: %s\n\nTHE GRAPH BEING WRITTEN IS %s\nIf that is not "
                    "the campaign you are working in, `GP_ROOT` resolved "
                    "against this server's working directory rather than the "
                    "directory its `.mcp.json` sits in. Nothing above may be "
                    "about your campaign at all."
                    % (type(exc).__name__, exc, where))
    kinds = {}
    for e in events:
        kinds[e.get("ev")] = kinds.get(e.get("ev"), 0) + 1
    summary = ", ".join("%d %s" % (v, k) for k, v in sorted(kinds.items()))
    accepted = HK.read_baseline(root)["accepted"]
    findings = C.run(S.load(S.graph_path(root)), accepted)
    return _text("recorded %s in %s\n\n%s"
                 % (summary, where, C.render(findings, accepted)))


def h_portage_check(args, root):
    path = S.graph_path(root)
    if not os.path.exists(path):
        return _text("no graph yet at %s" % path)
    graph = S.load(path)
    accepted = HK.read_baseline(root)["accepted"]
    findings = C.run(graph, accepted)
    clean = C.clean_inferences(graph, findings)
    # `full` was declared in this tool's schema and never read here, so an
    # agent could ask to see carried obligations and be handed the same output.
    # A schema that lies is worse than a missing feature: it is a promise the
    # caller reasons from.
    accepted = HK.read_baseline(root)["accepted"]
    return _text("%s\nclean inferences (%d): %s"
                 % (C.render(findings, accepted, full=bool(args.get("full"))),
                    len(clean), ", ".join(clean) or "-"))


def h_portage_verify(args, root):
    from . import verify as V
    path = S.graph_path(root)
    if not os.path.exists(path):
        return _text("no graph yet at %s" % path)
    results = V.verify_all(root=root, timeout=int(args.get("timeout") or 300),
                           record=not args.get("dry_run"))
    if not results:
        return _text(
            "nothing to verify: no edge or claim carries the data a reduction "
            "needs.\n"
            "  Edges need `generators` and `ring_vars` on BOTH endpoints; "
            "IDENTITY claims need `lhs`, `rhs` and `ring_vars`.\n"
            "  `portage_check` reports which ones are missing them.")
    lines = []
    for subject, oid, verdict, why in results:
        lines.append("%s  %s %s\n    %s" % (verdict, subject, oid, why))
    lines.append("--dry-run: nothing was recorded."
                 if args.get("dry_run")
                 else "recorded %d verdict(s)." % len(results))
    return _text("\n\n".join(lines))


def h_portage_verify_elimination(args, root):
    from . import verify as V
    path = S.graph_path(root)
    if not os.path.exists(path):
        return _text("no graph yet at %s" % path)
    section = args.get("section")
    if not isinstance(section, dict):
        return _err("section must be an object mapping variables to polynomials")
    try:
        verdict, why, _representation = V.verify_elimination_section(
            root, args.get("edge"), section,
            timeout=int(args.get("timeout") or 300),
            record=not args.get("dry_run"))
    except (A.ArtifactError, OSError, S.GraphError, ValueError) as exc:
        return _err("elimination verification failed: %s" % exc)
    suffix = ("--dry-run: nothing was recorded."
              if args.get("dry_run") else "verdict recorded.")
    return _text("%s  elimination %s\n    %s\n\n%s"
                 % (verdict, args.get("edge"), why, suffix))

def h_portage_verify_elimination_point_lift(args, root):
    from . import verify as V
    path = S.graph_path(root)
    if not os.path.exists(path):
        return _text("no graph yet at %s" % path)
    certificate = args.get("certificate")
    if not isinstance(certificate, dict):
        return _err("certificate must be an object with charts and fallback")
    try:
        verdict, why, _representation = V.verify_elimination_point_lift(
            root, args.get("edge"), certificate,
            timeout=int(args.get("timeout") or 300),
            record=not args.get("dry_run"))
    except (A.ArtifactError, OSError, S.GraphError, ValueError) as exc:
        return _err("point-lift verification failed: %s" % exc)
    suffix = ("--dry-run: nothing was recorded."
              if args.get("dry_run") else "checked lift cover recorded.")
    return _text("%s  point lift %s\n    %s\n\n%s"
                 % (verdict, args.get("edge"), why, suffix))

def h_portage_verify_elimination_groebner(args, root):
    from . import verify as V
    path = S.graph_path(root)
    if not os.path.exists(path):
        return _text("no graph yet at %s" % path)
    try:
        verdict, why, _representation = V.verify_elimination_groebner(
            root, args.get("edge"),
            timeout=int(args.get("timeout") or 300),
            record=not args.get("dry_run"))
    except (A.ArtifactError, OSError, S.GraphError, ValueError) as exc:
        return _err("Groebner elimination verification failed: %s" % exc)
    suffix = ("--dry-run: nothing was recorded."
              if args.get("dry_run") else
              "checked proof and producer provenance recorded.")
    return _text("%s  elimination %s\n    %s\n\n%s"
                 % (verdict, args.get("edge"), why, suffix))
def _render(findings):
    if not findings:
        return "no findings: every recorded conclusion is licensed by the "\
               "transport it rests on."
    out = []
    for f in findings:
        out.append("%s  %s" % (f.severity, f.fid))
        out.extend("    " + l for l in f.detail.splitlines())
        out.append("    -> DISCHARGE: %s" % f.discharge)
        out.append("")
    return "\n".join(out)


def h_portage_show(args, root):
    path = S.graph_path(root)
    if not os.path.exists(path):
        return _text("no graph yet at %s" % path)
    g = S.load(path)
    out = []
    for mid in sorted(g.models):
        m = g.models[mid]
        tag = " ".join(x for x in (m.get("chart"), m.get("field")) if x)
        out.append("MODEL %-16s %-14s %s" % (mid, tag, m.get("desc", "")[:70]))
    for eid in sorted(g.edges):
        e = g.edges[eid]
        mark = ("  [WITHDRAWN by %s]" % e["withdrawn_by"]
                if e.get("withdrawn_by") else
                ("  [SUPERSEDED by %s]" % S.successors(e)
                 if e.get("superseded_by") else ""))
        out.append("EDGE  %-16s %s -> %s  %s%s"
                   % (eid, e["src"], e["dst"], e["type"], mark))
    for cid in sorted(g.claims):
        c = g.claims[cid]
        mark = ("  [RETRACTED by %s]" % c["retracted_by"]
                if c.get("retracted_by") else
                ("  [SUPERSEDED by %s]" % S.successors(c)
                 if c.get("superseded_by") else ""))
        out.append("CLAIM %-16s %-9s @%-14s scope=%s cert=%s%s"
                   % (cid, c["kind"],
                      c.get("model") or ("family:%s" % c.get("family")),
                      c.get("scope"),
                      c.get("certificate"), mark))
        if c.get("supersedes"):
            out.append("    supersedes %s (%s)"
                       % (c["supersedes"], c.get("discharge_kind")))
    # EVERY PREMISE, NOT JUST THE FIRST.
    #
    # This printer read `i["claim"]` and `i["path"]` -- the singular legacy
    # fields, which the fold keeps populated from the FIRST premise so that old
    # readers keep working.  So the one view designated as the handoff showed a
    # two-premise join as a one-premise chain, and silently omitted exactly the
    # construct the multi-premise form was added to make visible.  A campaign
    # read this output, concluded a claim was consumed by nothing, superseded
    # it, and found out otherwise only when the checker raised a stale premise.
    #
    # `premises` is the normalised form and always exists -- the single-premise
    # case is a list of one -- so there is no shape to special-case, and the
    # uniform rendering is what keeps a second premise from hiding behind a
    # branch that was only ever exercised with one.
    for iid in g.inference_order:
        i = g.inferences[iid]
        premises = i["premises"]
        # A record that is dead and prints like a live one is the whole reason
        # supersession exists; it has to be visible in the handoff view too.
        mark = ("  [RETRACTED by %s]" % i["retracted_by"]
                if i.get("retracted_by") else
                ("  [SUPERSEDED by %s]" % S.successors(i)
                 if i.get("superseded_by") else ""))
        out.append("INFER %-16s %d premise%s -> %s%s"
                   % (iid, len(premises), "" if len(premises) == 1 else "s",
                      i["concludes_at"], mark))
        for pr in premises:
            # AN OPEN SLOT is a premise the argument needs and does not have.
            # It licenses nothing, so it must print as an absence rather than
            # be skipped -- a hole nobody can see is indistinguishable from an
            # argument that never needed the premise.
            if pr.get("required_kind"):
                out.append("    premise MISSING: needs a claim of kind %s at "
                           "%s -- %s" % (pr["required_kind"], pr["at"],
                                         pr["missing_why"]))
                continue
            out.append("    premise %-14s via %s"
                       % (pr["claim"],
                          " ".join("%s/%s" % s for s in pr["path"])
                          or "(no path)"))
        if i.get("supersedes"):
            out.append("    supersedes %s (%s)"
                       % (i["supersedes"], i.get("discharge_kind")))
    return _text("\n".join(out) or "(empty graph)")


def h_portage_transport_table(args, root):
    rows = ["%-20s %-8s %s" % ("edge type", "dir",
                               " ".join("%-16s" % k for k in K.CLAIM_KINDS))]
    for t in K.DECLARABLE_TYPES:
        for d in K.DIRECTIONS:
            cells = []
            for k in K.CLAIM_KINDS:
                v = K.TRANSPORT[t][d][k]
                cells.append("%-16s" % ("yes" if v is True else
                                        "NO" if v is False else v))
            rows.append("%-20s %-8s %s" % (t, d, " ".join(cells)))
    rows.append("")
    rows.append("Certificate kinds. An EMPTY claim's SCOPE is derived from "
                "this, not from what you declare:")
    for c, bc in sorted(K.BUILTIN_CERTIFICATES.items()):
        rows.append("  %-28s %s" % (c, "base-changes (scope SCHEME)" if bc
                                    else "FIELD-RELATIVE -- name the field"))
    return _text("\n".join(rows))


def h_cas_classify_identity(args, root):
    origin, ev = cas.classify_identity(
        args["ring_vars"], args["lhs"], args["rhs"],
        generators=args.get("generators") or [],
        characteristic=args.get("characteristic", 0))
    lines = ["origin: %s" % origin,
             "  LHS - RHS in the polynomial ring : %s" % ev["difference"],
             "  reduced modulo the model's ideal : %s"
             % ev["reduced_modulo_ideal"], ""]
    if origin == K.AMBIENT:
        lines.append(
            "The difference is identically zero, so the rewriting holds "
            "before any of this model's equations are imposed. It travels in "
            "BOTH directions -- it never depended on what you may drop. "
            "Declare identity_origin AMBIENT.")
    elif origin == K.DERIVED:
        lines.append(
            "The difference is NOT zero in the polynomial ring but lies in "
            "the model's ideal, so the rewriting is a consequence of this "
            "model's equations. It restricts to tighter models and does NOT "
            "survive a step that drops equations. Declare identity_origin "
            "DERIVED.")
    else:
        lines.append(
            "NEITHER. The difference is nonzero in the polynomial ring AND "
            "does not reduce to zero modulo the ideal, so the rewriting does "
            "not hold at this model at all. This is not a transport question: "
            "the claim is false where it was made. Do not record an origin -- "
            "withdraw or correct the claim.")
    return _text("\n".join(lines))


HANDLERS = {
    "cas_ideal_is_unit": h_cas_ideal_is_unit,
    "cas_classify_identity": h_cas_classify_identity,
    "portage_declare": h_portage_declare,
    "portage_check": h_portage_check,
    "portage_verify": h_portage_verify,
    "portage_verify_elimination": h_portage_verify_elimination,
    "portage_verify_elimination_point_lift": (
        h_portage_verify_elimination_point_lift),
    "portage_verify_elimination_groebner": (
        h_portage_verify_elimination_groebner),
    "cas_health": h_cas_health,
    "portage_show": h_portage_show,
    "portage_transport_table": h_portage_transport_table,
}


# ---------------------------------------------------------------------------
# JSON-RPC 2.0
# ---------------------------------------------------------------------------
def dispatch(request, root=ROOT):
    """Return a response dict, or None for a notification."""
    method = request.get("method")
    rid = request.get("id")
    params = request.get("params") or {}

    if method == "initialize":
        asked = params.get("protocolVersion")
        version = asked if asked in SUPPORTED_PROTOCOLS else PROTOCOL_VERSION
        return _ok(rid, {
            "protocolVersion": version,
            "capabilities": {"tools": {}},
            "serverInfo": {"name": "grand-portage", "version": VERSION},
            "instructions": (
                "Every computation that produces a model must declare how that "
                "model relates to its source. Call portage_transport_table if "
                "you are unsure which type applies. Record conclusions with "
                "portage_declare so they are checked; an unrecorded conclusion "
                "is an unchecked one."),
        })
    if method in ("notifications/initialized", "notifications/cancelled"):
        return None
    if method == "ping":
        return _ok(rid, {})
    if method == "tools/list":
        return _ok(rid, {"tools": TOOLS})
    if method == "tools/call":
        name = params.get("name")
        handler = HANDLERS.get(name)
        if handler is None:
            return _fail(rid, -32602, "unknown tool %r" % (name,))
        # A PER-CALL ROOT, because the server cannot resolve one correctly.
        #
        # `GP_ROOT` defaults to "." and "." is the SERVER PROCESS's cwd, which
        # is the session root -- not the directory the `.mcp.json` declaring it
        # sits in, and not the campaign being worked on. So a campaign whose
        # config says `GP_ROOT: "."` writes to a DIFFERENT graph than `gp
        # check` inside that campaign reads. A live lane hit that in the worst
        # available way: the session-root graph was in a refused state from an
        # unrelated session, `declare` is transactional against the fold, and a
        # first declaration in a minutes-old campaign came back citing a claim
        # id nobody had ever seen.
        #
        # The comment on `h_portage_declare` says "resolving the root
        # differently is not available here -- the server does not know where
        # its config lives". True, and the caller does. Naming it per call
        # turns an environment guess into an argument.
        args = params.get("arguments") or {}
        call_root = args.get("root") or root
        try:
            return _ok(rid, handler(args, call_root))
        except (A.ArtifactError, cas.TransportNotDeclared,
                cas.IdentifierCollision, cas.CASError, S.GraphError,
                K.KernelRefusal) as exc:
            # Expected refusals.  These are the product, not a crash: the
            # message tells the caller what to do differently.
            return _ok(rid, _err("%s: %s" % (type(exc).__name__, exc)))
        except Exception:
            return _ok(rid, _err("unhandled error:\n%s"
                                 % traceback.format_exc()))
    if rid is None:
        return None
    return _fail(rid, -32601, "method not found: %r" % (method,))


def _ok(rid, result):
    return {"jsonrpc": "2.0", "id": rid, "result": result}


def _fail(rid, code, message):
    return {"jsonrpc": "2.0", "id": rid,
            "error": {"code": code, "message": message}}


def serve(stdin=None, stdout=None, root=None):
    stdin = stdin or sys.stdin
    stdout = stdout or sys.stdout
    root = root or ROOT
    for line in stdin:
        line = line.strip()
        if not line:
            continue
        try:
            request = json.loads(line)
        except ValueError:
            stdout.write(json.dumps(_fail(None, -32700, "parse error")) + "\n")
            stdout.flush()
            continue
        response = dispatch(request, root=root)
        if response is not None:
            stdout.write(json.dumps(response) + "\n")
            stdout.flush()


def main(argv=None):
    argv = sys.argv[1:] if argv is None else argv
    root = ROOT
    if "--root" in argv:
        root = argv[argv.index("--root") + 1]
    serve(root=root)
    return 0


if __name__ == "__main__":
    sys.exit(main())
