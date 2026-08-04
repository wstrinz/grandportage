"""Pinned Stacks references and non-authoritative applicability packets.

This module is deliberately outside :mod:`grandportage`.  Semantic search may
suggest a theorem, and this sidecar may check that a packet accounts for every
hypothesis, but neither action changes a GP graph or licenses an inference.
"""

from __future__ import print_function

import argparse
import hashlib
import json
import re
import subprocess
import sys
from pathlib import Path
from urllib.request import Request, urlopen


SHELF_SCHEMA = "gp_stacks_theorem_shelf_v1"
PACKET_SCHEMA = "gp_stacks_application_packet_v1"
DISCOVERY_SCHEMA = "gp_stacks_discovery_v1"
STACKS_REPOSITORY = "https://github.com/stacks/stacks-project.git"
THEOREMSEARCH_MCP = "https://api.theoremsearch.com/mcp"

TAG_RE = re.compile(r"^[0-9A-Z]{4}$")
COMMIT_RE = re.compile(r"^[0-9a-f]{40}$")
OFFICIAL_TAG_URL_RE = re.compile(
    r"^https://stacks\.math\.columbia\.edu/tag/([0-9A-Z]{4})/?$")
APPLICATION_STATUSES = {"BOUND", "OPEN", "MISSING", "UNSUPPORTED"}
ACCEPTANCE_STAGES = {
    "CITATION_PINNED",
    "EXTERNAL_THEOREM_ACCEPTED",
    "FORMALIZED_AND_VERIFIED",
}
FORBIDDEN_PIN_FIELDS = {
    "score",
    "similarity",
    "slogan",
    "slogan_id",
    "theorem_id",
    "search_query",
}


class SidecarError(ValueError):
    """The sidecar input is malformed or no longer matches its source."""


def _require(condition, message):
    if not condition:
        raise SidecarError(message)


def sha256_text(text):
    return hashlib.sha256(text.encode("utf-8")).hexdigest()


def load_json(path):
    with Path(path).open("r", encoding="utf-8") as handle:
        return json.load(handle)


def _unique_ids(records, field, where):
    values = [record.get(field) for record in records]
    _require(all(isinstance(value, str) and value for value in values),
             "%s needs a nonempty `%s` on every record" % (where, field))
    _require(len(values) == len(set(values)),
             "%s has duplicate `%s` values" % (where, field))
    return values


def validate_shelf(shelf):
    """Validate the portable shelf without consulting a checkout."""
    _require(shelf.get("schema") == SHELF_SCHEMA,
             "theorem shelf schema must be %s" % SHELF_SCHEMA)
    source = shelf.get("source") or {}
    _require(source.get("repository") == STACKS_REPOSITORY,
             "theorem shelf must name the official Stacks repository")
    _require(COMMIT_RE.match(str(source.get("commit") or "")),
             "theorem shelf needs a full lowercase Stacks commit")
    theorems = shelf.get("theorems")
    _require(isinstance(theorems, list) and theorems,
             "theorem shelf needs at least one theorem")
    _unique_ids(theorems, "tag", "theorem shelf")

    indexed = {}
    for theorem in theorems:
        tag = theorem["tag"]
        _require(TAG_RE.match(tag), "invalid Stacks tag %r" % tag)
        leaked = sorted(FORBIDDEN_PIN_FIELDS.intersection(theorem))
        _require(not leaked,
                 "pinned theorem %s contains discovery-only fields: %s"
                 % (tag, ", ".join(leaked)))
        _require(theorem.get("official_url") ==
                 "https://stacks.math.columbia.edu/tag/%s" % tag,
                 "pinned theorem %s has a noncanonical official URL" % tag)
        _require(theorem.get("source_file") and theorem.get("source_label"),
                 "pinned theorem %s needs its source file and label" % tag)
        _require(theorem.get("environment") in
                 {"lemma", "proposition", "theorem", "corollary"},
                 "pinned theorem %s has an unsupported environment" % tag)
        statement = theorem.get("statement_tex")
        _require(isinstance(statement, str) and statement.strip() == statement,
                 "pinned theorem %s needs a trimmed exact statement" % tag)
        digest = theorem.get("statement_sha256")
        _require(digest == sha256_text(statement),
                 "pinned theorem %s statement digest mismatch" % tag)

        hypotheses = theorem.get("hypotheses")
        _require(isinstance(hypotheses, list) and hypotheses,
                 "pinned theorem %s needs explicit hypotheses" % tag)
        _unique_ids(hypotheses, "id", "theorem %s hypotheses" % tag)
        for hypothesis in hypotheses:
            _require(hypothesis.get("statement"),
                     "theorem %s has an empty hypothesis" % tag)
        _require(theorem.get("conclusion"),
                 "pinned theorem %s needs an explicit conclusion" % tag)

        dependencies = theorem.get("dependencies") or []
        _unique_ids(dependencies, "source_ref",
                    "theorem %s dependencies" % tag)
        for dependency in dependencies:
            _require(TAG_RE.match(str(dependency.get("tag") or "")),
                     "theorem %s has an invalid dependency tag" % tag)
            _require(dependency.get("source_label"),
                     "theorem %s dependency needs a source label" % tag)
        indexed[tag] = theorem
    return indexed


def _tag_map(checkout):
    mapping = {}
    tags_path = checkout / "tags" / "tags"
    _require(tags_path.is_file(), "Stacks checkout has no tags/tags file")
    for line in tags_path.read_text(encoding="utf-8").splitlines():
        if not line or "," not in line:
            continue
        tag, label = line.split(",", 1)
        mapping[tag] = label
    return mapping


def _extract_theorem(source_text, environment, local_label):
    start_re = re.compile(
        r"\\begin\{%s\}(?:\[[^\]]*\])?\s*"
        r"\\label\{%s\}\s*" % (re.escape(environment),
                                   re.escape(local_label)))
    match = start_re.search(source_text)
    _require(match is not None, "could not find labelled %s %s"
             % (environment, local_label))
    end_marker = "\\end{%s}" % environment
    end = source_text.find(end_marker, match.end())
    _require(end >= 0, "could not find end of %s %s"
             % (environment, local_label))
    statement = source_text[match.end():end].strip()

    proof_start = source_text.find("\\begin{proof}", end + len(end_marker))
    proof = ""
    if proof_start >= 0:
        next_theorem = re.search(
            r"\\begin\{(?:lemma|proposition|theorem|corollary)\}",
            source_text[end + len(end_marker):])
        relative_proof = proof_start - (end + len(end_marker))
        if next_theorem is None or relative_proof < next_theorem.start():
            proof_end = source_text.find("\\end{proof}", proof_start)
            _require(proof_end >= 0, "could not find end of proof for %s"
                     % local_label)
            proof = source_text[proof_start:proof_end + len("\\end{proof}")]
    refs = re.findall(r"\\ref\{([^}]+)\}", statement + "\n" + proof)
    return statement, refs


def validate_checkout(shelf, checkout_path):
    """Prove that the shelf matches an exact official Stacks checkout."""
    indexed = validate_shelf(shelf)
    checkout = Path(checkout_path).resolve()
    _require(checkout.is_dir(), "Stacks checkout does not exist: %s" % checkout)
    try:
        actual_commit = subprocess.check_output(
            ["git", "rev-parse", "HEAD"], cwd=str(checkout),
            text=True).strip()
    except (OSError, subprocess.CalledProcessError) as exc:
        raise SidecarError("cannot read Stacks checkout commit: %s" % exc)
    expected_commit = shelf["source"]["commit"]
    _require(actual_commit == expected_commit,
             "Stacks checkout is %s, shelf is pinned to %s"
             % (actual_commit, expected_commit))

    tags = _tag_map(checkout)
    checked = []
    for tag, theorem in sorted(indexed.items()):
        _require(tags.get(tag) == theorem["source_label"],
                 "Stacks tag %s maps to %r, not %r"
                 % (tag, tags.get(tag), theorem["source_label"]))
        source_path = checkout / theorem["source_file"]
        _require(source_path.is_file(),
                 "Stacks source file is missing: %s" % source_path)
        source_text = source_path.read_text(encoding="utf-8")
        local_label = theorem["source_label"].split("-", 1)[1]
        statement, refs = _extract_theorem(
            source_text, theorem["environment"], local_label)
        _require(statement == theorem["statement_tex"],
                 "pinned statement for %s no longer matches source" % tag)
        declared_refs = {item["source_ref"]
                         for item in theorem.get("dependencies") or []}
        _require(set(refs) == declared_refs,
                 "dependency references for %s differ: source=%s shelf=%s"
                 % (tag, sorted(set(refs)), sorted(declared_refs)))
        for dependency in theorem.get("dependencies") or []:
            _require(tags.get(dependency["tag"]) ==
                     dependency["source_label"],
                     "dependency tag %s no longer maps to %s"
                     % (dependency["tag"], dependency["source_label"]))
        checked.append(tag)
    return {"status": "PINNED_SOURCE_VERIFIED", "commit": actual_commit,
            "tags": checked, "graph_effect": "NONE"}


def audit_application(shelf, packet):
    """Audit complete hypothesis accounting; never authorize a GP inference."""
    indexed = validate_shelf(shelf)
    _require(packet.get("schema") == PACKET_SCHEMA,
             "application packet schema must be %s" % PACKET_SCHEMA)
    pin = packet.get("theorem_pin") or {}
    tag = pin.get("tag")
    _require(tag in indexed, "application names an unpinned theorem %r" % tag)
    theorem = indexed[tag]
    _require(pin.get("statement_sha256") == theorem["statement_sha256"],
             "application theorem digest does not match pinned tag %s" % tag)
    stage = packet.get("theorem_acceptance")
    _require(stage in ACCEPTANCE_STAGES,
             "application has an unknown theorem acceptance stage")
    if stage == "FORMALIZED_AND_VERIFIED":
        _require(packet.get("formal_artifact"),
                 "formalized theorem application needs a formal artifact")

    mappings = packet.get("hypotheses")
    _require(isinstance(mappings, list),
             "application needs a hypothesis mapping list")
    mapped_ids = _unique_ids(mappings, "id", "application hypotheses")
    expected_ids = [item["id"] for item in theorem["hypotheses"]]
    _require(set(mapped_ids) == set(expected_ids),
             "application hypothesis map differs: expected=%s actual=%s"
             % (sorted(expected_ids), sorted(mapped_ids)))

    by_id = {item["id"]: item for item in mappings}
    unresolved = []
    for hypothesis in theorem["hypotheses"]:
        mapping = by_id[hypothesis["id"]]
        status = mapping.get("status")
        _require(status in APPLICATION_STATUSES,
                 "hypothesis %s has unknown status %r"
                 % (hypothesis["id"], status))
        if status == "BOUND":
            _require(mapping.get("gp_claim"),
                     "bound hypothesis %s needs a GP claim id"
                     % hypothesis["id"])
        else:
            _require(mapping.get("why"),
                     "unresolved hypothesis %s needs a reason"
                     % hypothesis["id"])
            unresolved.append({"kind": "theorem_hypothesis",
                               "id": hypothesis["id"], "status": status,
                               "why": mapping["why"]})

    bridge_premises = packet.get("application_premises") or []
    _unique_ids(bridge_premises, "id", "application bridge premises")
    for premise in bridge_premises:
        status = premise.get("status")
        _require(status in APPLICATION_STATUSES,
                 "application premise %s has unknown status %r"
                 % (premise["id"], status))
        _require(premise.get("statement"),
                 "application premise %s needs a statement" % premise["id"])
        if status == "BOUND":
            _require(premise.get("gp_claim"),
                     "bound application premise %s needs a GP claim id"
                     % premise["id"])
        else:
            _require(premise.get("why"),
                     "unresolved application premise %s needs a reason"
                     % premise["id"])
            unresolved.append({"kind": "application_bridge",
                               "id": premise["id"], "status": status,
                               "why": premise["why"]})

    if unresolved:
        decision = "REFUSED_MISSING_HYPOTHESES"
        authority = "NONE"
    elif stage == "CITATION_PINNED":
        decision = "HELD_EXTERNAL_THEOREM_NOT_ACCEPTED"
        authority = "NONE"
    else:
        decision = "READY_FOR_GP_REVIEW"
        authority = ("FORMAL_VERIFICATION" if
                     stage == "FORMALIZED_AND_VERIFIED"
                     else "EXTERNAL_HUMAN_THEOREM")
    return {
        "application_id": packet.get("application_id"),
        "tag": tag,
        "citation_status": "PINNED",
        "hypothesis_mapping": "COMPLETE",
        "application_bridge_count": len(bridge_premises),
        "decision": decision,
        "authority_if_recorded": authority,
        "unresolved": unresolved,
        "graph_effect": "NONE",
    }


def render_application(shelf, packet):
    indexed = validate_shelf(shelf)
    audit = audit_application(shelf, packet)
    theorem = indexed[audit["tag"]]
    mapped = {item["id"]: item for item in packet["hypotheses"]}
    lines = [
        "# Stacks applicability audit: %s" % packet["application_id"],
        "",
        "- Theorem: [%s](%s)" % (theorem["tag"], theorem["official_url"]),
        "- Pinned Stacks commit: `%s`" % shelf["source"]["commit"],
        "- Statement SHA-256: `%s`" % theorem["statement_sha256"],
        "- JC context: %s" % packet["target_context"],
        "- Intended conclusion: %s" % packet["intended_conclusion"],
        "- Decision: **%s**" % audit["decision"],
        "- Graph effect: **NONE**",
        "",
        "## Exact pinned statement",
        "",
        "```tex",
        theorem["statement_tex"],
        "```",
        "",
        "## Hypothesis accounting",
        "",
        "| Hypothesis | Exact premise | Status | GP binding / reason |",
        "| --- | --- | --- | --- |",
    ]
    for hypothesis in theorem["hypotheses"]:
        binding = mapped[hypothesis["id"]]
        detail = ("`%s`" % binding["gp_claim"] if
                  binding["status"] == "BOUND" else binding["why"])
        lines.append("| `%s` | %s | **%s** | %s |" % (
            hypothesis["id"], hypothesis["statement"],
            binding["status"], detail))
    bridge_premises = packet.get("application_premises") or []
    if bridge_premises:
        lines += [
            "",
            "## Application-specific bridge premises",
            "",
            "These are needed to use the theorem in this JC context even "
            "though they are not hypotheses in the printed Stacks statement.",
            "",
            "| Premise | Statement | Status | GP binding / reason |",
            "| --- | --- | --- | --- |",
        ]
        for premise in bridge_premises:
            detail = ("`%s`" % premise["gp_claim"] if
                      premise["status"] == "BOUND" else premise["why"])
            lines.append("| `%s` | %s | **%s** | %s |" % (
                premise["id"], premise["statement"], premise["status"],
                detail))
    lines += [
        "",
        "## Authority boundary",
        "",
        "This sidecar records discovery, source pinning, and premise accounting. "
        "It does not create or amend a GP claim, edge, inference, verdict, or "
        "kernel rule. Even `READY_FOR_GP_REVIEW` requires an explicit reviewed "
        "translation into the campaign graph.",
        "",
    ]
    return "\n".join(lines)


def _discovery_candidate(theorem):
    paper = theorem.get("paper") or {}
    link = paper.get("link") or theorem.get("link") or ""
    match = OFFICIAL_TAG_URL_RE.match(link)
    if not match:
        return None
    return {
        "tag": match.group(1),
        "name": theorem.get("name"),
        "official_url": link.rstrip("/"),
        "slogan": theorem.get("slogan"),
        "score": theorem.get("score"),
    }


def theoremsearch_discover(query, limit=5, timeout=30):
    """Call TheoremSearch MCP and return explicitly non-authoritative output."""
    payload = {
        "jsonrpc": "2.0",
        "id": 1,
        "method": "tools/call",
        "params": {
            "name": "theorem_search",
            "arguments": {
                "query": query,
                "n_results": limit,
                "sources": ["Stacks Project"],
            },
        },
    }
    request = Request(
        THEOREMSEARCH_MCP,
        data=json.dumps(payload).encode("utf-8"),
        headers={"Content-Type": "application/json",
                 "User-Agent": "grand-portage-stacks-spike/1"},
        method="POST",
    )
    with urlopen(request, timeout=timeout) as response:
        result = json.loads(response.read().decode("utf-8"))
    _require(not result.get("error"),
             "TheoremSearch MCP error: %s" % result.get("error"))
    structured = ((result.get("result") or {}).get("structuredContent") or {})
    candidates = []
    for theorem in structured.get("theorems") or []:
        candidate = _discovery_candidate(theorem)
        if candidate:
            candidates.append(candidate)
    return {
        "schema": DISCOVERY_SCHEMA,
        "provider": "TheoremSearch MCP",
        "query": query,
        "authority": "NONE",
        "warning": "Resolve every candidate against a pinned official source.",
        "candidates": candidates,
    }


def _defaults():
    root = Path(__file__).resolve().parent
    return root / "theorem_shelf.json"


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--shelf", default=str(_defaults()))
    subparsers = parser.add_subparsers(dest="command", required=True)

    validate_parser = subparsers.add_parser("validate-shelf")
    validate_parser.add_argument("--checkout")

    audit_parser = subparsers.add_parser("audit")
    audit_parser.add_argument("packet")

    render_parser = subparsers.add_parser("render")
    render_parser.add_argument("packet")
    render_parser.add_argument("--output")

    discover_parser = subparsers.add_parser("discover")
    discover_parser.add_argument("query")
    discover_parser.add_argument("--limit", type=int, default=5)

    args = parser.parse_args(argv)
    try:
        if args.command == "discover":
            result = theoremsearch_discover(args.query, args.limit)
            print(json.dumps(result, indent=2, sort_keys=True))
            return 0
        shelf = load_json(args.shelf)
        if args.command == "validate-shelf":
            if args.checkout:
                result = validate_checkout(shelf, args.checkout)
            else:
                result = {"status": "PORTABLE_SHELF_VERIFIED",
                          "tags": sorted(validate_shelf(shelf)),
                          "graph_effect": "NONE"}
            print(json.dumps(result, indent=2, sort_keys=True))
            return 0
        packet = load_json(args.packet)
        if args.command == "audit":
            print(json.dumps(audit_application(shelf, packet),
                             indent=2, sort_keys=True))
            return 0
        rendered = render_application(shelf, packet)
        if args.output:
            Path(args.output).write_text(rendered, encoding="utf-8")
        else:
            print(rendered)
        return 0
    except (OSError, ValueError, SidecarError) as exc:
        print("stacks sidecar: %s" % exc, file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
