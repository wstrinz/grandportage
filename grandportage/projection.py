"""Versioned, non-authoritative read projections of a folded campaign.

The append-only graph remains the authority.  This module produces a complete,
deterministic snapshot for visualization, review tools, and local experiments.
Nothing in the projection is accepted as input to the transport kernel.
"""

import hashlib
import json
import os


SCHEMA = "grand-portage-projection/v2"

# Verdict subjects describe verifier jobs, not always graph entity kinds.
# Keep this projection explicit and test it against Graph._VERDICTS: a
# certificate or witness verifies a claim, while ring/operation checks verify
# an edge.
VERDICT_TARGET_KINDS = {
    "claim": "claim",
    "certificate": "claim",
    "witness": "claim",
    "partition": "partition",
    "edge": "edge",
    "ring_iso": "edge",
    "operation": "edge",
    "elimination": "edge",
    "point_lift": "edge",
}


def _portable(value):
    """Project folded values into deterministic JSON data."""
    if value is None or isinstance(value, (bool, int, float, str)):
        return value
    if isinstance(value, dict):
        return {
            str(key): _portable(value[key])
            for key in sorted(value, key=lambda item: str(item))
        }
    if isinstance(value, (list, tuple)):
        return [_portable(item) for item in value]
    if isinstance(value, set):
        return sorted((_portable(item) for item in value), key=_sort_key)
    return str(value)


def _sort_key(value):
    return json.dumps(value, sort_keys=True, separators=(",", ":"))


def _record_map(value):
    return {
        str(key): _portable(record)
        for key, record in sorted(value.items(), key=lambda item: str(item[0]))
    }


def _source_record(path):
    absolute = os.path.abspath(path)
    with open(absolute, "rb") as stream:
        payload = stream.read()
    return {
        "path": os.path.normpath(path).replace(os.sep, "/"),
        "fingerprint": "sha256:" + hashlib.sha256(payload).hexdigest(),
        "bytes": len(payload),
    }


def _status(record):
    if record.get("withdrawn_by"):
        return "WITHDRAWN"
    if record.get("superseded_by"):
        return "SUPERSEDED"
    for field in (
            "verdict", "identity_verdict", "witness_verdict",
            "ring_iso_verdict", "section_verdict", "groebner_verdict"):
        if record.get(field):
            return str(record[field])
    return "DECLARED"


def _node(kind, identifier, record, label=None, record_ref=None):
    key = "%s:%s" % (kind, identifier)
    status = _status(record) if isinstance(record, dict) else "DECLARED"
    if kind == "finding" and isinstance(record, dict):
        status = str(record.get("severity") or status)
    node = {
        "key": key,
        "kind": kind,
        "id": str(identifier),
        "label": str(label if label is not None else identifier),
        "status": status,
    }
    if record_ref is None:
        node["record"] = _portable(record)
    else:
        node["record_ref"] = _portable(record_ref)
    return node


def resolve_record(projection, node):
    """Resolve a v2 node record without duplicating serialized JSON.

    Inline record remains supported for synthesized nodes and v1 inputs.
    References name a canonical record already present under collections.
    """
    if "record" in node:
        return node["record"]
    reference = node.get("record_ref")
    if not isinstance(reference, dict):
        raise ValueError("projected node has neither record nor record_ref")
    collection = projection.get("collections", {}).get(
        reference.get("collection"))
    if "id" in reference and isinstance(collection, dict):
        record = collection.get(str(reference["id"]))
    elif "index" in reference and isinstance(collection, list):
        index = reference["index"]
        record = (collection[index]
                  if isinstance(index, int) and 0 <= index < len(collection)
                  else None)
    else:
        record = None
    if record is None:
        raise ValueError("projected node record_ref does not resolve")
    if reference.get("field") is not None:
        if not isinstance(record, dict) or reference["field"] not in record:
            raise ValueError("projected node record_ref field does not resolve")
        record = record[reference["field"]]
    return record


def _relation(kind, source, target, label=""):
    return {
        "kind": kind,
        "source": source,
        "target": target,
        "label": label,
    }


def _resolve(identifier, nodes_by_kind):
    """Resolve an entity id only when its kind is unambiguous."""
    candidates = [
        "%s:%s" % (kind, identifier)
        for kind, identifiers in nodes_by_kind.items()
        if str(identifier) in identifiers
    ]
    return candidates[0] if len(candidates) == 1 else None


def build(graph, sources=(), findings=(), accepted=None, package_version=""):
    """Build a complete deterministic read model from a folded graph."""
    findings = [_portable(
        finding.as_dict() if hasattr(finding, "as_dict") else finding
    ) for finding in findings]
    findings.sort(key=lambda finding: finding.get("id", ""))
    accepted = _portable(accepted or {})

    tombstones = []
    for key, record in sorted(
            graph.retractions.items(), key=lambda item: str(item[0])):
        tombstones.append({
            "entity_kind": str(key[0]),
            "id": str(key[1]),
            "record": _portable(record),
        })

    collections = {
        "certificates": _record_map(graph.certificates),
        "certificate_records": _record_map(graph.cert_records),
        "certificate_sources": _record_map(graph.cert_source),
        "models": _record_map(graph.models),
        "edges": _record_map(graph.edges),
        "claims": _record_map(graph.claims),
        "inferences": {
            identifier: _portable(graph.inferences[identifier])
            for identifier in graph.inference_order
        },
        "built_by": _record_map(graph.built_by),
        "partitions": _record_map(graph.partitions),
        "families": _record_map(graph.families),
        "groups": _record_map(graph.groups),
        "aliases": _record_map(graph.aliases),
        "citations": _record_map(graph.citations),
        "evidence": _record_map(graph.evidence),
        "doubts": _record_map(graph.doubts),
        "verdicts": _record_map(graph.verdicts),
        "notes": [_portable(note) for note in graph.notes],
        "named_notes": _record_map(graph.named_notes),
        "tombstones": tombstones,
        "findings": findings,
        "baseline": accepted,
    }

    nodes = []
    nodes_by_kind = {}

    def add(kind, identifier, record, label=None, record_ref=None):
        node = _node(
            kind, identifier, record, label, record_ref=record_ref)
        nodes.append(node)
        nodes_by_kind.setdefault(kind, set()).add(str(identifier))

    entity_collections = (
        ("model", "models", collections["models"]),
        ("edge", "edges", collections["edges"]),
        ("claim", "claims", collections["claims"]),
        ("inference", "inferences", collections["inferences"]),
        ("partition", "partitions", collections["partitions"]),
        ("family", "families", collections["families"]),
        ("alias", "aliases", collections["aliases"]),
        ("citation", "citations", collections["citations"]),
        ("evidence", "evidence", collections["evidence"]),
        ("doubt", "doubts", collections["doubts"]),
        ("verdict", "verdicts", collections["verdicts"]),
        ("note", "named_notes", collections["named_notes"]),
    )
    for kind, collection_name, records in entity_collections:
        for identifier, record in records.items():
            add(kind, identifier, record, record_ref={
                "collection": collection_name, "id": str(identifier),
            })
    for index, record in enumerate(collections["notes"]):
        if not record.get("id"):
            add("note", "@%d" % index, record, "note %d" % (index + 1),
                record_ref={"collection": "notes", "index": index})
    for identifier, base_changes in collections["certificates"].items():
        record = dict(collections["certificate_records"].get(identifier, {}))
        record.setdefault("base_changes", base_changes)
        record["registry_source"] = collections["certificate_sources"].get(
            identifier, "unknown")
        add("certificate", identifier, record)
    for item in tombstones:
        add("tombstone", "%s:%s" % (item["entity_kind"], item["id"]),
            item["record"])
    for index, finding in enumerate(findings):
        add("finding", finding.get("id", "@%d" % len(nodes)), finding,
            finding.get("severity", "finding"),
            record_ref={"collection": "findings", "index": index})

    relations = []

    def link(kind, source, target, label=""):
        if source and target:
            relations.append(_relation(kind, source, target, label))

    for identifier, edge in collections["edges"].items():
        edge_key = "edge:%s" % identifier
        link("edge-source", "model:%s" % edge["src"], edge_key, "source")
        link("edge-target", edge_key, "model:%s" % edge["dst"], edge["type"])

    for identifier, claim in collections["claims"].items():
        claim_key = "claim:%s" % identifier
        if claim.get("model"):
            link("claim-model", "model:%s" % claim["model"], claim_key,
                 claim.get("kind", "claim"))
        if claim.get("established_by"):
            link("established-by", "inference:%s" % claim["established_by"],
                 claim_key, "establishes")
        reference = claim.get("citation")
        if reference in collections["citations"]:
            link("citation", "citation:%s" % reference, claim_key, "supports")
        certificate = claim.get("certificate")
        if certificate in collections["certificates"]:
            link("certificate", "certificate:%s" % certificate, claim_key,
                 "licenses scope")

    for identifier, inference in collections["inferences"].items():
        inference_key = "inference:%s" % identifier
        if inference.get("claim"):
            link("inference-claim", "claim:%s" % inference["claim"],
                 inference_key, "transported claim")
        for premise in inference.get("premises") or []:
            link("premise", _resolve(premise, nodes_by_kind), inference_key,
                 "premise")
        for step in inference.get("path") or []:
            if isinstance(step, (list, tuple)) and step:
                link("path", "edge:%s" % step[0], inference_key,
                     str(step[1]) if len(step) > 1 else "path")
        reference = inference.get("citation")
        if reference in collections["citations"]:
            link("citation", "citation:%s" % reference, inference_key,
                 "supports")

    for identifier, partition in collections["partitions"].items():
        partition_key = "partition:%s" % identifier
        link("partition-parent", "model:%s" % partition["parent"],
             partition_key, "parent")
        for branch in partition.get("branches") or []:
            link("partition-branch", partition_key, "model:%s" % branch,
                 "branch")

    for identifier, family in collections["families"].items():
        family_key = "family:%s" % identifier
        for member in family.get("members") or []:
            link("family-member", family_key, _resolve(member, nodes_by_kind),
                 "member")

    for identifier, alias in collections["aliases"].items():
        for model in alias.get("models") or []:
            link("alias-model", "alias:%s" % identifier,
                 "model:%s" % model, "same model")

    for identifier, evidence in collections["evidence"].items():
        link("evidence-for", "evidence:%s" % identifier,
             _resolve(evidence.get("for"), nodes_by_kind), evidence.get("method", ""))

    for identifier, doubt in collections["doubts"].items():
        link("doubt-about", "doubt:%s" % identifier,
             _resolve(doubt.get("about"), nodes_by_kind), doubt.get("kind", ""))

    for identifier, verdict in collections["verdicts"].items():
        subject = verdict.get("subject")
        target_kind = VERDICT_TARGET_KINDS.get(subject)
        target = ("%s:%s" % (target_kind, verdict.get("of"))
                  if target_kind else None)
        link("verdict-of", "verdict:%s" % identifier, target,
             verdict.get("verdict", ""))
    for model, inferences in collections["built_by"].items():
        for inference in inferences:
            link("built-by", "inference:%s" % inference,
                 "model:%s" % model, "builds")

    for finding in findings:
        finding_key = "finding:%s" % finding.get("id")
        link("finding-subject", finding_key,
             _resolve(finding.get("subject"), nodes_by_kind),
             finding.get("severity", ""))
        for trace in finding.get("trace") or []:
            if trace.get("edge") in collections["edges"]:
                link("finding-trace", "edge:%s" % trace["edge"],
                     finding_key, str(trace.get("direction", "")))

    for kind, _collection_name, records in entity_collections:
        for identifier, record in records.items():
            successors = record.get("superseded_by") or []
            if isinstance(successors, str):
                successors = [successors]
            for successor in successors:
                link("superseded-by", "%s:%s" % (kind, identifier),
                     "%s:%s" % (kind, successor), "superseded by")

    relations.sort(key=lambda relation: (
        relation["source"], relation["target"], relation["kind"],
        relation["label"],
    ))
    nodes.sort(key=lambda node: (node["kind"], node["id"]))

    counts = {name: len(value) for name, value in collections.items()
              if isinstance(value, (dict, list))}
    counts["accepted_findings"] = len(accepted.get("accepted", {}))
    return {
        "schema": SCHEMA,
        "authority": "DERIVED_READ_MODEL_ONLY",
        "source": {
            "graphs": [_source_record(path) for path in sources],
            "graph_format": graph.graph_format,
            "kernel_epoch": graph.kernel_epoch,
            "created_with": graph.created_with,
            "projected_with": package_version,
        },
        "counts": counts,
        "orders": {
            "inferences": [str(identifier)
                           for identifier in graph.inference_order],
        },
        "collections": collections,
        "nodes": nodes,
        "relations": relations,
    }


def focus(projection, selector, radius=2):
    """Return an undirected neighborhood view around one entity.

    This is a presentation filter, not a mathematical dependency theorem.
    """
    if not selector:
        return projection
    if not isinstance(radius, int) or radius < 0:
        raise ValueError("focus radius must be a nonnegative integer")
    nodes = {node["key"]: node for node in projection["nodes"]}
    if ":" in selector and selector in nodes:
        key = selector
    else:
        matches = [node["key"] for node in projection["nodes"]
                   if node["id"] == selector]
        if not matches:
            raise ValueError("focus entity %r does not exist" % selector)
        if len(matches) != 1:
            raise ValueError(
                "focus id %r is ambiguous; use kind:id (%s)"
                % (selector, ", ".join(matches)))
        key = matches[0]

    adjacency = {node_key: set() for node_key in nodes}
    for relation in projection["relations"]:
        source, target = relation["source"], relation["target"]
        if source in adjacency and target in adjacency:
            adjacency[source].add(target)
            adjacency[target].add(source)
    keep = {key}
    frontier = {key}
    for _step in range(radius):
        frontier = set().union(*(adjacency[item] for item in frontier)) - keep
        keep.update(frontier)
        if not frontier:
            break

    answer = dict(projection)
    answer["focus"] = {
        "selector": selector,
        "resolved": key,
        "radius": radius,
        "semantics": "UNDIRECTED_PRESENTATION_NEIGHBORHOOD",
    }
    answer["nodes"] = [node for node in projection["nodes"]
                       if node["key"] in keep]
    answer["relations"] = [
        relation for relation in projection["relations"]
        if relation["source"] in keep and relation["target"] in keep
    ]
    return answer


def canonical_json(projection, pretty=True):
    return json.dumps(
        projection, sort_keys=True, indent=2 if pretty else None,
        separators=None if pretty else (",", ":"), ensure_ascii=True,
    ) + "\n"
