"""Durable, content-addressed backend execution artifacts.

The graph carries mathematical declarations and compact provenance references.
Exact programs, transcripts, parse results, and certificates live beside it as
immutable objects.  Object availability is audited explicitly: moving an
object store must not make the same append-only graph fold differently.
"""

import json
import os
import re
import secrets

from . import backend as B


ARTIFACT_DIR = "artifacts"
HASH_ALGORITHM = "sha256"
ENVELOPE_SCHEMA = 1
NOTE_REFERENCE_PREFIX = "gp-artifact-v1:"
_FINGERPRINT = re.compile(r"^sha256:([0-9a-f]{64})$")


class ArtifactError(ValueError):
    """A durable artifact is missing, malformed, or inconsistent."""


def _canonical_bytes(value):
    return json.dumps(
        value, sort_keys=True, separators=(",", ":"), ensure_ascii=True
    ).encode("utf-8")


def envelope(artifact):
    """Return the closed, canonical envelope for one frozen execution."""
    if not isinstance(artifact, B.ExecutionArtifact):
        raise TypeError("artifact store accepts ExecutionArtifact values")
    return artifact.payload()


def fingerprint(value):
    """Content address an envelope by its exact canonical UTF-8 bytes."""
    import hashlib
    return "sha256:" + hashlib.sha256(_canonical_bytes(value)).hexdigest()


def artifact_path(root, artifact_fingerprint):
    """Derive an object path without accepting path-like hash input."""
    match = _FINGERPRINT.match(str(artifact_fingerprint))
    if match is None:
        raise ArtifactError("artifact fingerprint is malformed")
    digest = match.group(1)
    return os.path.join(
        os.path.abspath(root), ".portage", ARTIFACT_DIR, HASH_ALGORITHM,
        digest[:2], digest[2:] + ".json",
    )


def _validate_envelope(value, expected_fingerprint=None):
    fields = {
        "schema", "backend", "semantic_input_fingerprint",
        "program_fingerprint", "program_text", "completion_nonce", "argv",
        "returncode", "aborted", "abort_reason", "stdout", "stderr",
        "stdout_fingerprint", "stderr_fingerprint", "parsed_output",
        "certificate",
    }
    if not isinstance(value, dict) or set(value) != fields:
        raise ArtifactError("execution artifact has an unknown or missing field")
    if value["schema"] != ENVELOPE_SCHEMA:
        raise ArtifactError("execution artifact schema is unsupported")
    backend_fields = {
        "contract", "implementation", "implementation_version",
        "protocol_version", "binary_version",
    }
    backend = value["backend"]
    if not isinstance(backend, dict) or set(backend) != backend_fields:
        raise ArtifactError("execution artifact backend identity is malformed")
    if (not all(isinstance(backend[field], str) and backend[field]
                for field in ("contract", "implementation", "binary_version"))
            or type(backend["implementation_version"]) is not int
            or backend["implementation_version"] < 1
            or type(backend["protocol_version"]) is not int
            or backend["protocol_version"] < 1):
        raise ArtifactError("execution artifact backend identity is ill-typed")
    if not all(B.valid_fingerprint(value[field]) for field in (
            "semantic_input_fingerprint", "program_fingerprint",
            "stdout_fingerprint", "stderr_fingerprint")):
        raise ArtifactError("execution artifact contains a malformed fingerprint")
    if not all(isinstance(value[field], str) for field in (
            "program_text", "completion_nonce", "stdout", "stderr")):
        raise ArtifactError("execution artifact text fields are ill-typed")
    if (value["abort_reason"] is not None
            and not isinstance(value["abort_reason"], str)):
        raise ArtifactError("execution artifact abort reason is ill-typed")
    if any(value[field] is not None and not isinstance(value[field], str)
           for field in ("parsed_output", "certificate")):
        raise ArtifactError("execution artifact parsed fields are ill-typed")
    if (not isinstance(value["argv"], list)
            or not all(isinstance(part, str) for part in value["argv"])
            or type(value["returncode"]) is not int
            or type(value["aborted"]) is not bool):
        raise ArtifactError("execution artifact process fields are ill-typed")
    if value["program_fingerprint"] != B.text_fingerprint(value["program_text"]):
        raise ArtifactError("execution artifact program hash does not match")
    if value["stdout_fingerprint"] != B.text_fingerprint(value["stdout"]):
        raise ArtifactError("execution artifact stdout hash does not match")
    if value["stderr_fingerprint"] != B.text_fingerprint(value["stderr"]):
        raise ArtifactError("execution artifact stderr hash does not match")
    actual = fingerprint(value)
    if expected_fingerprint is not None and actual != expected_fingerprint:
        raise ArtifactError("execution artifact address does not match its content")
    return value


def persist(root, artifact):
    """Atomically publish one immutable object, refusing corrupt collisions."""
    value = _validate_envelope(envelope(artifact))
    artifact_fingerprint = fingerprint(value)
    path = artifact_path(root, artifact_fingerprint)
    directory = os.path.dirname(path)
    os.makedirs(directory, exist_ok=True)
    encoded = _canonical_bytes(value)
    if os.path.exists(path):
        with open(path, "rb") as fh:
            existing = fh.read()
        if existing != encoded:
            raise ArtifactError(
                "content-addressed artifact path already contains other bytes")
        return artifact_fingerprint
    temporary = os.path.join(
        directory, ".%s.%s.tmp" % (os.getpid(), secrets.token_hex(8)))
    try:
        with open(temporary, "xb") as fh:
            fh.write(encoded)
            fh.flush()
            os.fsync(fh.fileno())
        try:
            os.link(temporary, path)
        except FileExistsError:
            with open(path, "rb") as fh:
                existing = fh.read()
            if existing != encoded:
                raise ArtifactError(
                    "concurrent artifact publication found different bytes")
        except (AttributeError, NotImplementedError, OSError) as exc:
            # Immutability is the contract. A replace fallback has a race in
            # which another publisher's object can be overwritten between an
            # existence check and the replace. Filesystems without atomic
            # hard-link publication therefore fail closed.
            raise ArtifactError(
                "filesystem cannot atomically publish immutable artifact: %s"
                % exc)
    finally:
        if temporary is not None and os.path.exists(temporary):
            os.unlink(temporary)
    return artifact_fingerprint


def load(root, artifact_fingerprint):
    """Load and fully validate one referenced execution envelope."""
    path = artifact_path(root, artifact_fingerprint)
    try:
        with open(path, "rb") as fh:
            encoded = fh.read()
    except FileNotFoundError:
        raise ArtifactError("missing artifact %s" % artifact_fingerprint)
    try:
        value = json.loads(encoded.decode("utf-8"))
    except (UnicodeDecodeError, ValueError):
        raise ArtifactError("artifact is not canonical UTF-8 JSON")
    _validate_envelope(value, artifact_fingerprint)
    if encoded != _canonical_bytes(value):
        raise ArtifactError("artifact bytes are not in canonical form")
    return value


def persist_all(root, artifacts):
    """Persist a sequence and return fingerprints in trace order."""
    return [persist(root, artifact) for artifact in artifacts]


def reference_fields(artifact, artifact_fingerprint):
    """Project a durable object into a non-authoritative graph note."""
    value = _validate_envelope(
        envelope(artifact), expected_fingerprint=artifact_fingerprint)
    reference = {
        "artifact_fingerprint": artifact_fingerprint,
        "semantic_input_fingerprint": value["semantic_input_fingerprint"],
        "program_fingerprint": value["program_fingerprint"],
    }
    return {"source": NOTE_REFERENCE_PREFIX + _canonical_bytes(
        reference).decode("ascii")}


def note_reference(value):
    """Decode one graph-note reference; unrelated source strings return None."""
    if not isinstance(value, str) or not value.startswith(
            NOTE_REFERENCE_PREFIX):
        return None
    try:
        reference = json.loads(value[len(NOTE_REFERENCE_PREFIX):])
    except (TypeError, ValueError):
        raise ArtifactError("artifact note reference is malformed")
    fields = {
        "artifact_fingerprint", "semantic_input_fingerprint",
        "program_fingerprint",
    }
    if (not isinstance(reference, dict) or set(reference) != fields
            or not all(B.valid_fingerprint(reference[field])
                       for field in fields)):
        raise ArtifactError("artifact note reference is malformed")
    return reference


def audit_manifest(root, manifest):
    """Validate every object reference and its projection into a manifest."""
    problems = []
    trace = manifest.get("executions") if isinstance(manifest, dict) else None
    if not isinstance(trace, list):
        return ["backend manifest has no execution list"]
    identity_fields = (
        "contract", "implementation", "implementation_version",
        "protocol_version", "binary_version",
    )
    for index, entry in enumerate(trace):
        ref = entry.get("artifact_fingerprint") if isinstance(entry, dict) else None
        try:
            value = load(root, ref)
        except ArtifactError as exc:
            problems.append("execution %d: %s" % (index, exc))
            continue
        projected = {
            "semantic_input_fingerprint": value["semantic_input_fingerprint"],
            "program_fingerprint": value["program_fingerprint"],
            "stdout_fingerprint": value["stdout_fingerprint"],
            "stderr_fingerprint": value["stderr_fingerprint"],
            "returncode": value["returncode"],
            "aborted": value["aborted"],
            "artifact_fingerprint": ref,
        }
        if projected != entry:
            problems.append(
                "execution %d: artifact projection does not match trace" % index)
        if any(value["backend"].get(field) != manifest.get(field)
               for field in identity_fields):
            problems.append(
                "execution %d: artifact backend does not match manifest" % index)
    return problems


def audit_graph(root, graph):
    """Audit all syntactically current and stale verdict history."""
    problems = []
    from . import provenance as P
    for verdict_id in sorted(graph.verdicts):
        event = graph.verdicts[verdict_id]
        encoded = event.get("backend")
        manifest = P.backend_provenance(encoded, current_only=False)
        if manifest is None:
            if (isinstance(encoded, str)
                    and encoded.startswith(P.BACKEND_PROVENANCE_PREFIX)):
                problems.append(
                    "%s: backend v2 manifest is malformed" % verdict_id)
            continue
        for problem in audit_manifest(root, manifest):
            problems.append("%s: %s" % (verdict_id, problem))
        if (event.get("verifier") == "verify.elimination_groebner"
                and event.get("verdict") == "VERIFIED_GROEBNER"):
            trace = manifest.get("executions") or []
            if not trace:
                problems.append(
                    "%s: Groebner authority has no producer execution"
                    % verdict_id)
                continue
            try:
                final = load(root, trace[-1]["artifact_fingerprint"])
                certificate = json.loads(final["certificate"])
            except (ArtifactError, TypeError, ValueError, KeyError) as exc:
                problems.append(
                    "%s: final producer artifact has no readable checked "
                    "certificate (%s)" % (verdict_id, exc))
                continue
            proof = (event.get("representation") or {}).get("proof")
            if certificate != proof:
                problems.append(
                    "%s: final producer artifact certificate does not match "
                    "the verdict proof" % verdict_id)
    for index, note in enumerate(graph.notes):
        try:
            fields = note_reference(note.get("source"))
        except ArtifactError as exc:
            problems.append("note %d: %s" % (index, exc))
            continue
        if fields is None:
            continue
        try:
            value = load(root, fields["artifact_fingerprint"])
        except ArtifactError as exc:
            problems.append("note %d: %s" % (index, exc))
            continue
        if (fields["semantic_input_fingerprint"]
                != value["semantic_input_fingerprint"]
                or fields["program_fingerprint"]
                != value["program_fingerprint"]):
            problems.append(
                "note %d: artifact projection does not match note" % index)
    return problems
