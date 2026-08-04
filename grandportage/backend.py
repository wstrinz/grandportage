"""Backend-neutral requests and immutable execution artifacts.

The graph stores mathematical declarations.  A backend execution is evidence
about one of those declarations, not the declaration itself.  Keeping the
execution shape here prevents a CAS adapter from quietly deciding graph
semantics and gives differential tests one common object to compare.
"""

from abc import ABC, abstractmethod
from dataclasses import dataclass
import hashlib
import json
import re


BACKEND_PROTOCOL_VERSION = 2
SINGULAR_CONTRACT = "singular"
SINGULAR_IMPLEMENTATION = "grandportage.cas.SingularBackend"
SINGULAR_IMPLEMENTATION_VERSION = 3


def _canonical(value):
    return json.dumps(
        value, sort_keys=True, separators=(",", ":"), ensure_ascii=True
    )


def semantic_fingerprint(kind, payload):
    """Content-address a backend request independently of presentation."""
    encoded = _canonical({"kind": kind, "payload": payload}).encode("utf-8")
    return "sha256:" + hashlib.sha256(encoded).hexdigest()


def text_fingerprint(text):
    return "sha256:" + hashlib.sha256(text.encode("utf-8")).hexdigest()


_FINGERPRINT_RE = re.compile(r"^sha256:[0-9a-f]{64}$")
EXECUTION_TRACE_FIELDS = {
    "semantic_input_fingerprint", "program_fingerprint",
    "stdout_fingerprint", "stderr_fingerprint", "returncode", "aborted",
    "artifact_fingerprint",
}


def valid_fingerprint(value):
    return isinstance(value, str) and _FINGERPRINT_RE.match(value) is not None


def execution_trace_entry(artifact):
    """Project an immutable artifact into persisted, content-addressed trace."""
    return {
        "semantic_input_fingerprint": artifact.semantic_input_fingerprint,
        "program_fingerprint": artifact.program_fingerprint,
        "stdout_fingerprint": artifact.stdout_fingerprint,
        "stderr_fingerprint": artifact.stderr_fingerprint,
        "returncode": artifact.returncode,
        "aborted": artifact.aborted,
        "artifact_fingerprint": execution_artifact_fingerprint(artifact),
    }


def valid_execution_trace_entry(entry):
    """Reject a trace hash over malformed or type-confused execution data."""
    if not isinstance(entry, dict) or set(entry) != EXECUTION_TRACE_FIELDS:
        return False
    if not all(valid_fingerprint(entry[field]) for field in (
            "semantic_input_fingerprint", "program_fingerprint",
            "stdout_fingerprint", "stderr_fingerprint",
            "artifact_fingerprint")):
        return False
    return (type(entry["returncode"]) is int
            and type(entry["aborted"]) is bool)


@dataclass(frozen=True)
class RingSpec:
    """The coefficient domain and ordered variables a backend must preserve."""

    variables: tuple
    characteristic: int
    ordering: str = "dp"

    def payload(self):
        return {
            "variables": list(self.variables),
            "characteristic": self.characteristic,
            "coefficient_domain": (
                "Q" if self.characteristic == 0
                else "F_%d" % self.characteristic
            ),
            "ordering": self.ordering,
        }


@dataclass(frozen=True)
class BackendIdentity:
    contract: str
    implementation: str
    implementation_version: int
    binary_version: str

    def payload(self):
        return {
            "contract": self.contract,
            "implementation": self.implementation,
            "implementation_version": self.implementation_version,
            "binary_version": self.binary_version,
            "protocol_version": BACKEND_PROTOCOL_VERSION,
        }


@dataclass(frozen=True)
class ExecutionArtifact:
    """A snapshot of exactly what ran and exactly what came back.

    ``parsed_output`` and ``certificate`` are canonical JSON strings rather
    than mutable dictionaries.  The artifact can therefore be retained safely
    even when compatibility callers mutate the legacy result dictionary.
    """

    backend: BackendIdentity
    semantic_input_fingerprint: str
    program_fingerprint: str
    program_text: str
    completion_nonce: str
    argv: tuple
    returncode: int
    aborted: bool
    abort_reason: object
    stdout: str
    stderr: str
    stdout_fingerprint: str
    stderr_fingerprint: str
    parsed_output: object = None
    certificate: object = None

    def payload(self):
        """Closed JSON value persisted by the content-addressed store."""
        return {
            "schema": 1,
            "backend": self.backend.payload(),
            "semantic_input_fingerprint": self.semantic_input_fingerprint,
            "program_fingerprint": self.program_fingerprint,
            "program_text": self.program_text,
            "completion_nonce": self.completion_nonce,
            "argv": list(self.argv),
            "returncode": self.returncode,
            "aborted": self.aborted,
            "abort_reason": self.abort_reason,
            "stdout": self.stdout,
            "stderr": self.stderr,
            "stdout_fingerprint": self.stdout_fingerprint,
            "stderr_fingerprint": self.stderr_fingerprint,
            "parsed_output": self.parsed_output,
            "certificate": self.certificate,
        }

    def with_parsed(self, values, certificate=None):
        return ExecutionArtifact(
            backend=self.backend,
            semantic_input_fingerprint=self.semantic_input_fingerprint,
            program_fingerprint=self.program_fingerprint,
            program_text=self.program_text,
            completion_nonce=self.completion_nonce,
            argv=self.argv,
            returncode=self.returncode,
            aborted=self.aborted,
            abort_reason=self.abort_reason,
            stdout=self.stdout,
            stderr=self.stderr,
            stdout_fingerprint=self.stdout_fingerprint,
            stderr_fingerprint=self.stderr_fingerprint,
            parsed_output=_canonical(values),
            certificate=(
                _canonical(certificate) if certificate is not None else None
            ),
        )


def execution_artifact_fingerprint(artifact):
    """Address the complete immutable artifact, not merely its transcript."""
    if not isinstance(artifact, ExecutionArtifact):
        raise TypeError("expected an ExecutionArtifact")
    encoded = _canonical(artifact.payload()).encode("utf-8")
    return "sha256:" + hashlib.sha256(encoded).hexdigest()


class BackendExecution(dict):
    """A legacy-compatible result dictionary carrying an immutable artifact."""

    def __init__(self, raw, *, backend, program, execution_program,
                 completion_nonce, semantic_input_fingerprint):
        super().__init__(raw)
        text = execution_program.text
        stdout = str(raw.get("stdout", ""))
        stderr = str(raw.get("stderr", ""))
        self.program = program
        self.execution_program = execution_program
        self.artifact = ExecutionArtifact(
            backend=backend,
            semantic_input_fingerprint=semantic_input_fingerprint,
            program_fingerprint=text_fingerprint(text),
            program_text=text,
            completion_nonce=completion_nonce,
            argv=tuple(raw.get("argv") or ()),
            returncode=int(raw.get("returncode", -1)),
            aborted=bool(raw.get("aborted")),
            abort_reason=raw.get("abort_reason"),
            stdout=stdout,
            stderr=stderr,
            stdout_fingerprint=text_fingerprint(stdout),
            stderr_fingerprint=text_fingerprint(stderr),
        )
        self._publish_artifact_fields()

    def _publish_artifact_fields(self):
        """Expose audit fields to old dict-shaped callers as additive keys."""
        self["backend"] = self.artifact.backend.contract
        self["backend_implementation"] = self.artifact.backend.implementation
        self["backend_implementation_version"] = (
            self.artifact.backend.implementation_version
        )
        self["backend_binary_version"] = (
            self.artifact.backend.binary_version
        )
        self["semantic_input_fingerprint"] = (
            self.artifact.semantic_input_fingerprint
        )
        self["program_fingerprint"] = self.artifact.program_fingerprint
        self["program"] = self.program
        self["raw_output"] = {
            "stdout": self.artifact.stdout,
            "stderr": self.artifact.stderr,
        }

    def attach_parsed(self, values, certificate=None):
        self.artifact = self.artifact.with_parsed(values, certificate)
        self["parsed_values"] = values
        if certificate is not None:
            self["certificate"] = certificate
        return self


def validate_execution_artifact(execution, program=None):
    """Bind retained bytes and fingerprints to one exact executed program."""
    if not isinstance(execution, BackendExecution):
        raise TypeError("backend answer did not retain a BackendExecution")
    artifact = execution.artifact
    if program is not None:
        execution_text = getattr(program, "execution_text", None)
        text = (
            execution_text(artifact.completion_nonce)
            if callable(execution_text)
            else getattr(program, "text", None)
        )
        if not isinstance(text, str):
            raise TypeError("backend answer returned a program without text")
        if artifact.program_text != text:
            raise ValueError("backend artifact belongs to a different program")
    if artifact.program_fingerprint != text_fingerprint(artifact.program_text):
        raise ValueError("backend artifact program fingerprint does not match")
    if artifact.stdout_fingerprint != text_fingerprint(artifact.stdout):
        raise ValueError("backend artifact stdout fingerprint does not match")
    if artifact.stderr_fingerprint != text_fingerprint(artifact.stderr):
        raise ValueError("backend artifact stderr fingerprint does not match")
    if not valid_fingerprint(artifact.semantic_input_fingerprint):
        raise ValueError("backend semantic input fingerprint is malformed")
    return artifact


class Backend(ABC):
    """Semantic CAS boundary implemented by Singular and future cross-checkers."""

    @property
    @abstractmethod
    def identity(self):
        raise NotImplementedError

    @property
    @abstractmethod
    def can_record_verdicts(self):
        """Whether this exact adapter is trusted to persist authority."""
        raise NotImplementedError

    @property
    @abstractmethod
    def execution_count(self):
        """Opaque cursor used to delimit the executions for one verdict."""
        raise NotImplementedError

    @abstractmethod
    def provenance(self, start=0):
        """Return the canonical manifest for executions since ``start``."""
        raise NotImplementedError

    @abstractmethod
    def execute(self, program, timeout=300, semantic_input=None):
        """Execute a validated backend program and retain an exact artifact."""
        raise NotImplementedError

    @abstractmethod
    def classify_identity(self, ring_vars, lhs, rhs, generators=(),
                          characteristic=0, timeout=300):
        raise NotImplementedError

    @abstractmethod
    def membership(self, ring_vars, target, generators, characteristic=0,
                   timeout=300):
        raise NotImplementedError

    @abstractmethod
    def check_membership(self, ring_vars, target, generators, cofactors,
                         characteristic=0, timeout=300):
        raise NotImplementedError

    @abstractmethod
    def unit_ideal(self, ring_vars, generators, characteristic=0,
                   timeout=300):
        raise NotImplementedError

    @abstractmethod
    def check_unit_ideal(self, ring_vars, generators, cofactors,
                         characteristic=0, timeout=300):
        raise NotImplementedError

    @abstractmethod
    def pullback_reduce(self, ring_vars, expr, images, generators=(),
                        characteristic=0, timeout=300):
        raise NotImplementedError

    @abstractmethod
    def evaluate_point(self, ring_vars, generators, point, characteristic=0,
                       timeout=300):
        raise NotImplementedError

    @abstractmethod
    def saturate(self, ring_vars, generators, at, characteristic=0,
                 timeout=300):
        raise NotImplementedError

    @abstractmethod
    def eliminate(self, ring_vars, generators, variables, characteristic=0,
                  timeout=300):
        raise NotImplementedError

    @abstractmethod
    def partition_cover(self, ring_vars, parent_generators, branches,
                        characteristic=0, timeout=300):
        raise NotImplementedError

    @abstractmethod
    def factorizing_decomposition(self, ring_vars, generators,
                                  characteristic=0, timeout=300,
                                  return_program=False):
        raise NotImplementedError
