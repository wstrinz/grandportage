"""Small structural harness for out-of-tree evidence adapters."""

import importlib
import json
import re
import sys


REQUIRED_ENVELOPE_FIELDS = {
    "schema", "context", "source_bindings", "checked_proposition",
    "certificate_payload", "licenses", "outstanding_premises",
    "graph_effect", "authority_boundary",
}
_DIGEST = re.compile(r"^sha256:[0-9a-f]{64}$")


class AdapterConformanceError(ValueError):
    pass


def _require(condition, message):
    if not condition:
        raise AdapterConformanceError(message)


def check_adapter(adapter):
    graph_effect = getattr(adapter, "GRAPH_EFFECT", None)
    mutations = getattr(adapter, "MUTATION_CONTROLS", None)
    build = getattr(adapter, "build_envelope", None)
    replay = getattr(adapter, "replay", None)
    _require(isinstance(graph_effect, str) and graph_effect,
             "adapter must declare GRAPH_EFFECT")
    _require(isinstance(mutations, tuple) and mutations and
             all(isinstance(value, str) and value for value in mutations),
             "adapter must declare nonempty MUTATION_CONTROLS")
    _require(callable(build), "adapter must provide build_envelope()")
    _require(callable(replay), "adapter must provide replay(envelope)")
    envelope = build()
    _require(isinstance(envelope, dict) and
             set(envelope) == REQUIRED_ENVELOPE_FIELDS,
             "adapter envelope fields do not match the shared contract")
    _require(envelope["graph_effect"] == graph_effect,
             "adapter and envelope graph effects disagree")
    bindings = envelope["source_bindings"]
    _require(isinstance(bindings, list) and bindings,
             "adapter needs at least one source binding")
    for binding in bindings:
        _require(isinstance(binding, dict) and set(binding) == {"id", "sha256"},
                 "source binding must contain id and sha256")
        _require(isinstance(binding["id"], str) and binding["id"],
                 "source binding id is empty")
        _require(isinstance(binding["sha256"], str) and
                 _DIGEST.fullmatch(binding["sha256"]),
                 "source binding digest is not canonical sha256")
    first = replay(envelope)
    second = replay(envelope)
    _require(first == second, "adapter replay is not deterministic")
    _require(isinstance(first, dict) and first.get("verified") is True,
             "adapter replay did not verify its envelope")
    return {
        "status": "CONFORMING",
        "authority": "DESCRIPTIVE_ONLY",
        "graph_effect": graph_effect,
        "schema": envelope["schema"],
        "source_binding_count": len(bindings),
        "mutation_controls": list(mutations),
    }


def main(argv=None):
    argv = list(sys.argv[1:] if argv is None else argv)
    if len(argv) != 1:
        print(json.dumps({"status": "REFUSED",
                          "error": "usage: adapter_conformance MODULE"}))
        return 2
    try:
        report = check_adapter(importlib.import_module(argv[0]))
    except (ImportError, AdapterConformanceError, AttributeError) as exc:
        print(json.dumps({"status": "REFUSED", "error": str(exc)},
                         sort_keys=True))
        return 1
    print(json.dumps(report, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
