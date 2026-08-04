"""Composition checker for Laurent lowering followed by coefficient expansion."""

import hashlib
import json

from . import coefficient_expansion as CE
from . import groebner as G
from . import laurent_lowering as LL


SCHEMA = "laurent_coefficient_pipeline_v1"
VERIFIED = "VERIFIED_LAURENT_COEFFICIENT_PIPELINE"


class LaurentCoefficientPipelineError(ValueError):
    """A proposed compiler-pass composition is malformed or unbound."""


def _require(condition, message):
    if not condition:
        raise LaurentCoefficientPipelineError(message)


def _closed(value, fields, where):
    _require(isinstance(value, dict), "%s must be an object" % where)
    extra = set(value) - set(fields)
    _require(not extra, "%s has unknown field(s): %s" % (
        where, ", ".join(sorted(extra))))


def _canonical_payload(value):
    return json.dumps(
        value, sort_keys=True, separators=(",", ":"), ensure_ascii=True
    )


def verify(spec):
    """Verify two compiler passes and bind every downstream image exactly."""
    _closed(spec, {
        "schema", "laurent", "coefficient_expansion", "bindings",
    }, "Laurent/coefficient pipeline specification")
    _require(spec.get("schema") == SCHEMA,
             "schema must be %s" % SCHEMA)
    laurent_spec = spec.get("laurent")
    coefficient_spec = spec.get("coefficient_expansion")
    try:
        laurent_report = LL.verify(laurent_spec)
    except LL.LaurentLoweringError as exc:
        raise LaurentCoefficientPipelineError(
            "Laurent pass failed: %s" % exc
        )
    try:
        coefficient_report = CE.verify(coefficient_spec)
    except CE.CoefficientExpansionError as exc:
        raise LaurentCoefficientPipelineError(
            "coefficient pass failed: %s" % exc
        )

    _require(laurent_spec["characteristic"]
             == coefficient_spec["characteristic"],
             "both passes must use the same characteristic")
    _require(laurent_spec["series_variable"]
             == coefficient_spec["parameter"],
             "Laurent series variable must equal coefficient parameter")
    _require(laurent_spec["coefficient_variables"]
             == coefficient_spec["coefficient_variables"],
             "both passes must use the same ordered coefficient variables")

    bindings = spec.get("bindings")
    _require(isinstance(bindings, list) and bindings,
             "bindings must be a nonempty list")
    _require(len(bindings) <= G._MAX_VARIABLES,
             "too many Laurent/coefficient bindings")
    exports = dict((item["id"], item) for item in laurent_report["exports"])
    images = coefficient_spec["images"]
    source_variables = coefficient_spec["source_variables"]
    reports = []
    seen_exports = set()
    seen_images = set()
    for position, binding in enumerate(bindings):
        where = "binding %d" % position
        _closed(binding, {"export", "image"}, where)
        export_id = binding.get("export")
        image = binding.get("image")
        _require(isinstance(export_id, str) and export_id in exports,
                 "%s export must name a verified Laurent export" % where)
        _require(isinstance(image, str) and image in images,
                 "%s image must name a coefficient source image" % where)
        _require(export_id not in seen_exports,
                 "a Laurent export cannot be bound twice")
        _require(image not in seen_images,
                 "a coefficient image cannot be bound twice")
        seen_exports.add(export_id)
        seen_images.add(image)
        _require(images[image] == exports[export_id]["polynomial"],
                 "%s downstream image differs from the named Laurent export"
                 % where)
        reports.append({"export": export_id, "image": image})

    _require(seen_images == set(source_variables),
             "bindings must cover every coefficient source image")
    return {
        "schema": SCHEMA,
        "verdict": VERIFIED,
        "licenses": [
            "bound_laurent_to_coefficient_pipeline",
            *coefficient_report["licenses"],
        ],
        "bindings": reports,
        "laurent_report": laurent_report,
        "coefficient_report": coefficient_report,
        "authority_boundary": (
            "exact pass composition only; no source derivation, chart "
            "validity, claim transport, or graph authority"
        ),
        "spec_fingerprint": hashlib.sha256(
            _canonical_payload(spec).encode("utf-8")
        ).hexdigest(),
    }
