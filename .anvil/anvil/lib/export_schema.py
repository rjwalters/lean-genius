"""Export pydantic schemas as JSON Schema documents.

Run from the repo root:

    python3 -m anvil.lib.export_schema

Two JSON Schema documents are emitted:

- ``anvil/lib/review_schema.json`` — the critic ``_review.json`` payload
  (union of ``Review`` and ``AggregatedReview``).
- ``anvil/lib/rubric_schema.json`` — the rubric YAML shape used by both
  generic convergence-gate rubrics (the skill's declared ``total``,
  ``40`` and ``44`` are the v0 observed shapes) and venue advisory
  overlays (loaded by ``anvil.lib.rubric.load_rubric``).

Both are consumed by non-Python callers (e.g., a future TypeScript
orchestrator) for validation against the same contract as the Python
models.

The review-schema document is the union of three schemas:

- ``$defs.Review`` — the per-critic ``_review.json`` payload.
- ``$defs.AggregatedReview`` — the merged result produced by
  ``anvil/lib/critics.py::aggregate``.
- ``$defs.ProbeLog`` — the ``probes.json`` perishable-verification
  re-probe list (issue #863).

The top-level review schema accepts any of those shapes (``oneOf``) so a
single validator can be pointed at any file in a critic sibling dir.

The rubric-schema document is a single ``Rubric`` shape covering both
generic and advisory venue overlays (discriminated by the ``advisory``
flag inside the document, not by separate top-level schemas).
"""

from __future__ import annotations

import json
from pathlib import Path

from anvil.lib.review_schema import AggregatedReview, ProbeLog, Review
from anvil.lib.rubric import Rubric


SCHEMA_PATH = Path(__file__).parent / "review_schema.json"
RUBRIC_SCHEMA_PATH = Path(__file__).parent / "rubric_schema.json"


def build_schema() -> dict:
    """Return the combined review JSON Schema document as a dict."""
    review_schema = Review.model_json_schema(ref_template="#/$defs/{model}")
    agg_schema = AggregatedReview.model_json_schema(
        ref_template="#/$defs/{model}"
    )
    probe_log_schema = ProbeLog.model_json_schema(ref_template="#/$defs/{model}")

    # pydantic emits a top-level "$defs" inside each schema; pull them up so
    # the combined document has a single shared "$defs" map.
    shared_defs: dict = {}
    for sub_schema in (review_schema, agg_schema, probe_log_schema):
        sub_defs = sub_schema.pop("$defs", {})
        for name, defn in sub_defs.items():
            shared_defs.setdefault(name, defn)

    shared_defs["Review"] = review_schema
    shared_defs["AggregatedReview"] = agg_schema
    shared_defs["ProbeLog"] = probe_log_schema

    return {
        "$schema": "https://json-schema.org/draft/2020-12/schema",
        "$id": "https://anvil.dev/schemas/review_schema.json",
        "title": "Anvil critic output schema",
        "description": (
            "Canonical JSON contract written by Anvil critic siblings "
            "as _review.json, and produced by the aggregator. Generated "
            "from anvil/lib/review_schema.py; do not edit by hand."
        ),
        "oneOf": [
            {"$ref": "#/$defs/Review"},
            {"$ref": "#/$defs/AggregatedReview"},
            {"$ref": "#/$defs/ProbeLog"},
        ],
        "$defs": shared_defs,
    }


def build_rubric_schema() -> dict:
    """Return the rubric JSON Schema document as a dict.

    Covers both generic convergence-gate rubrics (the skill's declared
    ``total`` — ``40`` and ``44`` are the v0 observed shapes) and
    advisory venue overlays; the ``advisory`` field inside the document
    discriminates them (advisory rubrics relax the sum-to-total
    invariant and the threshold requirement).
    """
    rubric_schema = Rubric.model_json_schema(ref_template="#/$defs/{model}")

    shared_defs: dict = {}
    sub_defs = rubric_schema.pop("$defs", {})
    for name, defn in sub_defs.items():
        shared_defs.setdefault(name, defn)
    shared_defs["Rubric"] = rubric_schema

    return {
        "$schema": "https://json-schema.org/draft/2020-12/schema",
        "$id": "https://anvil.dev/schemas/rubric_schema.json",
        "title": "Anvil rubric YAML schema",
        "description": (
            "Canonical YAML/JSON contract for Anvil rubric files. "
            "Covers both generic convergence-gate rubrics (the skill's "
            "declared `total`; /40 and /44 are the v0 observed shapes) "
            "and advisory venue overlays (discriminated by the "
            "`advisory` field). Generated from anvil/lib/rubric.py; do "
            "not edit by hand."
        ),
        "$ref": "#/$defs/Rubric",
        "$defs": shared_defs,
    }


def write_schema(path: Path = SCHEMA_PATH) -> Path:
    """Write the review schema JSON to ``path`` and return the path."""
    data = build_schema()
    path.write_text(json.dumps(data, indent=2, sort_keys=True) + "\n")
    return path


def write_rubric_schema(path: Path = RUBRIC_SCHEMA_PATH) -> Path:
    """Write the rubric schema JSON to ``path`` and return the path."""
    data = build_rubric_schema()
    path.write_text(json.dumps(data, indent=2, sort_keys=True) + "\n")
    return path


def main() -> None:
    review_out = write_schema()
    rubric_out = write_rubric_schema()
    print(f"Wrote JSON Schema to {review_out}")
    print(f"Wrote JSON Schema to {rubric_out}")


if __name__ == "__main__":
    main()
