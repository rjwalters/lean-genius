"""Typed schema and loader for Anvil rubric YAML files.

This module is the machine-readable canonicalization of the rubric shape
documented in ``anvil/lib/snippets/rubric.md``. It is sibling to
``review_schema.py`` (the on-disk shape of critic outputs) and
``critics.py`` (discovery + aggregation): rubrics define the dimension
list and weights that scores are taken against.

Two kinds of rubric coexist in the ecosystem:

1. **Generic convergence-gate rubrics** — every skill ships one as a
   markdown file (``anvil/skills/<skill>/rubric.md``). These define the
   dimensions whose weighted sum drives the
   ``advance = (total >= threshold) AND (no critical flag)`` decision.
   The v0 shipped skills declare either ``total: 40`` (8 dimensions)
   or ``total: 44`` (9 dimensions); the lib is total-agnostic and
   accepts any positive integer. The per-skill shape requirements are
   documented in ``snippets/rubric.md`` §"Shape requirements".
2. **Advisory venue-pinned overlays** — venue YAMLs (e.g. ``neurips.yaml``,
   ``nature.yaml``, ``arxiv.yaml``) under
   ``anvil/skills/paper/rubrics/``. These produce supplementary scoring
   that the reviser consumes for venue-specific signal, but do NOT
   contribute to the convergence-gate decision. Their weights need not
   sum to the declared ``total``, and ``threshold`` may be omitted.

Both kinds use the same ``Rubric`` pydantic model. The discriminator is
the ``advisory`` flag:

- ``advisory: false`` (default) — sum-of-weights MUST equal ``total``.
- ``advisory: true`` — sum-of-weights NEED NOT equal ``total``; the
  loader accepts the mismatch and the convergence gate ignores the rubric.

This split lets venue overlays declare any sensible total (NeurIPS /16,
Nature /15, arXiv /10) without breaking the per-skill gate-rubric
invariant that the skill's declared ``total`` means the same thing
across versions of that skill's reviewer.

Discovery
---------

Venue rubrics are looked up via ``discover_venue_rubric`` with a
three-tier search order documented inline. The per-thread tier lets a
single thread use a non-shipped venue without modifying the consumer
install; the consumer-installed tier lets a consumer ship a custom
venue across all their threads; the skill-shipped tier provides the
defaults.
"""

from __future__ import annotations

import json
from pathlib import Path
from typing import List, Optional

import yaml
from pydantic import BaseModel, ConfigDict, Field, model_validator


class RubricDimension(BaseModel):
    """One weighted dimension on a rubric.

    Mirrors ``Score`` (in ``review_schema.py``) on the rubric side:
    ``Score`` carries one critic's integer score against a dimension's
    ``max``; ``RubricDimension`` declares that ``max`` (here called
    ``weight``) plus the prose calibration guidance a scoring agent
    reads to assign the score.
    """

    model_config = ConfigDict(extra="forbid")

    id: str = Field(
        ...,
        description=(
            "Stable dimension identifier matched against ``Score.dimension`` "
            "on the critic side. Skills choose convention "
            "(e.g. ``soundness`` for venue rubrics, ``2_problem_clarity`` "
            "for ordinal-prefixed generic rubrics). Opaque to the lib."
        ),
    )
    name: str = Field(
        ...,
        description=(
            "Human-readable dimension name shown in reviewer prose and "
            "the scoring table. May be more verbose than ``id``."
        ),
    )
    weight: int = Field(
        ...,
        ge=1,
        description=(
            "Maximum score for this dimension (also called ``max`` on "
            "``Score``). Integer points; must be at least 1."
        ),
    )
    description: str = Field(
        ...,
        description=(
            "What this dimension measures. Two or more sentences so a "
            "scoring agent can actually apply the dimension without "
            "reading other context."
        ),
    )
    calibration: Optional[str] = Field(
        None,
        description=(
            "Optional calibration prose: what a full-weight score looks "
            "like vs. half-weight vs. zero. Strongly recommended for "
            "rubrics intended to be consumed by an LLM scoring agent."
        ),
    )


class CriticalFlagDefinition(BaseModel):
    """Definition of one critical-flag type a rubric recognizes.

    Mirrors ``CriticalFlag`` (in ``review_schema.py``) on the rubric
    side: ``CriticalFlag`` carries one instance set by a critic;
    ``CriticalFlagDefinition`` declares the vocabulary so reviewer
    agents apply a consistent set of flag types per rubric.
    """

    model_config = ConfigDict(extra="forbid")

    type: str = Field(
        ...,
        description=(
            "Short tag matching ``CriticalFlag.type``, e.g. "
            "``unverified_reproducibility_claim``. Lower_snake_case."
        ),
    )
    description: str = Field(
        ...,
        description=(
            "One-paragraph definition of when this flag should fire. "
            "Reviewer agents read this to decide whether a specific "
            "defect rises to flag-worthy severity."
        ),
    )


class Rubric(BaseModel):
    """A weighted-dimension rubric, generic or venue-pinned.

    Loaded from a YAML file via ``load_rubric``. The same model serves
    both the framework-wide convergence-gate rubrics (when shipped as
    YAML — markdown rubrics like ``anvil/skills/paper/rubric.md`` are
    not currently loaded by this module) and venue advisory overlays.
    The ``advisory`` flag distinguishes them. The lib is total-agnostic
    — gate rubrics declare any positive integer ``total`` (``40`` and
    ``44`` are the v0 observed shapes) and the validator enforces
    weight-sum-equals-``total`` only for non-advisory rubrics.
    """

    model_config = ConfigDict(extra="forbid")

    id: str = Field(
        ...,
        description=(
            "Stable rubric identifier matching ``Review.rubric``, e.g. "
            "``anvil-pub-v1`` for a /40 generic gate rubric, "
            "``anvil-memo-v2`` for a /44 generic gate rubric (post the "
            "/40 → /44 migration described in ``snippets/rubric.md`` "
            "§\"Per-review version stamping\"), or "
            "``anvil-pub-neurips-v1`` for a venue overlay. The lib does "
            "not enforce a naming scheme — the convention is documented "
            "in ``anvil/lib/README.md``."
        ),
    )
    name: str = Field(
        ...,
        description=(
            "Human-readable rubric name shown in reviewer prose, e.g. "
            "'NeurIPS reviewer rubric (2024 form)'."
        ),
    )
    venue: Optional[str] = Field(
        None,
        description=(
            "Venue slug (e.g. ``neurips``, ``nature``, ``arxiv``) when "
            "this rubric is a venue overlay. None for generic rubrics. "
            "Matches the ``venue`` field in ``<thread>/.anvil.json``."
        ),
    )
    total: int = Field(
        ...,
        ge=1,
        description=(
            "Total point pool. For ``advisory=False`` rubrics this MUST "
            "equal the sum of dimension weights. For ``advisory=True`` "
            "rubrics it is the declared total and need not match the "
            "weight sum (although matching is recommended for clarity)."
        ),
    )
    threshold: Optional[int] = Field(
        None,
        description=(
            "Advance threshold (integer score out of ``total``). Required "
            "for ``advisory=False`` rubrics (it drives the convergence "
            "gate). Optional for ``advisory=True`` rubrics (overlays are "
            "advisory; they have no gate)."
        ),
    )
    advisory: bool = Field(
        False,
        description=(
            "When True, this rubric is an advisory overlay: its scores "
            "are surfaced to the reviser for additional signal, but do "
            "NOT contribute to the convergence-gate decision and the "
            "sum-of-weights == total invariant is not enforced. Venue "
            "rubrics (NeurIPS, Nature, arXiv) ship with advisory=True. "
            "Generic convergence-gate rubrics (whatever their declared "
            "``total``) use advisory=False."
        ),
    )
    dimensions: List[RubricDimension] = Field(
        ...,
        min_length=1,
        description=(
            "Per-dimension rows. v0 generic gate rubrics ship with 8 "
            "dimensions (/40 shape) or 9 dimensions (/44 shape, dim 9 "
            "*Rhetorical economy*) per ``snippets/rubric.md``; advisory "
            "venue rubrics may have any number ≥ 1. The lib does not "
            "enforce a count."
        ),
    )
    critical_flags: List[CriticalFlagDefinition] = Field(
        default_factory=list,
        description=(
            "Critical-flag vocabulary for this rubric. May be empty for "
            "rubrics where any critic-judgment defect type is acceptable "
            "(no closed vocabulary)."
        ),
    )
    source: Optional[str] = Field(
        None,
        description=(
            "Public source for the rubric (URL, paper citation, or "
            "venue-form year). Required by convention for shipped venue "
            "YAMLs so they remain updateable as venue guidelines evolve."
        ),
    )

    @model_validator(mode="after")
    def _validate_weight_sum(self) -> "Rubric":
        weight_sum = sum(d.weight for d in self.dimensions)
        if not self.advisory:
            if weight_sum != self.total:
                raise ValueError(
                    f"Non-advisory rubric {self.id!r}: sum of dimension "
                    f"weights ({weight_sum}) must equal total "
                    f"({self.total}). Set advisory=true to opt out of "
                    f"the sum-to-total invariant."
                )
            if self.threshold is None:
                raise ValueError(
                    f"Non-advisory rubric {self.id!r}: threshold is "
                    f"required (it drives the convergence gate)."
                )
            if not 0 <= self.threshold <= self.total:
                raise ValueError(
                    f"Non-advisory rubric {self.id!r}: threshold "
                    f"({self.threshold}) must be in [0, total={self.total}]."
                )
        return self

    @model_validator(mode="after")
    def _validate_unique_dimension_ids(self) -> "Rubric":
        seen: set[str] = set()
        for d in self.dimensions:
            if d.id in seen:
                raise ValueError(
                    f"Rubric {self.id!r}: duplicate dimension id "
                    f"{d.id!r}; dimension ids must be unique."
                )
            seen.add(d.id)
        return self

    @model_validator(mode="after")
    def _validate_unique_critical_flag_types(self) -> "Rubric":
        seen: set[str] = set()
        for cf in self.critical_flags:
            if cf.type in seen:
                raise ValueError(
                    f"Rubric {self.id!r}: duplicate critical_flag type "
                    f"{cf.type!r}; critical flag types must be unique."
                )
            seen.add(cf.type)
        return self


# ---------------------------------------------------------------------------
# Loading
# ---------------------------------------------------------------------------


def load_rubric(path: Path) -> Rubric:
    """Load and validate a rubric YAML file.

    Raises ``FileNotFoundError`` if ``path`` does not exist,
    ``yaml.YAMLError`` on malformed YAML, and
    ``pydantic.ValidationError`` on schema violations (unknown fields,
    weight-sum mismatch on non-advisory rubrics, duplicate dimension ids,
    etc.).
    """
    path = Path(path)
    if not path.is_file():
        raise FileNotFoundError(f"Rubric file not found: {path}")
    with path.open("r", encoding="utf-8") as fh:
        data = yaml.safe_load(fh)
    if data is None:
        raise ValueError(f"Rubric file is empty: {path}")
    if not isinstance(data, dict):
        raise ValueError(
            f"Rubric file {path} top-level must be a mapping; "
            f"got {type(data).__name__}"
        )
    return Rubric.model_validate(data)


# ---------------------------------------------------------------------------
# Discovery
# ---------------------------------------------------------------------------


def _read_anvil_json(thread_dir: Path) -> dict:
    """Read ``<thread_dir>/.anvil.json`` and return parsed dict (or {})."""
    anvil_json = thread_dir / ".anvil.json"
    if not anvil_json.is_file():
        return {}
    try:
        with anvil_json.open("r", encoding="utf-8") as fh:
            data = json.load(fh)
    except (json.JSONDecodeError, OSError):
        return {}
    if not isinstance(data, dict):
        return {}
    return data


def discover_venue_rubric(
    thread_dir: Path,
    skill_root: Path,
    *,
    consumer_root: Optional[Path] = None,
) -> Optional[Rubric]:
    """Discover and load the venue overlay rubric for a thread.

    Reads ``<thread_dir>/.anvil.json`` for the ``venue`` field. If no
    venue is declared (no ``.anvil.json``, or no ``venue`` key, or
    ``venue`` is null/empty), returns ``None``.

    Otherwise searches three tiers in order — first hit wins:

    1. **Per-thread**: ``<thread_dir>/.anvil/rubrics/<venue>.yaml``.
       For a single thread that wants a non-shipped venue overlay
       without modifying the consumer install.
    2. **Consumer-installed**: ``<consumer_root>/.anvil/skills/paper/rubrics/<venue>.yaml``.
       For a consumer who wants to ship a custom venue across all their
       threads. ``consumer_root`` defaults to ``thread_dir.parent``
       (the portfolio directory) when not supplied.
    3. **Skill-shipped**: ``<skill_root>/rubrics/<venue>.yaml`` (where
       ``skill_root`` is typically ``anvil/skills/paper`` in the source
       tree or ``.anvil/skills/paper`` in an installed consumer repo).
       The framework defaults (``neurips``, ``nature``, ``arxiv``).

    Returns the loaded ``Rubric`` on hit, or ``None`` when ``venue``
    is declared but no YAML is found in any tier (caller can warn and
    proceed without the overlay — the generic gate is still in force).
    """
    config = _read_anvil_json(thread_dir)
    venue = config.get("venue")
    if not isinstance(venue, str) or not venue.strip():
        return None
    venue = venue.strip()

    # Build the search order. `consumer_root` defaults to the portfolio
    # directory (the thread's parent), which is the natural home for a
    # per-portfolio `.anvil/skills/paper/rubrics/<venue>.yaml` override.
    if consumer_root is None:
        consumer_root = thread_dir.parent

    candidates = [
        thread_dir / ".anvil" / "rubrics" / f"{venue}.yaml",
        consumer_root / ".anvil" / "skills" / "paper" / "rubrics" / f"{venue}.yaml",
        Path(skill_root) / "rubrics" / f"{venue}.yaml",
    ]

    for candidate in candidates:
        if candidate.is_file():
            return load_rubric(candidate)

    return None


__all__ = [
    "CriticalFlagDefinition",
    "Rubric",
    "RubricDimension",
    "discover_venue_rubric",
    "load_rubric",
]
