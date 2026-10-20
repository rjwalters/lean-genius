"""Vision-language-model critic core.

This module ships the framework primitive for VLM critique of rendered
artifacts (decks, slides, figures). It is consumed by per-skill vision
commands such as ``anvil/skills/deck/commands/deck-vision.md`` and is
the architectural answer to #23 / #24 / #25 (vision-only defects that
markdown-side critics cannot catch).

Two public types:

- ``VisionRubric`` — a small dataclass listing the vision-critic-owned
  dimensions (each scored 0..max). Skills compose their own rubric by
  passing a custom list; the default exported here ships the six initial
  dimensions from the curator's D4 decision (#30):

  ``vertical_overflow``, ``label_cropping``, ``axis_legibility``,
  ``palette_adherence``, ``mathtext_artifacts``, ``slide_density``.

- ``VisionCritic`` — the critic object. Constructed either with a pinned
  Anthropic model id (default path: SDK call) or an injectable callback
  for offline/CI use. ``critique`` takes a list of rendered PNGs and a
  rubric and returns a fully-formed ``Review`` with ``kind=Kind.VISION``
  and ``rendered_artifact`` populated.

Design notes
------------

1. **No schema changes.** This module produces ``Review`` objects that
   validate against the canonical schema landed in #26 (PR #39). The
   ``Kind.VISION`` value and the ``rendered_artifact`` field were
   reserved for exactly this critic.

2. **Callback injection is first-class.** The default path uses the
   Anthropic Python SDK, but every test in this module passes a stub
   callback. Consumers without an API key (CI, offline development,
   deterministic test suites) inject a callable with signature
   ``(images: list[Path], prompt: str) -> dict``. The returned dict is
   the raw VLM payload that the critic post-processes into a ``Review``.

3. **VLM call is the only source of nondeterminism.** Image base64
   encoding, prompt assembly, JSON parsing, and ``Review`` construction
   are all pure. The model call is the boundary; everything around it
   is testable without ever touching Anthropic.

4. **Critical-flag policy** (per D5): two initial categories raise
   verdict-blocking flags — ``rendered_overflow_unrecoverable`` (visual
   overflow that loses load-bearing information) and
   ``mathtext_artifact_breaks_meaning`` (the #23 catch — a ``$X``
   rendered as italic ``X`` where the dollar sign carries semantic
   weight). Other vision findings surface as ``Finding`` items with
   severity major/minor/nit.
"""

from __future__ import annotations

import base64
import json
import re
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any, Callable, List, Optional, Sequence

from anvil.lib.review_schema import (
    CriticalFlag,
    Finding,
    Kind,
    Review,
    Score,
)


# Default model. Pinned for reproducibility per the canonical schema's
# strong recommendation. Consumers override by passing ``model=`` to the
# ``VisionCritic`` constructor.
DEFAULT_MODEL = "claude-opus-4-7-20251022"


# ---------------------------------------------------------------------------
# Rubric
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class VisionDimension:
    """One vision-rubric dimension. ``max`` is the per-dim weight.

    Each dimension is scored on ``[0, max]`` with a brief justification.
    The dimensions a vision critic owns are skill-defined; the default
    list below is the shipped six per #30 D4.
    """

    name: str
    max: int
    description: str


@dataclass(frozen=True)
class VisionRubric:
    """A rubric for vision critique.

    Parameters
    ----------
    dimensions:
        Ordered list of ``VisionDimension`` instances the critic scores.
        Order is the order in which the critic's ``_review.json`` lists
        the dimensions, and the order matters when other critics need to
        merge against this rubric (the aggregator preserves first-seen
        order).
    rubric_id:
        Optional stable identifier (e.g. ``"anvil-deck-vision-v1"``).
        Surfaced on the resulting ``Review``'s ``rubric`` field.
    """

    dimensions: Sequence[VisionDimension] = field(default_factory=list)
    rubric_id: Optional[str] = None

    def max_total(self) -> int:
        return sum(d.max for d in self.dimensions)


# The six default dimensions per the curator addendum (D4). Each is
# scored 0..5; max_total = 30.
DEFAULT_VISION_DIMENSIONS: Sequence[VisionDimension] = (
    VisionDimension(
        name="vertical_overflow",
        max=5,
        description=(
            "Content cut off below the slide bottom; rendered-bbox-based, "
            "not source-based. 5 = nothing clipped; 0 = critical content "
            "(numbers, names, citations) lost beneath the safe area."
        ),
    ),
    VisionDimension(
        name="label_cropping",
        max=5,
        description=(
            "Chart axis labels, legends, annotations truncated by the "
            "slide or figure border. 5 = all labels fully visible; 0 = "
            "key data labels unreadable."
        ),
    ),
    VisionDimension(
        name="axis_legibility",
        max=5,
        description=(
            "Font size of chart axis labels and tick marks vs projection "
            "scale. 5 = readable at the back of the conference room; 0 = "
            "illegible at 50% zoom on the rendered PNG."
        ),
    ),
    VisionDimension(
        name="palette_adherence",
        max=5,
        description=(
            "Figures match the Marp theme palette (e.g. deck palette "
            "#1f4e7a / #1a1a1a / #6b6b6b / #d6d6d6 / #f5f5f5 per #23). "
            "5 = consistent; 0 = default matplotlib palette overrides "
            "the theme."
        ),
    ),
    VisionDimension(
        name="mathtext_artifacts",
        max=5,
        description=(
            "Italic letters adjacent to dollar signs (direct catch for "
            "#23); LaTeX source rendered literally; mathtext renders "
            "instead of intended literal text. 5 = no artifacts; 0 = "
            "$11B rendered as italic 11B (semantic meaning lost)."
        ),
    ),
    VisionDimension(
        name="slide_density",
        max=5,
        description=(
            "Walls of text exceeding ~30 words per slide / ~6 bullets "
            "(IC-grade decks). 5 = disciplined throughout; 0 = wall of "
            "text on most slides."
        ),
    ),
)


def default_vision_rubric() -> VisionRubric:
    """Return the shipped default vision rubric (six dims, /30)."""
    return VisionRubric(
        dimensions=DEFAULT_VISION_DIMENSIONS,
        rubric_id="anvil-vision-v1",
    )


# ---------------------------------------------------------------------------
# Critical-flag policy
# ---------------------------------------------------------------------------

# Two initial verdict-blocking flag types per D5.
CRITICAL_FLAG_RENDERED_OVERFLOW_UNRECOVERABLE = "rendered_overflow_unrecoverable"
CRITICAL_FLAG_MATHTEXT_ARTIFACT_BREAKS_MEANING = "mathtext_artifact_breaks_meaning"


VISION_CRITICAL_FLAG_TYPES = frozenset(
    {
        CRITICAL_FLAG_RENDERED_OVERFLOW_UNRECOVERABLE,
        CRITICAL_FLAG_MATHTEXT_ARTIFACT_BREAKS_MEANING,
    }
)


# ---------------------------------------------------------------------------
# Callback type
# ---------------------------------------------------------------------------

# A vision callback receives the list of rendered images and the assembled
# prompt, and returns a dict matching the schema below (which the critic
# then maps onto a ``Review``):
#
#     {
#         "scores": [
#             {"dimension": "vertical_overflow", "score": 4, "critical": false,
#              "justification": "...", "fix": "..."},
#             ...
#         ],
#         "findings": [
#             {"severity": "major", "dimension": "...", "rationale": "...",
#              "suggested_fix": "...", "evidence_span": "..."},
#             ...
#         ],
#         "critical_flags": [
#             {"type": "rendered_overflow_unrecoverable", "justification": "...",
#              "evidence_span": "..."},
#             ...
#         ]
#     }
#
# Missing keys default to empty lists. ``score`` may be ``null`` for an
# unowned dimension (though by construction a vision critic owns all the
# rubric dims it ships).
VisionCallback = Callable[[List[Path], str], dict]


# ---------------------------------------------------------------------------
# Prompt template
# ---------------------------------------------------------------------------


def build_prompt(rubric: VisionRubric, context: Optional[str] = None) -> str:
    """Build the JSON-instruction prompt sent to the VLM.

    The prompt enumerates the rubric and asks for a JSON payload matching
    the callback contract. The model is told the critical-flag taxonomy
    so it raises flags by name rather than free-text.

    The optional ``context`` is appended to give the model rendering
    context (e.g. "This is slide 4 of a pitch deck"). Kept short to leave
    room for the images.
    """
    lines: List[str] = []
    lines.append(
        "You are a visual-design critic evaluating rendered presentation "
        "images. For each image, evaluate the rubric below and return ONE "
        "JSON object with the shape described."
    )
    lines.append("")
    lines.append("Rubric dimensions (score each 0..max):")
    for d in rubric.dimensions:
        lines.append(f"- {d.name} (0..{d.max}): {d.description}")
    lines.append("")
    lines.append("Critical-flag taxonomy (raise by type when applicable):")
    lines.append(
        f"- {CRITICAL_FLAG_RENDERED_OVERFLOW_UNRECOVERABLE}: content "
        "cropped below the safe area such that load-bearing information "
        "(numbers, names, citations) is lost."
    )
    lines.append(
        f"- {CRITICAL_FLAG_MATHTEXT_ARTIFACT_BREAKS_MEANING}: a $ "
        "rendered as italicized math (e.g. $11B → italic 11B) where the "
        "dollar sign carries semantic weight (financial slides)."
    )
    lines.append("")
    lines.append("Return JSON ONLY (no markdown wrapper, no commentary):")
    lines.append(
        '{"scores": [{"dimension": "<name>", "score": <int|null>, '
        '"critical": <bool>, "justification": "<1-3 sentences>", '
        '"fix": "<one sentence|null>"}, ...], '
        '"findings": [{"severity": "blocker|major|minor|nit", '
        '"dimension": "<name|null>", "rationale": "<1-2 sentences>", '
        '"suggested_fix": "<one sentence>", '
        '"evidence_span": "<path>:slide=<N>|null"}, ...], '
        '"critical_flags": [{"type": "<flag-name>", '
        '"justification": "<one paragraph>", '
        '"evidence_span": "<path>:slide=<N>|null"}, ...]}'
    )
    if context:
        lines.append("")
        lines.append(f"Context: {context}")
    return "\n".join(lines)


# ---------------------------------------------------------------------------
# Image helpers
# ---------------------------------------------------------------------------


def _encode_image(path: Path) -> dict:
    """Encode a local image as an Anthropic content block."""
    suffix = path.suffix.lower().lstrip(".")
    media_type = {
        "png": "image/png",
        "jpg": "image/jpeg",
        "jpeg": "image/jpeg",
        "webp": "image/webp",
        "gif": "image/gif",
    }.get(suffix, "image/png")
    data = base64.b64encode(path.read_bytes()).decode("ascii")
    return {
        "type": "image",
        "source": {
            "type": "base64",
            "media_type": media_type,
            "data": data,
        },
    }


# ---------------------------------------------------------------------------
# VisionCritic
# ---------------------------------------------------------------------------


class VisionCritic:
    """A VLM critic that scores rendered images against a VisionRubric.

    The default path constructs an Anthropic SDK client and calls
    ``messages.create`` with the images as content blocks. Tests and
    offline consumers inject a ``callback`` that bypasses the SDK
    entirely.

    Parameters
    ----------
    model:
        Anthropic model id (e.g. ``"claude-opus-4-7-20251022"``,
        ``"claude-sonnet-4-5-20251022"``). Recorded on the resulting
        ``Review.model`` for reproducibility.
    callback:
        Optional callable with signature ``(images, prompt) -> dict`` that
        returns the raw VLM payload. When provided, the SDK is not used.
        Test suites pass a stub here; CI/offline consumers pass a mock.
    critic_id:
        Identifier recorded on the resulting ``Review.critic_id``.
        Defaults to ``"vision"``; skills typically override with
        ``"deck-vision"``, ``"slides-vision"``, etc.
    """

    def __init__(
        self,
        model: str = DEFAULT_MODEL,
        callback: Optional[VisionCallback] = None,
        critic_id: str = "vision",
    ) -> None:
        self.model = model
        self.callback = callback
        self.critic_id = critic_id

    # -- Public API ---------------------------------------------------------

    def critique(
        self,
        images: List[Path],
        rubric: VisionRubric,
        version_dir: str,
        rendered_artifact: str,
        context: Optional[str] = None,
    ) -> Review:
        """Score ``images`` against ``rubric`` and return a Review.

        Parameters
        ----------
        images:
            Paths to the rendered PNGs (one per slide / page / figure).
        rubric:
            The vision rubric to score against.
        version_dir:
            Name of the version directory being critiqued (e.g.
            ``"acme-seed.1"``). Surfaced on ``Review.version_dir``.
        rendered_artifact:
            Path (relative to ``version_dir``) of the rendered artifact
            (e.g. ``"deck.pdf"``). Required because ``Kind.VISION``
            validates this field.
        context:
            Optional context string passed into the prompt (e.g.
            ``"This is a 12-slide pitch deck for a seed-stage startup."``).

        Returns
        -------
        A fully-validated ``Review`` with ``kind=Kind.VISION``.

        Raises
        ------
        ValueError
            If the VLM returns a payload that does not satisfy the
            ``Review`` schema (most commonly: missing scores entries).
        """
        prompt = build_prompt(rubric, context=context)

        if self.callback is not None:
            payload = self.callback(images, prompt)
        else:
            payload = self._call_anthropic(images, prompt)

        return self._payload_to_review(
            payload=payload,
            rubric=rubric,
            version_dir=version_dir,
            rendered_artifact=rendered_artifact,
        )

    # -- Internal helpers ---------------------------------------------------

    def _call_anthropic(self, images: List[Path], prompt: str) -> dict:
        """Default path: invoke the Anthropic SDK and return the JSON payload."""
        try:
            import anthropic  # type: ignore
        except ImportError as exc:
            raise RuntimeError(
                "anthropic SDK not installed. Either `pip install "
                "anthropic` or pass a `callback=` to bypass the SDK."
            ) from exc

        client = anthropic.Anthropic()
        content: List[Any] = [_encode_image(p) for p in images]
        content.append({"type": "text", "text": prompt})

        response = client.messages.create(
            model=self.model,
            max_tokens=4096,
            messages=[{"role": "user", "content": content}],
        )

        # The SDK returns a list of content blocks; we take the first
        # text block. The model is instructed to return JSON only.
        text_blocks = [
            b.text for b in response.content if getattr(b, "type", None) == "text"
        ]
        raw = text_blocks[0] if text_blocks else ""
        return _parse_json_payload(raw)

    def _payload_to_review(
        self,
        payload: dict,
        rubric: VisionRubric,
        version_dir: str,
        rendered_artifact: str,
    ) -> Review:
        """Map a callback payload to a validated Review.

        The payload may omit dims (we fill with score=None), and the
        ``critical`` per-dim flag and the critical_flags list together
        drive the aggregator's BLOCK verdict.
        """
        # Index incoming scores by dim name. The rubric enumerates the
        # required dimensions; entries in the payload for names not in
        # the rubric are silently dropped (a future-proofing choice).
        incoming_scores = {
            s.get("dimension"): s for s in payload.get("scores", [])
        }

        scores: List[Score] = []
        total: int = 0
        for dim in rubric.dimensions:
            entry = incoming_scores.get(dim.name) or {}
            raw_score = entry.get("score")
            if raw_score is not None:
                # Clamp to [0, max] defensively; the schema validator
                # would reject out-of-range scores otherwise.
                try:
                    s_int = int(raw_score)
                except (TypeError, ValueError):
                    s_int = None  # type: ignore[assignment]
                else:
                    s_int = max(0, min(dim.max, s_int))
                    total += s_int
                score_val: Optional[int] = s_int
            else:
                score_val = None
            scores.append(
                Score(
                    dimension=dim.name,
                    score=score_val,
                    max=dim.max,
                    critical=bool(entry.get("critical", False)),
                    fix=entry.get("fix") or None,
                    justification=entry.get("justification") or None,
                    evidence_span=entry.get("evidence_span") or None,
                )
            )

        findings: List[Finding] = []
        for f in payload.get("findings", []):
            sev = f.get("severity", "minor")
            if sev not in {"blocker", "major", "minor", "nit"}:
                sev = "minor"
            findings.append(
                Finding(
                    severity=sev,  # type: ignore[arg-type]
                    dimension=f.get("dimension") or None,
                    rationale=f.get("rationale", ""),
                    suggested_fix=f.get("suggested_fix", ""),
                    evidence_span=f.get("evidence_span") or None,
                )
            )

        critical_flags: List[CriticalFlag] = []
        for cf in payload.get("critical_flags", []):
            critical_flags.append(
                CriticalFlag(
                    type=cf.get("type", "unspecified"),
                    justification=cf.get("justification", ""),
                    evidence_span=cf.get("evidence_span") or None,
                )
            )

        return Review(
            schema_version="1",
            kind=Kind.VISION,
            version_dir=version_dir,
            critic_id=self.critic_id,
            model=self.model,
            rubric=rubric.rubric_id,
            scores=scores,
            findings=findings,
            critical_flags=critical_flags,
            total=total,
            threshold=rubric.max_total(),
            rendered_artifact=rendered_artifact,
        )


# ---------------------------------------------------------------------------
# JSON parsing helper
# ---------------------------------------------------------------------------

# Matches the first ``{ ... }`` block in a string (greedy across newlines).
# Used to forgive a model that wraps its JSON in ```json``` fences despite
# instructions.
_JSON_OBJECT = re.compile(r"\{.*\}", re.DOTALL)


def _parse_json_payload(text: str) -> dict:
    """Parse a JSON payload from a model's text response.

    The prompt asks for raw JSON, but models occasionally wrap output in
    ```json``` fences or precede it with a one-line preamble. We extract
    the first ``{ ... }`` block and parse that.

    Raises ``ValueError`` if no JSON object is found or parsing fails.
    """
    text = text.strip()
    if not text:
        raise ValueError("VLM returned empty text")
    try:
        return json.loads(text)
    except json.JSONDecodeError:
        pass
    match = _JSON_OBJECT.search(text)
    if match is None:
        raise ValueError(
            "VLM response did not contain a JSON object: "
            f"{text[:200]!r}"
        )
    return json.loads(match.group(0))


__all__ = [
    "DEFAULT_MODEL",
    "VisionDimension",
    "VisionRubric",
    "VisionCritic",
    "VisionCallback",
    "DEFAULT_VISION_DIMENSIONS",
    "default_vision_rubric",
    "build_prompt",
    "CRITICAL_FLAG_RENDERED_OVERFLOW_UNRECOVERABLE",
    "CRITICAL_FLAG_MATHTEXT_ARTIFACT_BREAKS_MEANING",
    "VISION_CRITICAL_FLAG_TYPES",
]
