"""Sidecar overlay assembly for `anvil:diff` (issue #925).

Translates the framework's typed review payloads into the plain
:class:`anvil.lib.prose_diff.OverlayNote` shape the renderer consumes.
This is deliberately a separate module from ``anvil.lib.prose_diff``: the
diff/render core is stdlib-only (see that module's docstring), while this
module is where the ``pydantic``-based ``review_schema`` /
``anvil.lib.critics`` and the ``rhetoric_lint`` overlays are composed --
both already base-dep / stdlib framework modules, just not ones the core
diff renderer should have to import.

Two overlay sources, both **read-only** and **non-throwing** (a missing
or malformed sidecar degrades to an empty overlay, never an exception --
the issue's "degrades gracefully" acceptance criterion):

- :func:`load_review_overlay` -- every ``.review``-shaped critic sibling
  of a version dir (found via ``anvil.lib.critics.discover_critics`` /
  ``load_review``), translated into per-dimension score notes and
  per-finding notes. Anchored to a line when the critic's
  ``evidence_span`` carries one (``<path>:L<start>-L<end>`` -- see
  ``anvil/lib/review_schema.py``'s ``Score.evidence_span`` docs);
  otherwise rendered as a document-level (unanchored) note.
- :func:`load_rhetoric_lint_overlay` -- runs the deterministic
  ``anvil.lib.rhetoric_lint`` pass over a text and translates its
  findings, which already carry a real 1-based ``line`` (or ``None`` for
  a document-level finding).
"""

from __future__ import annotations

import re
from pathlib import Path
from typing import List, Optional

from anvil.lib import critics
from anvil.lib.prose_diff import OverlayNote
from anvil.lib.rhetoric_lint import lint_rhetoric

__all__ = ["load_review_overlay", "load_rhetoric_lint_overlay"]


# Matches the trailing ``:L<start>`` or ``:L<start>-L<end>`` of the
# documented evidence_span format; anchors on the start line.
_SPAN_LINE_RE = re.compile(r":L(\d+)(?:-L\d+)?\s*$")


def _line_from_evidence_span(span: Optional[str]) -> Optional[int]:
    if not span:
        return None
    match = _SPAN_LINE_RE.search(span)
    if not match:
        return None
    try:
        return int(match.group(1))
    except ValueError:  # pragma: no cover - regex only matches digits
        return None


def load_review_overlay(version_dir: Path) -> List[OverlayNote]:
    """Load every critic sibling's scorecard + findings for ``version_dir``.

    Read-only over ``version_dir``'s siblings; never writes anything.
    Non-throwing: any discovery/parse failure (missing sibling, malformed
    ``_review.json``, unrecognized legacy shape) is skipped rather than
    raised, so a missing or partial ``.review/`` sidecar degrades to
    fewer notes instead of an error.
    """

    version_dir = Path(version_dir)
    notes: List[OverlayNote] = []
    try:
        critic_dirs = critics.discover_critics(version_dir)
    except OSError:
        return notes

    for critic_dir in critic_dirs:
        try:
            review = critics.load_review(critic_dir)
        except Exception:
            # Malformed / unrecognized sidecar payload -- skip it, don't
            # let one bad critic sibling blank the whole overlay.
            continue

        tag = critic_dir.name.rsplit(".", 1)[-1]

        for score in review.scores:
            if score.score is None:
                continue
            message = f"{score.dimension}: {score.score}/{score.max}"
            if score.justification:
                message = f"{message} -- {score.justification}"
            notes.append(
                OverlayNote(
                    line=_line_from_evidence_span(score.evidence_span),
                    severity="major" if score.critical else "info",
                    message=message,
                    source=f"review:{tag}",
                )
            )

        for finding in review.findings:
            message = finding.rationale
            if finding.suggested_fix:
                message = f"{message} -- {finding.suggested_fix}"
            notes.append(
                OverlayNote(
                    line=_line_from_evidence_span(finding.evidence_span),
                    severity=finding.severity,
                    message=message,
                    source=f"review:{tag}",
                )
            )

    return notes


def load_rhetoric_lint_overlay(text: str) -> List[OverlayNote]:
    """Run the deterministic rhetoric lint over ``text`` and translate it.

    Non-throwing: any lint failure degrades to an empty overlay rather
    than raising (the lint itself is documented as advisory-only and
    already non-throwing in practice, but this keeps the contract
    explicit at the overlay boundary too).
    """

    try:
        result = lint_rhetoric(text)
    except Exception:
        return []

    return [
        OverlayNote(
            line=finding.line,
            severity=finding.severity,
            message=f"[{finding.rule_id}] {finding.message}",
            source="rhetoric_lint",
        )
        for finding in result.findings
    ]
