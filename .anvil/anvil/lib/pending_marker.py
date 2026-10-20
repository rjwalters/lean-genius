"""Deterministic pending-measurement placeholder gate (issues #841 / #842).

Phase 1 of parent tracking issue #841, scoped by #842. Fifth member of
the deterministic-checks family (alongside
``anvil/lib/numeric_consistency.py``, ``anvil/lib/render_gate.py``,
``anvil/lib/marp_lint.py``, and ``anvil/lib/revise_consistency.py``).

The problem
-----------

Drafting an artifact whose load-bearing numbers do not yet exist
(measurement pending, benchmark queued, quote not returned) is a common
situation. Without a supported convention, correct behavior depends on
ad-hoc per-thread prompt discipline hand-written into ``BRIEF.md``
instead of being a first-class skill feature — and critics have no way
to distinguish "number missing because pending" from "number missing
because the drafter was sloppy (or fabricated a value to avoid the
awkward gap)". A deliberately-incomplete draft scores as defective when
it shouldn't, or worse, a drafter fabricates a plausible-looking number
to paper over the gap.

The convention
---------------

A drafter marks a genuinely-outstanding value with a bracketed
placeholder naming its source::

    The model reaches [PENDING benchmark-run-2024-11] accuracy on the
    held-out set.

    Component cost is [PENDING: vendor-quote-acme] per unit at the
    quoted MOQ.

Syntax (see ``anvil/lib/snippets/pending_marker.md`` for the full
convention document): ``[PENDING <source>]`` or ``[PENDING: <source>]``
— the literal, case-sensitive keyword ``PENDING`` immediately after the
opening bracket, then a colon and/or whitespace separator, then a
non-empty ``<source>`` label naming what's pending (a benchmark run id,
a vendor name, "Q3 earnings call", etc.), then the closing bracket. The
uppercase keyword is deliberate — it mirrors the TODO/FIXME convention
so a genuine marker is visually and mechanically unambiguous, and it
means ordinary prose that merely uses the word "pending" (e.g. "results
are pending") is never mistaken for a marker. A near-miss with no
source label (``[PENDING]``, ``[PENDING ]``) is NOT a well-formed
marker and is silently ignored by this detector — it reads as
malformed bracketed text, not as a recognized placeholder, so it gets
neither the "known-incomplete, no penalty" treatment nor the
terminal-state gate. (The convention document recommends against ever writing a
source-less marker for exactly this reason: it degrades to "an
unexplained bracket" for both a human reader and this tool.)

Deterministic detection (pure regex — no LLM, no new deps)
------------------------------------------------------------

1. **Marker extraction**: every well-formed ``[PENDING <source>]`` /
   ``[PENDING: <source>]`` span in the body, with its line number and
   the extracted ``<source>`` label (whitespace-trimmed).
2. **Masking**: fenced code blocks, inline code spans, and (for
   ``.tex`` bodies) LaTeX comments are masked out before extraction —
   the same discipline as ``numeric_consistency.py`` — so a
   documentation passage that quotes the marker syntax in backticks is
   never mistaken for a live, unresolved marker.
3. **Resolution**: a marker is "unresolved" simply by being present in
   the body. There is no separate resolved/unresolved flag to
   maintain — resolving a pending value means replacing the marker text
   with the real value, at which point the next detector pass finds
   nothing.

Verdict wiring: a distinct, specially-resolved flag type (issue #842)
---------------------------------------------------------------------

The nuance that makes this gate correct — and the exact point the
naive "just emit an ordinary ``CriticalFlag``" design got wrong — is
that a pending marker must gate the **terminal state** (READY /
AUDITED) *without* being treated as a blocking defect the way an
ordinary critical flag is. An ordinary critical flag forces
``Verdict.BLOCK`` and, per each skill's reviser prose ("critical flags
trump everything ... MUST be addressed"), directs an LLM reviser to
*resolve* it in the prose — which, for an honest ``[PENDING ...]``
marker, means inventing the still-outstanding number. That is the
precise fabrication failure mode this convention exists to prevent.

So this module emits a **distinct** critical-flag type,
``convergence.PENDING_DEPENDENCY_FLAG_TYPE`` (``"pending_dependency"``),
which is additive (no schema-version bump) and carries its **own
priority tier** in ``anvil/lib/convergence.py`` /
``anvil/lib/critics.py``, modeled on the ``no_go`` precedent but with
the opposite posture:

- It is **visible** in ``AggregatedReview.critical_flags`` (so a critic
  and an operator can see "a declared value is still outstanding").
- It **never** forces ``Verdict.BLOCK``
  (``convergence.blocking_critical_flags`` filters it out of the
  generic-critical trigger).
- It **never** deducts a dimension score (every marker's ``Finding`` is
  emitted at the lowest severity ``"nit"``, and the module owns no
  rubric dimension).
- The **terminal-state gate is enforced separately** by the consuming
  skill (paper first): before promoting a thread to READY / AUDITED,
  the skill queries ``convergence.has_pending_dependency_flag(...)`` (or
  re-runs this module's CLI and checks the exit code) and refuses the
  terminal transition while any marker remains. This is the "gate the
  terminal state separately" half of the #842 contract — decoupled from
  the score/verdict path.

Whether a well-formed marker is still present is a **binary,
deterministic fact with no judgment call**, so the flag is emitted
mechanically (the gate does not depend on a reviewer *noticing* the
bracketed text) — but it is a *disclosure*, not a defect, and the
consuming prose (``anvil/skills/paper/commands/paper-revise.md``) is
explicitly told never to fabricate a value to clear it.

Suppression: `<!-- anvil-lint-disable: pending_marker -->`
-----------------------------------------------------------

Like every other deterministic-checks-family module
(``numeric_consistency``, ``render_gate``, ``marp_lint``), a marker may
be suppressed with a same-line or line-immediately-above
``<!-- anvil-lint-disable: pending_marker -->`` directive. A suppressed
marker is recorded (with an explicit "suppressed" rationale on its
``Finding``, for the audit trail) but is **never** gated: it is
excluded from ``PendingMarkerResult.active_markers`` (so it does not
count toward ``outstanding_sources``, does not emit a
``pending_dependency`` flag, and does not fail ``passed()``). This is
the escape hatch for a documentation passage that must show a
*live-looking* marker outside a code fence.

Optional `BRIEF.md` frontmatter: `pending_sources`
-----------------------------------------------------

A thread MAY declare the pending sources it expects to resolve over
its lifetime in `<thread>/BRIEF.md` YAML frontmatter — a list of bare
source labels, or ``{source, expected_by}`` mappings::

    ---
    pending_sources:
      - benchmark-run-2024-11
      - source: vendor-quote-acme
        expected_by: 2026-08-15
    ---

Parsing/validation lives in ``anvil/lib/project_brief.py``
(:func:`project_brief.resolve_pending_sources`, modeled on the
``spec_ref`` / ``code_ref`` companion-input validators
``_validate_companion_ref`` / ``resolve_spec_ref` in that same file) —
NOT a bespoke parser here. This is purely a **reporting aid**:
declaring a source has NO effect on gating (an undeclared marker still
gates; a declared-but-never-written source is not itself a defect).
:meth:`PendingMarkerResult.resolved_sources` is the set difference
between the declared source labels and the sources still found
unresolved in the body, letting a critic report "3 of 5 declared
pending sources resolved; 2 outstanding: vendor-quote-acme,
benchmark-run-2024-11" — the visibility half of the acceptance criteria.

Sidecar + discovery contract
-----------------------------

``write_review_dir`` writes ``<thread>.{N}.pending/_review.json`` via
``anvil/lib/sidecar.py::staged_sidecar`` (crash-safe atomic rename).
The ``.pending`` tag is a single segment, so
``anvil/lib/critics.py::discover_critics`` picks the sidecar up with
**no aggregator change** — same coordination shape as ``.numeric/``
(#462) and ``.hyperlinks/`` (#335). Because the check is deterministic
and cheaply re-runnable, an existing ``<version_dir>.pending/`` sidecar
from a prior pass is removed and regenerated by a later pass — the same
deterministic-regeneration carve-out ``numeric_consistency.py``
documents for its own sidecar.

CLI entry-point
----------------

``python -m anvil.lib.pending_marker <version_dir> [--write-review]
[--body PATH]``

Writes a JSON summary to stdout. Exit codes: ``0`` no unresolved
markers, ``1`` unresolved markers present (the terminal-gate signal),
``2`` invocation error. The body file is auto-detected: ``<slug>.md``
(the #295 slug-echo memo shape) first, then ``main.tex`` (the paper
shape). ``--body PATH`` overrides discovery for adopted-in-place legacy
threads.
"""

from __future__ import annotations

import json
import re
import sys
from dataclasses import dataclass, field
from pathlib import Path
from typing import List, Optional, Tuple

from anvil.lib.body_resolution import record_body_path, resolve_body_path
from anvil.lib.convergence import PENDING_DEPENDENCY_FLAG_TYPE
from anvil.lib.review_schema import (
    CriticalFlag,
    Finding,
    Kind,
    Review,
    Score,
)
from anvil.lib.sidecar import write_critic_review_dir

# ---------------------------------------------------------------------------
# Constants
# ---------------------------------------------------------------------------

CRITIC_ID = "pending"
"""Stable identifier for this critic in ``_review.json.critic_id``."""

CHECK_NAME = "pending_marker"
"""Check identifier echoed in JSON payloads (and the suppression rule)."""

DIM_PENDING = "pending_marker"
"""Dimension name surfaced on every emitted Finding."""

PENDING_SUFFIX = "pending"
"""Sidecar dir tag: ``<thread>.{N}.pending/``. Single segment so
``critics.discover_critics`` picks it up with no aggregator change."""

CRITICAL_PENDING_MARKER = PENDING_DEPENDENCY_FLAG_TYPE
"""Critical-flag ``type`` value emitted for an unresolved pending marker.

This is the specially-resolved, additive ``"pending_dependency"`` type
from ``anvil/lib/convergence.py`` — visible in the aggregate for the
terminal-state gate but never forcing ``Verdict.BLOCK`` (see the module
docstring). Aliased here so ``pending_marker``'s own callers/tests have a
local name."""

# Emitted schema ``Finding.severity`` values. Both are the lowest,
# non-defect severity (the schema ``Finding`` vocabulary is
# blocker/major/minor/nit — there is no "info" tier, so a suppressed hit
# maps to "nit" with a distinct rationale, mirroring
# ``numeric_consistency.py``'s suppressed→"nit" mapping). An ACTIVE marker
# is a "known-incomplete outstanding dependency"; a SUPPRESSED marker is a
# recorded-but-explicitly-silenced note. Neither ever deducts a score.
SEVERITY_ACTIVE = "nit"
SEVERITY_SUPPRESSED = "nit"

BRIEF_FILENAME = "BRIEF.md"
"""Thread-root brief filename read for the optional ``pending_sources``
frontmatter key (parsed by ``anvil/lib/project_brief.py``)."""

# Suppression directive (shared shape with numeric_consistency / render_gate).
# A directive on line L suppresses a marker on line L or line L+1.
_LINT_DISABLE_RE = re.compile(
    r"<!--\s*anvil-lint-disable:\s*(?P<rules>[a-zA-Z0-9_,\-\s]+?)\s*-->",
)


# ---------------------------------------------------------------------------
# Masking (code fences, inline code, LaTeX comments)
# ---------------------------------------------------------------------------

_MASK_PATTERNS: Tuple[re.Pattern, ...] = (
    # Fenced code blocks (``` ... ``` or ~~~ ... ~~~), multi-line.
    re.compile(r"(```|~~~).*?\1", re.DOTALL),
    # Inline code spans.
    re.compile(r"`[^`\n]*`"),
)

# LaTeX-only: unescaped % starts a comment.
_LATEX_COMMENT_RE = re.compile(r"(?<!\\)%[^\n]*")


def _mask_text(text: str, *, latex: bool = False) -> str:
    """Blank out non-prose regions while preserving offsets/line numbers."""

    def blank(m: "re.Match[str]") -> str:
        return "".join(c if c == "\n" else " " for c in m.group(0))

    masked = text
    for pattern in _MASK_PATTERNS:
        masked = pattern.sub(blank, masked)
    if latex:
        masked = _LATEX_COMMENT_RE.sub(blank, masked)
    return masked


# ---------------------------------------------------------------------------
# Marker extraction
# ---------------------------------------------------------------------------

# Well-formed marker: literal, case-sensitive "PENDING" immediately after
# the opening bracket, then either "<colon><optional ws>" or "<required
# ws>" as separator, then a non-empty source label, then the closing
# bracket. A bare "[PENDING]" or "[PENDING ]" (no source content) does
# NOT match — deliberately treated as malformed, not as a marker.
_PENDING_MARKER_RE = re.compile(
    r"\[PENDING(?:\s*:\s*|\s+)(?P<source>[^\]\n]+?)\s*\]"
)


def _line_of(offset: int, text: str) -> int:
    """1-based line number of ``offset`` in ``text``."""
    return text.count("\n", 0, offset) + 1


def _suppressed_lines(text: str) -> frozenset:
    """1-based line numbers covered by a ``pending_marker`` lint-disable.

    A directive on line L suppresses a marker on line L and line L+1
    (same-line or line-immediately-above placement, the shared
    deterministic-checks-family lint-disable convention).
    """
    suppressed = set()
    for lineno, line in enumerate(text.splitlines(), start=1):
        for m in _LINT_DISABLE_RE.finditer(line):
            rules = {r.strip() for r in m.group("rules").split(",")}
            if CHECK_NAME in rules:
                suppressed.add(lineno)
                suppressed.add(lineno + 1)
    return frozenset(suppressed)


@dataclass(frozen=True)
class PendingMarker:
    """One well-formed ``[PENDING <source>]`` marker found in the body.

    ``suppressed`` is ``True`` when a ``<!-- anvil-lint-disable:
    pending_marker -->`` directive covers the marker's line — a suppressed
    marker is recorded (for the audit trail as an ``info`` finding) but
    never gates.
    """

    source: str
    raw: str
    line: int
    start: int
    end: int
    suppressed: bool = False

    def to_dict(self) -> dict:
        return {
            "source": self.source,
            "raw": self.raw,
            "line": self.line,
            "suppressed": self.suppressed,
        }


def find_pending_markers(text: str, *, latex: bool = False) -> List[PendingMarker]:
    """Extract every well-formed pending marker from ``text``.

    Pure function of the text (no filesystem). Set ``latex=True`` for
    ``.tex`` bodies (enables the LaTeX ``%``-comment mask). Markers covered
    by a ``<!-- anvil-lint-disable: pending_marker -->`` directive are
    returned with ``suppressed=True`` (callers exclude them from gating).
    """
    masked = _mask_text(text, latex=latex)
    suppressed_lines = _suppressed_lines(text)
    markers: List[PendingMarker] = []
    for m in _PENDING_MARKER_RE.finditer(masked):
        source = m.group("source").strip()
        if not source:
            continue
        line = _line_of(m.start(), masked)
        markers.append(
            PendingMarker(
                source=source,
                raw=m.group(0).strip(),
                line=line,
                start=m.start(),
                end=m.end(),
                suppressed=line in suppressed_lines,
            )
        )
    return markers


def emit_pending_marker(source: str, *, colon: bool = False) -> str:
    """Render a well-formed marker string for a given source label.

    A small emitter helper (the issue's "lib-level helper for emitting
    and detecting it" acceptance criterion) so drafters/tooling can
    generate a marker programmatically instead of hand-typing the
    syntax. ``colon=True`` renders ``[PENDING: <source>]``; the default
    renders ``[PENDING <source>]``. Both are well-formed and detected
    identically by :func:`find_pending_markers`.
    """
    source = source.strip()
    if not source:
        raise ValueError("emit_pending_marker: source must be non-empty")
    sep = ": " if colon else " "
    return f"[PENDING{sep}{source}]"


# ---------------------------------------------------------------------------
# Optional BRIEF.md frontmatter: pending_sources
# ---------------------------------------------------------------------------
#
# Parsing/validation of the ``pending_sources:`` frontmatter block lives in
# ``anvil/lib/project_brief.py`` (``resolve_pending_sources``), modeled on
# the ``spec_ref`` / ``code_ref`` companion-input validators in that same
# file (issue #842). This module only consumes the resolved source LABELS
# (the reporting aid) — it deliberately does NOT re-implement frontmatter
# parsing.


def load_expected_pending_sources(thread_dir: Path) -> List[str]:
    """Read the optional ``pending_sources`` source labels for ``thread_dir``.

    Thin delegator to ``anvil/lib/project_brief.py::resolve_pending_sources``
    (which owns the frontmatter parsing + validation, modeled on the
    ``spec_ref`` companion-input resolver). Returns the list of declared
    source *labels* (each ``PendingSource.source``) — the reporting aid used
    to compute :meth:`PendingMarkerResult.resolved_sources`.

    Returns ``[]`` when the BRIEF is absent, has no frontmatter, or has no
    (or a malformed) ``pending_sources`` key — tolerant by design, since
    this is a reporting aid, not a gating input.
    """
    # Lazy import: keeps ``pending_marker`` importable in a minimal env and
    # avoids any import-ordering coupling with the large ``project_brief``
    # module (which itself imports only ``review_schema``).
    from anvil.lib.project_brief import resolve_pending_sources

    return [ps.source for ps in resolve_pending_sources(Path(thread_dir))]


# ---------------------------------------------------------------------------
# Result types
# ---------------------------------------------------------------------------


@dataclass
class PendingMarkerResult:
    """Outcome of one ``check_pending_markers`` pass.

    ``markers`` holds every well-formed marker found (active AND
    suppressed). Gating logic (``passed()``, ``outstanding_sources``,
    ``to_critical_flags``) considers only the ACTIVE (non-suppressed)
    markers — a ``<!-- anvil-lint-disable: pending_marker -->``-suppressed
    marker is recorded for the audit trail (an ``info`` finding) but never
    gates.
    """

    version_dir: str
    body_path: str
    markers: List[PendingMarker] = field(default_factory=list)
    expected_sources: List[str] = field(default_factory=list)

    @property
    def active_markers(self) -> List[PendingMarker]:
        """Non-suppressed markers — the ones that gate."""
        return [m for m in self.markers if not m.suppressed]

    @property
    def suppressed_markers(self) -> List[PendingMarker]:
        """Suppressed markers — recorded (info), never gating."""
        return [m for m in self.markers if m.suppressed]

    @property
    def outstanding_sources(self) -> List[str]:
        """Unique ACTIVE source labels still present, in first-seen order."""
        seen: List[str] = []
        for m in self.active_markers:
            if m.source not in seen:
                seen.append(m.source)
        return seen

    @property
    def resolved_sources(self) -> List[str]:
        """Declared ``expected_sources`` no longer present as an active marker.

        Purely observational (reporting aid) — has no bearing on
        ``passed()``.
        """
        outstanding = set(self.outstanding_sources)
        return [s for s in self.expected_sources if s not in outstanding]

    def passed(self) -> bool:
        """``True`` when no ACTIVE (unsuppressed) markers remain."""
        return not self.active_markers

    def to_json(self) -> dict:
        return {
            "check": CHECK_NAME,
            "version_dir": self.version_dir,
            "body_path": self.body_path,
            "markers": [m.to_dict() for m in self.markers],
            "outstanding_sources": self.outstanding_sources,
            "suppressed_count": len(self.suppressed_markers),
            "expected_sources": self.expected_sources,
            "resolved_sources": self.resolved_sources,
            "pass": self.passed(),
        }

    def to_critical_flags(self) -> List[CriticalFlag]:
        """One ``pending_dependency`` ``CriticalFlag`` summarizing every
        active unresolved marker.

        The flag type is the specially-resolved, additive
        ``convergence.PENDING_DEPENDENCY_FLAG_TYPE`` (``"pending_dependency"``)
        — visible in the aggregate for the terminal-state gate but NEVER
        forcing ``Verdict.BLOCK`` (see the module docstring). Empty when no
        active markers remain (a clean or fully-suppressed body).
        """
        active = self.active_markers
        if not active:
            return []
        sources = ", ".join(self.outstanding_sources)
        sample = "; ".join(m.raw for m in active[:3])
        more = f" (+{len(active) - 3} more)" if len(active) > 3 else ""
        return [
            CriticalFlag(
                type=CRITICAL_PENDING_MARKER,
                justification=(
                    f"{len(active)} unresolved pending marker(s) "
                    f"remain in the body (outstanding source(s): {sources}): "
                    f"{sample}{more}. This is an honestly-declared "
                    f"known-incomplete value, NOT a defect — it does not "
                    f"lower any dimension score and does not force "
                    f"Verdict.BLOCK. It is surfaced here as an outstanding "
                    f"dependency; the artifact cannot reach the terminal "
                    f"state (READY/AUDITED) until every marker is replaced "
                    f"with its real value. Never fabricate a value to clear "
                    f"this flag."
                ),
                evidence_span=f"{self.body_path}:L{active[0].line}",
            )
        ]

    def to_review(
        self,
        *,
        version_dir: str,
        critic_id: str = CRITIC_ID,
    ) -> Review:
        """Build a typed ``Review`` (``kind=Kind.TOOL_EVIDENCE``).

        Each ACTIVE marker emits an advisory ``Finding`` at severity
        ``"nit"`` (known-incomplete outstanding dependency, not a defect);
        each SUPPRESSED marker emits an ``"info"`` finding (recorded, never
        gating). When any active marker remains, one ``pending_dependency``
        ``CriticalFlag`` (via :meth:`to_critical_flags`) is emitted for
        visibility — it is specially resolved so it never forces
        ``Verdict.BLOCK`` and never deducts a dimension score. The
        terminal-state gate is enforced separately by the consuming skill.
        """
        scores = [
            Score(
                dimension=CHECK_NAME,
                score=None,
                max=1,
                justification=(
                    "pending-marker detection is a deterministic "
                    "placeholder-presence check; owns no rubric dim."
                ),
            )
        ]
        findings: List[Finding] = []
        for m in self.markers:
            if m.suppressed:
                findings.append(
                    Finding(
                        severity=SEVERITY_SUPPRESSED,
                        dimension=DIM_PENDING,
                        evidence_span=f"{self.body_path}:L{m.line}",
                        rationale=(
                            f"Suppressed pending marker {m.raw!r} (source: "
                            f"{m.source!r}) — covered by an "
                            f"<!-- anvil-lint-disable: {CHECK_NAME} --> "
                            f"directive; recorded for the audit trail but "
                            f"NOT gated."
                        ),
                        suggested_fix=(
                            "No action required — this marker is explicitly "
                            "suppressed. Remove the lint-disable directive "
                            "to re-activate gating."
                        ),
                        tool_calls=[],
                    )
                )
                continue
            findings.append(
                Finding(
                    severity=SEVERITY_ACTIVE,
                    dimension=DIM_PENDING,
                    evidence_span=f"{self.body_path}:L{m.line}",
                    rationale=(
                        f"Outstanding pending marker {m.raw!r} — declared "
                        f"as known-incomplete (source: {m.source!r}), not "
                        f"a defect. No dimension score penalty; gates the "
                        f"terminal state (READY/AUDITED) until resolved."
                    ),
                    suggested_fix=(
                        f"Resolve the pending source {m.source!r} and "
                        f"replace the marker with the real value, or "
                        f"confirm the value is still genuinely pending "
                        f"and leave the marker in place for a later pass. "
                        f"Never fabricate a value to clear the marker."
                    ),
                    tool_calls=[],
                )
            )
        return Review(
            schema_version="1",
            kind=Kind.TOOL_EVIDENCE,
            version_dir=version_dir,
            critic_id=critic_id,
            scores=scores,
            findings=findings,
            critical_flags=self.to_critical_flags(),
        )


# ---------------------------------------------------------------------------
# Filesystem entry point
# ---------------------------------------------------------------------------


def check_text(text: str, *, latex: bool = False) -> List[PendingMarker]:
    """Run the pending-marker check over body text (pure function)."""
    return find_pending_markers(text, latex=latex)


def check_pending_markers(
    version_dir: Path,
    *,
    body: Optional[Path] = None,
    expected_sources: Optional[List[str]] = None,
) -> PendingMarkerResult:
    """Run the check against a version directory's body file.

    ``expected_sources`` overrides the declared list (normally sourced
    from :func:`load_expected_pending_sources` against the thread root,
    i.e. ``version_dir.parent``); when omitted, the thread root's
    ``BRIEF.md`` is consulted automatically.
    """
    version_dir = Path(version_dir).resolve()
    if not version_dir.is_dir():
        raise FileNotFoundError(
            f"pending_marker: version_dir {version_dir!s} does not exist "
            f"or is not a directory."
        )
    body_file = resolve_body_path(
        version_dir, body=body, caller_name="pending_marker"
    )
    text = body_file.read_text(encoding="utf-8")
    markers = find_pending_markers(text, latex=body_file.suffix == ".tex")
    if expected_sources is None:
        expected_sources = load_expected_pending_sources(version_dir.parent)
    return PendingMarkerResult(
        version_dir=version_dir.name,
        body_path=record_body_path(version_dir, body_file),
        markers=markers,
        expected_sources=expected_sources,
    )


def write_review_dir(
    version_dir: Path,
    result: PendingMarkerResult,
    *,
    critic_id: str = CRITIC_ID,
) -> Path:
    """Write ``<version_dir>.pending/_review.json`` for auto-discovery.

    Delegates to the shared :func:`anvil.lib.sidecar.write_critic_review_dir`
    (issue #1086), which uses ``staged_sidecar`` (issue #350) so the
    sidecar only ever exists in complete form. Because this detector is
    deterministic and cheaply re-runnable, an existing
    ``<version_dir>.pending/`` from a prior run is removed and
    regenerated (``regenerate=True``, the shared helper's default) — a
    later pass supersedes an earlier one. Returns the path to the written
    ``_review.json``.

    The written review always carries the ``pending_dependency``
    ``CriticalFlag`` when active markers remain: it is specially resolved
    (never forces ``Verdict.BLOCK``, never deducts a dimension score), so
    it is safe to emit unconditionally at both review time (surfaces as an
    outstanding dependency) and the terminal-state gate.
    """
    version_dir = Path(version_dir)
    review = result.to_review(version_dir=version_dir.name, critic_id=critic_id)
    return write_critic_review_dir(version_dir, PENDING_SUFFIX, review)


# ---------------------------------------------------------------------------
# CLI entry-point
# ---------------------------------------------------------------------------


def _build_cli_parser():
    import argparse

    p = argparse.ArgumentParser(
        prog="python -m anvil.lib.pending_marker",
        description=(
            "Deterministic pending-measurement placeholder gate: detects "
            "well-formed [PENDING <source>] markers in a version "
            "directory's body file. Emits an advisory Finding per marker "
            "and, when any active marker remains, a specially-resolved "
            "'pending_dependency' CriticalFlag (visible for the terminal- "
            "state gate but never forcing Verdict.BLOCK). Exit code 1 "
            "signals unresolved markers — the terminal-gate signal."
        ),
    )
    p.add_argument(
        "version_dir",
        help="Path to <thread>.{N}/ containing <thread>.md or main.tex.",
    )
    p.add_argument(
        "--write-review",
        action="store_true",
        help=(
            "Also write <version_dir>.pending/_review.json (via "
            "staged_sidecar) for critic-sibling auto-discovery by "
            "aggregate()."
        ),
    )
    p.add_argument(
        "--body",
        metavar="PATH",
        default=None,
        help=(
            "Override body-file discovery (e.g. for adopted-in-place "
            "legacy threads whose entry point isn't <slug>.md/main.tex)."
        ),
    )
    return p


def main(argv: Optional[List[str]] = None) -> int:
    """CLI entry point. Returns the process exit code.

    Exit codes: ``0`` no unresolved markers, ``1`` unresolved markers
    present, ``2`` invocation error.
    """
    parser = _build_cli_parser()
    args = parser.parse_args(argv)
    try:
        result = check_pending_markers(
            Path(args.version_dir),
            body=Path(args.body) if args.body else None,
        )
    except FileNotFoundError as exc:
        print(f"error: {exc}", file=sys.stderr)
        return 2
    print(json.dumps(result.to_json(), indent=2))
    if args.write_review:
        out = write_review_dir(Path(args.version_dir), result)
        print(f"wrote {out}", file=sys.stderr)
    return 0 if result.passed() else 1


__all__ = [
    "CRITIC_ID",
    "CHECK_NAME",
    "DIM_PENDING",
    "PENDING_SUFFIX",
    "CRITICAL_PENDING_MARKER",
    "BRIEF_FILENAME",
    "PendingMarker",
    "PendingMarkerResult",
    "find_pending_markers",
    "emit_pending_marker",
    "load_expected_pending_sources",
    "check_text",
    "check_pending_markers",
    "write_review_dir",
    "main",
]


if __name__ == "__main__":
    raise SystemExit(main())
