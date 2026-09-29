"""Critic discovery, loading, aggregation, and verdict computation.

This module is the "N parallel critics, one reviser" first-class primitive
for Anvil. It handles:

- **Discovery**: walking the filesystem for sibling critic dirs at the same
  versioned thread (``<thread>.{N}.<tag>/``).
- **Loading**: parsing a critic's ``_review.json`` against the canonical
  schema in ``anvil/lib/review_schema.py``.
- **Aggregation**: merging N ``Review`` objects into one
  ``AggregatedReview`` (mean-of-non-null per dimension, OR of critical
  flags, union of fixes).
- **Verdict**: deciding ADVANCE / REVISE / BLOCK from the aggregated total
  + critical flags.
- **Legacy adapter**: reading the memo prose triple
  (``verdict.md`` + ``scoring.md`` + ``comments.md``) and the ip-uspto
  hybrid (``_summary.md`` + ``findings.md`` + ``_meta.json``) and emitting
  a ``Review`` so existing skill output remains discoverable while the
  per-skill migration to ``_review.json`` is rolled out separately.

Discovery precedence: when a critic sibling directory contains both
``_review.json`` and one of the legacy file triples, the canonical JSON
wins and the legacy files are treated as stale. A ``DeprecationWarning``
is emitted whenever the adapter is invoked, on a per-sibling-dir basis.

Aggregation rules
-----------------

For each rubric dimension:

- ``score``: mean of non-null per-critic scores, rounded to nearest int
  with round-half-to-even (Python ``round`` default). When no critic
  scored a dimension, the aggregated score is ``None`` and the dimension
  contributes 0 to the total.
- ``critical``: logical OR across critics.
- ``fix``: deduplicated union of non-null per-critic ``fix`` strings,
  joined by ``"; "`` for human readability.
- ``evidence_span``: first non-null span (in critic order).
- ``justification``: first non-null justification (in critic order).
- ``max``: required to be consistent across critics for a given dimension;
  a mismatch raises ``ValueError``.

Findings and critical flags are deduplicated by exact-string equality on
``(severity, dimension, rationale, suggested_fix)`` and
``(type, justification)`` respectively. This is intentionally
strict — two critics emitting *almost* the same finding will both surface,
so the reviser sees both phrasings.

The aggregator is a **pure function** of ``list[Review]``. It does no
filesystem access. This makes the test surface small and the orchestrator
simple.
"""

from __future__ import annotations

import json
import re
import warnings
from pathlib import Path
from typing import Iterable, List, Optional, Tuple

from anvil.lib.review_schema import (
    AggregatedReview,
    CriticalFlag,
    Finding,
    Kind,
    Review,
    Score,
    Verdict,
)


CANONICAL_REVIEW_FILENAME = "_review.json"

# Legacy file triples that the adapter recognizes.
LEGACY_MEMO_FILES = ("verdict.md", "scoring.md", "comments.md")
LEGACY_IP_USPTO_FILES = ("_summary.md", "findings.md", "_meta.json")


class CriticDiscoveryError(Exception):
    """A discovered critic dir does not contain any recognizable review."""


# ---------------------------------------------------------------------------
# Discovery
# ---------------------------------------------------------------------------


def discover_critics(version_dir: Path) -> List[Path]:
    """Return the list of critic sibling directories for a version dir.

    A critic sibling has the form ``<version_dir>.<tag>/`` for some tag
    (``review``, ``audit``, ``critic``, ``narrative``, ``market``, etc.)
    and contains either:

    - A canonical ``_review.json`` (preferred), OR
    - One of the legacy file triples that the adapter can read.

    Discovery is filesystem-only — this function does NOT parse the
    payload. Use ``load_review`` to parse a discovered dir.

    Parameters
    ----------
    version_dir:
        The version directory whose siblings to enumerate, e.g.
        ``Path("acme-seed.3")``. The siblings searched are in
        ``version_dir.parent`` matching the pattern
        ``<version_dir.name>.<tag>``.

    Returns
    -------
    List of paths to sibling critic directories, sorted by name.
    """
    version_dir = Path(version_dir)
    parent = version_dir.parent if version_dir.parent != Path("") else Path(".")
    base_name = version_dir.name
    prefix = f"{base_name}."

    candidates: List[Path] = []
    if not parent.exists():
        return candidates
    for child in sorted(parent.iterdir()):
        if not child.is_dir():
            continue
        if not child.name.startswith(prefix):
            continue
        # The version dir itself doesn't match because it has no trailing tag.
        tag = child.name[len(prefix):]
        if not tag or "." in tag:
            # Skip sub-versions like memo.3.1; tag must be a single segment.
            continue
        if _has_recognizable_review(child):
            candidates.append(child)
    return candidates


def _has_recognizable_review(critic_dir: Path) -> bool:
    if (critic_dir / CANONICAL_REVIEW_FILENAME).exists():
        return True
    if all((critic_dir / f).exists() for f in LEGACY_MEMO_FILES):
        return True
    if all((critic_dir / f).exists() for f in LEGACY_IP_USPTO_FILES):
        return True
    return False


# ---------------------------------------------------------------------------
# Loading (canonical + legacy adapter)
# ---------------------------------------------------------------------------


def load_review(critic_dir: Path) -> Review:
    """Parse and validate a critic dir into a ``Review``.

    Precedence:

    1. If ``_review.json`` exists, use it. (Even if legacy files also
       exist — they are treated as stale and a warning is emitted.)
    2. Else if the memo prose triple exists, run the memo legacy adapter
       and emit ``DeprecationWarning``.
    3. Else if the ip-uspto triple exists, run the ip-uspto legacy adapter
       and emit ``DeprecationWarning``.
    4. Else raise ``CriticDiscoveryError``.

    Raises ``pydantic.ValidationError`` on schema violation; raises
    ``CriticDiscoveryError`` when no recognizable payload is found.
    """
    critic_dir = Path(critic_dir)
    canonical = critic_dir / CANONICAL_REVIEW_FILENAME

    has_canonical = canonical.exists()
    has_memo_legacy = all(
        (critic_dir / f).exists() for f in LEGACY_MEMO_FILES
    )
    has_ip_uspto_legacy = all(
        (critic_dir / f).exists() for f in LEGACY_IP_USPTO_FILES
    )

    if has_canonical:
        if has_memo_legacy or has_ip_uspto_legacy:
            warnings.warn(
                f"{critic_dir}: both _review.json and legacy prose files "
                f"are present; using _review.json as canonical and "
                f"treating legacy files as stale.",
                DeprecationWarning,
                stacklevel=2,
            )
        with canonical.open() as fh:
            data = json.load(fh)
        return Review.model_validate(data)

    if has_memo_legacy:
        warnings.warn(
            f"{critic_dir}: reading legacy memo prose triple "
            f"({', '.join(LEGACY_MEMO_FILES)}). Migrate this critic to "
            f"write {CANONICAL_REVIEW_FILENAME}.",
            DeprecationWarning,
            stacklevel=2,
        )
        return _adapt_memo_legacy(critic_dir)

    if has_ip_uspto_legacy:
        warnings.warn(
            f"{critic_dir}: reading legacy ip-uspto triple "
            f"({', '.join(LEGACY_IP_USPTO_FILES)}). Migrate this critic "
            f"to write {CANONICAL_REVIEW_FILENAME}.",
            DeprecationWarning,
            stacklevel=2,
        )
        return _adapt_ip_uspto_legacy(critic_dir)

    raise CriticDiscoveryError(
        f"{critic_dir}: no recognizable review payload (neither "
        f"{CANONICAL_REVIEW_FILENAME} nor a known legacy triple)."
    )


# --- Memo legacy adapter ----------------------------------------------------

# Match the markdown scoring table row format used by memo and paper:
# | # | Dimension | Weight | Score | Justification |
#
# The weight/score cells tolerate surrounding markdown emphasis
# (``**5**``, ``*5*``, ``__5__``) — a reviewer bolding the score column
# for emphasis is natural markdown and must not silently drop the row
# (issue #912). ``_strip_emphasis`` removes the markers once matched;
# widening the digit alternation itself (rather than pre-stripping the
# whole cell) keeps the header/separator-row rejection behavior intact.
_MEMO_SCORE_ROW = re.compile(
    r"^\s*\|\s*(?P<num>\d+)\s*\|"
    r"\s*(?P<dim>[^|]+?)\s*\|"
    r"\s*(?P<weight>[*_]{0,2}\d+[*_]{0,2})\s*\|"
    r"\s*(?P<score>[*_]{0,2}(?:\d+|null|N/A|n/a|-)[*_]{0,2})\s*\|"
    r"\s*(?P<just>.*?)\s*\|\s*$"
)

# Verdict.md fields we extract from prose. The label side already
# tolerated emphasis (``\*?\*?Total\*?\*?``); the value side now does
# too (``**Total**: **44**/44``, `` `advance: **true**` ``) — issue #912.
_MEMO_TOTAL = re.compile(
    r"\*?\*?Total\*?\*?:\s*`?[*_]{0,2}(\d+)[*_]{0,2}`?"
    r"\s*/\s*[*_]{0,2}(\d+)[*_]{0,2}",
    re.IGNORECASE,
)
_MEMO_DECISION = re.compile(
    r"\*?\*?Decision\*?\*?:\s*`?advance:\s*[*_]{0,2}(true|false)[*_]{0,2}`?",
    re.IGNORECASE,
)
# NO-GO verdict line (issue #559) — surfaced when a memo-review writes the
# NO-GO shape into verdict.md (see memo SKILL.md §"NO-GO terminal state").
# Recognizes either ``**Verdict**: NO-GO`` or ``Verdict: NO-GO`` (with or
# without bold markers), matched case-insensitively. The dash variant
# matches both ``NO-GO`` (canonical) and ``NO_GO`` (defensive).
_MEMO_NO_GO_VERDICT = re.compile(
    r"\*?\*?Verdict\*?\*?:\s*`?NO[-_]GO`?", re.IGNORECASE
)


def _adapt_memo_legacy(critic_dir: Path) -> Review:
    """Bridge: read verdict.md + scoring.md + comments.md into a Review."""
    verdict_md = (critic_dir / "verdict.md").read_text()
    scoring_md = (critic_dir / "scoring.md").read_text()
    comments_md = (critic_dir / "comments.md").read_text()

    total, threshold = parse_memo_verdict_total(verdict_md)
    advance = parse_memo_verdict_decision(verdict_md)
    critical_flags = _parse_memo_critical_flags(verdict_md)
    no_go = bool(_MEMO_NO_GO_VERDICT.search(verdict_md))

    scores = parse_memo_scoring_table(scoring_md)
    findings = _parse_memo_comments(comments_md)

    # Derive verdict using the canonical decision rule, but defer to the
    # parsed "advance" hint when the rule would require info we don't have.
    # NO-GO (issue #559) takes precedence over every other path: the prose
    # ``**Verdict**: NO-GO`` line is the load-bearing signal that the
    # evaluator concluded the thesis itself fails.
    if no_go:
        verdict = Verdict.NO_GO
    elif critical_flags:
        verdict = Verdict.BLOCK
    elif total is not None and threshold is not None:
        verdict = Verdict.ADVANCE if total >= threshold else Verdict.REVISE
    elif advance is True:
        verdict = Verdict.ADVANCE
    elif advance is False:
        verdict = Verdict.REVISE
    else:
        verdict = None  # type: ignore[assignment]

    return Review(
        schema_version="1",
        kind=Kind.JUDGMENT,
        version_dir=_infer_version_dir(critic_dir),
        critic_id=_infer_critic_id(critic_dir),
        scores=scores,
        findings=findings,
        critical_flags=critical_flags,
        total=total,
        threshold=threshold,
        verdict=verdict,
    )


def parse_memo_verdict_total(text: str) -> Tuple[Optional[int], Optional[int]]:
    """Parse ``Total: X/Y`` from memo verdict.md prose.

    Returns ``(total, denominator)`` where the denominator is the declared
    point pool (e.g. the ``44`` in ``41/44``), or ``(None, None)`` when no
    total line is found. Public per issue #392 — consumed by
    ``anvil/lib/scorecard_check.py`` in addition to the legacy adapter.
    """
    m = _MEMO_TOTAL.search(text)
    if not m:
        return None, None
    return int(m.group(1)), int(m.group(2))


def parse_memo_verdict_decision(text: str) -> Optional[bool]:
    """Parse ``Decision: advance: true|false`` from memo verdict.md prose.

    Returns ``None`` when no decision line is found. Public per issue
    #392 — consumed by ``anvil/lib/scorecard_check.py`` in addition to
    the legacy adapter.
    """
    m = _MEMO_DECISION.search(text)
    if not m:
        return None
    return m.group(1).lower() == "true"


def parse_memo_verdict_no_go(text: str) -> bool:
    """Return True when ``verdict.md`` prose carries a ``**Verdict**: NO-GO`` line.

    Public per issue #559 — consumed by the ``memo-revise`` pre-check at
    `anvil/skills/memo/commands/memo-revise.md` step 4 to refuse to run
    against a NO-GO terminal thread, and by the orchestrator's state
    derivation to surface the NO-GO state. The terminal-sink semantics
    are documented at `anvil/skills/memo/SKILL.md` §"NO-GO terminal state".
    """
    return bool(_MEMO_NO_GO_VERDICT.search(text))


def parse_memo_verdict_kill_rationale(text: str) -> Optional[str]:
    """Extract the kill-rationale paragraph from a NO-GO ``verdict.md``.

    The NO-GO ``verdict.md`` shape (see memo SKILL.md §"NO-GO terminal
    state") carries a ``## Kill rationale`` heading followed by a
    one-paragraph rationale. This function returns the rationale text
    when both the ``Verdict: NO-GO`` line AND the heading are present;
    ``None`` otherwise. Used by ``memo-revise`` to surface the rationale
    in the refusal message.
    """
    if not parse_memo_verdict_no_go(text):
        return None
    # Find the heading and capture text up to the next heading (or EOF).
    heading_re = re.compile(
        r"^#+\s*Kill\s+rationale\s*$", re.IGNORECASE | re.MULTILINE
    )
    m = heading_re.search(text)
    if not m:
        return None
    rest = text[m.end():]
    # Stop at the next heading.
    next_heading = re.search(r"^#+\s+\S", rest, re.MULTILINE)
    body = rest[: next_heading.start()] if next_heading else rest
    body = body.strip()
    return body or None


def _parse_memo_critical_flags(text: str) -> List[CriticalFlag]:
    """Extract critical flags from verdict.md.

    The memo verdict.md format lists each flag as a markdown bullet under a
    ``## Critical flags`` heading (or similar). We extract any non-empty
    bullet under such a section as a CriticalFlag with type=tag,
    justification=full bullet text.
    """
    flags: List[CriticalFlag] = []
    # Find a critical-flags section heading.
    lines = text.splitlines()
    in_section = False
    for line in lines:
        stripped = line.strip()
        if not stripped:
            continue
        if stripped.startswith("#"):
            in_section = bool(re.search(r"critical\s+flags?", stripped, re.I))
            continue
        if not in_section:
            continue
        # Bullet under critical-flags section.
        if stripped.startswith(("- ", "* ")):
            body = stripped[2:].strip()
            # Try to extract a leading "**type**:" or "type:" prefix.
            tag_match = re.match(
                r"\*?\*?(?P<tag>[\w\- ]+?)\*?\*?\s*[:\-]\s*(?P<body>.+)$",
                body,
            )
            if tag_match:
                tag = tag_match.group("tag").strip().lower().replace(" ", "_")
                justification = tag_match.group("body").strip()
            else:
                tag = "unspecified"
                justification = body
            flags.append(
                CriticalFlag(type=tag, justification=justification)
            )
    return flags


def _strip_emphasis(cell: str) -> str:
    """Strip surrounding markdown emphasis markers from a table cell.

    Handles ``**5**``, ``*5*``, and ``__5__`` (issue #912) — a reviewer
    bolding the Weight/Score column for visual emphasis is natural
    markdown and must not prevent the numeric value underneath from
    being parsed. ``str.strip`` removes any run of ``*``/``_`` from
    either end, which is safe here because the capturing regex already
    constrains the cell to at most a handful of leading/trailing
    emphasis characters around a digit run or keyword.
    """
    return cell.strip().strip("*_")


def parse_memo_scoring_table(text: str) -> List[Score]:
    """Parse the memo ``scoring.md`` markdown table into ``Score`` rows.

    Recognizes the ``| # | Dimension | Weight | Score | Justification |``
    row shape, tolerating markdown emphasis around the Weight/Score cells
    (``**5**``, ``*5*``, ``__5__`` — issue #912) so a reviewer's natural
    emphasis on the score column does not silently drop the row. Raises
    ``pydantic.ValidationError`` when a parsed row violates the ``Score``
    bounds contract (score > weight, negative score). Public per issue
    #392 — consumed by ``anvil/lib/scorecard_check.py`` in addition to
    the legacy adapter.
    """
    scores: List[Score] = []
    for line in text.splitlines():
        m = _MEMO_SCORE_ROW.match(line)
        if not m:
            continue
        dim = m.group("dim").strip()
        # Skip the table header (where the "score" cell would be the word
        # "Score") and the separator row (which the regex won't match
        # because the cells are `---`, not digits/null).
        if dim.lower() == "dimension":
            continue
        weight = int(_strip_emphasis(m.group("weight")))
        raw_score = _strip_emphasis(m.group("score")).lower()
        if raw_score in {"null", "n/a", "-"}:
            score_val: Optional[int] = None
        else:
            score_val = int(raw_score)
        justification = m.group("just").strip() or None
        scores.append(
            Score(
                dimension=dim,
                score=score_val,
                max=weight,
                critical=False,
                justification=justification,
            )
        )
    return scores


def _parse_memo_comments(text: str) -> List[Finding]:
    """Extract findings from comments.md.

    Memo comments.md groups comments by severity within sub-sections. We
    extract any bullet that starts with a ``**<severity>**:`` prefix and
    use the rest as the rationale; suggested_fix defaults to the rationale
    when no separate fix is given.
    """
    findings: List[Finding] = []
    severity_re = re.compile(
        r"^\s*[-*]\s*\*\*(?P<sev>blocker|major|minor|nit)\*\*\s*:\s*(?P<body>.+)$",
        re.IGNORECASE,
    )
    current_dim: Optional[str] = None
    for line in text.splitlines():
        heading = re.match(r"^##+\s+(.+)$", line)
        if heading:
            current_dim = heading.group(1).strip() or None
            continue
        m = severity_re.match(line)
        if not m:
            continue
        sev = m.group("sev").lower()
        body = m.group("body").strip()
        findings.append(
            Finding(
                severity=sev,  # type: ignore[arg-type]
                dimension=current_dim,
                rationale=body,
                suggested_fix=body,
            )
        )
    return findings


# Backwards-compat aliases for the pre-#392 private names. New consumers
# should import the public names above.
_parse_memo_verdict_total = parse_memo_verdict_total
_parse_memo_verdict_decision = parse_memo_verdict_decision
_parse_memo_scoring_table = parse_memo_scoring_table


# --- ip-uspto legacy adapter ------------------------------------------------


def _adapt_ip_uspto_legacy(critic_dir: Path) -> Review:
    """Bridge: read _summary.md + findings.md + _meta.json into a Review."""
    summary_md = (critic_dir / "_summary.md").read_text()
    findings_md = (critic_dir / "findings.md").read_text()
    meta = json.loads((critic_dir / "_meta.json").read_text())

    # _summary.md typically contains a JSON-in-markdown block with a
    # "dimensions" map; we extract that block and treat each key as a
    # dimension.
    summary_data = _extract_ip_uspto_summary_json(summary_md)

    scores = _parse_ip_uspto_dimensions(summary_data)
    critical_flags = _parse_ip_uspto_critical_flags(summary_data)
    findings = _parse_ip_uspto_findings(findings_md)

    # ip-uspto's _summary.md typically does not carry total/threshold; the
    # aggregator computes total downstream. We do not invent values.
    return Review(
        schema_version="1",
        kind=Kind.JUDGMENT,
        version_dir=_infer_version_dir(critic_dir),
        critic_id=meta.get("critic", _infer_critic_id(critic_dir)),
        model=meta.get("model"),
        scores=scores,
        findings=findings,
        critical_flags=critical_flags,
    )


def _extract_ip_uspto_summary_json(text: str) -> dict:
    """Pull the first ```json ... ``` block out of _summary.md."""
    m = re.search(r"```json\s*(\{.+?\})\s*```", text, re.DOTALL)
    if not m:
        return {}
    return json.loads(m.group(1))


def _parse_ip_uspto_dimensions(data: dict) -> List[Score]:
    dims = data.get("dimensions", {})
    scores: List[Score] = []
    for name, entry in dims.items():
        if entry is None:
            # Unowned by this critic; emit a null-scored row so the
            # aggregator can still see the dimension if every critic
            # leaves it null.
            scores.append(Score(dimension=name, score=None, max=5))
            continue
        score_val = entry.get("score")
        weight = entry.get("weight", 5)
        scores.append(
            Score(
                dimension=name,
                score=score_val,
                max=weight,
                critical=False,
                justification=entry.get("justification"),
            )
        )
    return scores


def _parse_ip_uspto_critical_flags(data: dict) -> List[CriticalFlag]:
    if not data.get("critical_flag"):
        return []
    notes = data.get("critical_flag_notes", [])
    flags: List[CriticalFlag] = []
    for note in notes:
        flags.append(
            CriticalFlag(
                type=note.get("type", "unspecified"),
                justification=note.get("justification", ""),
                evidence_span=note.get("slide_ref") or note.get("evidence_span"),
            )
        )
    if not flags:
        # critical_flag was True but no notes — synthesize a placeholder.
        flags.append(
            CriticalFlag(
                type="unspecified",
                justification="critical_flag set in _summary.md without notes",
            )
        )
    return flags


def _parse_ip_uspto_findings(text: str) -> List[Finding]:
    """Extract findings from a numbered or bulleted list in findings.md."""
    findings: List[Finding] = []
    severity_re = re.compile(
        r"^\s*(?:\d+\.|[-*])\s*\*?\*?\[?(?P<sev>blocker|major|minor|nit)\]?\*?\*?"
        r"\s*(?P<body>.+)$",
        re.IGNORECASE,
    )
    for line in text.splitlines():
        m = severity_re.match(line)
        if not m:
            continue
        sev = m.group("sev").lower()
        body = m.group("body").strip()
        # Try to split into rationale + fix if there's a "Suggested fix:" tail.
        fix_match = re.search(
            r"(?:Suggested fix|Fix):\s*(?P<fix>.+)$", body, re.IGNORECASE
        )
        if fix_match:
            fix = fix_match.group("fix").strip()
            rationale = body[: fix_match.start()].rstrip(" .:")
        else:
            rationale = body
            fix = body
        findings.append(
            Finding(
                severity=sev,  # type: ignore[arg-type]
                rationale=rationale,
                suggested_fix=fix,
            )
        )
    return findings


# --- Common helpers ---------------------------------------------------------


def _infer_version_dir(critic_dir: Path) -> str:
    """Given .../foo.3.review/, return 'foo.3'."""
    name = critic_dir.name
    # Strip the last ".<tag>" segment.
    if "." in name:
        head, _, _tag = name.rpartition(".")
        if head:
            return head
    return name


def _infer_critic_id(critic_dir: Path) -> str:
    """Given .../foo.3.review/, return 'review' (the trailing tag)."""
    name = critic_dir.name
    if "." in name:
        return name.rpartition(".")[2] or name
    return name


# ---------------------------------------------------------------------------
# Aggregation
# ---------------------------------------------------------------------------


def aggregate(reviews: List[Review]) -> AggregatedReview:
    """Merge N per-critic Reviews into one AggregatedReview.

    Pure function: no filesystem access. Aggregation rules are documented at
    the top of this module.

    Raises ``ValueError`` if:
    - ``reviews`` is empty.
    - Reviews disagree on ``version_dir``.
    - Two critics enumerate the same dimension with different ``max``.
    """
    if not reviews:
        raise ValueError("aggregate requires at least one Review")

    version_dirs = {r.version_dir for r in reviews}
    if len(version_dirs) > 1:
        raise ValueError(
            f"aggregate: reviews target different version_dir values: "
            f"{sorted(version_dirs)}"
        )
    version_dir = next(iter(version_dirs))

    # Build per-dimension buckets, in first-seen order across reviews.
    dim_order: List[str] = []
    buckets: dict = {}
    for r in reviews:
        for s in r.scores:
            if s.dimension not in buckets:
                dim_order.append(s.dimension)
                buckets[s.dimension] = {
                    "max": s.max,
                    "scores": [],  # non-null int scores
                    "critical": False,
                    "fixes": [],  # ordered, deduped
                    "evidence_span": None,
                    "justification": None,
                }
            b = buckets[s.dimension]
            if b["max"] != s.max:
                raise ValueError(
                    f"aggregate: dimension {s.dimension!r} has inconsistent "
                    f"max ({b['max']} vs {s.max}) across critics"
                )
            if s.score is not None:
                b["scores"].append(s.score)
            if s.critical:
                b["critical"] = True
            if s.fix and s.fix not in b["fixes"]:
                b["fixes"].append(s.fix)
            if s.evidence_span and b["evidence_span"] is None:
                b["evidence_span"] = s.evidence_span
            if s.justification and b["justification"] is None:
                b["justification"] = s.justification

    aggregated_scores: List[Score] = []
    score_means: dict = {}
    total = 0
    for dim in dim_order:
        b = buckets[dim]
        if b["scores"]:
            mean = sum(b["scores"]) / len(b["scores"])
            rounded = int(round(mean))
            score_means[dim] = mean
        else:
            mean = None
            rounded = None
            score_means[dim] = None
        if rounded is not None:
            total += rounded
        fix_joined = "; ".join(b["fixes"]) if b["fixes"] else None
        aggregated_scores.append(
            Score(
                dimension=dim,
                score=rounded,
                max=b["max"],
                critical=b["critical"],
                fix=fix_joined,
                evidence_span=b["evidence_span"],
                justification=b["justification"],
            )
        )

    findings = _dedupe_findings(r.findings for r in reviews)
    critical_flags = _dedupe_critical_flags(r.critical_flags for r in reviews)

    # Threshold: take the first non-null threshold from the reviews. If none
    # is set, default to sum-of-max (which means: never advance on score
    # alone — caller can override with compute_verdict).
    threshold: Optional[int] = None
    for r in reviews:
        if r.threshold is not None:
            threshold = r.threshold
            break
    if threshold is None:
        threshold = sum(s.max for s in aggregated_scores)

    # ``pending_dependency`` flags (issue #842) are visible in
    # ``critical_flags`` for the terminal-state gate but must NOT force
    # ``Verdict.BLOCK`` — exclude them from the generic-critical trigger.
    from anvil.lib.convergence import blocking_critical_flags

    verdict = _compute_verdict_impl(
        total=total,
        threshold=threshold,
        any_critical=bool(blocking_critical_flags(critical_flags))
        or any(s.critical for s in aggregated_scores),
        critical_flags=critical_flags,
    )

    return AggregatedReview(
        schema_version="1",
        version_dir=version_dir,
        critic_ids=[r.critic_id for r in reviews],
        scores=aggregated_scores,
        score_means=score_means,
        findings=findings,
        critical_flags=critical_flags,
        total=total,
        threshold=threshold,
        verdict=verdict,
    )


def _dedupe_findings(iter_lists: Iterable[List[Finding]]) -> List[Finding]:
    seen: set = set()
    out: List[Finding] = []
    for findings in iter_lists:
        for f in findings:
            key = (f.severity, f.dimension, f.rationale, f.suggested_fix)
            if key in seen:
                continue
            seen.add(key)
            out.append(f)
    return out


def _dedupe_critical_flags(
    iter_lists: Iterable[List[CriticalFlag]],
) -> List[CriticalFlag]:
    seen: set = set()
    out: List[CriticalFlag] = []
    for flags in iter_lists:
        for cf in flags:
            key = (cf.type, cf.justification)
            if key in seen:
                continue
            seen.add(key)
            out.append(cf)
    return out


# ---------------------------------------------------------------------------
# Verdict
# ---------------------------------------------------------------------------


def compute_verdict(
    agg: AggregatedReview,
    threshold: Optional[int] = None,
    *,
    history: Optional[List[Optional[int]]] = None,
    iteration: Optional[int] = None,
    max_iterations: Optional[int] = None,
    window: int = 1,
    lookback: int = 2,
) -> Verdict:
    """Pure function: decide ADVANCE / REVISE / BLOCK / STALLED.

    Single-iteration semantics (when ``history`` is ``None``):

    - BLOCK if any critical flag (either top-level or per-dimension critical).
    - Else ADVANCE if total >= threshold.
    - Else REVISE.

    Multi-iteration semantics (when ``history`` is provided): delegates to
    ``anvil.lib.convergence.decide_termination``. In addition to the three
    verdicts above, this can return STALLED when the last ``lookback``
    aggregated totals (most recent first appended last in ``history``) are
    all within ``± window`` and below threshold. Hitting ``max_iterations``
    keeps the verdict at REVISE (with termination_reason MAX_ITERATIONS at
    the convergence layer); STALLED is reserved for a demonstrated plateau.

    Backward compatibility: when ``history`` is ``None`` (default), behavior
    is identical to the pre-#27 implementation. All call sites that do not
    opt in to convergence-aware verdicts continue to receive
    ADVANCE / REVISE / BLOCK only.

    Parameters
    ----------
    agg:
        The aggregated review.
    threshold:
        Optional override. Defaults to ``agg.threshold``.
    history:
        Optional per-iteration aggregated totals in iteration order. When
        provided, the function delegates to
        ``convergence.decide_termination`` and can return ``STALLED``. When
        ``None`` (default), the function uses single-iteration semantics
        and never returns ``STALLED``.
    iteration:
        Current iteration number (1-indexed). Required when ``history`` is
        provided.
    max_iterations:
        Iteration cap. Required when ``history`` is provided.
    window:
        Stability window (default ``1``). Only used when ``history`` is
        provided.
    lookback:
        Stability lookback (default ``2``). Only used when ``history`` is
        provided.
    """
    eff_threshold = threshold if threshold is not None else agg.threshold
    # ``pending_dependency`` flags (issue #842) stay visible in
    # ``agg.critical_flags`` but never contribute to the BLOCK trigger.
    from anvil.lib.convergence import blocking_critical_flags

    any_critical = bool(blocking_critical_flags(agg.critical_flags)) or any(
        s.critical for s in agg.scores
    )

    if history is None:
        return _compute_verdict_impl(
            agg.total,
            eff_threshold,
            any_critical,
            critical_flags=agg.critical_flags,
        )

    if iteration is None or max_iterations is None:
        raise ValueError(
            "compute_verdict: when 'history' is provided, both 'iteration' "
            "and 'max_iterations' must also be provided."
        )

    # Imported lazily to avoid a hard module-load dependency cycle when only
    # the single-iteration path is used.
    from anvil.lib.convergence import decide_termination

    verdict, _reason = decide_termination(
        history=history,
        threshold=eff_threshold,
        any_critical=any_critical,
        iteration=iteration,
        max_iterations=max_iterations,
        window=window,
        lookback=lookback,
        critical_flags=list(agg.critical_flags),
    )
    return verdict


def _compute_verdict_impl(
    total: int,
    threshold: int,
    any_critical: bool,
    critical_flags: Optional[List[CriticalFlag]] = None,
) -> Verdict:
    # NO-GO short-circuits everything else (issue #559) when a no_go-typed
    # critical flag is present. The typed list is the canonical input; the
    # any_critical bool stays for byte-identical backwards-compat with
    # pre-#559 callers (which never pass a no_go flag).
    if critical_flags:
        # Lazy import — avoid hard dep when the typed list isn't passed.
        from anvil.lib.convergence import _has_no_go_flag

        if _has_no_go_flag(critical_flags):
            return Verdict.NO_GO
    if any_critical:
        return Verdict.BLOCK
    if total >= threshold:
        return Verdict.ADVANCE
    return Verdict.REVISE


__all__ = [
    "CANONICAL_REVIEW_FILENAME",
    "LEGACY_MEMO_FILES",
    "LEGACY_IP_USPTO_FILES",
    "CriticDiscoveryError",
    "discover_critics",
    "load_review",
    "parse_memo_scoring_table",
    "parse_memo_verdict_total",
    "parse_memo_verdict_decision",
    "parse_memo_verdict_no_go",
    "parse_memo_verdict_kill_rationale",
    "aggregate",
    "compute_verdict",
]
