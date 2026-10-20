"""Hyperlink resolver critic (issue #335, Epic #328 Track B Phase 2; promoted under #460).

Deterministic link-validation pass that emits a canonical ``_review.json``
(``kind=Kind.TOOL_EVIDENCE``) for broken cross-thread refs, broken markdown
internal paths, broken wiki-links, and (behind ``--check-external``) failing
external HTTP links found in a markdown-bodied version directory
(``<thread>.{N}/<thread>.md`` per the #295 slug-echo convention — the
shape shared by ``anvil:memo`` and ``anvil:essay``).

Track B (mechanical detector) sibling to Track A's reviewer-prose enrichment
(#333 / #334) and Track B Phase 3's citation-coverage critic (#336). The
three pieces are deliberately decoupled — this critic owns hyperlink
resolution only; citation coverage is Phase 3's surface.

Design contract (settled at Epic #328 kickoff; do NOT re-litigate)
------------------------------------------------------------------

- **No schema delta.** Ships with the existing free-form ``Finding.fix``
  / ``Finding.suggested_fix`` text per ``anvil/lib/review_schema.py``.
  No ``action`` / ``target_anchor`` / ``proposed_content`` fields.
- **Promoted under #460.** Born skill-local at
  ``anvil/skills/memo/lib/hyperlink_resolver.py`` (#335) per the
  CLAUDE.md "wait for the second consumer" rule; ``anvil:essay`` (#460)
  is the second consumer (its review wires broken-link resolution as a
  convergence-blocking gate), so the canonical module now lives here at
  ``anvil/lib/hyperlink_resolver.py``. The memo path remains a
  back-compat re-export shim (the #382/#393 promotion pattern).
  ``citation_coverage.py`` deliberately stays memo-local — memo's
  detector finds unlinked load-bearing *claims*; essay's coverage
  concern is unlinked named *entities* (judgment-side,
  corpus-convention-dependent) and is carried as essay-review prose.
- **External HTTP check off by default.** ``check_external=False``
  keeps the critic offline-safe and CI-reproducible; opt in with the
  ``--check-external`` CLI flag or ``check_external=True`` kwarg.
- **Memo + essay.** Paper / report / etc. extensions land in follow-on
  issues when those skills surface the need.

Four link classes
-----------------

1. **Cross-thread refs** — ``[[../<other-slug>/<other-slug>.N]]`` or
   ``[[../<other-slug>/<other-slug>.latest]]``, with optional
   ``/<file>`` suffix. Delegates to
   :mod:`cross_thread_refs.find_cross_thread_refs` +
   :func:`cross_thread_refs.resolve_cross_thread_ref` — **no duplicate
   parsing**. Unresolved refs emit ``severity="blocker"`` findings AND
   raise the :data:`CRITICAL_BROKEN_CROSS_THREAD_ANCHOR` critical flag
   so the reviewer's verdict short-circuits to BLOCKED.
2. **Markdown internal links** — ``[text](path/to/file.md)`` whose path
   resolves relative-to-version-dir (or relative-to-project-root for a
   leading ``/``). Missing target file emits ``severity="major"``.
3. **Markdown external links** — ``[text](https://example.com/...)``.
   When ``check_external=False`` (default), recorded as discovered but
   NOT validated (no finding). When ``check_external=True``, each URL
   is probed via subprocess ``curl -I`` with a short timeout; 4xx / 5xx
   / network failures emit ``severity="major"`` findings; 2xx /
   redirects produce no finding.
4. **Wiki-links** — ``[[document-name]]`` (single-segment, no slash,
   no version specifier — distinct from cross-thread ref shape).
   Validated against the enclosing project's BRIEF.md
   ``documents:`` list when discoverable. Unknown document name emits
   ``severity="major"``.

Inactive-when-empty contract: a memo with no links of a given class
produces zero findings for that class — the critic's output is
byte-equivalent to a clean memo for the unused dimensions.

Public API
----------

``HyperlinkFinding`` — typed per-link result (class, raw text, line,
target, resolved, reason, severity). Sibling to
:class:`render_gate.GateFinding`.

``HyperlinkResolverResult`` — JSON-serializable batch result. Carries
``passed()`` + ``to_json()`` + ``to_review(version_dir, critic_id)``
mirroring :class:`render_gate.GateResult` and
:class:`revise_consistency.ConsistencyResult`.

``resolve_hyperlinks(version_dir, *, check_external=False) ->
HyperlinkResolverResult`` — main entry point. Reads the memo body
(``<slug>.md`` per #295) from ``version_dir``, walks all link
expressions, validates each, returns the batch result.

``write_review_dir(version_dir, result) -> Path`` — writes the
canonical ``<version_dir>.hyperlinks/_review.json`` sibling so
``anvil/lib/critics.py::aggregate`` auto-discovers the findings on
the next reviewer aggregation pass. The output-dir naming convention
(``<thread>.{N}.hyperlinks/``) is the **agreed coordination point**
with the Phase 3 citation-coverage critic (#336), which will write to
``<thread>.{N}.citations/``.

CLI entry-point
---------------

``python -m anvil.lib.hyperlink_resolver <version_dir>
[--check-external] [--write-review]``

Writes a JSON summary to stdout. When ``--write-review`` is set, also
writes ``<version_dir>.hyperlinks/_review.json``. The historical memo
invocation (``python -m anvil.skills.memo.lib.hyperlink_resolver``)
keeps working through the back-compat shim. The CLI entry-point
convention (``python -m <module> <version_dir>``) is documented as the
**agreed coordination point** with the Phase 3 citation-coverage critic
(#336) so both critics share an invocation shape.

Subprocess-only
---------------

External HTTP probing uses ``subprocess.run(["curl", "-I", ...])`` per
the CLAUDE.md "subprocess-only by default" contract. No new Python
deps. When ``curl`` is absent from PATH (rare; ships with macOS and
every modern Linux), each external probe records a graceful-degrade
``reason`` and the link is treated as unverified (NOT a finding).
"""

from __future__ import annotations

import json
import re
import shutil
import subprocess
import sys
from dataclasses import dataclass, field
from pathlib import Path
from typing import List, Optional, Tuple

from anvil.lib.review_schema import (
    CriticalFlag,
    Finding,
    Kind,
    Review,
    Score,
)


# ---------------------------------------------------------------------------
# Sibling-module imports (plain anvil.lib package imports)
# ---------------------------------------------------------------------------
#
# Post-promotion (#460) the siblings this module consumes already live in
# ``anvil/lib/`` (promoted under #382), so the historical memo-lib sys.path
# bootstrap is gone — plain package imports per the render_gate precedent.

from anvil.lib.cross_thread_refs import (
    CrossThreadRef,
    CrossThreadResolution,
    find_cross_thread_refs,
    resolve_cross_thread_ref,
)
from anvil.lib.project_brief import load_project_brief
from anvil.lib.project_discovery import discover_thread_root
from anvil.lib.sidecar import write_critic_review_dir


# ---------------------------------------------------------------------------
# Constants
# ---------------------------------------------------------------------------


CRITIC_ID = "hyperlinks"
"""Stable identifier for this critic in ``_review.json.critic_id``."""

DIM_HYPERLINKS = "hyperlinks"
"""Dimension name surfaced on every emitted Finding."""

CRITICAL_BROKEN_CROSS_THREAD_ANCHOR = "critical_broken_cross_thread_anchor"
"""Critical-flag ``type`` raised when a cross-thread ref's section anchor
or version dir is missing. Mirrors the issue #335 AC: 'memo A cites B
§N where §N doesn't exist'. Aggregator's ``compute_verdict`` short-
circuits to ``Verdict.BLOCK`` when this flag is set."""

# Class labels echoed in HyperlinkFinding.link_class and the JSON payload.
CLASS_CROSS_THREAD = "cross_thread_ref"
CLASS_MARKDOWN_INTERNAL = "markdown_internal"
CLASS_MARKDOWN_EXTERNAL = "markdown_external"
CLASS_WIKI_LINK = "wiki_link"

# Severity mapping per the issue body AC:
# - Broken internal (cross-thread + markdown internal + wiki) → blocker / major.
# - Broken external → major.
# - Uncheckable target (e.g. curl missing) → no finding (recorded as note).
SEVERITY_BROKEN_CROSS_THREAD = "blocker"
SEVERITY_BROKEN_MARKDOWN_INTERNAL = "major"
SEVERITY_BROKEN_MARKDOWN_EXTERNAL = "major"
SEVERITY_BROKEN_WIKI_LINK = "major"

# Output-dir naming. Coordination point with #336 (which uses .citations/).
HYPERLINKS_SUFFIX = "hyperlinks"

# Default external-probe timeout (seconds). Short by intent: a slow target
# should fall through to the "uncheckable" bucket rather than stall the
# critic. The test suite monkeypatches the curl call to avoid network.
# A bare timeout (no response either way) gets exactly one retry before
# it is reported as broken (issue #889) — see
# ``_is_transient_timeout_reason`` / ``_validate_external``.
DEFAULT_CURL_TIMEOUT_S = 5

# Markdown link regex: matches `[text](url)`. The `text` group is allowed
# to be empty (image-link `![]()` becomes `[](url)` after stripping the
# leading `!`); the `url` group captures up to the closing `)` excluding
# nested parens (markdown spec). Wiki-link form is matched separately.
_MD_LINK_RE = re.compile(
    r"""
    !?                                  # optional ! prefix for images
    \[(?P<text>[^\]]*)\]                # [text]
    \((?P<url>[^\s)]+)\)                # (url) — no whitespace; url cannot contain unescaped ')'
    """,
    re.VERBOSE,
)

# Wiki-link regex: `[[document-name]]`. Single-segment (no `/`); excludes
# the cross-thread shape `[[../slug/slug.N]]` and the explicit-version
# shape `[[slug.N]]`. The discriminator is "contains a `/` or a `.<digit>`"
# in the target — those are cross-thread or version-specifier shapes
# handled by ``cross_thread_refs``.
_WIKI_LINK_RE = re.compile(
    r"""
    \[\[                                # opening [[
    (?P<target>                         # capture: must not contain /, must not match version-N shape
        (?![./])                        # disallow leading . or / (cross-thread / relative shapes)
        [^/\]\[]+                       # one or more non-/, non-bracket chars
    )
    \]\]                                # closing ]]
    """,
    re.VERBOSE,
)

# Cheap discriminator for external URLs.
_EXTERNAL_URL_RE = re.compile(r"^(?:https?|ftp|mailto):", re.IGNORECASE)


# ---------------------------------------------------------------------------
# Result types
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class HyperlinkFinding:
    """One link-validation result.

    Attributes
    ----------
    link_class
        One of :data:`CLASS_CROSS_THREAD` / :data:`CLASS_MARKDOWN_INTERNAL`
        / :data:`CLASS_MARKDOWN_EXTERNAL` / :data:`CLASS_WIKI_LINK`.
    raw
        Verbatim link text (the matched markdown / wiki form, brackets
        included).
    line
        1-based source line in the memo body.
    target
        Resolved or attempted target (path string for internal classes,
        URL string for external, slug for wiki-link).
    resolved
        ``True`` when the target exists / responds; ``False`` when the
        link is broken (and a finding will be emitted).
    reason
        Short tag explaining the failure when ``resolved=False`` (e.g.
        ``"thread not found"`` for cross-thread, ``"file not found"``
        for markdown internal, ``"unknown document"`` for wiki,
        ``"HTTP 404"`` for external). ``None`` when ``resolved=True``.
    severity
        Severity tier of the resulting finding when ``resolved=False``.
        Determined by class per the issue #335 AC. ``None`` when
        ``resolved=True``.
    """

    link_class: str
    raw: str
    line: int
    target: str
    resolved: bool
    reason: Optional[str]
    severity: Optional[str]

    def to_dict(self) -> dict:
        return {
            "link_class": self.link_class,
            "raw": self.raw,
            "line": self.line,
            "target": self.target,
            "resolved": self.resolved,
            "reason": self.reason,
            "severity": self.severity,
        }


@dataclass
class HyperlinkResolverResult:
    """Outcome of one ``resolve_hyperlinks`` pass.

    JSON-serializable + :class:`Review`-emitter. Shape mirrors
    :class:`render_gate.GateResult` and
    :class:`revise_consistency.ConsistencyResult` so downstream
    aggregation is uniform across the deterministic-checks family.
    """

    version_dir: str
    body_path: str
    check_external: bool
    findings: List[HyperlinkFinding] = field(default_factory=list)
    reasons: List[str] = field(default_factory=list)
    # Internal: cross-thread refs that failed in a way that earns the
    # critical_broken_cross_thread_anchor flag.
    critical_cross_thread_count: int = 0

    def passed(self) -> bool:
        """``True`` when every link resolved (no broken findings)."""
        return not any(not f.resolved for f in self.findings)

    def to_json(self) -> dict:
        """Emit a JSON payload describing the pass.

        Keys: ``critic``, ``version_dir``, ``body_path``,
        ``check_external``, ``findings``, ``reasons``, ``pass``.
        Mirrors the render_gate JSON shape so a single consumer can read
        either payload uniformly.
        """
        return {
            "critic": CRITIC_ID,
            "version_dir": self.version_dir,
            "body_path": self.body_path,
            "check_external": self.check_external,
            "findings": [f.to_dict() for f in self.findings],
            "reasons": list(self.reasons),
            "pass": self.passed(),
        }

    def to_critical_flags(self) -> List[CriticalFlag]:
        """Emit one ``CriticalFlag`` when any cross-thread anchor is broken.

        Empty list when no broken cross-thread refs were found. The flag
        ``type`` is :data:`CRITICAL_BROKEN_CROSS_THREAD_ANCHOR` so the
        aggregator's ``compute_verdict`` short-circuits to ``Verdict.BLOCK``
        per the issue #335 AC.
        """
        if self.critical_cross_thread_count == 0:
            return []
        # Justification surfaces a deduplicated summary; full per-line
        # detail lives in the Finding[] entries.
        bad = [f for f in self.findings if f.link_class == CLASS_CROSS_THREAD and not f.resolved]
        sample = "; ".join(f"{f.raw} ({f.reason})" for f in bad[:3])
        more = f" (+{len(bad) - 3} more)" if len(bad) > 3 else ""
        return [
            CriticalFlag(
                type=CRITICAL_BROKEN_CROSS_THREAD_ANCHOR,
                justification=(
                    f"{self.critical_cross_thread_count} cross-thread "
                    f"reference(s) failed to resolve on disk. The cited "
                    f"sibling thread version or section anchor is missing, "
                    f"so the memo's evidence chain is incomplete: "
                    f"{sample}{more}."
                ),
                evidence_span=f"{self.body_path}:L{bad[0].line}" if bad else None,
            )
        ]

    def to_review(self, *, version_dir: str, critic_id: str = CRITIC_ID) -> Review:
        """Build a typed ``Review`` (``kind=Kind.TOOL_EVIDENCE``).

        Pattern mirrors :meth:`render_gate.GateResult.to_review` and
        :meth:`revise_consistency.ConsistencyResult.to_review`:

        - A single null-scored ``Score`` so ``scores`` is non-empty (the
          schema requires it) but contributes nothing to the aggregated
          total — the hyperlink resolver owns no rubric dimension; it is
          a pre-judgment mechanical detector that feeds the verdict via
          the critical-flag short-circuit (cross-thread anchors) or as
          tool-evidence findings the reviewer consumes alongside its
          own dim 3 scoring (markdown / wiki / external).
        - One ``Finding`` per **broken** :class:`HyperlinkFinding` with
          ``tool_calls=[]`` to satisfy the ``Kind.TOOL_EVIDENCE`` schema
          validator. Resolved links produce no finding (clean review).
        - ``CriticalFlag`` emission when any cross-thread anchor is
          broken (delegates to :meth:`to_critical_flags`).
        """
        scores = [
            Score(
                dimension=DIM_HYPERLINKS,
                score=None,
                max=1,
                justification=(
                    "hyperlink-resolver is a deterministic tool-evidence "
                    "critic; owns no rubric dim (feeds verdict via critical "
                    "flag on broken cross-thread anchors and as evidence "
                    "for the reviewer's dim 3 scoring loop)."
                ),
            )
        ]
        findings: List[Finding] = []
        for hf in self.findings:
            if hf.resolved:
                continue
            assert hf.severity is not None  # broken findings always carry severity
            findings.append(
                Finding(
                    severity=hf.severity,  # type: ignore[arg-type]
                    dimension=DIM_HYPERLINKS,
                    evidence_span=f"{self.body_path}:L{hf.line}",
                    rationale=(
                        f"{hf.link_class}: {hf.raw} did not resolve "
                        f"({hf.reason})."
                    ),
                    suggested_fix=_suggested_fix_for(hf),
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


def _suggested_fix_for(hf: HyperlinkFinding) -> str:
    """Build the free-form ``Finding.suggested_fix`` text per link class.

    Stays within the existing ``Finding.suggested_fix`` contract (free
    string) — no schema delta. The phrasing matches the issue body's
    examples ("Section was renamed — try '## Verification' instead of
    '## Verify'", "External target returned 404 — consider removing or
    replacing") so the reviewer downstream gets actionable instructions.
    """
    if hf.link_class == CLASS_CROSS_THREAD:
        return (
            f"Cross-thread reference {hf.raw} failed to resolve "
            f"({hf.reason}). Verify the cited sibling thread version "
            f"exists on disk; if the target was renamed or removed, "
            f"update the [[../slug/slug.N]] reference (or remove the "
            f"claim depending on it)."
        )
    if hf.link_class == CLASS_MARKDOWN_INTERNAL:
        return (
            f"Markdown internal link target {hf.target!r} not found "
            f"under the version directory. Verify the file path is "
            f"correct (relative to <thread>.{{N}}/) and the target "
            f"exists, or remove the link if the target was intentionally "
            f"deleted."
        )
    if hf.link_class == CLASS_MARKDOWN_EXTERNAL:
        return (
            f"External target {hf.target} returned {hf.reason}. "
            f"Consider removing or replacing the link with a current "
            f"source; if the failure is transient, re-run with "
            f"--check-external to retry."
        )
    if hf.link_class == CLASS_WIKI_LINK:
        return (
            f"Wiki-link [[{hf.target}]] does not match any document in "
            f"the project's BRIEF.md documents: list. Either add the "
            f"document to BRIEF.md or correct the wiki-link target."
        )
    # Defensive fallback — should be unreachable given the four classes.
    return f"Resolve link {hf.raw} ({hf.reason})."


# ---------------------------------------------------------------------------
# Link enumeration
# ---------------------------------------------------------------------------


def _line_of(text: str, offset: int) -> int:
    """1-based source line containing byte ``offset`` into ``text``."""
    return text.count("\n", 0, offset) + 1


def _normalize_raw(raw: str) -> str:
    """Collapse internal whitespace (incl. newlines) to single spaces.

    A matched link's raw text may embed a hard line wrap when its
    bracket text spans one (issue #889). The underlying match text is
    unchanged for resolution purposes; this is purely a display
    normalization so ``Finding.rationale`` / CLI JSON output reads as
    one line instead of splitting mid-sentence.
    """
    return re.sub(r"\s+", " ", raw).strip()


def _find_markdown_links(text: str) -> List[Tuple[int, str, str]]:
    """Return ``[(line, raw_text, url), ...]`` for every markdown link.

    Covers both ``[text](url)`` and image-link ``![text](url)`` (the
    leading ``!`` is matched-but-not-captured for finding purposes; the
    on-disk lint at memo-render time already validates image-target
    existence specifically). The enumeration is permissive — the per-link
    validator decides classification (internal vs. external) and
    pass/fail.

    Scans the **whole body in one pass**, not line-by-line (issue
    #889). A link written with hard-wrapped bracket text —

        gf180-bandgap's [target spec is
        ratified](https://github.com/...):

    — is invisible to a per-line scan, because neither line contains a
    matching ``[...]`` pair on its own; the previous per-``splitlines()``
    implementation missed every such link. ``_MD_LINK_RE``'s ``[^\\]]*``
    text group already matches across newlines (character classes are
    unaffected by ``re.DOTALL``), so applying it to the full text is
    sufficient — only the enumeration loop needed to change. ``line``
    reports the line on which the link *opens* (the ``[``).
    """
    out: List[Tuple[int, str, str]] = []
    for m in _MD_LINK_RE.finditer(text):
        line_idx = _line_of(text, m.start())
        out.append((line_idx, _normalize_raw(m.group(0)), m.group("url")))
    return out


def _find_wiki_links(text: str) -> List[Tuple[int, str, str]]:
    """Return ``[(line, raw_text, target), ...]`` for every wiki-link.

    Excludes the cross-thread shape ``[[../slug/slug.N]]`` (parsed by
    :func:`cross_thread_refs.find_cross_thread_refs`) and the
    explicit-version shape ``[[slug.N]]`` (rare; treated as wiki-form
    if it slips through). The regex is the authoritative discriminator;
    edge cases that look like both fall to whichever pattern matches
    first.

    Scans the whole body in one pass (not per line) for the same
    hard-line-wrap reason as :func:`_find_markdown_links` (issue #889).
    """
    out: List[Tuple[int, str, str]] = []
    for m in _WIKI_LINK_RE.finditer(text):
        target = m.group("target")
        # Defensive: skip shapes that look like version specifiers
        # (e.g., "slug.3" — would be a cross-thread intra-thread
        # shape, not handled by the wiki-link class).
        if re.search(r"\.\d+$|\.latest$", target):
            continue
        line_idx = _line_of(text, m.start())
        out.append((line_idx, _normalize_raw(m.group(0)), target))
    return out


# ---------------------------------------------------------------------------
# Per-class validators
# ---------------------------------------------------------------------------


def _validate_cross_thread(
    ref: CrossThreadRef, portfolio_root: Path
) -> Tuple[bool, Optional[str]]:
    """Resolve a cross-thread ref; return ``(resolved, reason)``.

    Thin wrapper around
    :func:`cross_thread_refs.resolve_cross_thread_ref` so the per-link
    enumeration stays uniform across classes.
    """
    res: CrossThreadResolution = resolve_cross_thread_ref(ref, portfolio_root)
    return res.resolved, res.reason


def _validate_markdown_internal(
    url: str, version_dir: Path
) -> Tuple[bool, Optional[str], str]:
    """Resolve a markdown internal link.

    Returns ``(resolved, reason, normalized_target_str)``. ``url`` may
    carry a trailing ``#anchor`` fragment; the fragment is stripped for
    file-existence purposes (the existence check is on the file, not
    the anchor — markdown anchor validity is a follow-on concern not
    covered by this critic per the issue body scope).
    """
    # Strip trailing fragment and query — neither affects file existence.
    bare = url.split("#", 1)[0].split("?", 1)[0]
    if not bare:
        # Pure-fragment link like "#section" — points at the body itself.
        # Treat as resolved (the file is the body, which obviously exists).
        return True, None, url
    target_path = (version_dir / bare).resolve()
    # Guard against path-traversal sneaking out of the version dir to
    # somewhere unintended; we still resolve, but the user-visible
    # target string echoes the bare form for clarity.
    if target_path.exists():
        return True, None, bare
    return False, "file not found", bare


def _validate_wiki_link(
    target: str, brief_documents: Optional[List[str]]
) -> Tuple[bool, Optional[str]]:
    """Resolve a wiki-link against BRIEF.md's ``documents:`` list.

    Returns ``(resolved, reason)``. When ``brief_documents`` is
    ``None`` (no BRIEF discoverable), every wiki-link is reported as
    ``"BRIEF.md not found"`` — distinct from "unknown document" so the
    operator can see at a glance whether the project layout is missing
    or the wiki-link target is wrong. Per the issue body the wiki-link
    severity remains ``major`` either way.
    """
    if brief_documents is None:
        return False, "BRIEF.md not found"
    if target in brief_documents:
        return True, None
    return False, "unknown document"


def _is_transient_timeout_reason(reason: Optional[str]) -> bool:
    """``True`` when a failed probe's reason looks like a bare timeout.

    Covers both failure shapes a curl timeout can surface as: the
    Python-side ``subprocess.TimeoutExpired`` (``--max-time`` didn't
    save it, the outer ``timeout=`` fired) and curl's own on-the-wire
    sentinel — ``%{http_code}`` prints ``000`` when the connection
    never completed (a dead socket, DNS failure, or ``--max-time``
    itself expiring), which surfaces here as ``"HTTP 0"``. Issue #889
    reported exactly the latter shape: a URL that returned 200 on an
    immediate re-probe with ``curl -sL`` was reported as failing with
    ``HTTP 0`` here. Distinguishing a real 4xx/5xx (never retried) from
    a transient no-response (retried once) is the point of this check.
    """
    if reason is None:
        return False
    return reason == "curl error: TimeoutExpired" or reason == "HTTP 0"


def _curl_probe_once(
    url: str, *, timeout_s: int
) -> Tuple[bool, Optional[str]]:
    """Run exactly one ``curl -I`` probe; return ``(resolved, reason)``.

    Treats HTTP 2xx and 3xx as resolved; 4xx and 5xx as broken; network
    errors / timeouts as broken with the curl exit code in the reason.
    Factored out of :func:`_validate_external` so the retry wrapper can
    call it twice without duplicating the subprocess invocation.
    """
    try:
        proc = subprocess.run(
            ["curl", "-I", "-s", "-o", "/dev/null", "-w", "%{http_code}", "--max-time", str(timeout_s), url],
            capture_output=True,
            text=True,
            check=False,
            timeout=timeout_s + 2,
        )
    except (subprocess.TimeoutExpired, OSError) as exc:
        return False, f"curl error: {type(exc).__name__}"
    code_str = (proc.stdout or "").strip()
    if not code_str.isdigit():
        return False, f"curl returned non-numeric status: {code_str!r}"
    code = int(code_str)
    if 200 <= code < 400:
        return True, None
    return False, f"HTTP {code}"


def _validate_external(
    url: str, *, timeout_s: int = DEFAULT_CURL_TIMEOUT_S
) -> Tuple[bool, Optional[str]]:
    """Probe an external URL via ``curl -I``; return ``(resolved, reason)``.

    When ``curl`` is absent from PATH, returns ``(True, None)`` — the
    link is recorded as **unverified** by the caller via a top-level
    ``reasons`` note, not as a finding (mirrors the
    ``check_*_available`` graceful-degrade contract in
    ``anvil/lib/render.py``).

    A single retry (issue #889) fires when the *first* probe fails
    with a bare-timeout shape (see :func:`_is_transient_timeout_reason`)
    — two consecutive real-world sessions saw a live URL (HTTP 200 on
    immediate manual re-probe) reported as broken here after one
    ``--max-time``-bounded ``curl -I`` timed out. A genuine 4xx/5xx is
    never retried — only the shape indistinguishable from "server
    didn't answer in time".
    """
    if shutil.which("curl") is None:
        # Caller surfaces this as a top-level reason; here we return
        # resolved=True so the link is not flagged as broken (the
        # critic cannot prove it broken without the tool).
        return True, None
    resolved, reason = _curl_probe_once(url, timeout_s=timeout_s)
    if not resolved and _is_transient_timeout_reason(reason):
        resolved, reason = _curl_probe_once(url, timeout_s=timeout_s)
    return resolved, reason


# ---------------------------------------------------------------------------
# Project / BRIEF discovery helper
# ---------------------------------------------------------------------------


def _discover_brief_documents(version_dir: Path) -> Optional[List[str]]:
    """Return the BRIEF.md ``documents:`` slug list, or ``None``.

    Walks upward from ``version_dir`` via
    :func:`project_discovery.discover_thread_root` to locate the
    project root and load its BRIEF. Returns the list of declared slugs
    (one per ``BriefDocument``). Returns ``None`` when no BRIEF is
    discoverable, when the BRIEF is malformed (the lenient loader
    returns ``None`` in that case), or when the discovery raises.
    Graceful-degrade: failures here MUST NOT raise — the wiki-link
    validator handles ``None`` by emitting an ``unknown document`` /
    ``BRIEF.md not found`` finding per link.
    """
    try:
        discovery = discover_thread_root(version_dir)
    except Exception:
        return None
    if discovery is None:
        return None
    try:
        brief = load_project_brief(discovery.project_root)
    except Exception:
        # Lenient loader returns None on missing / malformed BRIEF;
        # a hard exception means a schema-violating BRIEF — the wiki-
        # link validation still wants to fall back to a clean "BRIEF
        # not found" rather than propagate the schema error.
        return None
    if brief is None:
        return None
    return [doc.slug for doc in brief.documents]


# ---------------------------------------------------------------------------
# Body filename helper (mirrors render_gate._memo_body_filename)
# ---------------------------------------------------------------------------


def _memo_body_filename(version_dir: Path) -> str:
    """Return the memo body filename for a version directory.

    Per the #295 model lock the body filename echoes the thread slug:
    ``<thread>/<thread>.{N}/<thread>.md``. The slug is the parent dir
    name. Mirrors ``render_gate._memo_body_filename`` so the body-path
    convention is identical across the deterministic-checks family.
    """
    return f"{version_dir.parent.name}.md"


# ---------------------------------------------------------------------------
# Main entry point
# ---------------------------------------------------------------------------


def resolve_hyperlinks(
    version_dir: Path,
    *,
    check_external: bool = False,
    curl_timeout_s: int = DEFAULT_CURL_TIMEOUT_S,
) -> HyperlinkResolverResult:
    """Walk every link expression in a memo version dir; validate; return result.

    The single public entry point. Reads ``<slug>.md`` from
    ``version_dir`` (slug-echo per #295), enumerates the four link
    classes, validates each per :func:`_validate_cross_thread`,
    :func:`_validate_markdown_internal`, :func:`_validate_wiki_link`,
    and (when ``check_external=True``) :func:`_validate_external`,
    and assembles a :class:`HyperlinkResolverResult` for downstream
    aggregation / persistence.

    Parameters
    ----------
    version_dir
        Path to ``<thread>.{N}/`` containing ``<thread>.md``.
    check_external
        When ``True``, probe external HTTP/HTTPS links via ``curl -I``.
        Default ``False`` — the critic stays offline-safe.
    curl_timeout_s
        Per-probe timeout when ``check_external=True``. Default 5s.

    Returns
    -------
    HyperlinkResolverResult
        Batch result with per-link :class:`HyperlinkFinding`,
        top-level reasons, and the critical-cross-thread counter.

    Raises
    ------
    FileNotFoundError
        When ``version_dir`` does not exist or ``<slug>.md`` is missing
        inside it. The critic refuses to invent findings for a missing
        body — the caller's invocation is a programming error.
    """
    version_dir = Path(version_dir).resolve()
    if not version_dir.is_dir():
        raise FileNotFoundError(
            f"hyperlink_resolver: version_dir {version_dir!s} does not "
            f"exist or is not a directory."
        )
    body_filename = _memo_body_filename(version_dir)
    body_path = version_dir / body_filename
    if not body_path.is_file():
        raise FileNotFoundError(
            f"hyperlink_resolver: memo body {body_filename!r} not found "
            f"in {version_dir!s} (per #295 the body filename echoes the "
            f"thread slug, i.e. <thread>.{{N}}/<thread>.md)."
        )

    text = body_path.read_text(encoding="utf-8")
    portfolio_root = version_dir.parent.parent  # <thread>/<thread>.N/ → <portfolio>/

    findings: List[HyperlinkFinding] = []
    reasons: List[str] = []
    critical_cross_thread = 0

    # ---- Cross-thread refs ------------------------------------------------
    for ref in find_cross_thread_refs(text):
        resolved, reason = _validate_cross_thread(ref, portfolio_root)
        sev = None if resolved else SEVERITY_BROKEN_CROSS_THREAD
        if not resolved:
            critical_cross_thread += 1
        findings.append(
            HyperlinkFinding(
                link_class=CLASS_CROSS_THREAD,
                raw=ref.raw,
                line=ref.line,
                target=f"{ref.other_slug}.{ref.version}"
                + (f"/{ref.file}" if ref.file else ""),
                resolved=resolved,
                reason=reason,
                severity=sev,
            )
        )

    # ---- Markdown links (internal + external) ----------------------------
    external_probed = 0
    external_unverified = 0
    for line, raw, url in _find_markdown_links(text):
        if _EXTERNAL_URL_RE.match(url):
            link_class = CLASS_MARKDOWN_EXTERNAL
            if check_external:
                if shutil.which("curl") is None:
                    # First time we notice — record once at top level.
                    if external_unverified == 0:
                        reasons.append(
                            "markdown_external: curl not on PATH; external "
                            "links recorded as unverified (install curl to "
                            "enable external probing)."
                        )
                    external_unverified += 1
                    # Record as resolved so it doesn't fire a finding.
                    findings.append(
                        HyperlinkFinding(
                            link_class=link_class,
                            raw=raw,
                            line=line,
                            target=url,
                            resolved=True,
                            reason="unverified (curl unavailable)",
                            severity=None,
                        )
                    )
                    continue
                external_probed += 1
                resolved, reason = _validate_external(
                    url, timeout_s=curl_timeout_s
                )
                sev = None if resolved else SEVERITY_BROKEN_MARKDOWN_EXTERNAL
                findings.append(
                    HyperlinkFinding(
                        link_class=link_class,
                        raw=raw,
                        line=line,
                        target=url,
                        resolved=resolved,
                        reason=reason,
                        severity=sev,
                    )
                )
            else:
                # Off-by-default: discovered but not validated. We
                # record as resolved=True with a reason so the reviewer
                # can see the link was recognized.
                findings.append(
                    HyperlinkFinding(
                        link_class=link_class,
                        raw=raw,
                        line=line,
                        target=url,
                        resolved=True,
                        reason="external probe disabled (use --check-external)",
                        severity=None,
                    )
                )
        else:
            link_class = CLASS_MARKDOWN_INTERNAL
            resolved, reason, normalized = _validate_markdown_internal(
                url, version_dir
            )
            sev = None if resolved else SEVERITY_BROKEN_MARKDOWN_INTERNAL
            findings.append(
                HyperlinkFinding(
                    link_class=link_class,
                    raw=raw,
                    line=line,
                    target=normalized,
                    resolved=resolved,
                    reason=reason,
                    severity=sev,
                )
            )

    # Top-level reason summarizing external posture.
    if check_external and external_probed > 0:
        reasons.append(
            f"markdown_external: probed {external_probed} URL(s) via "
            f"curl -I (timeout {curl_timeout_s}s)."
        )
    elif not check_external:
        ext_count = sum(
            1 for f in findings if f.link_class == CLASS_MARKDOWN_EXTERNAL
        )
        if ext_count > 0:
            reasons.append(
                f"markdown_external: {ext_count} external link(s) "
                f"recorded but NOT probed (default offline mode; "
                f"re-run with --check-external to validate)."
            )

    # ---- Wiki-links -------------------------------------------------------
    wiki_hits = _find_wiki_links(text)
    if wiki_hits:
        brief_documents = _discover_brief_documents(version_dir)
        if brief_documents is None:
            reasons.append(
                "wiki_link: project BRIEF.md not discoverable from "
                "version_dir; wiki-links will report 'BRIEF.md not "
                "found' (this is the expected shape outside a "
                "project-layout repo)."
            )
        for line, raw, target in wiki_hits:
            resolved, reason = _validate_wiki_link(target, brief_documents)
            sev = None if resolved else SEVERITY_BROKEN_WIKI_LINK
            findings.append(
                HyperlinkFinding(
                    link_class=CLASS_WIKI_LINK,
                    raw=raw,
                    line=line,
                    target=target,
                    resolved=resolved,
                    reason=reason,
                    severity=sev,
                )
            )

    return HyperlinkResolverResult(
        version_dir=version_dir.name,
        body_path=body_filename,
        check_external=check_external,
        findings=findings,
        reasons=reasons,
        critical_cross_thread_count=critical_cross_thread,
    )


# ---------------------------------------------------------------------------
# Critic-sibling writer
# ---------------------------------------------------------------------------


def write_review_dir(
    version_dir: Path,
    result: HyperlinkResolverResult,
    *,
    critic_id: str = CRITIC_ID,
) -> Path:
    """Write ``<version_dir>.hyperlinks/_review.json`` for auto-discovery.

    Delegates to the shared :func:`anvil.lib.sidecar.write_critic_review_dir`
    (issue #1086), which stages + atomically renames the sidecar via
    ``staged_sidecar`` (issue #350) — a mid-write interrupt never leaves a
    partial ``<version_dir>.hyperlinks/`` at the final name. This is a
    behavior change from the pre-#1086 plain ``mkdir`` + ``write_text``
    shape (called out explicitly in the #1086 PR body); every consuming
    command's own markdown doc (e.g. ``memo-hyperlinks.md``) already
    mandated ``staged_sidecar`` for this critic, so the change closes a
    doc/code drift rather than introducing a new contract. Returns the
    path to the written ``_review.json``.

    The naming convention (``<version_dir>.hyperlinks/``) is the
    coordination point with the Phase 3 citation-coverage critic
    (#336) which writes to ``<version_dir>.citations/``. Both forms
    are picked up by ``anvil/lib/critics.py::discover_critics`` via
    the ``<version_dir>.<tag>/`` pattern without code changes.
    """
    version_dir = Path(version_dir)
    review = result.to_review(version_dir=version_dir.name, critic_id=critic_id)
    return write_critic_review_dir(version_dir, HYPERLINKS_SUFFIX, review)


# ---------------------------------------------------------------------------
# CLI entry-point
# ---------------------------------------------------------------------------


def _build_cli_parser() -> "object":
    """Build the argparse parser. Factored out for testability."""
    import argparse

    p = argparse.ArgumentParser(
        prog="python -m anvil.lib.hyperlink_resolver",
        description=(
            "Hyperlink resolver critic (memo + essay). Walks every "
            "link expression in a markdown-bodied version directory and "
            "validates each per its class (cross-thread refs, markdown "
            "internal, markdown external, wiki-links)."
        ),
    )
    p.add_argument(
        "version_dir",
        help="Path to <thread>.{N}/ containing <thread>.md.",
    )
    p.add_argument(
        "--check-external",
        action="store_true",
        help=(
            "Probe external HTTP/HTTPS links via `curl -I` "
            "(off by default; keeps the critic offline-safe)."
        ),
    )
    p.add_argument(
        "--write-review",
        action="store_true",
        help=(
            "Also write <version_dir>.hyperlinks/_review.json for "
            "critic-sibling auto-discovery by aggregate()."
        ),
    )
    p.add_argument(
        "--curl-timeout",
        type=int,
        default=DEFAULT_CURL_TIMEOUT_S,
        help=(
            "Per-probe curl timeout in seconds "
            f"(default {DEFAULT_CURL_TIMEOUT_S})."
        ),
    )
    return p


def main(argv: Optional[List[str]] = None) -> int:
    """CLI entry point. Returns the process exit code.

    Exit codes:
    - ``0``: every link resolved (clean pass).
    - ``1``: one or more findings (broken links present).
    - ``2``: invocation error (missing version_dir or body file).
    """
    parser = _build_cli_parser()
    args = parser.parse_args(argv)
    try:
        result = resolve_hyperlinks(
            Path(args.version_dir),
            check_external=args.check_external,
            curl_timeout_s=args.curl_timeout,
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
    "DIM_HYPERLINKS",
    "CRITICAL_BROKEN_CROSS_THREAD_ANCHOR",
    "CLASS_CROSS_THREAD",
    "CLASS_MARKDOWN_INTERNAL",
    "CLASS_MARKDOWN_EXTERNAL",
    "CLASS_WIKI_LINK",
    "HYPERLINKS_SUFFIX",
    "HyperlinkFinding",
    "HyperlinkResolverResult",
    "resolve_hyperlinks",
    "write_review_dir",
    "main",
]


if __name__ == "__main__":
    raise SystemExit(main())
