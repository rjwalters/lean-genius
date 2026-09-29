"""Dangling-citation lint for `anvil:project-share` (issue #758).

The exporter's `verify` step (issue #396) checks *layout* — the marker
is present, every planned file landed, no stripped name leaked — but it
never looks at *content*. A thread body (or a shared `research/` pool
file) can cite a project-root working document (e.g.
`STRATEGIC-OPTIONS.md`) or a sibling file that never makes it into the
export set; for the recipient that citation is a dangling pointer with
nothing on the other end. This surfaced in the studio (canary)
packaging sentinel: three exported files cited `STRATEGIC-OPTIONS.md`, a
project-root working document that was never part of the export.

This is the export-time analog of the memo skill's refs back-check:
references should resolve within the world the reader receives.

This module scans every markdown file the plan is about to copy
(per-doc body + refs, and the shared `research/` pool) for tokens that
look like a repo-relative file reference — a markdown link
(``[text](path)``) or a bare backticked/prose filename (`` `STRATEGIC-
OPTIONS.md` ``) — and, when that reference resolves to a REAL file
somewhere in the project tree that is NOT part of this export's planned
copy set, records a finding.

This is deliberately a **report, not a block** (the citation may be
intentional — an internal cross-reference the recipient isn't meant to
follow) per the issue's acceptance criteria. Findings surface in the run
summary (``--dry-run`` and apply mode alike, since the check only reads
already-collected plan data — nothing about it requires the out dir to
exist) and in ``EXPORT.md``.

Resolution is intentionally conservative: a candidate is only reported
when it resolves to a file that actually exists on disk somewhere in
the project. This avoids false positives on prose that merely LOOKS
like a filename (typos, external tool names, code identifiers) — those
don't resolve to anything and are silently ignored.
"""

from __future__ import annotations

import re
from dataclasses import dataclass, field
from pathlib import Path
from typing import List, Optional, Set

from .plan import FilePlan, SharePlan

# Markdown inline link: `[text](path "optional title")`, optionally
# angle-bracketed (`<path>`). Captures the path/URL only.
_MD_LINK_RE = re.compile(
    r"\[[^\]]*\]\(\s*<?([^)\s>]+)>?(?:\s+\"[^\"]*\")?\s*\)"
)

# A scheme prefix (`http:`, `https:`, `mailto:`, ...) marks a candidate
# as NOT a repo-relative file reference.
_SCHEME_RE = re.compile(r"^[a-zA-Z][a-zA-Z0-9+.\-]*:")

# Bare filename mention in prose/backticks, e.g. `STRATEGIC-OPTIONS.md`
# or plain BRIEF.md. Extensions are limited to common document/export
# filetypes to keep the false-positive rate low — this is a heuristic
# lint, not a full markdown AST walk.
_DOC_EXTENSIONS = ("md", "markdown", "pdf", "csv", "xlsx", "docx", "pptx", "txt")
_BARE_FILENAME_RE = re.compile(
    r"(?<![\w/.\-])([A-Za-z0-9][\w.\-]*\.(?:" + "|".join(_DOC_EXTENSIONS) + r"))"
    r"(?![\w/.\-])"
)


@dataclass
class DanglingCitation:
    """One citation to a repo-relative file that is not in the export set."""

    doc_slug: Optional[str]  # None for the shared research/ pool
    source_rel: str  # citing file's path, relative to the project root
    citation_text: str  # raw path/filename as written in the source
    resolved_rel: str  # resolved target's path, relative to the project root


@dataclass
class CitationLintResult:
    """Outcome of :func:`find_dangling_citations`."""

    findings: List[DanglingCitation] = field(default_factory=list)

    @property
    def ok(self) -> bool:
        return not self.findings

    def to_report(self) -> str:
        lines = ["## Citations", ""]
        if self.ok:
            lines.append("- OK: no dangling citations found.")
        else:
            lines.append(
                f"- **{len(self.findings)} possible dangling citation(s)** "
                f"(report only — the citation may be deliberate):"
            )
            for f in self.findings:
                lines.append(
                    f"  - `{f.source_rel}` cites `{f.citation_text}` -> "
                    f"`{f.resolved_rel}`, which is not part of this export"
                )
        lines.append("")
        return "\n".join(lines) + "\n"


def _extract_candidates(text: str) -> List[str]:
    """Pull citation-shaped tokens out of markdown ``text``."""
    out: List[str] = []
    for m in _MD_LINK_RE.finditer(text):
        candidate = m.group(1)
        if _SCHEME_RE.match(candidate):
            continue
        candidate = candidate.split("#", 1)[0]
        if candidate and not candidate.startswith("#"):
            out.append(candidate)
    for m in _BARE_FILENAME_RE.finditer(text):
        out.append(m.group(1))
    return out


def _resolve_candidate(
    candidate: str, source_file: Path, project_dir: Path
) -> Optional[Path]:
    """Best-effort resolution of a citation to an on-disk project file.

    Returns ``None`` when the candidate can't be resolved to a real
    file anywhere searched — the candidate is then assumed to be
    unrelated prose (typo, tool name, code identifier), not a dangling
    reference.
    """
    candidate = candidate.strip()
    if not candidate:
        return None

    has_sep = "/" in candidate or "\\" in candidate

    # Path-shaped candidate (markdown link with a `/` or `../`):
    # resolve relative to the citing file's own directory.
    if has_sep:
        try:
            direct = (source_file.parent / candidate).resolve()
        except (OSError, RuntimeError):
            return None
        if direct.is_file():
            return direct
        return None

    # Bare filename: search the citing file's own directory, then the
    # project root, then one level above it (portfolio root) — bounded,
    # mirrors the `apply.gitignore_suggestion` bounded-walk precedent.
    for base in (source_file.parent, project_dir, project_dir.parent):
        candidate_path = base / candidate
        if candidate_path.is_file():
            return candidate_path.resolve()
    return None


def _rel(path: Path, project_dir: Path) -> str:
    try:
        return str(path.relative_to(project_dir))
    except ValueError:
        return str(path)


def _scan_file(
    fp: FilePlan,
    doc_slug: Optional[str],
    project_dir: Path,
    exported_sources: Set[Path],
    findings: List[DanglingCitation],
) -> None:
    if fp.source.suffix.lower() not in (".md", ".markdown"):
        return
    try:
        text = fp.source.read_text(encoding="utf-8")
    except (OSError, UnicodeDecodeError):
        return

    seen: Set[str] = set()
    source_resolved = fp.source.resolve()
    for candidate in _extract_candidates(text):
        if candidate in seen:
            continue
        seen.add(candidate)
        resolved = _resolve_candidate(candidate, fp.source, project_dir)
        if resolved is None or resolved == source_resolved:
            continue
        if resolved in exported_sources:
            continue
        findings.append(
            DanglingCitation(
                doc_slug=doc_slug,
                source_rel=_rel(fp.source, project_dir),
                citation_text=candidate,
                resolved_rel=_rel(resolved, project_dir),
            )
        )


def find_dangling_citations(plan: SharePlan) -> CitationLintResult:
    """Scan every markdown file in ``plan`` for dangling repo-relative citations.

    Pure / read-only: only reads already-collected source files named
    in the plan, never writes anywhere. Safe to call in ``--dry-run``
    mode — the finding doesn't depend on the out dir existing.
    """
    result = CitationLintResult()
    project_dir = plan.project_dir
    exported_sources = {fp.source.resolve() for fp in plan.all_file_plans}

    for doc in plan.docs:
        if doc.failed:
            continue
        for fp in doc.files:
            _scan_file(
                fp, doc.slug, project_dir, exported_sources, result.findings
            )

    for fp in plan.research_files:
        _scan_file(fp, None, project_dir, exported_sources, result.findings)

    return result


__all__ = [
    "CitationLintResult",
    "DanglingCitation",
    "find_dangling_citations",
]
