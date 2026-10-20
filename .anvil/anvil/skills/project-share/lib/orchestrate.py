"""Top-level command orchestration for `anvil:project-share` (issue #396).

Composes :mod:`config`, :mod:`collect` (via :mod:`plan`), :mod:`plan`,
:mod:`apply`, and :mod:`verify` into the operator-facing flows:

- **Export** (``/anvil:project-share <project>``): config + plan +
  report + marker-guarded apply + verify. Unlike the bridge tools
  (``project-migrate`` / ``rubric-rebackport``), dry-run is a **flag,
  not the default** — deliberate divergence locked at curation: the
  bridge tools rewrite source-of-truth in place, so dry-run-first is
  mandatory there; this tool only writes into a disposable,
  marker-guarded build dir.
- **Dry-run** (``--dry-run``): config + plan + report. Writes nothing
  (SHA-256-verifiably side-effect-free; see
  ``tests/test_project_share_dry_run.py``).
- **Zip** (``--zip``): also produce
  ``<project>/<dirname>-share-YYYYMMDD.zip``.

The skill's command spec consumes this module's :func:`run` function as
the single entry. Returns a typed :class:`RunResult` and a markdown
report.
"""

from __future__ import annotations

from dataclasses import dataclass
from datetime import datetime
from pathlib import Path
from typing import List, Optional

from anvil.lib.project_brief import load_project_brief_strict

from .apply import ApplyResult, apply_plan
from .citations import CitationLintResult, find_dangling_citations
from .config import ExportConfig, load_export_config
from .plan import (
    ORDERING_EXPORT_ORDER,
    SharePlan,
    build_plan,
    inspect_out_dir,
)
from .verify import VerifyResult, verify_export


@dataclass
class RunResult:
    """Typed summary of a :func:`run` invocation.

    Attributes
    ----------
    project_dir
        Absolute project root.
    config
        Parsed ``export:`` config (defaults when absent).
    plan
        Generated plan (always present, even in dry-run).
    apply_result
        Apply outcome; ``None`` for dry-run.
    verify_result
        Verify outcome; ``None`` when apply was skipped or refused.
    citation_result
        Dangling-citation lint outcome (issue #758). Always present
        (including in dry-run) — the check only reads plan-collected
        source files, never the out dir. Report-only: a non-empty
        result does NOT affect ``success``.
    report
        Markdown report (printed to stdout by the command).
    success
        True iff the run completed without failures: every doc
        resolved, the rebuild was not refused, and (in apply mode)
        verification passed. A per-doc resolution failure makes
        ``success`` False even though the other docs still exported —
        the command maps this to a nonzero exit (AC 9).
    """

    project_dir: Path
    config: ExportConfig
    plan: SharePlan
    apply_result: Optional[ApplyResult] = None
    verify_result: Optional[VerifyResult] = None
    citation_result: Optional[CitationLintResult] = None
    report: str = ""
    success: bool = False


def _format_plan_report(plan: SharePlan, dry_run: bool) -> str:
    lines: List[str] = []
    lines.append(f"# Project share: {plan.project_name}")
    lines.append("")
    lines.append(f"**Project root**: `{plan.project_dir}`")
    lines.append(f"**Out dir**: `{plan.out_dir}`")
    ordering = (
        "`export.order` (BRIEF override)"
        if plan.ordering_source == ORDERING_EXPORT_ORDER
        else "`documents:` (BRIEF default)"
    )
    lines.append(f"**Ordering**: {ordering}")
    lines.append(f"**Out-dir state**: {inspect_out_dir(plan.out_dir)}")
    failed = plan.failed_docs
    lines.append(
        f"**Documents**: {len(plan.docs)} planned, {len(failed)} failed "
        f"to resolve, {len(plan.excluded_slugs)} excluded"
    )
    if dry_run:
        lines.append("**Mode**: dry-run (no writes)")
    lines.append("")
    lines.append("## Plan")
    lines.append("")
    for doc in plan.docs:
        lines.append(f"### `{doc.target_dirname}/`")
        lines.append("")
        if doc.failed:
            lines.append(f"- FAILED: {doc.failure}")
        else:
            c = doc.collection
            lines.append(
                f"- Resolved version: `{c.resolved_name}` "
                f"({c.resolution_mode})"
            )
            lines.append(f"- Files to copy: {len(doc.files)}")
            refs_count = sum(
                1
                for fp in doc.files
                if len(fp.target_rel.parts) > 1
                and fp.target_rel.parts[1] == "refs"
            )
            if refs_count:
                lines.append(f"- Per-thread refs: {refs_count} files")
            for pdf in c.pdfs:
                lines.append(
                    f"- PDF: `{pdf.filename}` (sha256 `{pdf.sha256[:12]}…`)"
                )
        for note in doc.notes:
            lines.append(f"  - note: {note}")
        lines.append("")
    if plan.research_files:
        lines.append(
            f"### `research/` — shared pool, {len(plan.research_files)} files"
        )
        lines.append("")
    if plan.cover_file is not None:
        lines.append(
            f"### Cover note — `{plan.cover_file.target_rel}` "
            f"(from `{plan.cover_file.source}`)"
        )
        lines.append("")
    for note in plan.notes:
        lines.append(f"- note: {note}")
    if plan.notes:
        lines.append("")
    return "\n".join(lines) + "\n"


def _format_apply_report(apply_result: ApplyResult) -> str:
    lines: List[str] = ["## Apply", ""]
    if apply_result.refused:
        lines.append(f"- **REFUSED**: {apply_result.refusal_reason}")
    else:
        lines.append(f"- Files copied: {apply_result.files_copied}")
        lines.append(f"- Index written: `{apply_result.export_md}`")
        if apply_result.zip_path is not None:
            lines.append(f"- Zip written: `{apply_result.zip_path}`")
        if apply_result.failed_doc_slugs:
            lines.append(
                f"- **Unresolved docs (exported without them)**: "
                f"{', '.join(apply_result.failed_doc_slugs)}"
            )
        if apply_result.gitignore_note is not None:
            lines.append(f"- Suggestion: {apply_result.gitignore_note}")
    lines.append("")
    return "\n".join(lines) + "\n"


def run(
    project_dir: Path,
    *,
    dry_run: bool = False,
    zip_output: bool = False,
    now: Optional[datetime] = None,
) -> RunResult:
    """Execute the project-share flow.

    Parameters
    ----------
    project_dir
        The project root (the directory carrying ``BRIEF.md``).
    dry_run
        When True, plan + report only — writes nothing.
    zip_output
        When True (apply mode only), also produce the datestamped zip.
    now
        Injectable build timestamp (tests pin it for idempotence
        assertions). Defaults to ``datetime.now(timezone.utc)``.

    Returns
    -------
    A :class:`RunResult` carrying the outcome and the formatted report.

    Raises
    ------
    FileNotFoundError
        When ``project_dir`` or its ``BRIEF.md`` does not exist.
    ValueError
        On a malformed BRIEF / ``export:`` block, an ``export.order``
        slug that is not in ``documents:``, or an ``export.out`` name
        colliding with a source-of-truth directory.
    """
    project_dir = Path(project_dir).resolve()
    if not project_dir.is_dir():
        raise FileNotFoundError(f"Project root not found: {project_dir}")

    config = load_export_config(project_dir)
    brief = load_project_brief_strict(project_dir)
    plan = build_plan(project_dir, brief, config)

    # Read-only lint (issue #758): scans the plan-collected source
    # markdown for citations to project files that never enter the
    # export set. Runs before dry-run's early return since it only
    # reads already-collected plan data — no out-dir dependency.
    citation_result = find_dangling_citations(plan)

    result = RunResult(
        project_dir=project_dir,
        config=config,
        plan=plan,
        citation_result=citation_result,
    )
    report = _format_plan_report(plan, dry_run)
    report += "\n" + citation_result.to_report()

    if dry_run:
        result.report = report
        result.success = not plan.failed_docs
        return result

    apply_result = apply_plan(
        plan, zip_output=zip_output, now=now, citations=citation_result
    )
    result.apply_result = apply_result
    report += "\n" + _format_apply_report(apply_result)

    if apply_result.refused:
        result.success = False
        result.report = report
        return result

    verify_result = verify_export(plan)
    result.verify_result = verify_result
    report += "\n" + verify_result.to_report()
    result.success = verify_result.ok and not plan.failed_docs
    result.report = report
    return result


__all__ = ["RunResult", "run"]
