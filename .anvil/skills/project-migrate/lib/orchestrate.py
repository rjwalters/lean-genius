"""Top-level command orchestration for `anvil:project-migrate` (issue #297).

Composes :mod:`detect`, :mod:`plan`, :mod:`apply`, and :mod:`verify` into
the four operator-facing flows:

- **Dry-run** (`/anvil:project-migrate <project>`): detect + plan + report.
- **Apply** (`/anvil:project-migrate <project> --apply`): detect + plan +
  report + apply + verify.
- **Report** (`/anvil:project-migrate <project> --report`): detect + plan
  + report.

The skill's command spec consumes this module's :func:`run` function as
the single entry. The function returns a typed :class:`RunResult` and the
markdown report; the command spec formats stderr / stdout from those.

Design notes
------------

- **One entry point per skill flow.** The command spec stays small (it
  invokes :func:`run` and prints results) because all orchestration logic
  lives here.
- **No side effects in dry-run / report modes.** The execution layer
  refuses to run apply unless the explicit `apply=True` flag is set.
"""

from __future__ import annotations

from dataclasses import dataclass
from pathlib import Path
from typing import List, Optional, Sequence, Tuple

from .apply import (
    ApplyResult,
    apply_plan,
    render_enroll_brief,
    render_migrate_brief,
)
from .detect import (
    Shape,
    inventory_project,
    _classify,
)
from .adopt_family import AdoptFamilyError, build_adopt_family_plan
from .adopt_review import (
    AdoptReviewError,
    apply_adopt_review_plan,
    apply_rescore_plan,
    build_adopt_review_plan,
    build_rescore_plan,
)
from .adopt_vn import AdoptVnError, build_adopt_vn_plan
from .enroll import EnrollError, build_enroll_plan
from .plan import (
    Plan,
    PlanError,
    build_plan,
)
from .verify import VerifyResult, verify_migration


@dataclass
class RunResult:
    """Typed summary of a :func:`run` invocation.

    Attributes
    ----------
    project_dir
        Absolute path of the project root.
    shape
        Detected shape.
    plan
        Generated plan (always present, even in dry-run).
    apply_result
        Apply outcome; ``None`` for dry-run / report modes.
    verify_result
        Verify outcome; ``None`` when apply was skipped or failed.
    report
        The markdown report (printed verbatim to stdout by the command).
    success
        True iff the run completed without errors. For dry-run this is
        True when shape is recognized; for apply it's True when every
        document migrated and verify passes.
    """

    project_dir: Path
    shape: Shape
    plan: Plan
    apply_result: Optional[ApplyResult] = None
    verify_result: Optional[VerifyResult] = None
    report: str = ""
    success: bool = False


def _format_plan_report(
    project_dir: Path, shape: Shape, plan: Plan
) -> str:
    """Format the plan as a markdown report."""
    lines: List[str] = []
    lines.append(f"# Project migration: {project_dir.name}")
    lines.append("")
    lines.append(f"**Project root**: `{project_dir}`")
    shape_suffix = ""
    if plan.synthesize_brief:
        # Bare sub-state (issue #408) — same PRE_283_CLASSIC dispatch,
        # but the BRIEF is synthesized from observed state rather than
        # merged from legacy config.
        shape_suffix = " (bare — BRIEF will be synthesized)"
    lines.append(f"**Detected shape**: `{shape.value}`{shape_suffix}")
    lines.append(f"**Documents in plan**: {len(plan.documents)}")
    lines.append("")

    if shape == Shape.UNKNOWN:
        lines.append("## Plan")
        lines.append("")
        lines.append(
            "Could not classify this project as a recognized shape. "
            "Verify the path points at a project root and that the "
            "project carries either a `BRIEF.md` or `<thread>.<N>/` "
            "version dirs."
        )
        lines.append("")
        return "\n".join(lines) + "\n"

    if shape == Shape.FULLY_MIGRATED:
        lines.append("## Plan")
        lines.append("")
        lines.append(
            "Project is already in the fully-migrated shape. "
            "No actions required. Re-running `--apply` is a no-op."
        )
        lines.append("")
        return "\n".join(lines) + "\n"

    lines.append("## Plan")
    lines.append("")

    for doc in plan.documents:
        lines.append(f"### `{doc.slug}`")
        lines.append("")
        if doc.is_noop:
            lines.append("- No actions required (already migrated).")
        else:
            for rename in doc.renames:
                try:
                    src_rel = rename.source.relative_to(project_dir)
                except ValueError:
                    src_rel = rename.source
                try:
                    tgt_rel = rename.target.relative_to(project_dir)
                except ValueError:
                    tgt_rel = rename.target
                lines.append(f"- Rename: `{src_rel}` → `{tgt_rel}`")
            for rewrite in doc.content_rewrites:
                try:
                    file_rel = rewrite.file_path.relative_to(project_dir)
                except ValueError:
                    file_rel = rewrite.file_path
                lines.append(
                    f"- Content rewrite in `{file_rel}`: "
                    f"`{rewrite.old_string}` → `{rewrite.new_string}` "
                    f"({rewrite.occurrences}x)"
                )
            if doc.brief_merge is not None:
                bm = doc.brief_merge
                tl_str = ""
                if bm.target_length is not None:
                    tl_str = (
                        f", target_length=[{bm.target_length[0]}, "
                        f"{bm.target_length[1]}]"
                    )
                ro_str = ""
                if bm.rubric_overrides:
                    ro_keys = ", ".join(sorted(bm.rubric_overrides.keys()))
                    ro_str = f", rubric_overrides={{{ro_keys}}}"
                inferred_str = ""
                if bm.inferred:
                    inferred_str = ", inferred — TODO marker emitted"
                lines.append(
                    f"- BRIEF merge: add `documents:` entry "
                    f"(artifact_type={bm.artifact_type}{tl_str}{ro_str}"
                    f"{inferred_str})"
                )
            if doc.anvil_json_to_delete is not None:
                try:
                    rel = doc.anvil_json_to_delete.relative_to(project_dir)
                except ValueError:
                    rel = doc.anvil_json_to_delete
                lines.append(f"- Delete: `{rel}`")
        lines.append("")

    if plan.extra_anvil_jsons_to_delete:
        lines.append("### Stray `.anvil.json` cleanup")
        lines.append("")
        for path in plan.extra_anvil_jsons_to_delete:
            try:
                rel = path.relative_to(project_dir)
            except ValueError:
                rel = path
            lines.append(f"- Delete: `{rel}`")
        lines.append("")

    # Full proposed BRIEF text (issue #408): rendered through the SAME
    # code path the apply step writes (`render_migrate_brief` — the
    # surgical field-level merge of issue #415 when an existing BRIEF
    # carries a documents block), so the dry-run preview is
    # byte-identical to what `--apply` would write. Read-only — the
    # formatter never touches disk beyond reading the existing BRIEF
    # (the dry-run no-mutation contract holds).
    if not plan.is_noop and any(
        doc.brief_merge is not None for doc in plan.documents
    ):
        existing_text: Optional[str] = None
        if plan.project_brief_path.is_file():
            try:
                existing_text = plan.project_brief_path.read_text(
                    encoding="utf-8"
                )
            except OSError:
                existing_text = None
        rendered, merge_notes = render_migrate_brief(
            plan, existing_text=existing_text
        )
        lines.append("## Proposed `BRIEF.md`")
        lines.append("")
        lines.append("````markdown")
        lines.append(rendered.rstrip("\n"))
        lines.append("````")
        lines.append("")
        for note in merge_notes:
            lines.append(f"- Note: {note}")
        if merge_notes:
            lines.append("")

    lines.append("## Verification preview")
    lines.append("")
    lines.append(
        "After apply, the project would round-trip cleanly through "
        "`discover_thread_root` + `load_project_brief`."
    )
    lines.append("")
    return "\n".join(lines) + "\n"


def _format_apply_report(apply_result: ApplyResult) -> str:
    """Format the apply outcome as a markdown report (appended to plan report)."""
    lines: List[str] = []
    lines.append("## Apply")
    lines.append("")
    lines.append(
        f"- Applied: {len(apply_result.applied_docs)} documents "
        f"({', '.join(apply_result.applied_docs) or '(none)'})"
    )
    if apply_result.failed_docs:
        lines.append(
            f"- **Failed**: {len(apply_result.failed_docs)} documents:"
        )
        for slug, err in apply_result.failed_docs:
            lines.append(f"  - `{slug}`: {err}")
    lines.append(f"- BRIEF written: {apply_result.brief_written}")
    lines.append(f"- Git used: {apply_result.git_used}")
    lines.append("")
    return "\n".join(lines) + "\n"


def run(
    project_dir: Path,
    *,
    apply: bool = False,
    report_only: bool = False,
    artifact_type: Optional[str] = None,
) -> RunResult:
    """Execute the project-migrate flow.

    Parameters
    ----------
    project_dir
        Project root.
    apply
        When True, run the apply step after detection + planning. When
        False (the default), perform a dry-run.
    report_only
        Emit a markdown report and exit. Equivalent to dry-run for
        side-effect purposes but reflects the operator's explicit choice.
        Mutually exclusive with ``apply``.
    artifact_type
        Optional ``--artifact-type`` (issue #878; two-tier #394
        validation). Applied to every synthesized ``documents:`` entry on
        a BARE project (:data:`ProjectInventory.is_bare`) instead of the
        inferred/defaulted value — closing the bare-synthesis
        circularity where the correct declaration would otherwise come
        from the very BRIEF this run synthesizes. Has no effect on
        non-bare projects. ``None`` (the default) preserves prior
        behavior byte-for-byte.

    Returns
    -------
    A :class:`RunResult` carrying the outcome and the formatted report.

    Raises
    ------
    ValueError
        When ``apply`` and ``report_only`` are both True.
    FileNotFoundError
        When ``project_dir`` does not exist or is not a directory.
    PlanError
        When ``artifact_type`` is given but is not a registered or
        consumer-declared artifact type. Raised BEFORE any mutation.
    """
    if apply and report_only:
        raise ValueError(
            "apply and report_only are mutually exclusive; pass one or "
            "neither."
        )

    project_dir = Path(project_dir).resolve()
    if not project_dir.is_dir():
        raise FileNotFoundError(
            f"Project directory not found: {project_dir}"
        )

    inv = inventory_project(project_dir)
    shape = _classify(inv)
    plan = build_plan(
        project_dir, shape=shape, inventory=inv, artifact_type=artifact_type
    )

    result = RunResult(
        project_dir=project_dir,
        shape=shape,
        plan=plan,
    )

    report = _format_plan_report(project_dir, shape, plan)

    if shape == Shape.UNKNOWN:
        result.report = report
        result.success = False
        return result

    if not apply:
        # Dry-run / report mode — return without mutations.
        result.report = report
        result.success = True
        return result

    # Apply mode.
    apply_result = apply_plan(plan)
    result.apply_result = apply_result
    report += "\n" + _format_apply_report(apply_result)

    # Verify only if apply succeeded.
    if not apply_result.failed_docs:
        verify_result = verify_migration(project_dir)
        result.verify_result = verify_result
        report += "\n" + verify_result.to_report()
        result.success = verify_result.ok
    else:
        result.success = False

    result.report = report
    return result


# ---------------------------------------------------------------------------
# Single-file enrollment (issue #406)
# ---------------------------------------------------------------------------


def _format_enroll_report(plan: Plan) -> str:
    """Format an enrollment plan as a markdown report.

    Includes the FULL proposed BRIEF text — rendered through the same
    ``render_enroll_brief`` code path the apply step writes, so the
    preview is byte-identical to the eventual write (the surgical
    append for an existing BRIEF; the synthesized BRIEF otherwise).
    Read-only: the formatter never touches disk beyond reading the
    existing BRIEF.
    """
    project_dir = plan.project_dir
    lines: List[str] = []
    lines.append(f"# Single-file enrollment: {project_dir.name}")
    lines.append("")
    lines.append(f"**Project root**: `{project_dir}`")
    if plan.brief_mode == "append":
        lines.append(
            "**BRIEF**: existing — extended by surgical append "
            "(every pre-existing byte preserved)"
        )
    else:
        lines.append(
            "**BRIEF**: none found — a minimal project BRIEF will be "
            "synthesized (TODO markers on every inferred value)"
        )
    lines.append(f"**Documents in plan**: {len(plan.documents)}")
    lines.append("")
    lines.append("## Plan")
    lines.append("")

    for doc in plan.documents:
        lines.append(f"### `{doc.slug}`")
        lines.append("")
        for rename in doc.renames:
            try:
                src_rel = rename.source.relative_to(project_dir)
            except ValueError:
                src_rel = rename.source
            try:
                tgt_rel = rename.target.relative_to(project_dir)
            except ValueError:
                tgt_rel = rename.target
            lines.append(f"- Move: `{src_rel}` → `{tgt_rel}`")
        if doc.brief_merge is not None:
            bm = doc.brief_merge
            inferred_str = (
                ", inferred — TODO marker emitted" if bm.inferred else ""
            )
            lines.append(
                f"- BRIEF entry: add `documents:` entry "
                f"(artifact_type={bm.artifact_type}{inferred_str})"
            )
        for note in doc.notes:
            lines.append(f"- Note: {note}")
        lines.append("")

    existing_text: Optional[str] = None
    if plan.project_brief_path.is_file():
        try:
            existing_text = plan.project_brief_path.read_text(
                encoding="utf-8"
            )
        except OSError:
            existing_text = None
    rendered = render_enroll_brief(plan, existing_text=existing_text)
    lines.append("## Proposed `BRIEF.md`")
    lines.append("")
    lines.append("````markdown")
    lines.append(rendered.rstrip("\n"))
    lines.append("````")
    lines.append("")
    return "\n".join(lines) + "\n"


def _verify_enrollment(
    plan: Plan, apply_result: ApplyResult
) -> Tuple[str, bool]:
    """Post-apply verification for an enrollment plan.

    Enrollment's contract is narrower than migrate's whole-project
    shape check: for every APPLIED doc, the target body must exist and
    ``discover_thread_root`` must resolve it (guarded import); the
    BRIEF must have been written and strict-parsed (the apply step
    already rolled it back otherwise).
    """
    lines: List[str] = []
    lines.append("## Enrollment verification")
    lines.append("")
    ok = bool(apply_result.brief_written) and not apply_result.failed_docs

    applied = set(apply_result.applied_docs)
    try:
        from anvil.lib.project_discovery import discover_thread_root
    except ImportError:
        discover_thread_root = None  # type: ignore[assignment]

    for doc in plan.documents:
        if doc.slug not in applied:
            continue
        body = doc.renames[0].target if doc.renames else None
        if body is None or not body.is_file():
            lines.append(f"- `{doc.slug}`: body missing at `{body}` — FAIL")
            ok = False
            continue
        if discover_thread_root is not None:
            result = discover_thread_root(body)
            if result is None or result.slug != doc.slug:
                lines.append(
                    f"- `{doc.slug}`: `discover_thread_root` did not "
                    f"resolve `{body}` — FAIL"
                )
                ok = False
                continue
        lines.append(f"- `{doc.slug}`: enrolled — OK")

    lines.append(
        f"- BRIEF written: {'OK' if apply_result.brief_written else 'FAIL'}"
    )
    lines.append("")
    lines.append(f"**Overall**: {'PASS' if ok else 'FAIL'}")
    return "\n".join(lines) + "\n", ok


def run_enroll(
    files: Sequence[Path],
    *,
    project: Optional[Path] = None,
    slug: Optional[str] = None,
    artifact_type: Optional[str] = None,
    apply: bool = False,
) -> RunResult:
    """Execute the single-file enrollment flow (issue #406).

    Mirrors :func:`run`'s signature shape: ``apply=False`` (the
    universal default in this skill) is a dry-run — detect + plan +
    report, zero mutations.

    Parameters
    ----------
    files
        Loose ``.md`` / ``.tex`` files to enroll (one or a batch). A
        batch enrolls into one project.
    project
        Optional explicit project root (``--project``).
    slug
        Optional explicit slug (``--slug``; single file only, must be
        canonical).
    artifact_type
        Optional explicit artifact type (``--artifact-type``;
        validated against the two-tier #394 registry).
    apply
        When True, execute the plan (per-doc atomicity; BRIEF written
        for the succeeded subset).

    Raises
    ------
    EnrollError
        On any plan-time refusal (slug collision, non-md/tex input,
        already-enrolled input, malformed existing BRIEF, …). Raised
        BEFORE any mutation — the whole batch aborts.
    """
    plan = build_enroll_plan(
        files, project=project, slug=slug, artifact_type=artifact_type
    )

    result = RunResult(
        project_dir=plan.project_dir,
        shape=plan.shape,
        plan=plan,
    )
    report = _format_enroll_report(plan)

    if not apply:
        result.report = report
        result.success = True
        return result

    apply_result = apply_plan(plan)
    result.apply_result = apply_result
    report += "\n" + _format_apply_report(apply_result)

    verify_report, ok = _verify_enrollment(plan, apply_result)
    report += "\n" + verify_report
    result.success = ok
    result.report = report
    return result


# ---------------------------------------------------------------------------
# vN report-dir adoption (issue #432)
# ---------------------------------------------------------------------------


def _format_adopt_vn_report(plan: Plan, source_dir: Path) -> str:
    """Format a vN-adoption plan as a markdown report.

    Includes the FULL proposed BRIEF text — rendered through the same
    ``render_enroll_brief`` code path the apply step writes
    (brief_mode-dispatched: surgical append for an existing BRIEF,
    #408-style synthesis otherwise), so the preview is byte-identical
    to the eventual write. Read-only: the formatter never touches disk
    beyond reading the existing BRIEF.
    """
    project_dir = plan.project_dir
    lines: List[str] = []
    lines.append(f"# vN report-dir adoption: {project_dir.name}")
    lines.append("")
    lines.append(f"**Project root**: `{project_dir}`")
    lines.append(f"**vN family dir**: `{source_dir}`")
    if plan.brief_mode == "append":
        lines.append(
            "**BRIEF**: existing — extended by surgical append "
            "(every pre-existing byte preserved)"
        )
    else:
        lines.append(
            "**BRIEF**: none found — a starter project BRIEF will be "
            "synthesized (TODO markers on every inferred value)"
        )
    lines.append(f"**Documents in plan**: {len(plan.documents)}")
    lines.append("")
    lines.append("## Plan")
    lines.append("")

    if not plan.documents:
        lines.append(
            f"No `v{{N}}` family found under `{source_dir}` — nothing "
            f"to adopt. Re-running --adopt-vn on an adopted tree is a "
            f"no-op."
        )
        lines.append("")
        return "\n".join(lines) + "\n"

    for doc in plan.documents:
        lines.append(f"### `{doc.slug}`")
        lines.append("")
        for rename in doc.renames:
            try:
                src_rel = rename.source.relative_to(project_dir)
            except ValueError:
                src_rel = rename.source
            try:
                tgt_rel = rename.target.relative_to(project_dir)
            except ValueError:
                tgt_rel = rename.target
            lines.append(f"- Rename: `{src_rel}` → `{tgt_rel}`")
        if doc.brief_merge is not None:
            bm = doc.brief_merge
            inferred_str = (
                ", inferred — TODO marker emitted" if bm.inferred else ""
            )
            lines.append(
                f"- BRIEF entry: add `documents:` entry "
                f"(artifact_type={bm.artifact_type}{inferred_str})"
            )
        for note in doc.notes:
            lines.append(f"- Note: {note}")
        lines.append("")

    existing_text: Optional[str] = None
    if plan.project_brief_path.is_file():
        try:
            existing_text = plan.project_brief_path.read_text(
                encoding="utf-8"
            )
        except OSError:
            existing_text = None
    rendered = render_enroll_brief(plan, existing_text=existing_text)
    lines.append("## Proposed `BRIEF.md`")
    lines.append("")
    lines.append("````markdown")
    lines.append(rendered.rstrip("\n"))
    lines.append("````")
    lines.append("")
    return "\n".join(lines) + "\n"


def _verify_adopt_vn(
    plan: Plan, apply_result: ApplyResult
) -> Tuple[str, bool]:
    """Post-apply verification for a vN-adoption plan.

    For the adopted document: every renamed version dir must exist at
    its target and ``discover_thread_root`` must resolve it to the
    adopted slug (the #408 non-renamed-body path — discovery accepts a
    version-dir path directly; guarded import). The BRIEF must have
    been written and strict-parsed (the apply step already rolled it
    back otherwise).
    """
    lines: List[str] = []
    lines.append("## Adoption verification")
    lines.append("")
    ok = bool(apply_result.brief_written) and not apply_result.failed_docs

    applied = set(apply_result.applied_docs)
    try:
        from anvil.lib.project_discovery import discover_thread_root
    except ImportError:
        discover_thread_root = None  # type: ignore[assignment]

    for doc in plan.documents:
        if doc.slug not in applied:
            continue
        version_targets = [
            r.target
            for r in doc.renames
            if r.target.name.startswith(f"{doc.slug}.")
            and r.target.name[len(doc.slug) + 1:].isdigit()
        ]
        doc_ok = True
        for target in version_targets:
            if not target.is_dir():
                lines.append(
                    f"- `{doc.slug}`: version dir missing at "
                    f"`{target}` — FAIL"
                )
                doc_ok = False
                continue
            if discover_thread_root is not None:
                resolved = discover_thread_root(target)
                if resolved is None or resolved.slug != doc.slug:
                    lines.append(
                        f"- `{doc.slug}`: `discover_thread_root` did "
                        f"not resolve `{target}` — FAIL"
                    )
                    doc_ok = False
        if doc_ok:
            lines.append(
                f"- `{doc.slug}`: {len(version_targets)} version dirs "
                f"adopted — OK"
            )
        else:
            ok = False

    lines.append(
        f"- BRIEF written: {'OK' if apply_result.brief_written else 'FAIL'}"
    )
    lines.append("")
    lines.append(f"**Overall**: {'PASS' if ok else 'FAIL'}")
    return "\n".join(lines) + "\n", ok


def run_adopt_vn(
    directory: Path,
    *,
    slug: Optional[str] = None,
    artifact_type: Optional[str] = None,
    apply: bool = False,
) -> RunResult:
    """Execute the vN report-dir adoption flow (issue #432).

    Mirrors :func:`run_enroll`'s signature shape: ``apply=False`` (the
    universal default in this skill) is a dry-run — scan + plan +
    report, zero mutations. A directory with no ``v{N}`` family is a
    successful no-op even under ``--apply`` (idempotence).

    Parameters
    ----------
    directory
        The directory holding the ``v{N}/`` family (e.g.
        ``projects/<proj>/reports/``).
    slug
        Optional explicit slug (``--slug``; must be canonical —
        rejected, never re-sanitized). Defaults to the sanitized
        enclosing-dir name.
    artifact_type
        Optional explicit artifact type (``--artifact-type``;
        validated against the two-tier #394 registry). Defaults to
        inferred ``report`` with a TODO marker.
    apply
        When True, execute the plan (per-doc snapshot atomicity;
        enroll-style BRIEF write with strict post-write validation).

    Raises
    ------
    AdoptVnError
        On any plan-time refusal (minor-versioned oddballs, versioned
        sidecar tags, slug/target collisions, malformed existing
        BRIEF, …). Raised BEFORE any mutation.
    """
    source_dir = Path(directory).resolve()
    plan = build_adopt_vn_plan(
        source_dir, slug=slug, artifact_type=artifact_type
    )

    result = RunResult(
        project_dir=plan.project_dir,
        shape=plan.shape,
        plan=plan,
    )
    report = _format_adopt_vn_report(plan, source_dir)

    if not plan.documents:
        # No vN family — successful no-op, even under --apply.
        result.report = report
        result.success = True
        return result

    if not apply:
        result.report = report
        result.success = True
        return result

    apply_result = apply_plan(plan)
    result.apply_result = apply_result
    report += "\n" + _format_apply_report(apply_result)

    verify_report, ok = _verify_adopt_vn(plan, apply_result)
    report += "\n" + verify_report
    result.success = ok
    result.report = report
    return result


# ---------------------------------------------------------------------------
# Letter-family adoption (issue #440 — Phase 2 of #432)
# ---------------------------------------------------------------------------


def _format_adopt_family_report(plan: Plan, source_dir: Path) -> str:
    """Format a letter-family adoption plan as a markdown report.

    Includes the FULL per-directory sidecar tag resolution (every
    sidecar's old name → new name — the operator confirms the table
    against reality before ``--apply``) and the FULL proposed BRIEF
    text, rendered through the same ``render_enroll_brief`` code path
    the apply step writes (brief_mode-dispatched: surgical append for
    an existing BRIEF, #408-style synthesis otherwise), so the preview
    is byte-identical to the eventual write. Read-only: the formatter
    never touches disk beyond reading the existing BRIEF.
    """
    project_dir = plan.project_dir
    lines: List[str] = []
    lines.append(f"# Letter-family adoption: {project_dir.name}")
    lines.append("")
    lines.append(f"**Project root**: `{project_dir}`")
    lines.append(f"**Family dir**: `{source_dir}`")
    if plan.brief_mode == "append":
        lines.append(
            "**BRIEF**: existing — extended by surgical append "
            "(every pre-existing byte preserved)"
        )
    else:
        lines.append(
            "**BRIEF**: none found — a starter project BRIEF will be "
            "synthesized (TODO markers on every inferred value)"
        )
    lines.append(f"**Documents in plan**: {len(plan.documents)}")
    lines.append("")
    lines.append("## Plan")
    lines.append("")

    if not plan.documents:
        lines.append(
            f"No `{{Project}}.{{Letter}}.{{N}}` family found under "
            f"`{source_dir}` — nothing to adopt. Re-running "
            f"--adopt-family on an adopted tree is a no-op."
        )
        lines.append("")
        return "\n".join(lines) + "\n"

    for doc in plan.documents:
        lines.append(f"### `{doc.slug}`")
        lines.append("")
        for rename in doc.renames:
            try:
                src_rel = rename.source.relative_to(project_dir)
            except ValueError:
                src_rel = rename.source
            try:
                tgt_rel = rename.target.relative_to(project_dir)
            except ValueError:
                tgt_rel = rename.target
            lines.append(f"- Rename: `{src_rel}` → `{tgt_rel}`")
        if doc.brief_merge is not None:
            bm = doc.brief_merge
            lines.append(
                f"- BRIEF entry: add `documents:` entry "
                f"(artifact_type={bm.artifact_type}, invocation-wide — "
                f"TODO marker emitted)"
            )
        for note in doc.notes:
            lines.append(f"- Note: {note}")
        lines.append("")

    # Full per-directory sidecar tag resolution (the #432 curation
    # contract: the dry-run prints every old name → new name so the
    # operator confirms the table before --apply).
    resolution = list(getattr(plan, "tag_resolution", []))
    lines.append("## Sidecar tag resolution")
    lines.append("")
    if resolution:
        for slug, old_name, new_name in resolution:
            lines.append(f"- `{old_name}/` → `{new_name}/` (`{slug}`)")
    else:
        lines.append(
            "- No critic sidecars observed (sidecar-free families — "
            "--tag-map not required)."
        )
    lines.append("")

    strays = list(getattr(plan, "family_strays", []))
    if strays:
        lines.append("## Strays (left untouched)")
        lines.append("")
        for name in strays:
            lines.append(
                f"- `{name}/` (not part of the "
                f"`{{Project}}.{{Letter}}.{{N}}` family grammar)"
            )
        lines.append("")

    existing_text: Optional[str] = None
    if plan.project_brief_path.is_file():
        try:
            existing_text = plan.project_brief_path.read_text(
                encoding="utf-8"
            )
        except OSError:
            existing_text = None
    rendered = render_enroll_brief(plan, existing_text=existing_text)
    lines.append("## Proposed `BRIEF.md`")
    lines.append("")
    lines.append("````markdown")
    lines.append(rendered.rstrip("\n"))
    lines.append("````")
    lines.append("")
    return "\n".join(lines) + "\n"


def _verify_adopt_family(
    plan: Plan, apply_result: ApplyResult
) -> Tuple[str, bool]:
    """Post-apply verification for a letter-family adoption plan.

    For every applied family: each renamed version dir must exist at
    its target and ``discover_thread_root`` must resolve it to the
    family's slug (the #408 non-renamed-body path — discovery accepts
    a version-dir path directly; guarded import). The BRIEF must have
    been written and strict-parsed (the apply step already rolled it
    back otherwise). The scout-interplay criterion (post-adopt names
    pass ``find_foreign_families`` clean) is regression-locked in the
    test suite — the adopted names are dot-free slugs with single-word
    tags by construction.
    """
    lines: List[str] = []
    lines.append("## Adoption verification")
    lines.append("")
    ok = bool(apply_result.brief_written) and not apply_result.failed_docs

    applied = set(apply_result.applied_docs)
    try:
        from anvil.lib.project_discovery import discover_thread_root
    except ImportError:
        discover_thread_root = None  # type: ignore[assignment]

    for doc in plan.documents:
        if doc.slug not in applied:
            continue
        version_targets = [
            r.target
            for r in doc.renames
            if r.target.name.startswith(f"{doc.slug}.")
            and r.target.name[len(doc.slug) + 1:].isdigit()
        ]
        doc_ok = True
        for target in version_targets:
            if not target.is_dir():
                lines.append(
                    f"- `{doc.slug}`: version dir missing at "
                    f"`{target}` — FAIL"
                )
                doc_ok = False
                continue
            if discover_thread_root is not None:
                resolved = discover_thread_root(target)
                if resolved is None or resolved.slug != doc.slug:
                    lines.append(
                        f"- `{doc.slug}`: `discover_thread_root` did "
                        f"not resolve `{target}` — FAIL"
                    )
                    doc_ok = False
        if doc_ok:
            lines.append(
                f"- `{doc.slug}`: {len(version_targets)} version dirs "
                f"adopted — OK"
            )
        else:
            ok = False

    lines.append(
        f"- BRIEF written: {'OK' if apply_result.brief_written else 'FAIL'}"
    )
    lines.append("")
    lines.append(f"**Overall**: {'PASS' if ok else 'FAIL'}")
    return "\n".join(lines) + "\n", ok


def run_adopt_family(
    directory: Path,
    *,
    tag_map: Optional[Path] = None,
    artifact_type: Optional[str] = None,
    apply: bool = False,
) -> RunResult:
    """Execute the letter-family adoption flow (issue #440).

    Mirrors :func:`run_adopt_vn`'s signature shape: ``apply=False``
    (the universal default in this skill) is a dry-run — scan + plan +
    report, zero mutations. A directory with no letter family is a
    successful no-op even under ``--apply`` (idempotence).

    Parameters
    ----------
    directory
        The directory holding the flat ``{Project}.{Letter}.{N}``
        dirs (one invocation = one directory = N families, batch).
    tag_map
        Path to the ``--tag-map`` JSON file (declarative foreign→
        canonical sidecar tag mapping — REQUIRED whenever any critic
        sidecar is observed; see :func:`adopt_family.load_tag_map`).
    artifact_type
        REQUIRED ``--artifact-type`` value — validated against the
        two-tier #394 registry and applied invocation-wide with
        per-family TODO markers. There is no inferred default.
    apply
        When True, execute the plan (per-doc snapshot atomicity;
        enroll-style BRIEF write for the succeeded subset with strict
        post-write validation).

    Raises
    ------
    AdoptFamilyError
        On any plan-time refusal (missing/incomplete tag map, tag
        collisions, missing artifact type, slug/target collisions,
        malformed existing BRIEF, …). Raised BEFORE any mutation —
        the whole batch aborts.
    """
    source_dir = Path(directory).resolve()
    plan = build_adopt_family_plan(
        source_dir, tag_map_path=tag_map, artifact_type=artifact_type
    )

    result = RunResult(
        project_dir=plan.project_dir,
        shape=plan.shape,
        plan=plan,
    )
    report = _format_adopt_family_report(plan, source_dir)

    if not plan.documents:
        # No letter family — successful no-op, even under --apply.
        result.report = report
        result.success = True
        return result

    if not apply:
        result.report = report
        result.success = True
        return result

    apply_result = apply_plan(plan)
    result.apply_result = apply_result
    report += "\n" + _format_apply_report(apply_result)

    verify_report, ok = _verify_adopt_family(plan, apply_result)
    report += "\n" + verify_report
    result.success = ok
    result.report = report
    return result


# ---------------------------------------------------------------------------
# Single-file review.md → stub conversion (issue #454 — Phase 3a of #432)
# ---------------------------------------------------------------------------


@dataclass
class AdoptReviewRunResult:
    """Typed summary of a :func:`run_adopt_review` invocation.

    A separate result type from :class:`RunResult`: this mode produces no
    ``Plan`` / BRIEF / shape — it is a pure critic-sibling content
    conversion on an already-adopted tree.

    Attributes
    ----------
    directory
        The adopted-tree root.
    plan
        The (possibly empty) :class:`adopt_review.AdoptReviewPlan`.
    apply_result
        Apply outcome; ``None`` for dry-run.
    report
        The markdown report.
    success
        True iff the run completed without errors. Dry-run is always a
        success (planning never mutates); apply is a success when every
        planned conversion lands.
    """

    directory: Path
    plan: object
    apply_result: object = None
    report: str = ""
    success: bool = False


def _format_adopt_review_report(plan, directory: Path) -> str:
    """Format a stub-conversion plan as a markdown report.

    Read-only — the formatter never touches disk. Lists every planned
    conversion (the new ``_review.json`` + ``_meta.json`` and the
    PRESERVED ``review.md``) plus skipped sidecars (already recognizable
    or no ``review.md`` payload).
    """
    lines: List[str] = []
    lines.append(f"# Foreign review.md → stub conversion: {directory.name}")
    lines.append("")
    lines.append(f"**Adopted tree**: `{directory}`")
    lines.append(
        "**Mode**: Phase 3a — honest unscored-foreign STUB conversion "
        "(NO LLM, NO synthesized scores)"
    )
    lines.append(f"**Conversions in plan**: {len(plan.conversions)}")
    lines.append("")
    lines.append("## Plan")
    lines.append("")

    if not plan.conversions:
        lines.append(
            "No `review.md`-only critic sidecars found — nothing to "
            "convert. Re-running `--adopt-review` on a tree whose sidecars "
            "already carry `_review.json` is a no-op."
        )
        lines.append("")
    else:
        for conv in plan.conversions:
            try:
                rel = conv.sidecar_dir.relative_to(directory)
            except ValueError:
                rel = conv.sidecar_dir
            lines.append(f"### `{rel}/`")
            lines.append("")
            lines.append(
                f"- Write stub `_review.json` "
                f"(version_dir=`{conv.version_dir}`, "
                f"critic_id=`{conv.critic_id}`, unscored — empty scores, "
                f"null total/threshold/verdict)"
            )
            lines.append(
                "- Write `_meta.json` foreign-provenance marker "
                "(`source: foreign-adopted`, `unscored: true`)"
            )
            lines.append(
                f"- Preserve `{conv.review_filename}` byte-identical "
                f"(never renamed, never mutated)"
            )
            lines.append("")

    if plan.skipped:
        lines.append("## Skipped (left untouched)")
        lines.append("")
        for name, reason in plan.skipped:
            lines.append(f"- `{name}/` — {reason}")
        lines.append("")

    return "\n".join(lines) + "\n"


def _format_adopt_review_apply(apply_result) -> str:
    """Format the apply outcome (appended to the plan report)."""
    lines: List[str] = []
    lines.append("## Apply")
    lines.append("")
    lines.append(
        f"- Converted: {len(apply_result.converted)} sidecar(s) "
        f"({', '.join(apply_result.converted) or '(none)'})"
    )
    if apply_result.failed:
        lines.append(f"- **Failed**: {len(apply_result.failed)} sidecar(s):")
        for name, err in apply_result.failed:
            lines.append(f"  - `{name}`: {err}")
    lines.append("")
    lines.append(f"**Overall**: {'PASS' if apply_result.ok else 'FAIL'}")
    lines.append("")
    return "\n".join(lines) + "\n"


def run_adopt_review(
    directory: Path,
    *,
    apply: bool = False,
    rescore: bool = False,
    scored_reviews: Optional[dict] = None,
) -> AdoptReviewRunResult:
    """Execute the single-file ``review.md`` stub-conversion flow (#454).

    Phase 3a of the #432 adoption arc. ``apply=False`` (the universal
    default in this skill) is a dry-run — scan + plan + report, zero
    mutations. A tree with no ``review.md``-only sidecar is a successful
    no-op even under ``--apply`` (idempotence).

    NO LLM call anywhere; NO score synthesis. Each conversion writes an
    honest unscored-foreign stub ``_review.json`` + a ``_meta.json``
    provenance marker beside the verbatim-preserved ``review.md``.

    Phase 3b: operator-driven LLM rescore (``rescore=True``, issue #507)
    -------------------------------------------------------------------

    When ``rescore=True``, the mode instead PLANS which Phase-3a stubs to
    turn into real scored reviews — resolving each stub's target rubric
    (BRIEF ``documents:`` → body-filename fallback; unresolvable stubs are
    SKIPPED, never guessed). The scoring itself is an operator-driven LLM
    step that lives in the slash-command runtime (precedent:
    ``rubric-rebackport/lib/rescore.py``); the runtime reads each stub's
    verbatim ``review.md`` + resolved rubric, produces per-dimension
    scores, and hands them back as ``scored_reviews`` (a
    ``{sidecar_name: ScoredReviewInput}`` map). ``apply=True`` then writes
    the scored reviews per-sidecar atomically (flip ``unscored`` to
    ``False``, stamp the rubric fields, record lineage). A target with no
    supplied score is left as an honest stub. Dry-run (``apply=False``)
    lists what WOULD be rescored and never mutates.

    Parameters
    ----------
    directory
        An adopted-tree root (project root or a single thread root) whose
        names are already canonical (post ``--adopt-family`` /
        ``--adopt-vn``).
    apply
        When True, execute the conversions / rescores (per-sidecar atomic,
        verbatim-preserving, via ``anvil/lib/sidecar.py::staged_sidecar``).
    rescore
        When True, run the Phase-3b rescore planner/applier instead of the
        Phase-3a stub conversion.
    scored_reviews
        Only consulted when ``rescore=True`` and ``apply=True``: a
        ``{sidecar_name: ScoredReviewInput}`` map from the operator/LLM
        step. Targets absent from the map are left as honest stubs.

    Raises
    ------
    AdoptReviewError
        When ``directory`` does not exist or is not a directory.
    """
    directory = Path(directory).resolve()

    if rescore:
        return _run_rescore(
            directory, apply=apply, scored_reviews=scored_reviews or {}
        )

    plan = build_adopt_review_plan(directory)

    result = AdoptReviewRunResult(directory=directory, plan=plan)
    report = _format_adopt_review_report(plan, directory)

    if plan.is_noop or not apply:
        # No conversions, or dry-run: zero mutations.
        result.report = report
        result.success = True
        return result

    apply_result = apply_adopt_review_plan(plan)
    result.apply_result = apply_result
    report += "\n" + _format_adopt_review_apply(apply_result)
    result.success = apply_result.ok
    result.report = report
    return result


def _format_rescore_report(plan, directory: Path) -> str:
    """Format a rescore plan as a markdown report (read-only)."""
    lines: List[str] = []
    lines.append(
        f"# Foreign stub → operator-LLM rescore: {directory.name}"
    )
    lines.append("")
    lines.append(f"**Adopted tree**: `{directory}`")
    lines.append(
        "**Mode**: Phase 3b — operator-driven LLM rescore of unscored "
        "foreign stubs (the LLM scoring step runs in the slash-command "
        "runtime; this plan resolves each stub's target rubric)"
    )
    lines.append(f"**Rescorable stubs in plan**: {len(plan.targets)}")
    lines.append("")
    lines.append("## Plan")
    lines.append("")

    if not plan.targets:
        lines.append(
            "No resolvable foreign stub found — nothing to rescore. "
            "Re-running `--adopt-review --rescore` on a tree whose stubs "
            "are already rescored (or which has no Phase-3a stub) is a "
            "no-op."
        )
        lines.append("")
    else:
        for target in plan.targets:
            try:
                rel = target.sidecar_dir.relative_to(directory)
            except ValueError:
                rel = target.sidecar_dir
            lines.append(f"### `{rel}/`")
            lines.append("")
            lines.append(
                f"- Resolved skill: `{target.skill}` "
                f"(via {target.skill_source})"
            )
            lines.append(
                f"- Target rubric: `{target.rubric.id}` "
                f"(total {target.rubric.total}, advance "
                f"{target.rubric.advance_threshold})"
            )
            lines.append(
                f"- Operator/LLM step: score `{target.review_filename}` "
                f"against `{target.rubric.id}`; write scored "
                f"`_review.json` (unscored → false) + stamp "
                f"`rubric_id`/`rubric_total`/`advance_threshold` in "
                f"`_meta.json` (`rescored_from: foreign-adopted`)"
            )
            lines.append("")

    if plan.skipped:
        lines.append("## Skipped (left as honest stubs / untouched)")
        lines.append("")
        for name, reason in plan.skipped:
            lines.append(f"- `{name}/` — {reason}")
        lines.append("")

    return "\n".join(lines) + "\n"


def _format_rescore_apply(apply_result) -> str:
    """Format the rescore apply outcome (appended to the plan report)."""
    lines: List[str] = []
    lines.append("## Apply")
    lines.append("")
    lines.append(
        f"- Rescored: {len(apply_result.rescored)} sidecar(s) "
        f"({', '.join(apply_result.rescored) or '(none)'})"
    )
    if apply_result.skipped_no_input:
        lines.append(
            f"- Left as honest stubs (no operator score supplied): "
            f"{len(apply_result.skipped_no_input)} sidecar(s) "
            f"({', '.join(apply_result.skipped_no_input)})"
        )
    if apply_result.failed:
        lines.append(f"- **Failed**: {len(apply_result.failed)} sidecar(s):")
        for name, err in apply_result.failed:
            lines.append(f"  - `{name}`: {err}")
    lines.append("")
    lines.append(f"**Overall**: {'PASS' if apply_result.ok else 'FAIL'}")
    lines.append("")
    return "\n".join(lines) + "\n"


def _run_rescore(
    directory: Path, *, apply: bool, scored_reviews: dict
) -> AdoptReviewRunResult:
    """Drive the Phase-3b rescore flow (planner + optional apply)."""
    plan = build_rescore_plan(directory)
    result = AdoptReviewRunResult(directory=directory, plan=plan)
    report = _format_rescore_report(plan, directory)

    if plan.is_noop or not apply:
        result.report = report
        result.success = True
        return result

    apply_result = apply_rescore_plan(plan, scored_reviews)
    result.apply_result = apply_result
    report += "\n" + _format_rescore_apply(apply_result)
    result.success = apply_result.ok
    result.report = report
    return result


__all__ = [
    "AdoptFamilyError",
    "AdoptReviewError",
    "AdoptReviewRunResult",
    "AdoptVnError",
    "EnrollError",
    "PlanError",
    "RunResult",
    "run",
    "run_adopt_family",
    "run_adopt_review",
    "run_adopt_vn",
    "run_enroll",
]
