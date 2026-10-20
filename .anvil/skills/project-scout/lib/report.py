"""Deterministic report rendering for `anvil:project-scout` (issue #407).

Two surfaces:

- :func:`render_markdown` — the operator-facing report (stdout by
  default; ``--report <path>`` writes it).
- :func:`build_json` — the versioned machine-readable sidecar
  (``schema_version: 1``) for future pipeline composition.

Both are **deterministic**: sorted paths, no timestamps — two runs over
the same tree are byte-identical, so tests can golden-file the output
and the second-run determinism check comes for free.

Honest-coverage rule: every pruned subtree (default exclude, dotdir, or
operator glob) is named; the coverage table carries the identity
``candidate_files == in_clusters + loose_classified + not_document``.
"""

from __future__ import annotations

from typing import List

from .cluster import (
    BUCKET_ALREADY_MIGRATED,
    BUCKET_BARE_THREADS,
    BUCKET_FOREIGN_GRAMMAR,
    BUCKET_LEGACY_MIGRATABLE,
    BUCKET_LOOSE_DOCUMENTS,
    Classification,
    Cluster,
)
from .walk import DEFAULT_EXCLUDES, WalkResult


SCHEMA_VERSION = 1

# Section order in the markdown report.
_BUCKET_ORDER = (
    BUCKET_LEGACY_MIGRATABLE,
    BUCKET_BARE_THREADS,
    BUCKET_LOOSE_DOCUMENTS,
    BUCKET_FOREIGN_GRAMMAR,
    BUCKET_ALREADY_MIGRATED,
)

_BUCKET_TITLES = {
    BUCKET_LEGACY_MIGRATABLE: "LEGACY_MIGRATABLE — run project-migrate",
    BUCKET_BARE_THREADS: "BARE_THREADS — run project-migrate "
    "(BRIEF synthesized)",
    BUCKET_LOOSE_DOCUMENTS: "LOOSE_DOCUMENTS — enroll candidates",
    BUCKET_FOREIGN_GRAMMAR: "FOREIGN_GRAMMAR — report-only",
    BUCKET_ALREADY_MIGRATED: "ALREADY_MIGRATED — nothing to do",
}


def _md_cluster(lines: List[str], c: Cluster) -> None:
    lines.append(f"### `{c.rel}`")
    lines.append("")
    if c.detected_shape:
        shape = c.detected_shape
        if c.is_bare:
            shape += " (bare)"
        lines.append(f"- detected shape: `{shape}`")
    if c.threads:
        for t in c.threads:
            versions = ", ".join(str(n) for n in t["versions"])
            lines.append(f"- thread `{t['slug']}` — versions [{versions}]")
    for ff in c.foreign_families:
        versions = ", ".join(str(n) for n in ff.versions)
        lines.append(
            f"- foreign family `{ff.stem}` — versions [{versions}]"
        )
        for why in ff.why:
            lines.append(f"  - why: {why}")
        for sc in ff.sidecars:
            lines.append(f"  - sidecar: `{sc}`")
    if c.recommended_command:
        lines.append(f"- recommended: `{c.recommended_command}`")
    lines.append(f"- confidence: {c.confidence}")
    for e in c.evidence:
        lines.append(f"- evidence: {e}")
    for n in c.notes:
        lines.append(f"- note: {n}")
    for doc in c.loose_documents:
        lines.append(f"- loose document `{doc.rel}` ({doc.confidence})")
        if doc.recommended_command:
            lines.append(f"  - recommended: `{doc.recommended_command}`")
        for n in doc.notes:
            lines.append(f"  - note: {n}")
        lines.append(
            "  - signals: " + ", ".join(doc.signals)
        )
    lines.append("")


def render_markdown(
    wr: WalkResult,
    cls: Classification,
    verbose: bool = False,
) -> str:
    """Render the operator-facing markdown report. Deterministic."""
    lines: List[str] = []
    lines.append("# anvil:project-scout report")
    lines.append("")
    lines.append(f"- root: `{wr.root}`")
    lines.append(
        "- include: "
        + (", ".join(f"`{g}`" for g in wr.include) if wr.include else "(none)")
    )
    lines.append(
        "- exclude: "
        + (", ".join(f"`{g}`" for g in wr.exclude) if wr.exclude else "(none)")
    )
    lines.append(
        "- default excludes: "
        + ", ".join(f"`{d}`" for d in DEFAULT_EXCLUDES)
    )
    lines.append("")

    for bucket in _BUCKET_ORDER:
        members = [c for c in cls.clusters if c.bucket == bucket]
        lines.append(
            f"## {_BUCKET_TITLES[bucket]} ({len(members)} cluster"
            f"{'s' if len(members) != 1 else ''})"
        )
        lines.append("")
        if not members:
            lines.append("(none)")
            lines.append("")
        for c in members:
            _md_cluster(lines, c)

    # NOT_DOCUMENT — counted, listed only under --verbose.
    lines.append(
        f"## NOT_DOCUMENT ({len(cls.not_document_files)} file"
        f"{'s' if len(cls.not_document_files) != 1 else ''}, "
        f"counted{'' if verbose else ', not listed; use --verbose'})"
    )
    lines.append("")
    if verbose:
        for nd in cls.not_document_files:
            lines.append(
                f"- `{nd.rel}` — " + ", ".join(nd.signals)
            )
        if not cls.not_document_files:
            lines.append("(none)")
        lines.append("")
    else:
        lines.append("")

    if cls.diagnostics:
        lines.append("## Diagnostics")
        lines.append("")
        for d in cls.diagnostics:
            lines.append(f"- {d}")
        lines.append("")

    # Honest coverage: pruned subtrees are named, never silent.
    lines.append(
        f"## Pruned subtrees ({len(wr.pruned_subtrees)})"
    )
    lines.append("")
    for p in wr.pruned_subtrees:
        rel = p.path.relative_to(wr.root).as_posix()
        lines.append(f"- `{rel}` ({p.reason})")
    if not wr.pruned_subtrees:
        lines.append("(none)")
    lines.append("")

    cov = cls.coverage
    lines.append("## Coverage")
    lines.append("")
    lines.append("| metric | count |")
    lines.append("|---|---|")
    lines.append(f"| directories scanned | {cov.dirs_scanned} |")
    lines.append(f"| candidate files (.md/.tex) | {cov.candidate_files} |")
    lines.append(f"| claimed by clusters | {cov.in_clusters} |")
    lines.append(f"| loose documents classified | {cov.loose_classified} |")
    lines.append(f"| not-document | {cov.not_document} |")
    lines.append(f"| pruned subtrees | {cov.pruned_subtrees} |")
    lines.append("")
    lines.append(
        "Coverage identity: candidate_files == in_clusters + "
        f"loose_classified + not_document — "
        f"{'holds' if cov.identity_holds else 'VIOLATED'} "
        f"({cov.candidate_files} == {cov.in_clusters} + "
        f"{cov.loose_classified} + {cov.not_document})."
    )
    lines.append("")
    return "\n".join(lines)


def build_json(
    wr: WalkResult,
    cls: Classification,
    verbose: bool = False,
) -> dict:
    """Build the versioned JSON sidecar. Deterministic (sorted, no times)."""
    clusters = []
    for c in cls.clusters:
        clusters.append(
            {
                "path": c.rel,
                "bucket": c.bucket,
                "detected_shape": c.detected_shape,
                "is_bare": c.is_bare,
                "threads": c.threads,
                "recommended_command": c.recommended_command,
                "confidence": c.confidence,
                "evidence": c.evidence,
                "notes": c.notes,
                "loose_documents": [d.rel for d in c.loose_documents],
            }
        )
    foreign = []
    for c in cls.clusters:
        if c.bucket != BUCKET_FOREIGN_GRAMMAR:
            continue
        foreign.append(
            {
                "path": c.rel,
                "families": [
                    {
                        "stem": ff.stem,
                        "versions": ff.versions,
                        "sidecars": ff.sidecars,
                        "why": ff.why,
                    }
                    for ff in c.foreign_families
                ],
            }
        )
    cov = cls.coverage
    return {
        "schema_version": SCHEMA_VERSION,
        "root": str(wr.root),
        "filters": {
            "include": list(wr.include),
            "exclude": list(wr.exclude),
            "default_excludes": list(DEFAULT_EXCLUDES),
            "pruned_subtrees": [
                {
                    "path": p.path.relative_to(wr.root).as_posix(),
                    "reason": p.reason,
                }
                for p in wr.pruned_subtrees
            ],
        },
        "clusters": clusters,
        "loose_documents": [
            {
                "path": d.rel,
                "enclosing_cluster": d.enclosing_cluster,
                "confidence": d.confidence,
                "signals": d.signals,
                "recommended_command": d.recommended_command,
                "notes": d.notes,
            }
            for d in cls.loose_documents
        ],
        "foreign_grammar": foreign,
        "not_document": {
            "count": len(cls.not_document_files),
            "paths": (
                [nd.rel for nd in cls.not_document_files] if verbose else []
            ),
        },
        "diagnostics": cls.diagnostics,
        "coverage": {
            "dirs_scanned": cov.dirs_scanned,
            "candidate_files": cov.candidate_files,
            "in_clusters": cov.in_clusters,
            "loose_classified": cov.loose_classified,
            "not_document": cov.not_document,
            "pruned_subtrees": cov.pruned_subtrees,
        },
    }


__all__ = ["SCHEMA_VERSION", "build_json", "render_markdown"]
