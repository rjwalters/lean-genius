"""Programmatic fixture trees for `anvil:project-scout` tests (issue #407).

One builder per taxonomy bucket, plus the mega tree composing all of
them under one root with default-excluded noise (``node_modules/``) and
a doc-site subtree (mkdocs marker) for exclude/coverage/SHA tests.
"""

from __future__ import annotations

from pathlib import Path


def _write(path: Path, content: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(content, encoding="utf-8")


# ---------------------------------------------------------------------------
# Bucket fixtures
# ---------------------------------------------------------------------------


def build_migrated_project(
    root: Path, project_name: str = "migrated-project"
) -> Path:
    """Post-#296 canonical shape → ALREADY_MIGRATED.

    ``BRIEF.md`` + ``<slug>/<slug>.N/<slug>.md`` nesting, no
    ``.anvil.json`` anywhere.
    """
    project = root / project_name
    _write(
        project / "BRIEF.md",
        "---\n"
        "project: migrated-project\n"
        "documents:\n"
        "  - slug: alpha-memo\n"
        "    artifact_type: investment-memo\n"
        "---\n\n# Project BRIEF\n",
    )
    for n in (1, 2):
        _write(
            project / "alpha-memo" / f"alpha-memo.{n}" / "alpha-memo.md",
            f"# Alpha memo v{n}\n\nBody prose.\n",
        )
    _write(
        project / "alpha-memo" / "alpha-memo.2.review" / "verdict.md",
        "# Verdict\n",
    )
    _write(project / "research" / "notes.md", "# Research notes\n")
    return project


def build_classic_project(
    root: Path, project_name: str = "classic-project"
) -> Path:
    """Pre-#283 classic shape → LEGACY_MIGRATABLE.

    ``memo.N/`` directly under the project root + a root ``.anvil.json``,
    no project BRIEF.
    """
    project = root / project_name
    for n in (1, 2, 3):
        _write(
            project / f"memo.{n}" / "memo.md",
            f"# Classic memo v{n}\n\nBody prose.\n",
        )
    _write(project / "memo.3.review" / "verdict.md", "# Verdict\n")
    _write(project / ".anvil.json", '{"artifact_type": "memo"}\n')
    return project


def build_bare_threads(
    root: Path,
    project_name: str = "bare-paper",
    slug: str = "bispectral-imaging",
) -> Path:
    """Bare version-dir threads (issue #408 shape) → BARE_THREADS.

    Mirrors project-migrate's ``build_bare_version_dir_threads``: ``.tex``
    bodies, deliberate version gaps ({1,3,4,5,6,7} — no ``.2``), mixed
    hand-rolled ``.review`` / ``.audit`` sidecars, ZERO anvil config.
    """
    project = root / project_name
    for n in (1, 3, 4, 5, 6, 7):
        _write(
            project / f"{slug}.{n}" / "paper.tex",
            "\\documentclass{article}\n"
            "\\begin{document}\n"
            f"Bispectral imaging draft v{n}.\n"
            "\\end{document}\n",
        )
    for n in (3, 4):
        _write(
            project / f"{slug}.{n}.review" / "review.md",
            f"# Review of draft v{n}\n\nHand-rolled reviewer notes.\n",
        )
    _write(
        project / f"{slug}.6.audit" / "audit.md",
        "# Audit of draft v6\n\nHand-rolled audit notes.\n",
    )
    _write(
        project / "paper.tex",
        "\\documentclass{article}\n% build entrypoint\n",
    )
    _write(project / "figures" / "fig1.png", "PNG-PLACEHOLDER\n")
    return project


def build_loose_docs_dir(
    root: Path, dir_name: str = "corp-docs"
) -> Path:
    """Loose-document directory → LOOSE_DOCUMENTS + NOT_DOCUMENT split.

    Dated loose docs + a frontmatter'd analysis, PLUS hard-negative
    repo files (``README.md`` / ``CHANGELOG.md`` / ``adr/0001-*.md``) in
    the same tree.
    """
    d = root / dir_name
    prose = ("Plain paragraph prose. " * 20).strip() + "\n"
    _write(
        d / "2026-05-19-board-update.md",
        "# Board update\n\n" + prose,
    )
    _write(
        d / "competitive-landscape-2026-05-20.md",
        "# Competitive landscape\n\n" + prose,
    )
    _write(
        d / "analysis" / "tam-analysis.md",
        "---\ntitle: TAM analysis\nauthor: Operator\n"
        "date: 2026-05-21\n---\n\n# TAM analysis\n\n" + prose,
    )
    _write(d / "README.md", "# corp-docs\n\nWhat lives here.\n")
    _write(d / "CHANGELOG.md", "# Changelog\n\n- v1\n")
    _write(
        d / "adr" / "0001-use-postgres.md",
        "# 1. Use Postgres\n\nStatus: accepted.\n" + prose,
    )
    return d


def build_foreign_grammar(
    root: Path, project_name: str = "foreign-whitepapers"
) -> Path:
    """The empirically verified foreign shape → FOREIGN_GRAMMAR.

    ``Whitepaper.<letter>.<N>`` families + ``.review-v2`` / ``.audit-v2``
    sidecar variants, ``paper.md`` bodies. Verified at curation: today's
    ``detect_shape`` returns PRE_283_CLASSIC on this tree (the greedy
    ``_VERSION_DIR_RE`` matches ``Whitepaper.A.3`` with stem
    ``Whitepaper.A``) — the regression the first scout test locks.
    """
    project = root / project_name
    for name in ("Whitepaper.A.1", "Whitepaper.A.2", "Whitepaper.B.1"):
        _write(
            project / name / "paper.md",
            f"# {name}\n\nForeign-grammar whitepaper body.\n",
        )
    _write(
        project / "Whitepaper.A.2.review-v2" / "review.md",
        "# Review v2\n",
    )
    _write(
        project / "Whitepaper.B.1.audit-v2" / "audit.md",
        "# Audit v2\n",
    )
    return project


def build_foreign_mixed(
    root: Path, project_name: str = "mixed-foreign"
) -> Path:
    """Foreign + clean families under ONE root → FOREIGN_GRAMMAR (whole root)."""
    project = build_foreign_grammar(root, project_name)
    for n in (1, 2):
        _write(
            project / f"clean-memo.{n}" / "memo.md",
            f"# Clean memo v{n}\n",
        )
    return project


# ---------------------------------------------------------------------------
# Composite fixtures
# ---------------------------------------------------------------------------


def build_nested_under_brief(root: Path) -> Path:
    """BRIEF-bearing root with a descendant flat family → one merged cluster.

    ``<project>/BRIEF.md`` + ``<project>/sub/draft.N`` — the descendant
    candidate merges upward into the BRIEF-bearing ancestor.
    """
    project = root / "brief-anchored"
    _write(
        project / "BRIEF.md",
        "---\nproject: brief-anchored\ndocuments:\n"
        "  - slug: main-memo\n---\n\n# BRIEF\n",
    )
    _write(
        project / "main-memo" / "main-memo.1" / "main-memo.md",
        "# Main memo v1\n",
    )
    for n in (1, 2):
        _write(
            project / "sub" / f"draft.{n}" / "draft.md",
            f"# Sub draft v{n}\n",
        )
    return project


def build_briefless_nest(root: Path) -> Path:
    """Two BRIEF-less candidates, one a descendant of the other → TWO clusters."""
    outer = root / "briefless-outer"
    for n in (1, 2):
        _write(outer / f"memo.{n}" / "memo.md", f"# Outer v{n}\n")
    inner = outer / "inner"
    for n in (1, 2):
        _write(inner / f"notes.{n}" / "notes.md", f"# Inner v{n}\n")
    return outer


def build_doc_site(root: Path, dir_name: str = "docs-site") -> Path:
    """An mkdocs doc site — every page is a hard-negative NOT_DOCUMENT."""
    d = root / dir_name
    _write(d / "mkdocs.yml", "site_name: docs\n")
    for i in range(5):
        _write(
            d / "docs" / f"page-{i}.md",
            f"# Page {i}\n\nDoc-site page prose. " * 5 + "\n",
        )
    return d


def build_mega_tree(root: Path) -> Path:
    """Everything under one root, plus noise, for coverage/SHA/exclude tests."""
    build_migrated_project(root)
    build_classic_project(root)
    build_bare_threads(root)
    build_loose_docs_dir(root)
    build_foreign_grammar(root)
    build_doc_site(root)
    # Default-excluded noise — must be pruned AND named in the report.
    _write(
        root / "node_modules" / "leftpad" / "README.md",
        "# leftpad\n",
    )
    # A loose doc inside the migrated cluster's subtree — first-class
    # enroll candidate listed under that cluster.
    _write(
        root / "migrated-project" / "2026-06-01-followup.md",
        "# Followup\n\n" + ("Cluster-local loose prose. " * 20) + "\n",
    )
    # Ordinary engineering docs at the root — NOT_DOCUMENT.
    _write(root / "README.md", "# mega\n")
    _write(root / "CONTRIBUTING.md", "# Contributing\n")
    return root
