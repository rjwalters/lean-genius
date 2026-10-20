"""Programmatic fixture builders for `anvil:project-share` tests (issue #396).

Trees are constructed in tmp dirs rather than baked on disk (mirrors
the `project-migrate` / `rubric-rebackport` fixture discipline). Every
builder takes a parent ``root`` and returns the project root.

The canonical fixture (:func:`build_full_project`) is a #295/#296-shaped
project mirroring the studio canary's hand-built fundraise package:

- ``series-a-deck`` (deck-shaped): ``deck.md`` + ``deck.pdf`` +
  ``speaker-notes.md`` + ``exhibits/``; walk-to-highest resolution
  (versions 1–2, no ``.latest``).
- ``investment-memo`` (memo-shaped): ``investment-memo.md`` +
  ``figures/`` but NO rendered PDF; thread-root ``refs/``;
  walk-to-highest (versions 1–3).
- ``market-analysis``: versions 1–3 with a **pinned** ``.latest``
  symlink at ``market-analysis.latest → market-analysis.2`` (the
  intentional pin to a non-highest version).

Every version dir carries ``_progress.json`` + ``changelog.md`` +
``_meta.json`` bookkeeping, plus a ``.tmp-staging/`` dir on one doc;
every thread has critic siblings (``<slug>.<N>.review/`` etc.); the
project root carries a shared ``research/`` pool.
"""

from __future__ import annotations

import json
import os
from pathlib import Path
from typing import Optional


def _write(path: Path, content: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(content, encoding="utf-8")


def _write_bytes(path: Path, content: bytes) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_bytes(content)


def _bookkeeping(version_dir: Path, slug: str, n: int) -> None:
    """Anvil bookkeeping every version dir carries (strip-list targets)."""
    _write(
        version_dir / "_progress.json",
        json.dumps(
            {"version": 1, "thread": slug, "phases": {"draft": "done"}},
            indent=2,
        )
        + "\n",
    )
    _write(
        version_dir / "changelog.md",
        f"# Changelog\n\n- v{n}: internal review state for {slug}.\n",
    )
    _write(
        version_dir / "_meta.json",
        json.dumps({"rubric_id": "anvil-memo-v2-44", "total": 44}) + "\n",
    )


def _critic_sibling(thread_dir: Path, slug: str, n: int, tag: str) -> None:
    sibling = thread_dir / f"{slug}.{n}.{tag}"
    _write(
        sibling / "_review.json",
        json.dumps({"verdict": "REVISE", "score": 33}) + "\n",
    )
    _write(sibling / "_summary.md", f"# {tag} of {slug}.{n}\n\nInternal.\n")


def brief_text(
    project_name: str = "Brains for Robots",
    *,
    export_block: Optional[str] = None,
    documents_yaml: Optional[str] = None,
) -> str:
    """Render a BRIEF.md with the standard three docs (overridable)."""
    documents = documents_yaml or (
        "documents:\n"
        "  - slug: series-a-deck\n"
        "    artifact_type: deck\n"
        "  - slug: investment-memo\n"
        "    artifact_type: investment-memo\n"
        "  - slug: market-analysis\n"
        "    artifact_type: position-paper\n"
    )
    export = (export_block.rstrip("\n") + "\n") if export_block else ""
    return (
        "---\n"
        f"project: {project_name}\n"
        "audience:\n"
        "  - investors\n"
        f"{documents}"
        f"{export}"
        "---\n"
        "\n"
        f"# Brief: {project_name}\n"
        "\n"
        "Internal calibration notes that must NOT reach recipients.\n"
    )


def build_full_project(
    root: Path,
    project_name: str = "smart-actuators",
    *,
    export_block: Optional[str] = None,
) -> Path:
    """Build the canonical full-project fixture under ``root/<name>/``."""
    project = root / project_name
    project.mkdir(parents=True, exist_ok=True)
    _write(project / "BRIEF.md", brief_text(export_block=export_block))

    # --- series-a-deck: deck-shaped, walk-to-highest (v2 wins) -------------
    deck_thread = project / "series-a-deck"
    for n in (1, 2):
        vdir = deck_thread / f"series-a-deck.{n}"
        _write(vdir / "deck.md", f"# Series A deck v{n}\n\n---\n\nSlide.\n")
        _write_bytes(
            vdir / "deck.pdf", b"%PDF-1.4 fake deck pdf v" + str(n).encode()
        )
        _write(vdir / "speaker-notes.md", f"# Speaker notes v{n}\n")
        _write_bytes(vdir / "exhibits" / "market.png", b"\x89PNG deck market")
        _bookkeeping(vdir, "series-a-deck", n)
    # Sidecar staging leftovers (strip-list ".tmp*" target).
    _write(
        deck_thread / "series-a-deck.2" / ".tmp-staging" / "partial.md",
        "half-written critic output\n",
    )
    _critic_sibling(deck_thread, "series-a-deck", 2, "review")

    # --- investment-memo: memo-shaped, refs/, NO pdf, walk-to-highest ------
    memo_thread = project / "investment-memo"
    for n in (1, 2, 3):
        vdir = memo_thread / f"investment-memo.{n}"
        _write(
            vdir / "investment-memo.md",
            f"# Investment memo v{n}\n\nThesis text.\n",
        )
        _write_bytes(
            vdir / "figures" / "traction.png", b"\x89PNG memo traction"
        )
        _bookkeeping(vdir, "investment-memo", n)
    _write_bytes(
        memo_thread / "refs" / "competitor-filing.pdf", b"%PDF-1.4 ref doc"
    )
    _write(memo_thread / "refs" / "notes.md", "# Ref notes\n")
    _critic_sibling(memo_thread, "investment-memo", 3, "review")
    _critic_sibling(memo_thread, "investment-memo", 3, "audit")

    # --- market-analysis: pinned .latest symlink → v2 (non-highest) --------
    ma_thread = project / "market-analysis"
    for n in (1, 2, 3):
        vdir = ma_thread / f"market-analysis.{n}"
        _write(
            vdir / "market-analysis.md",
            f"# Market analysis v{n}\n\nBody v{n}.\n",
        )
        _write_bytes(
            vdir / "market-analysis.pdf",
            b"%PDF-1.4 market analysis v" + str(n).encode(),
        )
        _bookkeeping(vdir, "market-analysis", n)
    os.symlink(
        "market-analysis.2",
        ma_thread / "market-analysis.latest",
        target_is_directory=True,
    )
    _critic_sibling(ma_thread, "market-analysis", 3, "review")

    # --- shared research pool ----------------------------------------------
    _write(project / "research" / "industry-notes.md", "# Industry notes\n")
    _write_bytes(
        project / "research" / "sources" / "robotics-survey.pdf",
        b"%PDF-1.4 survey",
    )

    return project


def build_zero_config_project(
    root: Path, project_name: str = "smart-actuators"
) -> Path:
    """Full project with NO ``export:`` block (defaults exercised)."""
    return build_full_project(root, project_name, export_block=None)


def build_project_with_unstarted_slug(
    root: Path, project_name: str = "early-stage"
) -> Path:
    """BRIEF lists a slug with no thread dir (resolution-failure fixture).

    ``investment-memo`` is real (one version); ``unstarted-deck`` has no
    directory at all.
    """
    project = root / project_name
    project.mkdir(parents=True, exist_ok=True)
    documents = (
        "documents:\n"
        "  - slug: investment-memo\n"
        "    artifact_type: investment-memo\n"
        "  - slug: unstarted-deck\n"
        "    artifact_type: deck\n"
    )
    _write(
        project / "BRIEF.md",
        brief_text("Early Stage", documents_yaml=documents),
    )
    vdir = project / "investment-memo" / "investment-memo.1"
    _write(vdir / "investment-memo.md", "# Memo v1\n")
    _bookkeeping(vdir, "investment-memo", 1)
    return project


def build_real_latest_dir_project(
    root: Path, project_name: str = "real-latest"
) -> Path:
    """Single-doc project whose ``.latest`` is a REAL directory (no symlink)."""
    project = root / project_name
    project.mkdir(parents=True, exist_ok=True)
    documents = (
        "documents:\n"
        "  - slug: memo-thread\n"
        "    artifact_type: investment-memo\n"
    )
    _write(
        project / "BRIEF.md",
        brief_text("Real Latest", documents_yaml=documents),
    )
    thread = project / "memo-thread"
    _write(thread / "memo-thread.1" / "memo-thread.md", "# v1\n")
    latest = thread / "memo-thread.latest"
    _write(latest / "memo-thread.md", "# latest (real dir)\n")
    _bookkeeping(latest, "memo-thread", 99)
    return project


def build_dangling_symlink_project(
    root: Path, project_name: str = "dangling"
) -> Path:
    """Single-doc project with a dangling ``.latest`` symlink and no
    version dirs at all (resolution failure)."""
    project = root / project_name
    project.mkdir(parents=True, exist_ok=True)
    documents = (
        "documents:\n"
        "  - slug: ghost\n"
        "    artifact_type: investment-memo\n"
    )
    _write(project / "BRIEF.md", brief_text("Ghost", documents_yaml=documents))
    thread = project / "ghost"
    thread.mkdir(parents=True, exist_ok=True)
    os.symlink("ghost.7", thread / "ghost.latest", target_is_directory=True)
    return project


def build_project_with_dangling_citation(
    root: Path, project_name: str = "dangling-citation"
) -> Path:
    """Single-doc project whose thread body cites a project-root working
    document (``STRATEGIC-OPTIONS.md``) that is never part of the export
    set (issue #758) — a bare backticked mention AND a relative markdown
    link, both pointing at the same non-exported file. Also cites a
    sibling doc's own exported body (should NOT be flagged) and a
    filename that doesn't exist anywhere (should NOT be flagged either).
    """
    project = root / project_name
    project.mkdir(parents=True, exist_ok=True)
    documents = (
        "documents:\n"
        "  - slug: investment-memo\n"
        "    artifact_type: investment-memo\n"
        "  - slug: kill-thresholds\n"
        "    artifact_type: investment-memo\n"
    )
    _write(
        project / "BRIEF.md",
        brief_text("Dangling Citation", documents_yaml=documents),
    )
    _write(
        project / "STRATEGIC-OPTIONS.md",
        "# Strategic options\n\nInternal working notes — NOT for export.\n",
    )

    memo_vdir = project / "investment-memo" / "investment-memo.1"
    _write(
        memo_vdir / "investment-memo.md",
        "# Investment memo v1\n\n"
        "See the kill thresholds discussion in `STRATEGIC-OPTIONS.md` for "
        "context. This mentions `not-a-real-file.md`, which doesn't exist "
        "anywhere and should not be flagged.\n",
    )
    _bookkeeping(memo_vdir, "investment-memo", 1)

    kill_vdir = project / "kill-thresholds" / "kill-thresholds.1"
    _write(
        kill_vdir / "kill-thresholds.md",
        "# Kill thresholds v1\n\n"
        "Cross-reference: [strategic options]"
        "(../../STRATEGIC-OPTIONS.md).\n"
        "Also see [the investment memo]"
        "(../../investment-memo/investment-memo.1/investment-memo.md), "
        "which IS part of this export.\n",
    )
    _bookkeeping(kill_vdir, "kill-thresholds", 1)

    return project


__all__ = [
    "brief_text",
    "build_dangling_symlink_project",
    "build_full_project",
    "build_project_with_dangling_citation",
    "build_project_with_unstarted_slug",
    "build_real_latest_dir_project",
    "build_zero_config_project",
]
