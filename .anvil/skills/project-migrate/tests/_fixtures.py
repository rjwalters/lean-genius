"""Programmatic fixture builders for `anvil:project-migrate` tests (issue #297).

The skill's fixtures are tree shapes the tests construct in tmp dirs
rather than baked-on-disk snapshots. This keeps the repo small and the
fixtures readable next to the tests that consume them.

Each builder takes a parent ``tmp_path`` and a project name and produces
the full project tree, returning the project root.

Builders match the three on-disk shapes the detector recognizes:

- ``build_pre_283_classic`` — `memo.N/` siblings directly under project
  root, no project BRIEF, `memo.md` body.
- ``build_post_283_anvil_json`` — `<project>/BRIEF.md` + `<slug>/<slug>.N/`
  with `.anvil.json` (per-thread or root) and possibly `memo.md` bodies.
- ``build_fully_migrated`` — target shape (everything correct).
- ``build_foundry_shaped`` — sanitized multi-thread snapshot exercising
  the canary case (multiple memo.N versions + critic siblings).
"""

from __future__ import annotations

import json
import textwrap
from pathlib import Path
from typing import Optional


def _write(path: Path, content: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(content, encoding="utf-8")


def build_pre_283_classic(
    root: Path,
    project_name: str = "acme-investment",
    *,
    n_versions: int = 3,
) -> Path:
    """Build a pre-#283 classic project under ``root/<project_name>/``.

    Shape:
      <project>/
        memo.1/memo.md
        memo.2/memo.md
        memo.3/memo.md
        .anvil.json
        BRIEF.md            ← optional, per-thread brief (NOT a project BRIEF)

    Returns the project root path.
    """
    project_dir = root / project_name
    project_dir.mkdir(parents=True, exist_ok=True)
    for n in range(1, n_versions + 1):
        version_dir = project_dir / f"memo.{n}"
        _write(
            version_dir / "memo.md",
            f"# memo version {n}\n\nSee memo.{n - 1} for prior context.\n"
            if n > 1
            else f"# memo version {n}\n\nFirst draft.\n",
        )
        _write(
            version_dir / "_progress.json",
            json.dumps(
                {
                    "version": 1,
                    "thread": "memo",
                    "phases": {"draft": {"state": "done"}},
                },
                indent=2,
            ) + "\n",
        )
    # Per-thread BRIEF.md (no documents: key — not a project BRIEF).
    brief_text = (
        "---\n"
        f"company: {project_name}\n"
        "sector: TODO\n"
        "---\n"
        "\n"
        f"# Brief: {project_name}\n"
        "\n"
        "Free-form per-thread brief from the pre-#283 era.\n"
    )
    _write(project_dir / "BRIEF.md", brief_text)
    _write(
        project_dir / ".anvil.json",
        json.dumps(
            {
                "max_iterations": 4,
                "target_length": {"words": [8000, 11000]},
            },
            indent=2,
        ) + "\n",
    )
    return project_dir


def build_post_283_anvil_json(
    root: Path,
    project_name: str = "smart-actuators",
    *,
    slugs: Optional[list] = None,
) -> Path:
    """Build a post-#283 project with `.anvil.json` files.

    Shape:
      <project>/
        BRIEF.md            ← project BRIEF with documents: list
        investment-memo/
          investment-memo.1/memo.md   ← skill-fixed body filename
          investment-memo.2/memo.md
          .anvil.json                  ← per-thread config
        latency-wall/
          latency-wall.1/memo.md
          .anvil.json
    """
    project_dir = root / project_name
    project_dir.mkdir(parents=True, exist_ok=True)
    if slugs is None:
        slugs = ["investment-memo", "latency-wall"]

    # Project BRIEF — has documents: but missing per-doc config.
    doc_lines: list = []
    for s in slugs:
        doc_lines.append(f"  - slug: {s}")
        doc_lines.append(f"    artifact_type: investment-memo")
    documents_yaml = "\n".join(doc_lines)
    brief_text = (
        "---\n"
        f"project: {project_name}\n"
        "audience:\n"
        "  - Operator\n"
        "hard_rules: []\n"
        "documents:\n"
        f"{documents_yaml}\n"
        "---\n"
        "\n"
        "# Project BRIEF\n"
    )
    _write(project_dir / "BRIEF.md", brief_text)

    for slug in slugs:
        slug_dir = project_dir / slug
        # Two version dirs per thread by default.
        for n in (1, 2):
            version_dir = slug_dir / f"{slug}.{n}"
            _write(
                version_dir / "memo.md",
                f"# {slug} v{n}\n\nBody for {slug}.\n",
            )
            _write(
                version_dir / "_progress.json",
                json.dumps(
                    {
                        "version": 1,
                        "thread": slug,
                        "phases": {"draft": {"state": "done"}},
                    },
                    indent=2,
                ) + "\n",
            )
        # Per-thread .anvil.json
        _write(
            slug_dir / ".anvil.json",
            json.dumps(
                {
                    "max_iterations": 4,
                    "target_length": {"words": [5000, 8000]},
                    "rubric_overrides": {
                        "memo_subtype": "synthesis-brief",
                        "dim_1_calibration": "Calibration text for dim 1.",
                    },
                },
                indent=2,
            ) + "\n",
        )
    return project_dir


def build_fully_migrated(
    root: Path,
    project_name: str = "smart-actuators-migrated",
    *,
    slugs: Optional[list] = None,
) -> Path:
    """Build a fully-migrated project.

    Shape:
      <project>/
        BRIEF.md             ← project BRIEF absorbing all config
        investment-memo/
          investment-memo.1/investment-memo.md
          investment-memo.2/investment-memo.md
        latency-wall/
          latency-wall.1/latency-wall.md
    """
    project_dir = root / project_name
    project_dir.mkdir(parents=True, exist_ok=True)
    if slugs is None:
        slugs = ["investment-memo", "latency-wall"]

    # Build documents YAML with target_length + rubric_overrides absorbed.
    doc_lines: list = []
    for s in slugs:
        doc_lines.append(f"  - slug: {s}")
        doc_lines.append(f"    artifact_type: investment-memo")
        doc_lines.append(f"    target_length: {{ words: [5000, 8000] }}")
        doc_lines.append(f"    rubric_overrides:")
        doc_lines.append(f"      memo_subtype: synthesis-brief")
        doc_lines.append(f"      dim_1_calibration: \"Calibration text for dim 1.\"")
    documents_yaml = "\n".join(doc_lines)
    brief_text = (
        "---\n"
        f"project: {project_name}\n"
        "audience:\n"
        "  - Operator\n"
        "hard_rules: []\n"
        "documents:\n"
        f"{documents_yaml}\n"
        "---\n"
        "\n"
        "# Project BRIEF\n"
    )
    _write(project_dir / "BRIEF.md", brief_text)

    for slug in slugs:
        slug_dir = project_dir / slug
        for n in (1, 2):
            version_dir = slug_dir / f"{slug}.{n}"
            _write(
                version_dir / f"{slug}.md",
                f"# {slug} v{n}\n\nBody for {slug}.\n",
            )
            _write(
                version_dir / "_progress.json",
                json.dumps(
                    {
                        "version": 1,
                        "thread": slug,
                        "phases": {"draft": {"state": "done"}},
                    },
                    indent=2,
                ) + "\n",
            )
    return project_dir


def build_foundry_shaped(
    root: Path, project_name: str = "foundry"
) -> Path:
    """Build a sanitized foundry-shaped pre-#283 snapshot.

    Multiple memo.N versions with critic siblings (review and audit dirs)
    to exercise the canary case where critic siblings need renaming
    alongside their version dirs.

    Shape:
      foundry/
        memo.1/memo.md
        memo.1.review/verdict.md
        memo.2/memo.md
        memo.2.review/verdict.md
        memo.2.audit/findings.md
        memo.3/memo.md
        memo.3.review/verdict.md
        .anvil.json
    """
    project_dir = root / project_name
    project_dir.mkdir(parents=True, exist_ok=True)
    for n in (1, 2, 3):
        version_dir = project_dir / f"memo.{n}"
        body_text = f"# foundry memo v{n}\n\n"
        if n == 3:
            # Add a cross-thread reference to memo.2 to exercise rewriting.
            body_text += (
                "See `memo.2` §3 for the original framing. The memo.1 "
                "draft is preserved at `memo.1/memo.md`.\n"
            )
        _write(version_dir / "memo.md", body_text)
        _write(
            version_dir / "_progress.json",
            json.dumps(
                {
                    "version": 1,
                    "thread": "memo",
                    "phases": {"draft": {"state": "done"}},
                },
                indent=2,
            ) + "\n",
        )
        # Review sibling.
        review_dir = project_dir / f"memo.{n}.review"
        _write(
            review_dir / "verdict.md",
            f"# Review of memo.{n}\n\nVerdict: advance.\n",
        )
        _write(
            review_dir / "_meta.json",
            json.dumps(
                {"critic": "reviewer", "scorecard_kind": "human-verdict"},
                indent=2,
            ) + "\n",
        )
    # Add an audit sibling on memo.2.
    audit_dir = project_dir / "memo.2.audit"
    _write(audit_dir / "findings.md", "# Audit\n\nClean.\n")
    # Project-level .anvil.json (pre-#283 layout).
    _write(
        project_dir / ".anvil.json",
        json.dumps(
            {
                "max_iterations": 4,
                "target_length": {"words": [8000, 11000]},
            },
            indent=2,
        ) + "\n",
    )
    return project_dir


def build_beacon_shaped_deck(
    root: Path,
    project_name: str = "smart-actuators",
    *,
    thread: str = "series-a-deck",
    with_project_brief: bool = False,
) -> Path:
    """Build a nested-but-flat deck project (issue #382).

    Sanitized snapshot of the studio canary's pre-``2cf3f37`` deck
    thread: a thread-root directory carrying the thread-level BRIEF,
    refs/, assets/, and the per-thread ``.anvil.json`` (the deck
    iteration-cap-rationale carrier), with the version dirs and critic
    siblings sitting FLAT at the project root.

    Shape:
      <project>/
        series-a-deck/
          BRIEF.md             ← thread-level deck brief (no documents:)
          refs/transcript-founder.md
          assets/logo.png
          .anvil.json          ← paired max_iterations + rationale
        series-a-deck.1/
          deck.md              ← Marp source (retained body filename)
          speaker-notes.md
          _progress.json
        series-a-deck.1.review/verdict.md
        series-a-deck.2/deck.md + speaker-notes.md
        series-a-deck.2.design/findings.md

    Migration target: ``<project>/series-a-deck/series-a-deck.N/`` with
    the thread-root contents (BRIEF/refs/assets) staying in place and
    the ``.anvil.json`` merged into the project BRIEF.

    When ``with_project_brief`` is True, a project-level BRIEF.md with a
    ``documents:`` list (naming only the deck thread) is also written —
    this exercises the POST_283 mixed-grammar dispatch (a flat thread in
    a BRIEF-bearing project).
    """
    project_dir = root / project_name
    project_dir.mkdir(parents=True, exist_ok=True)

    thread_root = project_dir / thread
    _write(
        thread_root / "BRIEF.md",
        "---\n"
        "company: Beacon Robotics\n"
        "stage: series-a\n"
        "---\n"
        "\n"
        f"# Brief: {thread}\n"
        "\n"
        "Thread-level deck brief (intake output).\n",
    )
    _write(
        thread_root / "refs" / "transcript-founder.md",
        "# Founder transcript\n\nQuote substrate.\n",
    )
    _write(thread_root / "assets" / "logo.png", "PNG-PLACEHOLDER\n")
    _write(
        thread_root / ".anvil.json",
        json.dumps(
            {
                "max_iterations": 6,
                "iteration_cap_rationale": (
                    "Well-conditioned thread: trajectory v1-v4 "
                    "monotonically improving; one extra pass to land "
                    "the outcome detail."
                ),
            },
            indent=2,
        ) + "\n",
    )

    for n in (1, 2):
        version_dir = project_dir / f"{thread}.{n}"
        _write(
            version_dir / "deck.md",
            f"---\nmarp: true\n---\n\n# {thread} v{n}\n\n---\n\n## Ask\n",
        )
        _write(
            version_dir / "speaker-notes.md",
            f"# Speaker notes v{n}\n",
        )
        _write(
            version_dir / "_progress.json",
            json.dumps(
                {
                    "version": 1,
                    "thread": thread,
                    "phases": {"draft": {"state": "done"}},
                },
                indent=2,
            ) + "\n",
        )
    _write(
        project_dir / f"{thread}.1.review" / "verdict.md",
        f"# Review of {thread}.1\n\nVerdict: revise.\n",
    )
    _write(
        project_dir / f"{thread}.2.design" / "findings.md",
        "# Design findings\n\nClean.\n",
    )

    if with_project_brief:
        _write(
            project_dir / "BRIEF.md",
            "---\n"
            f"project: {project_name}\n"
            "audience: []\n"
            "hard_rules: []\n"
            "documents:\n"
            f"  - slug: {thread}\n"
            "    artifact_type: investment-memo\n"
            "---\n"
            "\n"
            "# Project BRIEF\n",
        )

    return project_dir


def build_mixed_memo_deck_proposal(
    root: Path,
    project_name: str = "mixed-project",
) -> Path:
    """Build the mixed-skill canary case (issue #382).

    One project root with three pre-#295 flat threads:

    - ``beacon`` — memo thread (``beacon.N/memo.md`` + review sibling;
      skill-fixed body needs the slug-echo rename).
    - ``series-a-deck`` — deck thread in the nested-but-flat shape
      (thread root with BRIEF/refs/assets/.anvil.json as a sibling of
      flat ``series-a-deck.N/`` version dirs; ``deck.md`` body
      retained).
    - ``gossamer-lan`` — proposal thread (thread root with BRIEF/refs
      as a sibling of flat ``gossamer-lan.N/`` version dirs;
      ``proposal.tex`` body retained).

    No project-level BRIEF — the whole project classifies as
    PRE_283_CLASSIC and every thread gets the nesting plan.
    """
    project_dir = root / project_name
    project_dir.mkdir(parents=True, exist_ok=True)

    # --- memo thread (flat, named stem, skill-fixed body) ---
    for n in (1, 2):
        version_dir = project_dir / f"beacon.{n}"
        _write(
            version_dir / "memo.md",
            f"# beacon memo v{n}\n\nBody.\n",
        )
        _write(
            version_dir / "_progress.json",
            json.dumps(
                {
                    "version": 1,
                    "thread": "beacon",
                    "phases": {"draft": {"state": "done"}},
                },
                indent=2,
            ) + "\n",
        )
    _write(
        project_dir / "beacon.2.review" / "verdict.md",
        "# Review of beacon.2\n\nVerdict: advance.\n",
    )

    # --- deck thread (nested-but-flat; reuse the beacon-shaped builder
    # pieces inline so this fixture stays self-describing) ---
    deck = "series-a-deck"
    deck_root = project_dir / deck
    _write(
        deck_root / "BRIEF.md",
        "---\ncompany: Beacon Robotics\nstage: series-a\n---\n\n"
        f"# Brief: {deck}\n",
    )
    _write(
        deck_root / "refs" / "transcript-founder.md",
        "# Founder transcript\n",
    )
    _write(deck_root / "assets" / "logo.png", "PNG-PLACEHOLDER\n")
    _write(
        deck_root / ".anvil.json",
        json.dumps(
            {
                "max_iterations": 6,
                "iteration_cap_rationale": "One extra pass to land detail.",
            },
            indent=2,
        ) + "\n",
    )
    for n in (1, 2):
        version_dir = project_dir / f"{deck}.{n}"
        _write(
            version_dir / "deck.md",
            f"---\nmarp: true\n---\n\n# {deck} v{n}\n",
        )
        _write(version_dir / "speaker-notes.md", f"# Notes v{n}\n")
        _write(
            version_dir / "_progress.json",
            json.dumps(
                {
                    "version": 1,
                    "thread": deck,
                    "phases": {"draft": {"state": "done"}},
                },
                indent=2,
            ) + "\n",
        )
    _write(
        project_dir / f"{deck}.1.review" / "verdict.md",
        f"# Review of {deck}.1\n\nVerdict: revise.\n",
    )

    # --- proposal thread (nested-but-flat; LaTeX body) ---
    prop = "gossamer-lan"
    prop_root = project_dir / prop
    _write(
        prop_root / "BRIEF.md",
        "---\ncustomer_kind: external\n---\n\n"
        f"# Brief: {prop}\n",
    )
    _write(
        prop_root / "refs" / "quote-vendor.md",
        "# Vendor quote\n",
    )
    _write(
        project_dir / f"{prop}.1" / "proposal.tex",
        "\\documentclass{anvil-proposal}\n"
        "\\begin{document}\nGossamer LAN v1.\n\\end{document}\n",
    )
    _write(
        project_dir / f"{prop}.1" / "_progress.json",
        json.dumps(
            {
                "version": 1,
                "thread": prop,
                "phases": {"draft": {"state": "done"}},
            },
            indent=2,
        ) + "\n",
    )
    _write(
        project_dir / f"{prop}.1.review" / "verdict.md",
        f"# Review of {prop}.1\n\nVerdict: advance.\n",
    )
    _write(
        project_dir / f"{prop}.1.audit" / "findings.md",
        "# Audit findings\n\nBOM arithmetic clean.\n",
    )

    return project_dir


def build_bare_version_dir_threads(
    root: Path,
    project_name: str = "paper",
    *,
    slug: str = "bispectral-imaging",
    documentclass: str = "article",
) -> Path:
    """Build a BARE version-dir project (issue #408).

    Anonymized reproduction of the adoption-target monorepo shape: a
    hand-rolled review/revise workflow that independently converged on
    Anvil's ``{thread}.{N}/`` + ``.review``/``.audit`` sibling grammar,
    but carries ZERO anvil config (no BRIEF.md anywhere, no
    ``.anvil.json``) and a fixed ``paper.tex`` body filename consumed
    by external tooling (root-level ``paper.tex``/``paper.pdf`` build
    artifacts).

    Shape (version gaps deliberate — no ``.2``):

      <project>/
        <slug>.1/paper.tex
        <slug>.3/paper.tex
        <slug>.3.review/review.md      ← hand-rolled, unstamped
        <slug>.4/paper.tex
        <slug>.4.review/review.md
        <slug>.5/paper.tex
        <slug>.6/paper.tex
        <slug>.6.audit/audit.md        ← hand-rolled, unstamped
        <slug>.7/paper.tex
        figures/fig1.png
        paper.tex                      ← root-level build entrypoint
        paper.pdf

    ``documentclass`` parametrizes the inference path: ``article``
    (default) infers ``paper``; ``anvil-proposal`` infers ``proposal``.
    """
    project_dir = root / project_name
    project_dir.mkdir(parents=True, exist_ok=True)

    versions = (1, 3, 4, 5, 6, 7)
    for n in versions:
        _write(
            project_dir / f"{slug}.{n}" / "paper.tex",
            f"\\documentclass{{{documentclass}}}\n"
            "\\begin{document}\n"
            f"Bispectral imaging draft v{n}.\n"
            "\\end{document}\n",
        )
    # Hand-rolled review siblings: a bare `review.md` is NOT a
    # recognizable payload for `discover_critics` (no `_review.json`,
    # no legacy triple) — invisible-but-intact per the #346 additive
    # contract; rebackportable later via anvil:rubric-rebackport.
    for n in (3, 4):
        _write(
            project_dir / f"{slug}.{n}.review" / "review.md",
            f"# Review of draft v{n}\n\nHand-rolled reviewer notes.\n",
        )
    _write(
        project_dir / f"{slug}.6.audit" / "audit.md",
        "# Audit of draft v6\n\nHand-rolled audit notes.\n",
    )
    # Root-level build artifacts: direct evidence that external tooling
    # (latexmk / Makefile) consumes the fixed `paper.tex` name — the
    # #382 slug-echo carve-out applies (record, never rename).
    _write(
        project_dir / "paper.tex",
        f"\\documentclass{{{documentclass}}}\n"
        "% build entrypoint consumed by latexmk\n",
    )
    _write(project_dir / "paper.pdf", "PDF-PLACEHOLDER\n")
    _write(project_dir / "figures" / "fig1.png", "PNG-PLACEHOLDER\n")
    return project_dir


def build_bare_foreign_md_body_threads(
    root: Path,
    project_name: str = "wave-two-five-blocks",
    *,
    slug: str = "wave-two-five-blocks",
    body_filename: str = "post.md",
) -> Path:
    """Build a BARE project with a FOREIGN ``.md`` body filename (#878).

    Anonymized reproduction of the `anvil:essay` adoption-target shape: a
    hand-rolled blog pipeline that independently converged on the anvil
    ``{thread}.{N}/`` + ``.review``/``.audit`` sibling grammar, but names
    its body file ``post.md`` — a foreign pipeline's fixed name, not any
    anvil skill's historical fixed name (``_SKILL_FIXED_BODY_FILENAMES``
    doesn't recognize it, so the historical rename loop has nothing to
    match). Zero anvil config anywhere (no `BRIEF.md`, no `.anvil.json`).

    Shape:

      <project>/
        <slug>.1/post.md
        <slug>.2/post.md
        <slug>.2.review/review.md      ← hand-rolled, unstamped
        <slug>.3/post.md
    """
    project_dir = root / project_name
    project_dir.mkdir(parents=True, exist_ok=True)

    for n in (1, 2, 3):
        _write(
            project_dir / f"{slug}.{n}" / body_filename,
            f"# Wave two, five blocks (v{n})\n\nPost body draft v{n}.\n",
        )
    _write(
        project_dir / f"{slug}.2.review" / "review.md",
        "# Review of draft v2\n\nHand-rolled reviewer notes.\n",
    )
    return project_dir


def build_bare_ambiguous_md_body_threads(
    root: Path,
    project_name: str = "ambiguous-post",
    *,
    slug: str = "ambiguous-post",
) -> Path:
    """Build a BARE project with TWO distinct foreign ``.md`` bodies (#878).

    A single thread whose version dirs disagree on the foreign body
    filename (``post.md`` on one version, ``draft.md`` on another) — the
    ambiguous case the single-candidate constraint in
    ``_foreign_md_body_candidates`` refuses to guess at. No rename should
    be planned; the plan should surface an operator-facing note instead.
    """
    project_dir = root / project_name
    project_dir.mkdir(parents=True, exist_ok=True)

    _write(
        project_dir / f"{slug}.1" / "post.md",
        "# Ambiguous post v1\n",
    )
    _write(
        project_dir / f"{slug}.2" / "draft.md",
        "# Ambiguous post v2 (renamed pipeline mid-flight)\n",
    )
    return project_dir


# Operator-authored project BRIEF used by the enrollment fixtures
# (issue #406). Deliberately carries every byte-preservation tripwire
# the curator verified the re-render path drops: a top-level `theme:`,
# YAML comments (including a `# TODO(operator)` marker), per-doc
# `render_*` / `latex_header_includes` keys, quoted strings, and
# non-alphabetical entry order. The surgical-append tests assert this
# text survives as a byte-identical prefix.
ENROLL_OPERATOR_BRIEF = (
    "---\n"
    "project: corporate-memos\n"
    "theme: sphere-brand  # operator-pinned theme\n"
    "audience:\n"
    '  - "Board of Directors"\n'
    "hard_rules:\n"
    "  - 'No forward-looking statements'\n"
    "documents:\n"
    "  - slug: zeta-memo\n"
    "    artifact_type: investment-memo  # TODO(operator): confirm\n"
    "    render_engine: xelatex\n"
    "    render_metadata:\n"
    '      doc-type: "Investment Memo"\n'
    "    latex_header_includes: |\n"
    "      \\usepackage{xcolor}\n"
    "  - slug: alpha-memo\n"
    "    artifact_type: position-paper\n"
    "---\n"
    "\n"
    "# Project BRIEF\n"
    "\n"
    "Operator-authored prose that must survive byte-identically.\n"
)


def build_loose_file_in_existing_project(
    root: Path,
    project_name: str = "corporate-memos",
    *,
    loose_filename: str = "2026-05-19-board-update.md",
) -> Path:
    """Build a migrated project + one dated loose file (issue #406).

    Shape:
      <project>/
        BRIEF.md                  ← operator-authored (tripwire-laden:
                                    theme:, render_* keys, YAML
                                    comments, quoting, zeta-before-alpha
                                    entry order)
        zeta-memo/zeta-memo.1/zeta-memo.md
        alpha-memo/alpha-memo.1/alpha-memo.md
        <loose_filename>          ← the enrollment target

    Returns the project root path.
    """
    project_dir = root / project_name
    project_dir.mkdir(parents=True, exist_ok=True)
    _write(project_dir / "BRIEF.md", ENROLL_OPERATOR_BRIEF)
    for slug in ("zeta-memo", "alpha-memo"):
        _write(
            project_dir / slug / f"{slug}.1" / f"{slug}.md",
            f"# {slug} v1\n\nBody.\n",
        )
    _write(
        project_dir / loose_filename,
        "# Board update\n\nLoose memo awaiting enrollment.\n",
    )
    return project_dir


def build_post_283_with_operator_brief(
    root: Path,
    project_name: str = "corporate-memos",
    *,
    extra_unlisted_slug: Optional[str] = None,
) -> Path:
    """Build a tripwire-laden MIGRATE target (issue #415).

    The operator-authored ``ENROLL_OPERATOR_BRIEF`` plus one thread
    that still needs migrate work, so a migrate-mode ``--apply``
    rewrites the BRIEF over the operator's config:

    Shape:
      <project>/
        BRIEF.md                  ← ENROLL_OPERATOR_BRIEF (theme:,
                                    render_* keys, YAML comments,
                                    quoting, zeta-before-alpha order)
        zeta-memo/
          zeta-memo.1/memo.md     ← skill-fixed body → slug-echo rename
          .anvil.json             ← target_length carrier to merge
        alpha-memo/alpha-memo.1/alpha-memo.md   ← already migrated
        [<extra>/<extra>.1/memo.md]             ← unlisted in BRIEF
                                                  (entry gets appended)

    Classifies POST_283_ANVIL_JSON. The intended migrate deltas are:
    rename ``memo.md`` → ``zeta-memo.md``, merge the ``.anvil.json``
    ``target_length`` into the zeta entry, delete the ``.anvil.json``,
    and (when ``extra_unlisted_slug`` is set) append a new entry for
    the unlisted thread. Every other BRIEF byte must survive.
    """
    project_dir = root / project_name
    project_dir.mkdir(parents=True, exist_ok=True)
    _write(project_dir / "BRIEF.md", ENROLL_OPERATOR_BRIEF)

    zeta = project_dir / "zeta-memo"
    _write(zeta / "zeta-memo.1" / "memo.md", "# zeta v1\n\nBody.\n")
    _write(
        zeta / ".anvil.json",
        json.dumps(
            {"target_length": {"words": [5000, 8000]}}, indent=2
        ) + "\n",
    )

    _write(
        project_dir / "alpha-memo" / "alpha-memo.1" / "alpha-memo.md",
        "# alpha v1\n\nBody.\n",
    )

    if extra_unlisted_slug is not None:
        _write(
            project_dir / extra_unlisted_slug
            / f"{extra_unlisted_slug}.1" / "memo.md",
            f"# {extra_unlisted_slug} v1\n\nBody.\n",
        )
    return project_dir


def build_loose_file_no_project(
    root: Path,
    dir_name: str = "memos",
) -> Path:
    """Build a bare topical dir with dated loose files (issue #406).

    Shape (both date forms from the issue's examples):
      <dir>/
        2026-05-19-topic-a.md     ← date PREFIX
        topic-b-2026-05-19.md     ← date SUFFIX

    No BRIEF anywhere — enrollment must synthesize one. Returns the
    topical dir path.
    """
    topical_dir = root / dir_name
    topical_dir.mkdir(parents=True, exist_ok=True)
    _write(
        topical_dir / "2026-05-19-topic-a.md",
        "# Topic A\n\nLoose memo (date-prefixed filename).\n",
    )
    _write(
        topical_dir / "topic-b-2026-05-19.md",
        "# Topic B\n\nLoose memo (date-suffixed filename).\n",
    )
    return topical_dir


def build_loose_file_batch(
    root: Path,
    dir_name: str = "ip",
) -> Path:
    """Build a batch of loose files (issue #406).

    Shape:
      <dir>/
        2026-05-19-topic-a.md           ← enrolls (md, date prefix)
        draft-response-2026-05-19.md    ← enrolls (md, date suffix)
        whitepaper.tex                  ← enrolls (tex, \\documentclass
                                          → paper inference)
        2026-05-19-same-topic.md        ← collision pair member 1
        same-topic-2026-05-20.md        ← collision pair member 2
                                          (both derive `same-topic`)
        notes.txt                       ← refused (non-md/tex)

    No BRIEF anywhere. Returns the topical dir path; tests pass file
    subsets to exercise the batch semantics.
    """
    topical_dir = root / dir_name
    topical_dir.mkdir(parents=True, exist_ok=True)
    _write(
        topical_dir / "2026-05-19-topic-a.md",
        "# Topic A\n\nAnalysis.\n",
    )
    _write(
        topical_dir / "draft-response-2026-05-19.md",
        "# Draft response\n\nCounterparty response.\n",
    )
    _write(
        topical_dir / "whitepaper.tex",
        "\\documentclass{article}\n"
        "\\begin{document}\nWhitepaper draft.\n\\end{document}\n",
    )
    _write(
        topical_dir / "2026-05-19-same-topic.md",
        "# Same topic (one)\n",
    )
    _write(
        topical_dir / "same-topic-2026-05-20.md",
        "# Same topic (two)\n",
    )
    _write(topical_dir / "notes.txt", "scratch notes\n")
    return topical_dir


def build_vn_report_dirs(
    root: Path,
    project_name: str = "sphere-project",
    *,
    dir_name: str = "reports",
    versions: tuple = (1, 2, 3, 5),
    review_versions: tuple = (3, 5),
    with_minor: bool = False,
    with_leading_zero_dup: bool = False,
    with_project_brief: bool = False,
) -> Path:
    """Build a foreign vN report-dir family (issue #432).

    Anonymized reproduction of the sphere-survey report grammar:
    ``projects/<proj>/reports/v{N}/`` version dirs with ``v{N}.review/``
    siblings, hand-rolled ``report.md`` bodies, a stray non-versioned
    dir mixed in, and (optionally) a ``v14.1``-style minor-versioned
    oddball or a ``v07``/``v7`` leading-zero twin pair (issue #458 —
    both parse to version slot 7).

    Shape (default ``versions=(1, 2, 3, 5)`` — gap at v4 deliberate):

      <root>/<project_name>/<dir_name>/
        v1/report.md
        v2/report.md
        v3/report.md
        v3.review/review.md            ← hand-rolled, unstamped
        v5/report.md
        v5.review/review.md
        notes-archive/scratch.md       ← stray non-versioned dir
        [v14.1/report.md]              ← with_minor=True
        [v7/report.md + v07/report.md] ← with_leading_zero_dup=True

    When ``with_project_brief`` is True the enclosing project gets the
    tripwire-laden ``ENROLL_OPERATOR_BRIEF`` plus its two listed
    threads on disk — exercising the surgical-append path. Otherwise
    no BRIEF exists anywhere (starter-synthesis path).

    Returns the vN family dir (``<project>/<dir_name>/``); the project
    root is its parent.
    """
    project_dir = root / project_name
    reports_dir = project_dir / dir_name
    reports_dir.mkdir(parents=True, exist_ok=True)

    for n in versions:
        _write(
            reports_dir / f"v{n}" / "report.md",
            f"# Report v{n}\n\nHand-rolled report draft v{n}.\n",
        )
    for n in review_versions:
        _write(
            reports_dir / f"v{n}.review" / "review.md",
            f"# Review of v{n}\n\nHand-rolled reviewer notes.\n",
        )
    _write(
        reports_dir / "notes-archive" / "scratch.md",
        "# Scratch\n\nStray non-versioned dir content.\n",
    )
    if with_minor:
        _write(
            reports_dir / "v14.1" / "report.md",
            "# Report v14.1\n\nMinor-versioned oddball.\n",
        )
    if with_leading_zero_dup:
        _write(
            reports_dir / "v7" / "report.md",
            "# Report v7\n\nLeading-zero twin (plain).\n",
        )
        _write(
            reports_dir / "v07" / "report.md",
            "# Report v07\n\nLeading-zero twin (zero-padded).\n",
        )

    if with_project_brief:
        _write(project_dir / "BRIEF.md", ENROLL_OPERATOR_BRIEF)
        for slug in ("zeta-memo", "alpha-memo"):
            _write(
                project_dir / slug / f"{slug}.1" / f"{slug}.md",
                f"# {slug} v1\n\nBody.\n",
            )
    return reports_dir


# The full default tag map for `build_letter_family_threads` (issue
# #440): identity mappings for the canonical-shaped vocabulary plus the
# `review-v2` → `review` remap (legal because no plain `.review` sits on
# the same version dir in the default fixture).
DEFAULT_TAG_MAP = {
    "review": "review",
    "review-v2": "review",
    "enablement": "enablement",
    "pre_flight": "pre_flight",
    "s101": "s101",
    "audit": "audit",
    "audit2": "audit2",
}


def write_tag_map(path: Path, mapping: dict) -> Path:
    """Write a ``--tag-map`` JSON file with the canonical shape."""
    _write(path, json.dumps({"tag_map": dict(mapping)}, indent=2) + "\n")
    return path


def build_letter_family_threads(
    root: Path,
    project_name: str = "agent-workspace",
    *,
    with_sidecars: bool = True,
    with_leading_zero_dup: bool = False,
    with_project_brief: bool = False,
) -> Path:
    """Build foreign letter-family threads (issue #440 — Phase 2 of #432).

    Anonymized reproduction of the sphere-survey ip-thread grammar:
    flat ``{Project}.{Letter}.{N}/`` version dirs with foreign-tagged
    critic siblings, hand-rolled single-file ``review.md`` payloads, a
    stray non-versioned dir, and an orphan sidecar.
    ``with_leading_zero_dup=True`` adds a ``Meridian.C.07/`` twin of
    the existing ``Meridian.C.7/`` (issue #458 — both parse to
    ``Meridian.C`` version slot 7).

    Shape (two letter families, gap at ``Meridian.C.6`` deliberate)::

      <root>/<project_name>/
        Meridian.A.1/spec.md
        Meridian.A.2/spec.md
        Meridian.A.2.review/review.md          ← single-file payload
        Meridian.C.5/spec.md
        Meridian.C.5.review-v2/review.md       ← versioned foreign tag
        Meridian.C.5.pre_flight/review.md
        Meridian.C.7/spec.md
        Meridian.C.7.enablement/review.md
        Meridian.C.7.s101/review.md
        Meridian.C.7.audit/review.md           ← same-dir .audit/.audit2
        Meridian.C.7.audit2/review.md             pair (distinct tags)
        Meridian.C.9.fto/review.md             ← orphan sidecar (no C.9)
        notes-archive/scratch.md               ← stray non-versioned dir
        Meridian.C.7.1/oddball.md              ← stray (matches neither
                                                  grammar: numeric tag)

    ``with_sidecars=False`` builds only the version dirs + strays (the
    sidecar-free variant where ``--tag-map`` is optional).

    When ``with_project_brief`` is True the project gets the
    tripwire-laden ``ENROLL_OPERATOR_BRIEF`` plus its two listed
    threads on disk — exercising the surgical-append path. Otherwise
    no BRIEF exists anywhere (starter-synthesis path).

    Returns the family dir (== the project root in this mode).
    """
    project_dir = root / project_name
    project_dir.mkdir(parents=True, exist_ok=True)

    version_dirs = {
        "Meridian.A": (1, 2),
        "Meridian.C": (5, 7),
    }
    for stem, versions in version_dirs.items():
        for n in versions:
            _write(
                project_dir / f"{stem}.{n}" / "spec.md",
                f"# {stem} v{n}\n\nHand-rolled ip draft v{n}.\n",
            )
    if with_leading_zero_dup:
        _write(
            project_dir / "Meridian.C.07" / "spec.md",
            "# Meridian.C v07\n\nLeading-zero twin (zero-padded).\n",
        )

    if with_sidecars:
        sidecar_names = (
            "Meridian.A.2.review",
            "Meridian.C.5.review-v2",
            "Meridian.C.5.pre_flight",
            "Meridian.C.7.enablement",
            "Meridian.C.7.s101",
            "Meridian.C.7.audit",
            "Meridian.C.7.audit2",
            "Meridian.C.9.fto",  # orphan: Meridian.C.9 absent
        )
        for name in sidecar_names:
            _write(
                project_dir / name / "review.md",
                f"# {name}\n\nHand-rolled single-file reviewer notes.\n",
            )

    _write(
        project_dir / "notes-archive" / "scratch.md",
        "# Scratch\n\nStray non-versioned dir content.\n",
    )
    _write(
        project_dir / "Meridian.C.7.1" / "oddball.md",
        "# Oddball\n\nMinor-versioned-looking stray.\n",
    )

    if with_project_brief:
        _write(project_dir / "BRIEF.md", ENROLL_OPERATOR_BRIEF)
        for slug in ("zeta-memo", "alpha-memo"):
            _write(
                project_dir / slug / f"{slug}.1" / f"{slug}.md",
                f"# {slug} v1\n\nBody.\n",
            )
    return project_dir


# Verbatim prose body every foreign single-file `review.md` carries in the
# adopted-review fixture (issue #454). Kept as a module constant so the
# apply/dry-run tests can assert byte-identical preservation against it.
FOREIGN_REVIEW_PROSE = (
    "# Enablement review\n\n"
    "Hand-rolled reviewer notes that were NEVER scored on any anvil "
    "rubric.\n\n"
    "- The disclosure is thorough but the claim scope is broad.\n"
    "- No per-dimension table, no Total: X/Y, no advance: true|false.\n"
)


def build_adopted_review_threads(
    root: Path,
    project_name: str = "agent-workspace",
    *,
    with_real_sibling: bool = False,
    pre_converted: bool = False,
) -> Path:
    """Build a POST-adoption tree with foreign `review.md`-only sidecars.

    The Phase-3a (`--adopt-review`, issue #454) input shape: an already-
    adopted tree (canonical `<slug>/<slug>.{N}/` version dirs with
    `<slug>.{N}.<tag>` critic siblings) whose siblings still hold only a
    single-file prose `review.md` — they fail
    `critics._has_recognizable_review` and stay invisible to
    `discover_critics` until converted.

    Shape (two adopted threads)::

      <root>/<project_name>/
        meridian-c/
          meridian-c.5/spec.md
          meridian-c.5.review/review.md          ← review.md-only sidecar
          meridian-c.7/spec.md
          meridian-c.7.enablement/review.md      ← review.md-only sidecar
          meridian-c.7.s101/review.md            ← review.md-only sidecar
        meridian-a/
          meridian-a.2/spec.md
          meridian-a.2.review/review.md          ← review.md-only sidecar

    ``with_real_sibling=True`` adds a co-sibling `meridian-c.7.audit/`
    that already carries a canonical `_review.json` WITH real scores (so
    the load-bearing zero-dimension-tolerance test can aggregate a stub
    alongside a genuinely-scored critic on the SAME version dir).

    ``pre_converted=True`` drops a stub `_review.json` + `_meta.json` into
    EVERY foreign sidecar up front (the idempotence fixture: a re-run
    must find nothing to convert).

    Returns the project root (== the adopted-tree dir passed to
    `--adopt-review`).
    """
    project_dir = root / project_name
    project_dir.mkdir(parents=True, exist_ok=True)

    threads = {
        "meridian-c": {
            5: ("review",),
            7: ("enablement", "s101"),
        },
        "meridian-a": {
            2: ("review",),
        },
    }
    for slug, versions in threads.items():
        for n, tags in versions.items():
            _write(
                project_dir / slug / f"{slug}.{n}" / "spec.md",
                f"# {slug} v{n}\n\nHand-rolled ip draft v{n}.\n",
            )
            for tag in tags:
                sidecar = project_dir / slug / f"{slug}.{n}.{tag}"
                _write(sidecar / "review.md", FOREIGN_REVIEW_PROSE)
                if pre_converted:
                    _write_stub_payload(sidecar, f"{slug}.{n}", tag)

    if with_real_sibling:
        # A genuinely-scored co-sibling on meridian-c.7 (alongside the
        # foreign .enablement / .s101 stubs). Real per-dimension scores +
        # a real total/threshold/verdict — the aggregate of [stub, this]
        # must reflect THIS critic's numbers untouched.
        real = project_dir / "meridian-c" / "meridian-c.7.audit"
        _write(
            real / "_review.json",
            json.dumps(
                {
                    "schema_version": "1",
                    "kind": "judgment",
                    "version_dir": "meridian-c.7",
                    "critic_id": "audit",
                    "scores": [
                        {
                            "dimension": "enablement",
                            "score": 8,
                            "max": 10,
                            "critical": False,
                        },
                        {
                            "dimension": "clarity",
                            "score": 7,
                            "max": 10,
                            "critical": False,
                        },
                    ],
                    "findings": [],
                    "critical_flags": [],
                    "total": 15,
                    "threshold": 14,
                    "verdict": "ADVANCE",
                },
                indent=2,
            )
            + "\n",
        )

    return project_dir


def _write_stub_payload(sidecar: Path, version_dir: str, tag: str) -> None:
    """Drop a Phase-3a stub `_review.json` + `_meta.json` into ``sidecar``.

    Mirrors what `adopt_review.apply_adopt_review_plan` writes, so the
    idempotence fixture presents an already-converted sidecar.
    """
    _write(
        sidecar / "_review.json",
        json.dumps(
            {
                "schema_version": "1",
                "kind": "judgment",
                "version_dir": version_dir,
                "critic_id": tag,
                "model": None,
                "rubric": None,
                "scores": [],
                "findings": [],
                "critical_flags": [],
                "total": None,
                "threshold": None,
                "verdict": None,
                "rendered_artifact": None,
                "unscored": True,
            },
            indent=2,
        )
        + "\n",
    )
    _write(
        sidecar / "_meta.json",
        json.dumps(
            {
                "source": "foreign-adopted",
                "unscored": True,
                "origin_filename": "review.md",
                "adopted_by": "anvil:project-migrate#454",
            },
            indent=2,
        )
        + "\n",
    )


# Provisional-spec body content. A native consumer's `provisional.tex`
# uses `\documentclass{anvil-uspto}` — the SAME class anvil's full
# ip-uspto spec (`spec.tex`) uses — which is exactly why a
# `\documentclass` scan cannot disambiguate the two (issue #503).
_PROVISIONAL_TEX = (
    "\\documentclass{anvil-uspto}\n"
    "\\begin{document}\n"
    "Provisional specification draft.\n"
    "\\end{document}\n"
)
# A counsel memo body (the COUNSEL-READY companion, #480). Content is
# never inspected — it is recognized by filename only.
_COUNSEL_MEMO_TEX = (
    "\\documentclass{anvil-uspto}\n"
    "\\begin{document}\n"
    "Counsel filing memo (companion, never a body).\n"
    "\\end{document}\n"
)


def build_bare_native_provisional(
    root: Path,
    project_name: str = "widget-sensor-provisional",
    *,
    slug: str = "widget-sensor",
    with_counsel_memo: bool = False,
    counsel_only: bool = False,
) -> Path:
    """Build a BARE native ip-uspto-provisional thread (issue #503).

    A hand-rolled provisional with ZERO anvil config: ``<slug>.N/``
    version dirs whose body is ``provisional.tex`` (NOT anvil's canonical
    ``spec.tex``), no BRIEF.md, no ``.anvil.json``. Classifies
    PRE_283_CLASSIC / ``is_bare``; the planner must FILENAME-recognize
    ``provisional.tex`` → ``ip-uspto-provisional`` (never a
    ``\\documentclass`` scan, which would mis-infer ``paper``).

    Shape::

      <project>/
        <slug>.1/provisional.tex
        <slug>.2/provisional.tex
        [<slug>.2/counsel_memo.tex]    ← with_counsel_memo (companion)

    ``with_counsel_memo`` adds a ``counsel_memo.tex`` companion alongside
    the newest ``provisional.tex`` (recognized, never the body, never
    renamed). ``counsel_only`` builds version dirs carrying ONLY
    ``counsel_memo.tex`` (no ``provisional.tex``) — the counsel-only
    refusal fixture.
    """
    project_dir = root / project_name
    project_dir.mkdir(parents=True, exist_ok=True)

    for n in (1, 2):
        if counsel_only:
            _write(
                project_dir / f"{slug}.{n}" / "counsel_memo.tex",
                _COUNSEL_MEMO_TEX,
            )
        else:
            _write(
                project_dir / f"{slug}.{n}" / "provisional.tex",
                _PROVISIONAL_TEX,
            )
    if with_counsel_memo and not counsel_only:
        _write(
            project_dir / f"{slug}.2" / "counsel_memo.tex",
            _COUNSEL_MEMO_TEX,
        )
    return project_dir


def build_loose_provisional_file(
    root: Path,
    project_name: str = "ip-portfolio",
    *,
    loose_filename: str = "provisional.tex",
) -> Path:
    """Build a migrated project + one loose ``provisional.tex`` (#503).

    Mirrors :func:`build_loose_file_in_existing_project` (the #406 enroll
    fixture) but drops a loose ``provisional.tex`` (or
    ``counsel_memo.tex`` when overridden) at the project root as the
    enrollment target.

    Returns the project root path.
    """
    project_dir = root / project_name
    project_dir.mkdir(parents=True, exist_ok=True)
    _write(project_dir / "BRIEF.md", ENROLL_OPERATOR_BRIEF)
    for slug in ("zeta-memo", "alpha-memo"):
        _write(
            project_dir / slug / f"{slug}.1" / f"{slug}.md",
            f"# {slug} v1\n\nBody.\n",
        )
    body = (
        _COUNSEL_MEMO_TEX
        if loose_filename == "counsel_memo.tex"
        else _PROVISIONAL_TEX
    )
    _write(project_dir / loose_filename, body)
    return project_dir


def build_provisional_letter_family(
    root: Path,
    project_name: str = "agent-workspace",
    *,
    with_counsel_memo: bool = False,
    counsel_only: bool = False,
) -> Path:
    """Build a letter-family with provisional bodies (issue #503).

    A single ``{Project}.{Letter}.{N}`` family whose version-dir body is
    ``provisional.tex``. Used by the ``--adopt-family`` counsel-memo
    companion-preservation and counsel-only-refusal tests.

    Shape::

      <root>/<project_name>/
        Meridian.P.1/provisional.tex
        Meridian.P.2/provisional.tex
        [Meridian.P.2/counsel_memo.tex]   ← with_counsel_memo

    ``counsel_only`` builds version dirs carrying ONLY
    ``counsel_memo.tex`` (the refusal fixture). Returns the family dir
    (== the project root in this mode).
    """
    project_dir = root / project_name
    project_dir.mkdir(parents=True, exist_ok=True)
    for n in (1, 2):
        if counsel_only:
            _write(
                project_dir / f"Meridian.P.{n}" / "counsel_memo.tex",
                _COUNSEL_MEMO_TEX,
            )
        else:
            _write(
                project_dir / f"Meridian.P.{n}" / "provisional.tex",
                _PROVISIONAL_TEX,
            )
    if with_counsel_memo and not counsel_only:
        _write(
            project_dir / "Meridian.P.2" / "counsel_memo.tex",
            _COUNSEL_MEMO_TEX,
        )
    return project_dir


__all__ = [
    "DEFAULT_TAG_MAP",
    "ENROLL_OPERATOR_BRIEF",
    "FOREIGN_REVIEW_PROSE",
    "build_adopted_review_threads",
    "build_beacon_shaped_deck",
    "build_bare_native_provisional",
    "build_bare_version_dir_threads",
    "build_foundry_shaped",
    "build_fully_migrated",
    "build_letter_family_threads",
    "build_loose_file_batch",
    "build_loose_file_in_existing_project",
    "build_loose_file_no_project",
    "build_loose_provisional_file",
    "build_mixed_memo_deck_proposal",
    "build_post_283_anvil_json",
    "build_post_283_with_operator_brief",
    "build_pre_283_classic",
    "build_provisional_letter_family",
    "build_vn_report_dirs",
    "write_tag_map",
]
