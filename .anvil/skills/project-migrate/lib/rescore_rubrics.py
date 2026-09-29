"""Skill + rubric resolution for ``--adopt-review --rescore`` (issue #507).

Phase 3b of the #432 foreign-grammar adoption arc needs, per Phase-3a
stub, the **target anvil rubric** the operator/LLM will score the
preserved ``review.md`` against. This module is the thin, skill-local
resolver that maps a stub sidecar → owning skill → :class:`RubricIdentity`
(``rubric_id`` / ``rubric_total`` / ``advance_threshold``).

Why a skill-local catalog (not a shared import)
-----------------------------------------------

``rubric-rebackport`` already maintains a ``KNOWN_RUBRICS`` catalog, but
the issue #507 curation comment is explicit: do NOT couple this mode to
``rubric-rebackport`` (its detector cannot even see foreign stubs, and its
rescore contract requires a prior anvil score a stub lacks). The CLAUDE.md
"wait for the second consumer before promoting to ``anvil/lib/``"
discipline applies — a skill-local copy is the correct first cut. If a
third consumer ever needs this triple, promote it to ``anvil/lib/`` then.

Resolution priority (mirrors rubric-rebackport's ``_infer_skill``)
------------------------------------------------------------------

1. **BRIEF ``documents:`` block** — the highest-confidence signal. A
   project ``BRIEF.md`` whose ``documents:`` list declares the stub's
   thread slug with an ``artifact_type`` resolves the skill directly.
2. **Body-filename fallback** — the sibling version dir (``<slug>.{N}/``)
   carries a known skill-fixed body filename (``memo.md``, ``ip-uspto.md``,
   …).
3. **Unknown** — no rule fires. The caller SKIPS the stub with an
   operator-visible note (the honesty guard) — a rubric is NEVER guessed.
"""

from __future__ import annotations

import re
from dataclasses import dataclass
from pathlib import Path
from typing import Dict, Optional, Tuple

from .detect import _VERSION_DIR_RE


@dataclass(frozen=True)
class RubricIdentity:
    """The (id, total, advance_threshold) triple stamped per rescored review.

    Attributes
    ----------
    id
        The ``rubric_id`` literal (e.g. ``"anvil-memo-v2"``). Echoed into
        the scored ``Review.rubric`` and the ``_meta.json`` ``rubric_id``.
    total
        The rubric's declared point pool (``rubric_total``). Also the
        scored review's ``threshold`` denominator context.
    advance_threshold
        The rubric's advance threshold (``advance_threshold`` /
        ``Review.threshold``).
    """

    id: str
    total: int
    advance_threshold: int


# The current per-review rubric for each shipped skill (mirrors
# ``rubric-rebackport``'s ``CURRENT_RUBRIC_BY_SKILL`` — kept skill-local
# per the issue #507 curation note). A rescore always targets the skill's
# CURRENT rubric: a foreign stub was never scored on any rubric, so there
# is no legacy-vs-current transition to record (unlike rubric-rebackport).
CURRENT_RUBRIC_BY_SKILL: Dict[str, RubricIdentity] = {
    "memo": RubricIdentity("anvil-memo-v2", 44, 35),
    "proposal": RubricIdentity("anvil-proposal-v2", 44, 35),
    # `pub` skill renamed to `paper` under #694; keyed on the current
    # name, the rubric_id literal stays the frozen `anvil-pub-v2`.
    "paper": RubricIdentity("anvil-pub-v2", 44, 35),
    "report": RubricIdentity("anvil-report-v2", 44, 39),
    "deck": RubricIdentity("anvil-deck-v2", 44, 39),
    "slides": RubricIdentity("anvil-slides-v2", 44, 35),
    "installation": RubricIdentity("anvil-installation-v2", 44, 35),
    "ip-uspto": RubricIdentity("anvil-ip-uspto-v2", 45, 39),
    "datasheet": RubricIdentity("anvil-datasheet-v1", 44, 39),
    "ip-uspto-provisional": RubricIdentity("anvil-ip-provisional-v1", 45, 39),
    "essay": RubricIdentity("anvil-essay-v1", 44, 35),
}


# Body filename → skill (the rule-2 fallback). Mirrors
# ``rubric-rebackport/lib/detect.py::_BODY_FILENAME_TO_SKILL``.
_BODY_FILENAME_TO_SKILL: Dict[str, str] = {
    "memo.md": "memo",
    "proposal.md": "proposal",
    "report.md": "report",
    "installation.md": "installation",
    "paper.md": "paper",
    # Legacy body filename (issue #694): a pre-rename `pub.md` body
    # resolves to the current skill name `paper`.
    "pub.md": "paper",
    "deck.md": "deck",
    "slides.md": "slides",
    "ip-uspto.md": "ip-uspto",
}


# BRIEF ``artifact_type`` → skill (the rule-1 map). Mirrors
# ``rubric-rebackport/lib/detect.py::_load_brief_skill_map``.
_ARTIFACT_TYPE_TO_SKILL: Dict[str, str] = {
    "investment-memo": "memo",
    "position-memo": "memo",
    "strategy-memo": "memo",
    "memo": "memo",
    "proposal": "proposal",
    "report": "report",
    "deck": "deck",
    "slides": "slides",
    "paper": "paper",
    # Legacy artifact_type strings (issue #694): pre-rename `pub` /
    # informal `publication` resolve to the current skill name `paper`.
    "pub": "paper",
    "publication": "paper",
    "ip-uspto": "ip-uspto",
    "patent": "ip-uspto",
    "installation": "installation",
    "datasheet": "datasheet",
    "ip-uspto-provisional": "ip-uspto-provisional",
    "essay": "essay",
}


# A ``  - slug: <slug>`` documents-block list-entry start line.
_DOC_SLUG_RE = re.compile(r"^\s*-\s+slug:\s*(?P<slug>\S+)\s*$")
# An ``artifact_type: <type>`` field line within a documents entry.
_DOC_ARTIFACT_TYPE_RE = re.compile(
    r"^\s+artifact_type:\s*(?P<type>[^\s#]+)"
)


def _version_stem(sidecar_name: str) -> Optional[str]:
    """Return the thread slug for a ``<slug>.{N}.<tag>`` sidecar name.

    The slug is the ``<slug>`` of the ``<slug>.{N}`` version stem (the
    portion before the final ``.{N}``). Returns ``None`` when the name is
    not a critic-sibling shape.
    """
    head, sep, _tag = sidecar_name.rpartition(".")
    if not sep or not head:
        return None
    if _VERSION_DIR_RE.match(head) is None:
        return None
    m = _VERSION_DIR_RE.match(head)
    if m is None:
        return None
    return m.group("stem")


def _walk_for_briefs(root: Path) -> list:
    """Return every ``BRIEF.md`` at or under ``root`` (shallow-ish walk).

    Walks the adopted tree (project root + ``<slug>/`` thread roots).
    Skips dot-dirs and obvious infrastructure dirs.
    """
    briefs: list = []
    skip = {".git", "node_modules", "__pycache__", ".venv", "venv"}

    def _descend(d: Path, depth: int) -> None:
        if depth > 3:
            return
        try:
            children = sorted(d.iterdir())
        except OSError:
            return
        for child in children:
            if child.is_file() and child.name == "BRIEF.md":
                briefs.append(child)
            elif (
                child.is_dir()
                and not child.name.startswith(".")
                and child.name not in skip
            ):
                _descend(child, depth + 1)

    _descend(root, 0)
    return briefs


def _parse_brief_slug_map(brief_text: str) -> Dict[str, str]:
    """Map ``slug`` → skill from a BRIEF ``documents:`` block.

    A line-oriented scan tolerant of the canonical block form::

        documents:
          - slug: latency-wall
            artifact_type: investment-memo
          - slug: beacon
            artifact_type: ip-uspto

    Each ``- slug:`` opens an entry; the first ``artifact_type:`` field
    seen before the next ``- slug:`` (or end) is the entry's type. An
    unrecognized ``artifact_type`` is dropped (the slug stays unmapped).
    """
    out: Dict[str, str] = {}
    current_slug: Optional[str] = None
    in_documents = False
    for raw in brief_text.splitlines():
        stripped = raw.strip()
        if stripped.startswith("documents:"):
            in_documents = True
            continue
        if not in_documents:
            continue
        # A non-indented, non-empty, non-list line ends the documents block.
        if (
            stripped
            and not raw.startswith(" ")
            and not raw.startswith("\t")
            and not stripped.startswith("-")
        ):
            break
        m_slug = _DOC_SLUG_RE.match(raw)
        if m_slug is not None:
            current_slug = m_slug.group("slug").strip("\"'")
            continue
        m_type = _DOC_ARTIFACT_TYPE_RE.match(raw)
        if m_type is not None and current_slug is not None:
            artifact_type = m_type.group("type").strip("\"'")
            skill = _ARTIFACT_TYPE_TO_SKILL.get(artifact_type)
            if skill is not None:
                out[current_slug] = skill
            current_slug = None
    return out


def _build_brief_skill_map(directory: Path) -> Dict[str, str]:
    """Map slug → skill across every BRIEF under ``directory``."""
    out: Dict[str, str] = {}
    for brief in _walk_for_briefs(directory):
        try:
            text = brief.read_text(encoding="utf-8")
        except OSError:
            continue
        out.update(_parse_brief_slug_map(text))
    return out


def resolve_skill_for_sidecar(
    sidecar_dir: Path,
    *,
    brief_skill_map: Dict[str, str],
) -> Tuple[Optional[str], str]:
    """Return ``(skill, source)`` for a stub sidecar.

    ``source`` is ``"brief"`` / ``"body-filename"`` / ``"unknown"`` —
    surfaced in the operator report. ``skill`` is ``None`` when no rule
    fires (the caller skips the stub — the honesty guard).
    """
    slug = _version_stem(sidecar_dir.name)
    if slug is None:
        return None, "unknown"

    # Rule 1 — BRIEF documents: block.
    if slug in brief_skill_map:
        return brief_skill_map[slug], "brief"

    # Rule 2 — sibling version-dir body filename.
    head, _sep, _tag = sidecar_dir.name.rpartition(".")
    version_dir = sidecar_dir.parent / head
    if version_dir.is_dir():
        for body_name, skill_name in _BODY_FILENAME_TO_SKILL.items():
            if (version_dir / body_name).is_file():
                return skill_name, "body-filename"

    return None, "unknown"


def resolve_rubric_for_sidecar(
    sidecar_dir: Path,
    *,
    brief_skill_map: Dict[str, str],
) -> Tuple[Optional[RubricIdentity], Optional[str], str]:
    """Return ``(rubric, skill, source)`` for a stub sidecar.

    ``rubric`` is ``None`` when the skill cannot be resolved OR the
    resolved skill has no cataloged current rubric — both cases the caller
    treats as a skip-with-note (never a guess).
    """
    skill, source = resolve_skill_for_sidecar(
        sidecar_dir, brief_skill_map=brief_skill_map
    )
    if skill is None:
        return None, None, source
    rubric = CURRENT_RUBRIC_BY_SKILL.get(skill)
    if rubric is None:
        return None, skill, source
    return rubric, skill, source


__all__ = [
    "CURRENT_RUBRIC_BY_SKILL",
    "RubricIdentity",
    "resolve_rubric_for_sidecar",
    "resolve_skill_for_sidecar",
]
