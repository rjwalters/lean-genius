"""Document-ish heuristic for `anvil:project-scout` (issue #407).

:func:`classify_document` is a **pure function** of
``(filename, text, context)`` — deterministic, no I/O, unit-testable on
strings. The context (:class:`DocContext`) carries the few ambient facts
the classifier needs (parent dirname, doc-site markers in ancestors);
:func:`build_doc_context` is the filesystem helper that computes it
(read-only).

Conservative bias, locked at curation: ties break toward NOT_DOCUMENT —
a false negative costs a missed suggestion; a false positive recommends
moving someone's README into a version thread.

Verdict mapping:

- any **hard negative**  → NOT_DOCUMENT, regardless of positives;
- 0 positive signals     → NOT_DOCUMENT;
- >= 2 positives, no soft negative → DOCUMENT / ``high`` confidence;
- exactly 1 positive, no soft negative → DOCUMENT / ``medium``;
- positives present but the fence-density soft negative too →
  DOCUMENT / ``low`` (the report withholds the ``--enroll``
  recommendation at low confidence: "verify before enrolling").
"""

from __future__ import annotations

import re
from dataclasses import dataclass, field
from pathlib import Path
from typing import List, Optional, Tuple


VERDICT_DOCUMENT = "document"
VERDICT_NOT_DOCUMENT = "not_document"

CONFIDENCE_HIGH = "high"
CONFIDENCE_MEDIUM = "medium"
CONFIDENCE_LOW = "low"

# ---------------------------------------------------------------------------
# Hard negatives
# ---------------------------------------------------------------------------

# Well-known repository basenames (compared on the upper-cased stem, so
# `Readme.md`, `readme.md`, `README.md` all hit). Explicit tuple per the
# curation notes — auditable, no fuzzy matching.
HARD_NEGATIVE_BASENAMES = frozenset(
    {
        "README",
        "CHANGELOG",
        "CONTRIBUTING",
        "LICENSE",
        "CODE_OF_CONDUCT",
        "SECURITY",
        "SUPPORT",
        "TODO",
        "INSTALL",
        "UPGRADING",
        "AGENTS",
        "CLAUDE",
        "SKILL",
        "BRIEF",
        "ROADMAP",
        "WORK_LOG",
        "WORK_PLAN",
    }
)

# ADR / RFC convention: `NNN-title.md` inside a decisions directory.
_ADR_BASENAME_RE = re.compile(r"^\d{3,4}-")
_ADR_DIRNAMES = frozenset({"adr", "adrs", "decisions", "rfc", "rfcs"})

# Document-ish parent dirnames (positive signal, not a verdict by itself).
DOCUMENT_DIRNAMES = frozenset(
    {
        "memos",
        "memo",
        "ip",
        "reports",
        "papers",
        "drafts",
        "letters",
        "analysis",
        "proposals",
    }
)

# Doc-site markers checked in ancestors up to the scan root.
_DOC_SITE_MARKERS = ("mkdocs.yml", "mkdocs.yaml")
_DOCUSAURUS_GLOB = "docusaurus.config.*"

# ISO-date tokens at the head or tail of a filename stem. Mirrors the
# #406 enrollment regexes (`project-migrate/lib/enroll.py`:
# `_DATE_PREFIX_RE` / `_DATE_SUFFIX_RE`) — the same tokens `--enroll`
# will strip when deriving the slug, so a filename that scores this
# positive signal is exactly one enroll already handles.
_DATE_PREFIX_RE = re.compile(r"^(?P<date>\d{4}-\d{2}-\d{2})[-_ ]+")
_DATE_SUFFIX_RE = re.compile(r"[-_ .]+(?P<date>\d{4}-\d{2}-\d{2})$")

# Prose-mass threshold (words in paragraph lines).
_PROSE_MASS_WORDS = 300

# Fence-density soft-negative threshold (fenced lines / total lines).
_FENCE_DENSITY_THRESHOLD = 0.25


@dataclass(frozen=True)
class DocContext:
    """Ambient facts about a candidate file's location (no file content).

    Computed once per file by :func:`build_doc_context`;
    :func:`classify_document` itself never touches the filesystem.
    """

    parent_dirname: str = ""
    ancestor_dirnames: Tuple[str, ...] = ()
    in_doc_site: bool = False


@dataclass
class DocVerdict:
    verdict: str
    confidence: Optional[str]  # None for NOT_DOCUMENT
    signals: List[str] = field(default_factory=list)


# ---------------------------------------------------------------------------
# Context builder (read-only filesystem helper)
# ---------------------------------------------------------------------------


def build_doc_context(file_path: Path, root: Path) -> DocContext:
    """Compute the :class:`DocContext` for ``file_path`` under ``root``.

    Read-only. Ancestor dirnames are the directory names strictly
    between the scan root and the file (nearest first). Doc-site
    detection looks for ``mkdocs.yml``, Sphinx (``conf.py`` +
    ``index.rst``), or ``docusaurus.config.*`` in any ancestor up to and
    including the scan root.
    """
    file_path = Path(file_path)
    root = Path(root)
    ancestors: List[str] = []
    in_doc_site = False
    cur = file_path.parent
    while True:
        if cur != root:
            ancestors.append(cur.name)
        for marker in _DOC_SITE_MARKERS:
            if (cur / marker).is_file():
                in_doc_site = True
        if (cur / "conf.py").is_file() and (cur / "index.rst").is_file():
            in_doc_site = True
        try:
            if any(cur.glob(_DOCUSAURUS_GLOB)):
                in_doc_site = True
        except OSError:
            pass
        if cur == root or cur.parent == cur:
            break
        cur = cur.parent
    return DocContext(
        parent_dirname=file_path.parent.name,
        ancestor_dirnames=tuple(ancestors),
        in_doc_site=in_doc_site,
    )


# ---------------------------------------------------------------------------
# Text-shape helpers (pure)
# ---------------------------------------------------------------------------


def _frontmatter_keys(text: str) -> List[str]:
    """Top-level keys of a leading YAML frontmatter block, or ``[]``.

    String-level scan (no yaml dependency): the block must open with
    ``---`` on the first non-blank line and close with another ``---``.
    """
    lines = text.splitlines()
    i = 0
    while i < len(lines) and lines[i].strip() == "":
        i += 1
    if i >= len(lines) or lines[i].strip() != "---":
        return []
    keys: List[str] = []
    for line in lines[i + 1 :]:
        if line.strip() == "---":
            return keys
        m = re.match(r"^([A-Za-z_][A-Za-z0-9_-]*):", line)
        if m is not None:
            keys.append(m.group(1))
    return []  # unterminated block — not frontmatter


def _fence_density(lines: List[str]) -> float:
    if not lines:
        return 0.0
    fenced = 0
    in_fence = False
    for line in lines:
        stripped = line.lstrip()
        if stripped.startswith("```") or stripped.startswith("~~~"):
            fenced += 1
            in_fence = not in_fence
            continue
        if in_fence:
            fenced += 1
    return fenced / len(lines)


def _paragraph_lines(lines: List[str]) -> List[str]:
    """Non-heading, non-fence, non-list, non-frontmatter prose lines."""
    out: List[str] = []
    in_fence = False
    in_frontmatter = False
    for idx, line in enumerate(lines):
        stripped = line.strip()
        if idx == 0 and stripped == "---":
            in_frontmatter = True
            continue
        if in_frontmatter:
            if stripped == "---":
                in_frontmatter = False
            continue
        if stripped.startswith("```") or stripped.startswith("~~~"):
            in_fence = not in_fence
            continue
        if in_fence:
            continue
        if not stripped:
            continue
        if stripped.startswith("#"):
            continue
        if re.match(r"^([-*+]\s|\d+[.)]\s|>\s?)", stripped):
            continue
        if stripped.startswith("|"):
            continue
        out.append(stripped)
    return out


def _single_h1_then_prose(lines: List[str]) -> bool:
    """Exactly one H1, with paragraph prose somewhere after it."""
    h1_indices = [
        i
        for i, line in enumerate(lines)
        if re.match(r"^#\s+\S", line.strip())
    ]
    if len(h1_indices) != 1:
        return False
    after = lines[h1_indices[0] + 1 :]
    return len(_paragraph_lines(after)) > 0


# ---------------------------------------------------------------------------
# Classifier (pure)
# ---------------------------------------------------------------------------


def classify_document(
    filename: str, text: str, ctx: DocContext
) -> DocVerdict:
    """Classify one candidate file. Pure — no I/O.

    See the module docstring for the verdict mapping. The returned
    ``signals`` list names every signal that fired (hard negatives,
    positives, and the soft negative) so the report can show its work
    and the operator can audit the heuristic.
    """
    stem = filename
    for suffix in (".md", ".tex"):
        if stem.endswith(suffix):
            stem = stem[: -len(suffix)]
            break
    is_tex = filename.endswith(".tex")
    fm_keys = _frontmatter_keys(text)
    lines = text.splitlines()

    # ---- hard negatives -------------------------------------------------
    hard: List[str] = []
    if stem.upper() in HARD_NEGATIVE_BASENAMES:
        hard.append(f"hard-negative:basename:{stem.upper()}")
    if (
        _ADR_BASENAME_RE.match(filename)
        and ctx.parent_dirname.lower() in _ADR_DIRNAMES
    ):
        hard.append("hard-negative:adr-convention")
    if ctx.in_doc_site:
        hard.append("hard-negative:doc-site")
    if ".github" in ctx.ancestor_dirnames:
        hard.append("hard-negative:under-dot-github")
    if "templates" in ctx.ancestor_dirnames or (
        ctx.parent_dirname == "templates"
    ):
        hard.append("hard-negative:under-templates")
    if "user-invocable" in fm_keys:
        hard.append("hard-negative:skill-frontmatter")
    if hard:
        return DocVerdict(
            verdict=VERDICT_NOT_DOCUMENT, confidence=None, signals=hard
        )

    # ---- positive signals ------------------------------------------------
    signals: List[str] = []
    if _DATE_PREFIX_RE.match(stem) or _DATE_SUFFIX_RE.search(stem):
        signals.append("iso-date-filename")
    fm_doc_keys = sorted(
        k for k in fm_keys if k in ("title", "author", "date")
    )
    if fm_doc_keys:
        signals.append("frontmatter:" + ",".join(fm_doc_keys))
    if is_tex and "\\documentclass" in text:
        signals.append("documentclass")
    paragraphs = _paragraph_lines(lines)
    prose_words = sum(len(p.split()) for p in paragraphs)
    if prose_words >= _PROSE_MASS_WORDS:
        signals.append(f"prose-mass:{prose_words}-words")
    if not is_tex and _single_h1_then_prose(lines):
        signals.append("single-h1-structure")
    if ctx.parent_dirname.lower() in DOCUMENT_DIRNAMES:
        signals.append(f"document-dirname:{ctx.parent_dirname.lower()}")

    positives = len(signals)

    # ---- soft negative -----------------------------------------------------
    density = _fence_density(lines)
    soft = density >= _FENCE_DENSITY_THRESHOLD
    if soft:
        signals.append(f"soft-negative:fence-density:{density:.2f}")

    if positives == 0:
        return DocVerdict(
            verdict=VERDICT_NOT_DOCUMENT,
            confidence=None,
            signals=signals or ["no-positive-signals"],
        )
    if soft:
        confidence = CONFIDENCE_LOW
    elif positives >= 2:
        confidence = CONFIDENCE_HIGH
    else:
        confidence = CONFIDENCE_MEDIUM
    return DocVerdict(
        verdict=VERDICT_DOCUMENT, confidence=confidence, signals=signals
    )


__all__ = [
    "CONFIDENCE_HIGH",
    "CONFIDENCE_LOW",
    "CONFIDENCE_MEDIUM",
    "DOCUMENT_DIRNAMES",
    "DocContext",
    "DocVerdict",
    "HARD_NEGATIVE_BASENAMES",
    "VERDICT_DOCUMENT",
    "VERDICT_NOT_DOCUMENT",
    "build_doc_context",
    "classify_document",
]
