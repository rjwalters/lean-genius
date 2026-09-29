"""Project shape detection — shared framework primitive (issues #297, #407).

Born as ``anvil/skills/project-migrate/lib/detect.py`` (issue #297).
Promoted to ``anvil/lib/`` when ``anvil:project-scout`` (issue #407) became
the second consumer of the detector core — the CLAUDE.md "wait for the
second consumer before generalizing" trigger (#10/#26/#69/#102/#382/#393
pattern). The historical import path is preserved by a full-fidelity
re-export shim at ``anvil/skills/project-migrate/lib/detect.py``, so
project-migrate's lib siblings (``plan``, ``apply``, ``enroll``,
``verify``, ``orchestrate``) and its test suite run unchanged.

Given a project directory, classify its on-disk shape so the planner can
choose the right migration steps. Three shapes are recognized:

- ``Shape.FULLY_MIGRATED`` — post-#296 target: project-level ``BRIEF.md``
  absorbs all per-doc config; every thread lives at
  ``<project>/<slug>/<slug>.N/<slug>.md``.
- ``Shape.POST_283_ANVIL_JSON`` — project-level ``BRIEF.md`` exists with
  ``documents:`` listed, but per-thread ``.anvil.json`` files persist and/or
  body filenames are still skill-fixed (``memo.md``).
- ``Shape.PRE_283_CLASSIC`` — no project-level ``BRIEF.md``; ``memo.N/``
  sibling version dirs directly under the project root; skill-fixed
  ``memo.md`` bodies. This shape ALSO covers the nested-but-flat
  deck/slides/proposal variant (issue #382 — the studio canary's
  ``series-a-deck`` shape): a thread-root directory (``<slug>/`` with
  BRIEF + refs + assets) sitting as a sibling of flat ``<slug>.N/``
  version dirs at the project root. The slug heuristic resolves the
  stem itself as the slug (the stem is not a skill name), and any
  per-thread ``.anvil.json`` inside the thread root is recorded for
  the BRIEF merge.

``Shape.UNKNOWN`` is returned for inputs that don't match any of the three
patterns (e.g., an empty directory, or a directory whose contents look like
non-anvil project material).

Design notes
------------
- **Pure detector — no mutations.** The detection routine reads files but
  never writes. This is load-bearing for the dry-run contract: the same code
  path that drives ``/anvil:project-migrate`` (dry-run) and
  ``/anvil:project-migrate --apply`` (apply) goes through detection, and
  detection MUST never touch disk.
- **Skill-local first, lib promotion later.** Lived under
  ``anvil/skills/project-migrate/lib/`` per the CLAUDE.md pattern until
  ``anvil:project-scout`` (#407) became the second consumer; now canonical
  here, with the skill-local path kept as a re-export shim.
- **No new Python deps.** Uses ``pyyaml`` (already a base dep via
  ``project_brief.py``) only for ``.anvil.json`` is JSON-only (stdlib) and
  the BRIEF frontmatter check is a thin reuse of the existing
  ``project_discovery.has_project_brief`` helper through a path manipulation
  shim (we vendor the small predicate logic here to avoid a fragile import
  chain at install time).

Public API
----------

- ``Shape`` — IntEnum of recognized shapes.
- ``ProjectInventory`` — typed snapshot of what the detector found
  (per-slug directory list, per-slug ``.anvil.json`` presence, etc.).
- ``detect_shape(project_dir)`` — top-level classifier.
- ``inventory_project(project_dir)`` — return the typed inventory without
  collapsing it to a single ``Shape``.
"""

from __future__ import annotations

import re
from dataclasses import dataclass, field
from enum import Enum
from pathlib import Path
from typing import Dict, List, Optional


# ---------------------------------------------------------------------------
# Constants
# ---------------------------------------------------------------------------


BRIEF_FILENAME = "BRIEF.md"
ANVIL_JSON_FILENAME = ".anvil.json"
MEMO_BODY_FILENAME = "memo.md"

# Frontmatter delimiter — three hyphens on their own line. Mirrors the
# convention used by ``project_discovery._extract_frontmatter`` so the two
# parsers accept the same on-disk shape.
_FRONTMATTER_DELIM = "---"

# Version-dir naming: <stem>.<N> where N is one or more digits.
_VERSION_DIR_RE = re.compile(r"^(?P<stem>.+)\.(?P<num>\d+)$")

# Skill-local body filenames historically shipped by anvil skills. When we
# see one of these in a thread dir, we know the thread is pre-#295 (the
# slug-echo contract had not yet landed).
#
# NOTE (issue #382): ``deck.md`` (the Marp source used by both anvil:deck
# and anvil:slides) and ``proposal.tex`` (the XeLaTeX source used by
# anvil:proposal) are deliberately NOT in this tuple. Those skills retain
# their skill-fixed body filenames in v1 — the slug-echo body rename is
# scoped out because the filenames are consumed by external tooling
# (marp CLI, xelatex, anvil-proposal.cls). The migration for those
# skills is directory nesting only.
_SKILL_FIXED_BODY_FILENAMES = (
    "memo.md",
    "proposal.md",
    "report.md",
    "installation.md",
    # Legacy pre-#295 body filename for the `pub` skill (renamed to
    # `paper` under #694; the current skill body is `main.tex`). A
    # pre-rename unmigrated thread may still carry `pub.md`.
    "pub.md",
)

# Body filenames that are canonical *as-is* for skills that retained a
# skill-fixed body name post-#295 (issue #382). A version dir carrying
# one of these (plus any auxiliary markdown like ``speaker-notes.md``)
# counts as fully migrated; only the ``_SKILL_FIXED_BODY_FILENAMES``
# above are pre-#295 evidence.
#
# These are observed on a SEPARATE inventory surface
# (``ThreadInventory.retained_body_filenames`` — issue #386) so the
# planner can infer the BRIEF's artifact_type and surface the
# inference note for ``.tex``-bodied proposal threads too. They are
# deliberately kept OUT of ``ThreadInventory.body_filenames`` /
# ``_classify`` evidence: ``body_filenames`` collects ``*.md`` only,
# and ``proposal.tex`` is not pre-#295 shape evidence.
_RETAINED_BODY_FILENAMES = frozenset({"deck.md", "proposal.tex"})

# Extensions scanned for OBSERVED candidate bodies (issue #408): non-`.md`,
# non-retained files inside a version dir that look like a hand-rolled
# body (e.g. ``paper.tex`` in a bare version-dir thread). A third
# inventory surface (``ThreadInventory.observed_body_files``) with the
# same discipline as ``retained_body_filenames``: kept OUT of
# ``_classify`` evidence — observed bodies inform the planner's
# artifact-type inference only, never the shape classification.
_OBSERVED_BODY_EXTENSIONS = (".tex",)

# Native ip-uspto-provisional body filename (issue #503). A version dir
# carrying ``provisional.tex`` declares — by FILENAME, never by
# ``\documentclass`` content — that the thread is an
# ``anvil:ip-uspto-provisional`` provisional. This is the only safe
# provisional signal: anvil's own provisional body is ``spec.tex`` with
# ``\documentclass{anvil-uspto}`` — the SAME class the full ip-uspto
# spec uses — so a ``\documentclass`` scan cannot disambiguate a
# provisional from a full application (SKILL.md:160 forbids that
# inference). The operator's body filename is the declaration.
PROVISIONAL_BODY_FILENAME = "provisional.tex"

# COUNSEL-READY companion filename (issue #503 / #480). In anvil,
# ``counsel_memo.*`` is a finalize-OUTPUT artifact (written into
# ``<thread>.counsel/`` by ``ip-uspto-provisional-finalize``), never a
# version-dir body. A native ``counsel_memo.tex`` sitting alongside
# ``provisional.tex`` in a version dir is a PRESERVED COMPANION: recognized,
# recorded, left in place, NEVER selected as the body and NEVER renamed.
# A version dir carrying ``counsel_memo.tex`` but NO ``provisional.tex``
# is a refusal (a counsel memo is not a fileable body).
COUNSEL_MEMO_FILENAME = "counsel_memo.tex"

# Sibling directories that are never thread dirs (review siblings, audit
# siblings, generic critic siblings, plus bookkeeping dirs the operator
# may have placed at the project root).
_NON_THREAD_DIRNAME_PREFIXES = (".",)
_INFRASTRUCTURE_DIRS = frozenset({"research", "refs", "build", "_archive"})


class Shape(Enum):
    """Recognized on-disk project shapes (issue #297).

    The detector returns one of these for any project directory it is asked
    about. The planner dispatches on the value.

    Members
    -------
    FULLY_MIGRATED
        Target shape per issues #295 and #296. No work to do.
    POST_283_ANVIL_JSON
        Project root + `BRIEF.md` listing `documents:`, but at least one
        per-thread `.anvil.json` exists and/or body filenames are still
        skill-fixed (`memo.md`).
    PRE_283_CLASSIC
        No project-level `BRIEF.md`. `<thread>.N/` siblings directly under
        the project root. Skill-fixed body filenames (`memo.md`).
    ENROLL
        Plan-mode tag for single-file enrollment (issue #406) — NOT a
        detected on-disk shape. ``detect_shape`` never returns it; the
        enroll planner (:mod:`enroll`) stamps it on the :class:`Plan`
        so apply / report dispatch can distinguish an enrollment plan
        (succeeded-subset BRIEF write, surgical append) from a
        whole-project migration plan.
    ADOPT_VN
        Plan-mode tag for vN report-dir adoption (issue #432) — NOT a
        detected on-disk shape, following the ENROLL precedent.
        ``detect_shape`` never returns it and ``_classify`` is
        untouched; the adopt-vn planner
        (project-migrate's ``lib/adopt_vn.py``) stamps it on the plan
        so apply / report dispatch can route the BRIEF write through
        the enroll-style append/synthesize path.
    ADOPT_FAMILY
        Plan-mode tag for letter-family adoption (issue #440 — Phase 2
        of #432) — NOT a detected on-disk shape, following the ENROLL /
        ADOPT_VN precedent. ``detect_shape`` never returns it and
        ``_classify`` is untouched; the adopt-family planner
        (project-migrate's ``lib/adopt_family.py``) stamps it on the
        plan so apply / report dispatch can route the BRIEF write
        through the enroll-style append/synthesize path.
    UNKNOWN
        Directory is not recognizable as any of the above. Caller should
        treat as an error.
    """

    FULLY_MIGRATED = "fully_migrated"
    POST_283_ANVIL_JSON = "post_283_anvil_json"
    PRE_283_CLASSIC = "pre_283_classic"
    ENROLL = "enroll"
    ADOPT_VN = "adopt_vn"
    ADOPT_FAMILY = "adopt_family"
    UNKNOWN = "unknown"


@dataclass
class ThreadInventory:
    """Per-slug snapshot of what the detector found on disk.

    Attributes
    ----------
    slug
        The slug (the canonical short name for the thread). For pre-#283
        the slug is inferred from the project dir name (since classic
        threads put `memo.N/` directly under the project root).
    parent_dir
        The directory that contains this thread's version dirs. For
        pre-#283 this is the project root itself; for post-#283 / fully-
        migrated it is `<project>/<slug>/`.
    version_dirs
        Sorted list of `<stem>.<N>` directories belonging to this thread.
    body_filenames
        The set of body filenames observed across the version dirs. The
        canonical post-#295 form is `{<slug>.md}`; pre-#295 threads carry
        skill-fixed names like `{memo.md}`. Mixed sets surface as a
        diagnostic during planning. ``*.md`` only — this surface feeds
        `_classify` and deliberately excludes `.tex` (not pre-#295
        shape evidence).
    retained_body_filenames
        Filenames from `_RETAINED_BODY_FILENAMES` (`deck.md`,
        `proposal.tex`) observed across the version dirs (issue #386).
        A separate surface from `body_filenames` so the planner can
        infer the BRIEF entry's artifact_type (deck.md → deck,
        proposal.tex → proposal) without contaminating `_classify`
        evidence.
    observed_body_files
        Non-``.md``, non-retained candidate body filenames observed
        across the version dirs (issue #408 — ``*.tex`` at minimum,
        e.g. the bare hand-rolled ``paper.tex``). Same discipline as
        ``retained_body_filenames``: feeds the planner's artifact-type
        inference only and is deliberately kept OUT of `_classify`
        shape evidence.
    anvil_json_path
        Path to a per-thread `.anvil.json` if one exists; `None` otherwise.
    """

    slug: str
    parent_dir: Path
    version_dirs: List[Path] = field(default_factory=list)
    body_filenames: List[str] = field(default_factory=list)
    retained_body_filenames: List[str] = field(default_factory=list)
    observed_body_files: List[str] = field(default_factory=list)
    anvil_json_path: Optional[Path] = None


@dataclass
class ProjectInventory:
    """Typed snapshot of what the detector found across the whole project.

    Attributes
    ----------
    project_dir
        The directory passed to the detector.
    has_project_brief
        True iff `<project_dir>/BRIEF.md` exists and parses to a non-empty
        `documents:` list.
    project_brief_path
        Path to the project BRIEF if present; `None` otherwise.
    threads
        Per-slug inventory list. Empty when no recognizable thread shapes
        were found.
    extra_anvil_jsons
        Paths to any `.anvil.json` files NOT associated with a discovered
        thread (e.g., at the project root in pre-#283 layouts where the
        operator put one file per project). The planner folds these into
        the BRIEF merge step.
    """

    project_dir: Path
    has_project_brief: bool = False
    project_brief_path: Optional[Path] = None
    threads: List[ThreadInventory] = field(default_factory=list)
    extra_anvil_jsons: List[Path] = field(default_factory=list)

    @property
    def is_bare(self) -> bool:
        """True iff version-dir families exist with NO anvil config anywhere.

        Sub-state of :data:`Shape.PRE_283_CLASSIC` (issue #408): the bare
        hand-rolled shape (e.g. ``<slug>.N/`` dirs with ``paper.tex``
        bodies and ``.review``/``.audit`` sidecars) already classifies
        and migrates as PRE_283_CLASSIC — this predicate only flags
        that the project BRIEF must be SYNTHESIZED from observed state
        (there is nothing to merge from), so the planner emits inferred
        values with operator-confirmation TODO markers instead of
        silent defaults. Deliberately a derived sub-state rather than a
        new ``Shape`` member: a new enum member would force
        near-duplicate dispatch branches in plan/orchestrate/verify.

        The predicate: threads present, no project BRIEF, no
        ``.anvil.json`` anywhere, no skill-fixed bodies, no retained
        bodies.
        """
        if self.has_project_brief or not self.threads:
            return False
        if self.extra_anvil_jsons:
            return False
        for t in self.threads:
            if t.anvil_json_path is not None:
                return False
            if any(b in _SKILL_FIXED_BODY_FILENAMES for b in t.body_filenames):
                return False
            if t.retained_body_filenames:
                return False
        return True


# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------


def _list_subdirectories(directory: Path) -> List[Path]:
    """Return sorted list of subdirectories of ``directory``.

    Tolerates missing directories and permission errors by returning an
    empty list. Skips dotfiles (``.git``, ``.anvil-migrate-rollback``, …) —
    those are bookkeeping, not project content.
    """
    if not directory.is_dir():
        return []
    try:
        children = sorted(directory.iterdir(), key=lambda c: c.name)
    except OSError:
        return []
    out: List[Path] = []
    for child in children:
        if not child.is_dir():
            continue
        if child.name.startswith(_NON_THREAD_DIRNAME_PREFIXES):
            continue
        out.append(child)
    return out


def _list_version_dirs(directory: Path, stem: str) -> List[Path]:
    """Return ``<directory>/<stem>.<N>`` subdirs sorted by N.

    The match is anchored: ``<stem>.<digits>`` only. ``memo.txt`` does not
    match; ``memo.1.bak`` does not match.
    """
    if not directory.is_dir():
        return []
    out: List[Path] = []
    try:
        for child in directory.iterdir():
            if not child.is_dir():
                continue
            m = _VERSION_DIR_RE.match(child.name)
            if m is None:
                continue
            if m.group("stem") != stem:
                continue
            out.append(child)
    except OSError:
        return []
    out.sort(key=lambda p: int(_VERSION_DIR_RE.match(p.name).group("num")))
    return out


def _list_all_version_dirs(directory: Path) -> Dict[str, List[Path]]:
    """Group ``<directory>/<stem>.<N>`` subdirs by stem.

    Returns a dict keyed by stem; each value is the sorted list of version
    dirs for that stem. Skips dotfiles and non-version subdirs.
    """
    grouped: Dict[str, List[Path]] = {}
    if not directory.is_dir():
        return grouped
    try:
        children = list(directory.iterdir())
    except OSError:
        return grouped
    for child in children:
        if not child.is_dir():
            continue
        if child.name.startswith(_NON_THREAD_DIRNAME_PREFIXES):
            continue
        m = _VERSION_DIR_RE.match(child.name)
        if m is None:
            continue
        grouped.setdefault(m.group("stem"), []).append(child)
    for stem, dirs in grouped.items():
        dirs.sort(
            key=lambda p: int(_VERSION_DIR_RE.match(p.name).group("num"))
        )
    return grouped


def _observed_body_filenames(version_dir: Path) -> List[str]:
    """Return sorted list of ``*.md`` filenames in a version directory.

    Excludes ``_progress.json`` / ``changelog.md`` / other infrastructure
    files. The relevant set for shape detection is: every ``*.md`` that
    looks like it could be the body markdown.
    """
    if not version_dir.is_dir():
        return []
    out: List[str] = []
    try:
        for child in version_dir.iterdir():
            if not child.is_file():
                continue
            if not child.name.endswith(".md"):
                continue
            if child.name == "changelog.md":
                continue
            out.append(child.name)
    except OSError:
        return []
    out.sort()
    return out


def _observed_retained_body_filenames(version_dir: Path) -> List[str]:
    """Return sorted retained-body filenames present in a version dir.

    Second scan (issue #386), separate from :func:`_observed_body_filenames`:
    checks for the `_RETAINED_BODY_FILENAMES` allowlist (`deck.md`,
    `proposal.tex`) so a `.tex`-bodied proposal thread is visible to
    the planner's artifact-type inference. Kept OUT of
    ``ThreadInventory.body_filenames`` — `_classify` must not see
    `.tex` files as shape evidence.
    """
    if not version_dir.is_dir():
        return []
    out: List[str] = []
    for name in _RETAINED_BODY_FILENAMES:
        if (version_dir / name).is_file():
            out.append(name)
    out.sort()
    return out


def _observed_candidate_body_files(version_dir: Path) -> List[str]:
    """Return sorted non-``.md``, non-retained candidate body filenames.

    Third scan (issue #408), separate from both
    :func:`_observed_body_filenames` (``*.md`` shape evidence) and
    :func:`_observed_retained_body_filenames` (the #386 allowlist):
    collects files with an extension in ``_OBSERVED_BODY_EXTENSIONS``
    (``*.tex`` at minimum) so a bare hand-rolled ``paper.tex`` body is
    visible to the planner's artifact-type inference. Kept OUT of
    ``ThreadInventory.body_filenames`` / `_classify` evidence.
    """
    if not version_dir.is_dir():
        return []
    out: List[str] = []
    try:
        for child in version_dir.iterdir():
            if not child.is_file():
                continue
            if child.name in _RETAINED_BODY_FILENAMES:
                continue
            if child.suffix not in _OBSERVED_BODY_EXTENSIONS:
                continue
            out.append(child.name)
    except OSError:
        return []
    out.sort()
    return out


def has_native_provisional_body(filenames) -> bool:
    """Return True iff ``provisional.tex`` is among ``filenames`` (issue #503).

    Filename-driven recognition of a native ``anvil:ip-uspto-provisional``
    body. ``filenames`` is any iterable of basenames (e.g.
    ``ThreadInventory.observed_body_files`` or the directory listing of a
    version dir). Recognition is by NAME only — content is never inspected
    (SKILL.md:160: no provisional-vs-full ``\\documentclass`` inference).
    """
    return PROVISIONAL_BODY_FILENAME in set(filenames)


def has_counsel_memo_companion(filenames) -> bool:
    """Return True iff ``counsel_memo.tex`` is among ``filenames`` (issue #503).

    The COUNSEL-READY companion (#480). Recognized so callers can record
    it as a preserved companion (never the body) and refuse a
    counsel-memo-only version dir (a counsel memo is not a fileable body).
    """
    return COUNSEL_MEMO_FILENAME in set(filenames)


def _has_project_brief(project_dir: Path) -> bool:
    """Return True iff ``<project_dir>/BRIEF.md`` has a non-empty documents: list.

    Inlined copy of ``project_discovery.has_project_brief`` — we duplicate
    the small predicate here so the detector has no runtime import
    dependency on the memo skill. The contract: a project BRIEF qualifies
    when it has YAML frontmatter with a ``documents:`` key whose value is a
    non-empty list. Malformed YAML or missing frontmatter → False.

    Uses ``yaml`` only if pyyaml is available. If it isn't, falls back to a
    cheap regex-based check ("documents:\\n  - " near the top of the file)
    so the detector keeps working in install layouts that haven't synced
    deps yet.
    """
    brief = project_dir / BRIEF_FILENAME
    if not brief.is_file():
        return False
    try:
        text = brief.read_text(encoding="utf-8")
    except OSError:
        return False
    fm = _extract_frontmatter(text)
    if fm is None:
        return False
    docs = fm.get("documents")
    if not isinstance(docs, list):
        return False
    return len(docs) > 0


def _extract_frontmatter(text: str) -> Optional[dict]:
    """Extract YAML frontmatter from ``text`` as a dict, or return None.

    Pure-stdlib-first: tries ``yaml.safe_load`` when pyyaml is on the path
    (the normal install case), falls back to a minimal hand-rolled parser
    that handles the canonical project BRIEF shape (``documents:`` list of
    ``slug:`` / ``artifact_type:`` mappings) when pyyaml is absent.

    Returns ``None`` when the text has no frontmatter or the frontmatter
    can't be parsed under either path.
    """
    lines = text.splitlines()
    if lines and lines[0].startswith("﻿"):
        lines[0] = lines[0][1:]
    first_idx = 0
    while first_idx < len(lines) and lines[first_idx].strip() == "":
        first_idx += 1
    if first_idx >= len(lines):
        return None
    if lines[first_idx].strip() != _FRONTMATTER_DELIM:
        return None
    close_idx = None
    for i in range(first_idx + 1, len(lines)):
        if lines[i].strip() == _FRONTMATTER_DELIM:
            close_idx = i
            break
    if close_idx is None:
        return None
    yaml_text = "\n".join(lines[first_idx + 1:close_idx])
    try:
        import yaml  # type: ignore
        parsed = yaml.safe_load(yaml_text)
    except Exception:
        # Fallback: very narrow hand-rolled parse. We only need to detect
        # "documents:" with at least one "- slug:" child. Anything else is
        # treated as absent so the detector errs toward "not a project
        # brief" rather than confidently claiming one exists.
        parsed = _hand_parse_minimal_yaml(yaml_text)
    if not isinstance(parsed, dict):
        return None
    return parsed


def _hand_parse_minimal_yaml(yaml_text: str) -> Optional[dict]:
    """Minimal hand-rolled YAML parser for the project BRIEF shape.

    Recognizes only ``documents:`` followed by ``- slug: <name>`` entries.
    Used as a last-resort fallback when pyyaml isn't importable (an unusual
    install state). Returns ``{"documents": [{"slug": ...}, ...]}`` or
    ``None``.
    """
    docs: List[dict] = []
    in_documents = False
    for raw_line in yaml_text.splitlines():
        line = raw_line.rstrip()
        if not line.strip():
            continue
        if line.startswith("documents:"):
            in_documents = True
            continue
        if in_documents and re.match(r"^\s*-\s+slug:\s*", line):
            slug_match = re.match(r"^\s*-\s+slug:\s*(\S+)", line)
            if slug_match:
                docs.append({"slug": slug_match.group(1).strip('"\'')})
            continue
        if in_documents and re.match(r"^[A-Za-z_]+:", line):
            # New top-level key — exit documents.
            in_documents = False
    if docs:
        return {"documents": docs}
    return None


def _project_brief_slugs(project_dir: Path) -> List[str]:
    """Return the list of slugs declared in ``<project_dir>/BRIEF.md``.

    Returns an empty list when no project BRIEF is present or the BRIEF
    has no documents. Tolerant of malformed BRIEFs (returns ``[]`` rather
    than raising).
    """
    brief = project_dir / BRIEF_FILENAME
    if not brief.is_file():
        return []
    try:
        text = brief.read_text(encoding="utf-8")
    except OSError:
        return []
    fm = _extract_frontmatter(text)
    if fm is None:
        return []
    docs = fm.get("documents")
    if not isinstance(docs, list):
        return []
    slugs: List[str] = []
    for entry in docs:
        if isinstance(entry, dict):
            slug = entry.get("slug")
            if isinstance(slug, str) and slug.strip():
                slugs.append(slug)
        elif isinstance(entry, str) and entry.strip():
            slugs.append(entry)
    return slugs


# ---------------------------------------------------------------------------
# Public API
# ---------------------------------------------------------------------------


def inventory_project(project_dir: Path) -> ProjectInventory:
    """Return a typed inventory of ``project_dir`` without classifying.

    The inventory carries:

    - Whether a project BRIEF is present (``has_project_brief``).
    - Per-slug thread inventories under ``threads`` — one for each
      discovered thread.
    - Any ``.anvil.json`` files that aren't tied to a thread under
      ``extra_anvil_jsons``.

    Used by :func:`detect_shape` and by the planner to inspect the same
    snapshot without re-walking.
    """
    project_dir = Path(project_dir).resolve()
    inv = ProjectInventory(project_dir=project_dir)

    if not project_dir.is_dir():
        return inv

    # Project BRIEF check.
    inv.has_project_brief = _has_project_brief(project_dir)
    if inv.has_project_brief:
        inv.project_brief_path = project_dir / BRIEF_FILENAME

    # Pre-#283 shape detection: <project>/<stem>.<N>/ directly under the
    # project root. Group by stem.
    classic_groups = _list_all_version_dirs(project_dir)

    # Post-#283 / fully-migrated detection: <project>/<slug>/<slug>.N/.
    # Walk subdirectories of the project root. For each, look for
    # <slug>.N/ children.
    for child in _list_subdirectories(project_dir):
        if child.name in _INFRASTRUCTURE_DIRS:
            continue
        if child.name in classic_groups:
            # This subdir IS a version dir under the project root (pre-#283).
            # Skip — it's handled by classic_groups below.
            continue
        version_dirs = _list_version_dirs(child, child.name)
        if not version_dirs:
            continue
        body_files: List[str] = []
        retained_files: List[str] = []
        observed_files: List[str] = []
        for vd in version_dirs:
            body_files.extend(_observed_body_filenames(vd))
            retained_files.extend(_observed_retained_body_filenames(vd))
            observed_files.extend(_observed_candidate_body_files(vd))
        anvil_json_path = None
        # Check for .anvil.json at the thread root.
        candidate = child / ANVIL_JSON_FILENAME
        if candidate.is_file():
            anvil_json_path = candidate
        inv.threads.append(
            ThreadInventory(
                slug=child.name,
                parent_dir=child,
                version_dirs=version_dirs,
                body_filenames=sorted(set(body_files)),
                retained_body_filenames=sorted(set(retained_files)),
                observed_body_files=sorted(set(observed_files)),
                anvil_json_path=anvil_json_path,
            )
        )

    # Add pre-#283 classic groups (version dirs directly under project root).
    project_slug = project_dir.name
    for stem, version_dirs in sorted(classic_groups.items()):
        # Determine slug: for pre-#283 layouts the version-dir stem is
        # typically the skill name ("memo") not the project slug. We use
        # the project dir name as the canonical slug because that's what
        # the migration will rename to.
        body_files: List[str] = []
        retained_files: List[str] = []
        observed_files: List[str] = []
        for vd in version_dirs:
            body_files.extend(_observed_body_filenames(vd))
            retained_files.extend(_observed_retained_body_filenames(vd))
            observed_files.extend(_observed_candidate_body_files(vd))
        # The .anvil.json for classic layouts lives at the project root.
        # Don't pre-claim it here; we'll fold it in via extra_anvil_jsons
        # when classifying, since the canary uses "memo" as the stem AND
        # one .anvil.json per project.
        # Slug heuristic: if stem matches a known skill name, use the
        # project_slug; otherwise use the stem itself (handles the
        # post-#283 layout where the operator already renamed memo.N
        # to <slug>.N but never moved them into <slug>/).
        # `paper` (renamed from `pub` under #694) plus the legacy `pub`
        # stem — an unmigrated pre-rename thread may still carry it.
        if stem in {"memo", "proposal", "report", "deck", "slides",
                    "ip-uspto", "installation", "paper", "pub"}:
            slug = project_slug
        else:
            slug = stem
        # Nested-but-flat thread roots (issue #382 — the studio canary's
        # deck shape): a sibling ``<project>/<stem>/`` directory carrying
        # the thread-level BRIEF / refs / assets may exist alongside the
        # flat ``<stem>.N/`` version dirs. When it carries a per-thread
        # ``.anvil.json`` (the deck iteration-cap-rationale carrier),
        # record it so the planner can merge it into the project BRIEF.
        anvil_json_path = None
        thread_root_candidate = project_dir / stem / ANVIL_JSON_FILENAME
        if thread_root_candidate.is_file():
            anvil_json_path = thread_root_candidate
        inv.threads.append(
            ThreadInventory(
                slug=slug,
                parent_dir=project_dir,
                version_dirs=version_dirs,
                body_filenames=sorted(set(body_files)),
                retained_body_filenames=sorted(set(retained_files)),
                observed_body_files=sorted(set(observed_files)),
                anvil_json_path=anvil_json_path,
            )
        )

    # Look for stray .anvil.json files at the project root (the classic
    # one-per-project location).
    root_anvil_json = project_dir / ANVIL_JSON_FILENAME
    if root_anvil_json.is_file():
        # If no thread already claims it, record as extra.
        already_claimed = any(
            t.anvil_json_path == root_anvil_json for t in inv.threads
        )
        if not already_claimed:
            inv.extra_anvil_jsons.append(root_anvil_json)

    return inv


def detect_shape(project_dir: Path) -> Shape:
    """Classify the on-disk shape of ``project_dir``.

    Returns a :class:`Shape` enum. The classification rules:

    1. **FULLY_MIGRATED** — has a project BRIEF, every thread is under
       ``<project>/<slug>/<slug>.N/`` (NOT directly at project root), no
       ``.anvil.json`` files anywhere, every version dir's body filename
       is ``<slug>.md`` (NOT ``memo.md`` / etc.).
    2. **POST_283_ANVIL_JSON** — has a project BRIEF, but at least one
       thread retains an ``.anvil.json`` OR has a skill-fixed body
       filename. Also matches a post-#283 layout that's almost migrated
       but still has a stray ``.anvil.json`` somewhere.
    3. **PRE_283_CLASSIC** — no project BRIEF; ``<stem>.N/`` version dirs
       directly under the project root.
    4. **UNKNOWN** — none of the above.
    """
    inv = inventory_project(project_dir)
    return _classify(inv)


def _classify(inv: ProjectInventory) -> Shape:
    """Classify an inventory into a :class:`Shape`.

    Separated from :func:`detect_shape` so callers (including the planner)
    can share the inventory rather than re-walking.
    """
    if not inv.threads and not inv.has_project_brief:
        # Empty directory or one with no recognizable anvil content.
        return Shape.UNKNOWN

    # Detect classic-root threads (version dirs directly under project root).
    classic_threads = [
        t for t in inv.threads if t.parent_dir == inv.project_dir
    ]
    nested_threads = [
        t for t in inv.threads if t.parent_dir != inv.project_dir
    ]

    has_anvil_json = bool(inv.extra_anvil_jsons) or any(
        t.anvil_json_path is not None for t in inv.threads
    )

    has_skill_fixed_body = any(
        any(b in _SKILL_FIXED_BODY_FILENAMES for b in t.body_filenames)
        for t in inv.threads
    )

    # Fully migrated: project BRIEF + nested threads only + no .anvil.json
    # + body filename equals slug for every thread.
    if (
        inv.has_project_brief
        and nested_threads
        and not classic_threads
        and not has_anvil_json
    ):
        # Verify no thread retains a pre-#295 skill-fixed body filename.
        #
        # The check is "no skill-fixed body present", NOT "every body is
        # `<slug>.md`": skills that retained their body filenames
        # post-#295 (deck/slides keep `deck.md` per issue #382's
        # slug-echo scope-out; auxiliary markdown like
        # `speaker-notes.md` is artifact content, not a body) must
        # classify as fully migrated once nested. Only the filenames in
        # `_SKILL_FIXED_BODY_FILENAMES` are pre-#295 evidence.
        fully = not has_skill_fixed_body
        if fully:
            return Shape.FULLY_MIGRATED
        # Else fall through.

    if inv.has_project_brief:
        return Shape.POST_283_ANVIL_JSON

    if classic_threads and not inv.has_project_brief:
        return Shape.PRE_283_CLASSIC

    return Shape.UNKNOWN


__all__ = [
    "ANVIL_JSON_FILENAME",
    "BRIEF_FILENAME",
    "COUNSEL_MEMO_FILENAME",
    "MEMO_BODY_FILENAME",
    "PROVISIONAL_BODY_FILENAME",
    "ProjectInventory",
    "Shape",
    "ThreadInventory",
    "detect_shape",
    "has_counsel_memo_companion",
    "has_native_provisional_body",
    "inventory_project",
]
