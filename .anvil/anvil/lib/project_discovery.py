"""Project-as-thread-root discovery for the memo skill (issue #284, #295).

Sub-deliverable 1 of #283 — the **foundational** discovery primitive that
later sub-deliverables (BRIEF parser #285, rubric overlay selection #286,
cross-thread ref validation #287) depend on knowing where to look.

Simplification under issue #295
-------------------------------
Originally (PR #290) this module shipped **dual-layout** discovery,
recognizing both a "classic siblings-under-portfolio" layout and a
"project-as-thread-root" layout. Issue #295 retires the classic layout:
every memo thread now lives inside a project root with a project-level
``BRIEF.md``. The ``LAYOUT_CLASSIC`` constant, its branch in
``_resolve_layout``, and the layout-precedence reasoning are removed.
The discovery surface shrinks to "find the project root; identify the
thread slug within it".

Background — the canonical layout
---------------------------------
A **project root** carries a project-level ``BRIEF.md`` whose YAML
frontmatter enumerates per-document metadata in a ``documents:`` list.
Each entry names a slug; that slug names a sibling directory that holds
version dirs::

    <project>/
      BRIEF.md                ← single project brief with documents: list
                                 (carries every per-doc and project-level
                                 anvil config knob; issue #296)
      <slug-a>/
        <slug-a>.1/<slug-a>.md
        <slug-a>.2/<slug-a>.md
        ...
      <slug-b>/
        <slug-b>.1/<slug-b>.md
        ...
      research/               ← shared evidence pool (already shipped, #281)
      refs/                   ← shared per-project references (optional)

The body filename inside a version directory **echoes** the slug
(``<slug>.md``) — see SKILL.md §"Artifact contract" for the on-disk
contract documented under issue #295.

See parent issue #283 and #295 for the consolidated model. This module
is **scoped to discovery only**: it identifies the project root and the
thread slug for any path under a project. Full BRIEF schema parsing is
sub-deliverable 2 (#285); rubric overlay selection is sub-deliverable 3
(#286).

Public API
----------

``discover_thread_root(path: Path) -> Optional[DiscoveryResult]``
    Walk upward from ``path`` until the project root and thread slug
    are identified. Returns a typed result with the thread root, the
    project root, and the thread's slug.

``DiscoveryResult`` (dataclass)
    Typed return value. ``project_root`` and ``slug`` are always
    populated for any successful match (the project-brief layout is
    the only recognized shape).

``LAYOUT_PROJECT_BRIEF``
    String constant for the recognized layout. Retained as a sentinel
    so downstream consumers (and the audit trail) dispatch on a
    source-of-truth literal even though there's only one shape.

``BRIEF_FILENAME`` / ``DOCUMENTS_FRONTMATTER_KEY``
    Module constants for the on-disk filename (``"BRIEF.md"``) and the
    YAML frontmatter key (``"documents"``) that gates the project
    layout. Surfaced as constants so the layout contract has a single
    source of truth across this module, its tests, and downstream
    consumers.

``has_project_brief(directory: Path) -> bool``
    Cheap predicate: returns True when ``<directory>/BRIEF.md`` exists
    AND its YAML frontmatter has a non-empty ``documents:`` list.
    Surfaced as a standalone helper so the layout-gate rule (project
    BRIEF must have a non-empty ``documents:`` list) is independently
    testable and reusable.

Algorithm
---------

Given a ``path`` (file or directory; may be a version dir, a thread
root, a project root, or any nested artifact like
``<slug>.1/<slug>.md``):

1. Normalize: start from ``path`` if it's a directory, else from
   ``path.parent``. Resolve to an absolute path to make the walk
   filesystem-stable.
2. Walk upward. At each candidate directory ``D``:

   a. **Version-dir check:** if ``D.name`` matches ``<parent>.<N>`` for
      some integer ``N`` (the version-dir naming convention), the
      thread root is ``D.parent``. The project root is ``D.parent.parent``
      iff it has a project BRIEF listing the slug.
   b. **Thread-root check:** if ``D`` contains any subdirectory matching
      ``<D.name>.<N>`` (i.e., version dirs whose stem matches ``D``'s
      basename), ``D`` is the thread root.
   c. **Project-root check:** if ``D`` has ``BRIEF.md`` with a non-empty
      ``documents:`` list AND the original ``path`` lives inside
      ``D/<slug>/`` for one of the slugs we can recognize from the path
      components, treat ``D/<slug>/`` as the thread root.
3. Stop at the filesystem root. Return ``None`` if no thread root
   identified.

Layout gate
-----------

The project-brief layout matches when the parent of the candidate
thread root has a project BRIEF whose ``documents:`` list names the
thread's slug. A stray subdirectory inside a project (not listed in
``documents:``) returns ``None`` rather than being silently promoted
to a thread — discovery is conservative under configuration drift.

A project BRIEF with an **empty** ``documents:`` list (``documents: []``
or ``documents:`` with no value) does NOT satisfy ``has_project_brief``
— discovery returns ``None`` for any path under such a directory. A
project must enumerate at least one document for any thread under it to
be discoverable.

No new Python deps
------------------

YAML frontmatter parsing uses ``yaml.safe_load`` from ``pyyaml``, which
is already declared as a base ``[project]`` dep in ``pyproject.toml``
(load-bearing for ``anvil/lib/rubric.py``). No new dependency is
introduced.

Skill-local first
-----------------

Lives under ``anvil/skills/memo/lib/`` per the CLAUDE.md "skill-local
first, lib promotion later" pattern and the precedent set by
``refs_resolver.py`` (PR #281) and ``rubric_overrides_suffix.py``
(PR #265). Promotion to ``anvil/lib/`` is queued for the second-consumer
trigger — likely ``anvil:proposal`` (which has its own portfolio shape)
or ``anvil:paper``.
"""

from __future__ import annotations

import re
from dataclasses import dataclass
from pathlib import Path
from typing import Optional

from anvil.lib.frontmatter import extract_frontmatter as _extract_frontmatter


# On-disk filename for the brief. Surfaced as a constant so the layout
# contract has a single source of truth across this module, its tests,
# and downstream consumers (BRIEF parser in sub-deliverable 2 shares
# this literal).
BRIEF_FILENAME = "BRIEF.md"

# YAML frontmatter key that gates the project layout. When this key is
# present AND its value is a non-empty list, the BRIEF is a project-level
# BRIEF that enumerates per-document metadata and discovery dispatches
# from it.
DOCUMENTS_FRONTMATTER_KEY = "documents"

# Layout marker string. Retained as a sentinel so the audit trail and
# downstream dispatch surfaces have a stable literal to read; with the
# classic layout retired under #295 there is only one value.
LAYOUT_PROJECT_BRIEF = "project-brief"

# Compiled regex for version-dir naming: <stem>.<N> where N is an
# integer. The stem is captured so we can match it against the parent
# directory's basename when identifying a version dir. The pattern
# anchors the dot-N at the end so e.g. "thread.draft" doesn't match.
_VERSION_DIR_RE = re.compile(r"^(?P<stem>.+)\.(?P<num>\d+)$")


@dataclass(frozen=True)
class DiscoveryResult:
    """Typed return value from :func:`discover_thread_root`.

    Attributes
    ----------
    thread_root
        The directory that holds (or would hold) the version dirs
        ``<thread_root.name>.N/`` for this thread. Always populated;
        equals ``<project_root>/<slug>/``.
    layout
        Always :data:`LAYOUT_PROJECT_BRIEF`. The field is retained
        (rather than removed) so the dataclass shape stays stable for
        downstream consumers and the audit trail records a single
        source-of-truth literal.
    project_root
        The directory containing the project BRIEF (``<project>/``).
        Always populated.
    slug
        The thread's slug as it appears in the project BRIEF's
        ``documents:`` list. Always populated; matches
        ``thread_root.name``.
    """

    thread_root: Path
    layout: str
    project_root: Path
    slug: str


# ---------------------------------------------------------------------------
# YAML frontmatter helpers
# ---------------------------------------------------------------------------
#
# ``_extract_frontmatter`` used to be defined here; it is now the shared
# ``anvil/lib/frontmatter.py::extract_frontmatter`` primitive (issue #1075),
# imported above and aliased to the historical private name so every call
# site in this module (and this module's own downstream re-exporters,
# e.g. ``project_brief.py``) is unchanged.


def has_project_brief(directory: Path) -> bool:
    """Return True when ``<directory>/BRIEF.md`` is a project-level BRIEF.

    A BRIEF qualifies as **project-level** when:

    1. ``<directory>/BRIEF.md`` exists and is a file.
    2. Its YAML frontmatter parses to a dict.
    3. The frontmatter contains a ``documents:`` key whose value is a
       **non-empty list**.

    Returns False for every other shape (missing BRIEF, no frontmatter,
    malformed YAML, ``documents:`` absent, ``documents:`` empty list,
    ``documents:`` non-list value). This is the layout gate: discovery
    only matches when the documents list is non-empty.

    The function does NOT validate the per-entry schema of the
    ``documents:`` list — that's sub-deliverable 2 (#285). It only
    checks "non-empty list". A list containing entries that fail later
    schema validation still triggers project-brief layout dispatch; the
    BRIEF parser will surface the schema errors downstream.

    Parameters
    ----------
    directory
        Candidate project root.

    Returns
    -------
    bool
        True iff ``directory`` is a project root carrying a non-empty
        documents list.
    """
    if not directory.is_dir():
        return False
    brief = directory / BRIEF_FILENAME
    if not brief.is_file():
        return False
    try:
        text = brief.read_text(encoding="utf-8")
    except OSError:
        return False
    fm = _extract_frontmatter(text)
    if fm is None:
        return False
    docs = fm.get(DOCUMENTS_FRONTMATTER_KEY)
    if not isinstance(docs, list):
        return False
    return len(docs) > 0


def _project_brief_lists_slug(project_dir: Path, slug: str) -> bool:
    """Return True when ``<project_dir>/BRIEF.md``'s ``documents:`` lists ``slug``.

    Each entry in the ``documents:`` list is checked for a ``slug:``
    field matching ``slug``. The check is intentionally lenient on the
    surrounding entry shape — a string entry equal to ``slug`` also
    matches (forward-compat with a shorthand form). The full per-entry
    schema (artifact_type, target_length, etc.) is sub-deliverable 2;
    this helper only needs to recognize "is this slug in the list".

    Returns False when:

    - ``project_dir`` is not a project root (no project BRIEF), OR
    - the documents list is empty, OR
    - no entry's ``slug:`` matches ``slug``.
    """
    if not has_project_brief(project_dir):
        return False
    brief = project_dir / BRIEF_FILENAME
    try:
        text = brief.read_text(encoding="utf-8")
    except OSError:
        return False
    fm = _extract_frontmatter(text)
    if fm is None:
        return False
    docs = fm.get(DOCUMENTS_FRONTMATTER_KEY)
    if not isinstance(docs, list):
        return False
    for entry in docs:
        if isinstance(entry, dict):
            if entry.get("slug") == slug:
                return True
        elif isinstance(entry, str):
            if entry == slug:
                return True
    return False


# ---------------------------------------------------------------------------
# Directory-shape predicates
# ---------------------------------------------------------------------------


def _is_version_dir(directory: Path) -> bool:
    """Return True when ``directory`` is a version dir ``<parent>.<N>``.

    A version dir's basename must match ``<parent.name>.<N>`` for some
    non-negative integer ``N``. This is the on-disk convention codified
    across every memo / proposal / paper thread.
    """
    match = _VERSION_DIR_RE.match(directory.name)
    if match is None:
        return False
    return match.group("stem") == directory.parent.name


def _contains_version_dirs(directory: Path) -> bool:
    """Return True when ``directory`` contains any ``<directory.name>.<N>/`` subdir."""
    if not directory.is_dir():
        return False
    try:
        children = list(directory.iterdir())
    except OSError:
        return False
    for child in children:
        if not child.is_dir():
            continue
        match = _VERSION_DIR_RE.match(child.name)
        if match is None:
            continue
        if match.group("stem") == directory.name:
            return True
    return False


# ---------------------------------------------------------------------------
# Layout resolution
# ---------------------------------------------------------------------------


def _resolve_layout(thread_root: Path) -> Optional[DiscoveryResult]:
    """Build a :class:`DiscoveryResult` for a candidate ``thread_root``.

    Returns the discovery result iff the parent directory carries a
    project BRIEF whose ``documents:`` list names this thread's slug.
    Otherwise returns ``None`` — every thread root must be acknowledged
    by a project BRIEF under #295.

    The slug-in-documents check is load-bearing: a candidate thread
    that has version dirs but whose parent does not list its slug is a
    stray (perhaps a draft that hasn't been added to the project BRIEF
    yet, or a directory that landed under a project by mistake). The
    conservative choice under #295 is to treat such a thread as
    not-yet-discoverable rather than silently returning a result with
    no project context.
    """
    slug = thread_root.name
    parent = thread_root.parent
    if not _project_brief_lists_slug(parent, slug):
        return None
    return DiscoveryResult(
        thread_root=thread_root,
        layout=LAYOUT_PROJECT_BRIEF,
        project_root=parent,
        slug=slug,
    )


# ---------------------------------------------------------------------------
# Public discovery entry point
# ---------------------------------------------------------------------------


def discover_thread_root(path: Path) -> Optional[DiscoveryResult]:
    """Walk upward from ``path`` and return the enclosing thread root.

    Recognizes the project-as-thread-root layout: every thread lives
    inside a project root with a project-level ``BRIEF.md`` whose
    ``documents:`` list names the thread's slug.

    The walk terminates at the first thread root encountered.

    Parameters
    ----------
    path
        Any path under a thread or project. May be a file (e.g. a memo
        body inside a version dir), a directory (a version dir, a
        thread root, a project root), or even a non-existent path
        whose parent components exist (the walk uses ``Path``
        arithmetic and consults the filesystem only at each candidate
        directory).

    Returns
    -------
    Optional[DiscoveryResult]
        ``None`` when no thread root is identifiable — the walk
        reached the filesystem root without finding a version dir
        pattern under an acknowledging project BRIEF. Otherwise a
        typed result carrying the thread root, layout marker, project
        root, and slug.

    Algorithm
    ---------
    See module docstring for the full walk-up algorithm. Summary:

    1. Normalize ``path`` to a directory (use ``.parent`` if file).
    2. Walk upward, examining each candidate directory ``D``:

       - If ``D`` is a version dir (``<parent>.<N>``), the thread
         root is ``D.parent``.
       - Else if ``D`` contains version dirs (``<D.name>.<N>``), the
         thread root is ``D``.
       - Else if ``D`` is a project root (has a project BRIEF), and
         the original ``path`` lives inside ``D/<slug>/`` for some
         listed slug, the thread root is ``D/<slug>/``.

    3. Stop at the first match, or at the filesystem root.

    Discovery only returns a match when the candidate thread root's
    parent has a project BRIEF whose ``documents:`` list names the
    thread's slug. Stray subdirectories inside a project (not listed)
    return ``None``.
    """
    # Normalize to a directory. A non-existent path is tolerated; the
    # walk uses Path arithmetic and only consults the filesystem at
    # each candidate.
    p = Path(path)
    try:
        # Use ``.absolute()`` rather than ``.resolve()`` so we don't
        # collapse symlinks the caller deliberately set up — the
        # discovery walk is logical (operates on the path the caller
        # passed), not physical.
        original = p.absolute()
    except OSError:
        original = p

    current = original if original.is_dir() else original.parent

    # The walk-up terminates when ``current == current.parent`` (the
    # filesystem root). ``Path.parents`` would also work, but the
    # explicit loop makes the termination condition load-bearing-
    # readable for the test author chasing edge cases.
    visited: set = set()
    while True:
        # Defensive guard against pathological loops (resolved paths
        # never loop, but a caller passing a logical path with ``..``
        # could in principle).
        key = str(current)
        if key in visited:
            return None
        visited.add(key)

        # (a) Version-dir check: ``current`` is a version dir.
        if _is_version_dir(current):
            thread_root = current.parent
            return _resolve_layout(thread_root)

        # (b) Thread-root check: ``current`` contains version dirs.
        if _contains_version_dirs(current):
            return _resolve_layout(current)

        # (c) Project-root check: ``current`` is a project root and
        #     the original path lives inside one of its slug subdirs.
        if has_project_brief(current):
            # Determine which slug the original path was inside. The
            # first path component between ``current`` and ``original``
            # is the slug candidate.
            try:
                rel = original.relative_to(current)
            except ValueError:
                rel = None
            if rel is not None and rel.parts:
                slug = rel.parts[0]
                thread_root = current / slug
                if _project_brief_lists_slug(current, slug):
                    return DiscoveryResult(
                        thread_root=thread_root,
                        layout=LAYOUT_PROJECT_BRIEF,
                        project_root=current,
                        slug=slug,
                    )
            # We're at a project root but couldn't tie ``original`` to
            # a listed slug — either the path is the project root
            # itself, or it's in an unlisted subdir. Treat as not-a-
            # thread (return None rather than guessing a slug).
            return None

        # Stop at the filesystem root.
        if current.parent == current:
            return None
        current = current.parent


__all__ = [
    "BRIEF_FILENAME",
    "DOCUMENTS_FRONTMATTER_KEY",
    "DiscoveryResult",
    "LAYOUT_PROJECT_BRIEF",
    "discover_thread_root",
    "has_project_brief",
]
