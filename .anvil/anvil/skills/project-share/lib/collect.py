"""Per-document collection for `anvil:project-share` (issue #396).

For each BRIEF ``documents:`` slug, resolve the thread's current
version directory via the canonical ``.latest`` resolver
(``anvil/lib/latest_resolution.py::resolve_latest``), dereference it to
a concrete on-disk version dir, classify the resolution mode, locate
the per-thread ``refs/`` directory, and fingerprint any rendered PDFs.

Resolution caveat (load-bearing, per the curator's enrichment): when a
``<slug>.latest`` symlink or real directory exists, ``resolve_latest``
returns the ``.latest`` path **itself**, not the dereferenced target.
This module calls ``.resolve()`` so the concrete version-dir name
(e.g., ``investment-memo.4``) — not the symbolic ``.latest`` — is what
lands in ``EXPORT.md`` provenance.

Failure tolerance: a thread that fails to resolve (no version dirs;
dangling ``.latest`` symlink) yields a :class:`DocCollection` carrying
a ``failure`` reason instead of raising — other docs still export and
the orchestrator turns failures into a nonzero exit (AC 9).
"""

from __future__ import annotations

import hashlib
from dataclasses import dataclass, field
from pathlib import Path
from typing import List, Optional

from anvil.lib.latest_resolution import LATEST, resolve_latest

# Resolution-mode labels recorded in EXPORT.md provenance.
RESOLUTION_PINNED_SYMLINK = "pinned-symlink"
RESOLUTION_REAL_DIR = "real-dir"
RESOLUTION_WALK_TO_HIGHEST = "walk-to-highest"

# Project-level shared evidence pool (copied once to <out>/research/).
RESEARCH_DIRNAME = "research"

# Per-thread references directory (thread ROOT, sibling of the version
# dirs — NOT inside them).
REFS_DIRNAME = "refs"


@dataclass
class PdfInfo:
    """A rendered PDF found at the top level of the resolved version dir."""

    filename: str
    sha256: str


@dataclass
class DocCollection:
    """Resolution outcome for one BRIEF ``documents:`` slug.

    Attributes
    ----------
    slug
        The thread slug.
    thread_dir
        ``<project>/<slug>/`` (may not exist for unstarted threads).
    resolved_dir
        The **dereferenced** concrete version directory, or ``None``
        when resolution failed.
    resolved_name
        The concrete version-dir name (``investment-memo.4``) recorded
        in EXPORT.md, or ``None`` on failure.
    resolution_mode
        One of :data:`RESOLUTION_PINNED_SYMLINK`,
        :data:`RESOLUTION_REAL_DIR`, :data:`RESOLUTION_WALK_TO_HIGHEST`;
        ``None`` on failure.
    refs_dir
        ``<thread_dir>/refs/`` when it exists and contains at least one
        file (recursively); ``None`` otherwise. The include/exclude
        decision (``include_refs``) is the planner's job — collection
        just reports what is on disk.
    pdfs
        Top-level ``*.pdf`` files in the resolved version dir, with
        SHA-256 fingerprints for EXPORT.md provenance (AC 11).
    failure
        Human-readable reason when the thread could not be resolved;
        ``None`` on success.
    """

    slug: str
    thread_dir: Path
    resolved_dir: Optional[Path] = None
    resolved_name: Optional[str] = None
    resolution_mode: Optional[str] = None
    refs_dir: Optional[Path] = None
    pdfs: List[PdfInfo] = field(default_factory=list)
    failure: Optional[str] = None

    @property
    def failed(self) -> bool:
        return self.failure is not None


def sha256_file(path: Path) -> str:
    """SHA-256 hex digest of a file's bytes."""
    h = hashlib.sha256()
    with open(path, "rb") as fh:
        for chunk in iter(lambda: fh.read(1 << 16), b""):
            h.update(chunk)
    return h.hexdigest()


def _dir_has_files(directory: Path) -> bool:
    """True when ``directory`` contains at least one file, recursively."""
    try:
        for child in directory.rglob("*"):
            if child.is_file():
                return True
    except OSError:
        return False
    return False


def collect_doc(project_dir: Path, slug: str) -> DocCollection:
    """Resolve one slug's thread to a concrete version dir.

    Never raises on per-doc problems — failures are recorded on the
    returned :class:`DocCollection` so other docs still export.
    """
    project_dir = Path(project_dir)
    thread_dir = project_dir / slug
    out = DocCollection(slug=slug, thread_dir=thread_dir)

    if not thread_dir.is_dir():
        out.failure = (
            f"thread directory does not exist: {thread_dir} (the BRIEF "
            f"lists `{slug}` but no draft has been started)"
        )
        return out

    raw = resolve_latest(thread_dir, slug)
    if raw is None:
        out.failure = (
            f"no version directories found under {thread_dir} (expected "
            f"`{slug}.<N>/` or a `{slug}.{LATEST}` reference)"
        )
        return out

    if raw.name == f"{slug}.{LATEST}":
        mode = (
            RESOLUTION_PINNED_SYMLINK
            if raw.is_symlink()
            else RESOLUTION_REAL_DIR
        )
    else:
        mode = RESOLUTION_WALK_TO_HIGHEST

    resolved = raw.resolve()
    if not resolved.is_dir():
        out.failure = (
            f"`{slug}.{LATEST}` resolves to {resolved}, which does not "
            f"exist (dangling symlink with no fallback)"
        )
        return out

    out.resolved_dir = resolved
    out.resolved_name = resolved.name
    out.resolution_mode = mode

    # Per-thread refs live at the THREAD ROOT (sibling of the version
    # dirs), per the post-#295 project model.
    refs_dir = thread_dir / REFS_DIRNAME
    if refs_dir.is_dir() and _dir_has_files(refs_dir):
        out.refs_dir = refs_dir

    # Rendered PDFs at the top level of the resolved version dir.
    try:
        pdf_paths = sorted(
            p
            for p in resolved.iterdir()
            if p.is_file() and p.suffix.lower() == ".pdf"
        )
    except OSError:
        pdf_paths = []
    for pdf in pdf_paths:
        out.pdfs.append(PdfInfo(filename=pdf.name, sha256=sha256_file(pdf)))

    return out


def collect_research(project_dir: Path) -> Optional[Path]:
    """Return ``<project>/research/`` when present and non-empty."""
    research = Path(project_dir) / RESEARCH_DIRNAME
    if research.is_dir() and _dir_has_files(research):
        return research
    return None


__all__ = [
    "DocCollection",
    "PdfInfo",
    "REFS_DIRNAME",
    "RESEARCH_DIRNAME",
    "RESOLUTION_PINNED_SYMLINK",
    "RESOLUTION_REAL_DIR",
    "RESOLUTION_WALK_TO_HIGHEST",
    "collect_doc",
    "collect_research",
    "sha256_file",
    "_dir_has_files",
]
