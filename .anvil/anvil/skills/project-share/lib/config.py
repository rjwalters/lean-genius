"""Skill-local export configuration for `anvil:project-share` (issue #396).

Parses the optional ``export:`` block out of the project ``BRIEF.md``
frontmatter into a typed :class:`ExportConfig`. Per the curator's design
the parser is **skill-local** — the shared
``anvil/lib/project_brief.py::ProjectBrief`` model is NOT extended
(``ProjectBrief`` is ``extra="forbid"`` on the model but its parse path
``_parse_brief_body`` explicitly ignores unknown top-level frontmatter
keys, so an ``export:`` block is safe to add to a BRIEF today with zero
changes to the shared parser).

Zero-config contract: a BRIEF with no ``export:`` block at all yields
:class:`ExportConfig` defaults — full export of every ``documents:``
entry in BRIEF order, refs + research + assets included, the default
strip list applied, output to ``SHARE/``.

Config surface (all fields optional)::

    export:
      order: [series-a-deck, investment-memo, ...]  # include-list AND order
      include_research: true     # default true
      include_refs: true         # default true
      include_assets: true       # default true
      strip: [...]               # default: _progress.json, changelog.md,
                                 #          "_*.json", "*.tmp", ".tmp*",
                                 #          "__pycache__", "*.pyc", ".DS_Store"
      out: SHARE                 # default SHARE
      cover: SHARE-README.md     # optional recipient-facing cover note
      cover_as: README.md        # optional dest filename; default README.md

``cover`` (issue #757): a hand-written recipient-facing note (what this
share is, read order, what's being asked of the reader) is destroyed on
every marker-guarded blow-away rebuild if it lives inside the export
root itself. Pointing ``export.cover`` at a durable source file OUTSIDE
the out dir (e.g. a project-root file, never itself exported) means the
apply step copies it into the export root on every run, so rebuilds and
``--zip`` include it automatically. ``cover`` is a path relative to the
project root; the copy destination inside the export root defaults to
``README.md`` and is overridable via ``cover_as`` (a bare filename, no
path separators). Both the source-file existence check and the
collision check against the ``EXPORT.md`` marker filename happen at
plan time (:mod:`plan`), not here — this parser has no knowledge of the
project root or the marker filename.

``order`` semantics (locked at curation): when present it is the
authoritative include-list and ordering — slugs omitted from ``order``
are excluded from the export (with an informational note); slugs in
``order`` that do not appear in BRIEF ``documents:`` are a hard error.
The cross-check against the BRIEF happens in :mod:`plan` (this module
has no knowledge of the documents list).
"""

from __future__ import annotations

import re
from pathlib import Path
from typing import Any, List, Optional

from pydantic import BaseModel, ConfigDict, Field, ValidationError, field_validator

from anvil.lib.frontmatter import extract_frontmatter as _extract_frontmatter

# The BRIEF filename mirrors ``anvil/lib/project_brief.py`` (single
# on-disk convention).
BRIEF_FILENAME = "BRIEF.md"

# The top-level BRIEF frontmatter key this skill owns.
EXPORT_FRONTMATTER_KEY = "export"

# Default output directory name. The skill is named ``project-share``
# (not ``project-export``) because (a) it matches this directory and
# (b) ``anvil/lib/export_schema.py`` already owns the word "export"
# for an unrelated meaning (emitting JSON Schema documents).
DEFAULT_OUT = "SHARE"

# Default strip list: anvil bookkeeping that must never reach an
# outside recipient. ``_*.json`` covers ``_progress.json`` /
# ``_meta.json`` / any future underscore-prefixed sidecar JSON;
# ``.tmp*`` covers the ``staged_sidecar`` staging convention
# (``anvil/lib/sidecar.py``); ``__pycache__`` (a directory-name
# pattern — matched per path component by ``is_stripped()`` in
# :mod:`plan`, so it excludes the whole subtree), ``*.pyc``, and
# ``.DS_Store`` cover Python bytecode caches and macOS droppings that
# can end up in a project's ``research/`` pool (issue #756).
DEFAULT_STRIP = (
    "_progress.json",
    "changelog.md",
    "_*.json",
    "*.tmp",
    ".tmp*",
    "__pycache__",
    "*.pyc",
    ".DS_Store",
)

# Default destination filename for `export.cover` inside the export root
# (issue #757). Deliberately distinct from `MARKER_FILENAME` ("EXPORT.md")
# in `lib/plan.py` — the plan-time collision guard checks `cover_as`
# against that name whenever `cover` is configured.
DEFAULT_COVER_AS = "README.md"


class ExportConfig(BaseModel):
    """Typed view of the BRIEF ``export:`` frontmatter block.

    Attributes
    ----------
    order
        Optional explicit doc ordering. When present it is the
        authoritative include-list AND ordering for the export. When
        absent (``None``), every BRIEF ``documents:`` entry exports in
        BRIEF order.
    include_research
        Copy the shared ``<project>/research/`` pool to
        ``<out>/research/`` (default True).
    include_refs
        Copy per-thread ``<project>/<slug>/refs/`` into each doc folder
        (default True; only when non-empty).
    include_assets
        Copy subdirectories of the resolved version dir (``figures/``,
        ``exhibits/``, ...) alongside the source body. When False, only
        top-level files of the version dir are copied (default True).
    strip
        Filename patterns (``fnmatch`` against every path component)
        omitted from the export. Defaults to :data:`DEFAULT_STRIP`.
    out
        Output directory name under the project root (default
        ``SHARE``). Must be a bare directory name — no path separators.
    cover
        Optional path (relative to the project root) to a recipient-facing
        cover note that is copied into the export root on every apply, so
        it survives the marker-guarded blow-away rebuild (default
        ``None`` — no cover file copied).
    cover_as
        Destination filename for ``cover`` inside the export root
        (default ``README.md``). Must be a bare filename — no path
        separators. Ignored when ``cover`` is unset.
    """

    model_config = ConfigDict(extra="forbid")

    order: Optional[List[str]] = Field(default=None)
    include_research: bool = Field(default=True)
    include_refs: bool = Field(default=True)
    include_assets: bool = Field(default=True)
    strip: List[str] = Field(default_factory=lambda: list(DEFAULT_STRIP))
    out: str = Field(default=DEFAULT_OUT)
    cover: Optional[str] = Field(default=None)
    cover_as: str = Field(default=DEFAULT_COVER_AS)

    @field_validator("order")
    @classmethod
    def _order_entries_nonempty_unique(
        cls, value: Optional[List[str]]
    ) -> Optional[List[str]]:
        if value is None:
            return None
        seen = set()
        for i, entry in enumerate(value):
            if not isinstance(entry, str) or not entry.strip():
                raise ValueError(
                    f"export.order[{i}] must be a non-empty string; got "
                    f"{entry!r}. Suggested fix: list document slugs only."
                )
            if entry in seen:
                raise ValueError(
                    f"export.order lists slug {entry!r} more than once. "
                    f"Suggested fix: remove the duplicate entry."
                )
            seen.add(entry)
        return value

    @field_validator("strip")
    @classmethod
    def _strip_entries_nonempty(cls, value: List[str]) -> List[str]:
        for i, entry in enumerate(value):
            if not isinstance(entry, str) or not entry.strip():
                raise ValueError(
                    f"export.strip[{i}] must be a non-empty string "
                    f"pattern; got {entry!r}."
                )
        return value

    @field_validator("out")
    @classmethod
    def _out_is_bare_dirname(cls, value: str) -> str:
        if not value or not value.strip():
            raise ValueError(
                "export.out must be a non-empty directory name; got "
                f"{value!r}."
            )
        if "/" in value or "\\" in value:
            raise ValueError(
                f"export.out must be a bare directory name under the "
                f"project root (no path separators); got {value!r}. "
                f"Suggested fix: use a single name like `SHARE`."
            )
        if value in (".", ".."):
            raise ValueError(
                f"export.out must not be {value!r} — it would resolve to "
                f"the project root (or above) and the marker-guarded "
                f"rebuild would refuse it anyway."
            )
        return value

    @field_validator("cover")
    @classmethod
    def _cover_is_safe_relative_path(cls, value: Optional[str]) -> Optional[str]:
        if value is None:
            return None
        if not isinstance(value, str) or not value.strip():
            raise ValueError(
                f"export.cover must be a non-empty path string; got "
                f"{value!r}."
            )
        if value.startswith("/") or value.startswith("\\"):
            raise ValueError(
                f"export.cover must be a path relative to the project "
                f"root (no leading path separator); got {value!r}. "
                f"Suggested fix: use a project-root-relative path like "
                f"`SHARE-README.md`."
            )
        if any(part == ".." for part in re.split(r"[\\/]+", value)):
            raise ValueError(
                f"export.cover must not contain a `..` path-traversal "
                f"component; got {value!r}. Suggested fix: use a path "
                f"that stays under the project root, e.g. "
                f"`refs/cover-note.md`."
            )
        return value

    @field_validator("cover_as")
    @classmethod
    def _cover_as_is_bare_filename(cls, value: str) -> str:
        if not value or not value.strip():
            raise ValueError(
                f"export.cover_as must be a non-empty filename; got "
                f"{value!r}."
            )
        if "/" in value or "\\" in value:
            raise ValueError(
                f"export.cover_as must be a bare filename under the "
                f"export root (no path separators); got {value!r}. "
                f"Suggested fix: use a single name like `README.md`."
            )
        return value


# ``_extract_frontmatter`` used to be defined here (a local copy mirroring
# ``anvil/lib/project_brief.py``'s); it is now the shared
# ``anvil/lib/frontmatter.py::extract_frontmatter`` primitive (issue
# #1075), imported above and aliased to the historical private name so
# every call site in this module is unchanged.


def load_export_config(project_dir: Path) -> ExportConfig:
    """Load the ``export:`` block from ``<project_dir>/BRIEF.md``.

    Returns
    -------
    ExportConfig
        Parsed config; all-defaults when the BRIEF has no ``export:``
        block (the zero-config contract).

    Raises
    ------
    FileNotFoundError
        When ``<project_dir>/BRIEF.md`` does not exist.
    ValueError
        When the BRIEF has no parseable frontmatter, or the ``export:``
        block is present but malformed (wrong type, unknown key, bad
        ``out`` name, non-string ``order`` / ``strip`` entries).
    """
    project_dir = Path(project_dir)
    brief_path = project_dir / BRIEF_FILENAME
    if not brief_path.is_file():
        raise FileNotFoundError(
            f"No BRIEF found at {brief_path}. The export reads its "
            f"config (and the documents list) from the project BRIEF."
        )
    text = brief_path.read_text(encoding="utf-8")
    fm = _extract_frontmatter(text)
    if fm is None:
        raise ValueError(
            f"BRIEF at {brief_path} has no parseable YAML frontmatter."
        )

    raw: Any = fm.get(EXPORT_FRONTMATTER_KEY)
    if raw is None:
        return ExportConfig()
    if not isinstance(raw, dict):
        raise ValueError(
            f"BRIEF.export must be a mapping (an `export:` block with "
            f"keys); got {type(raw).__name__} at {brief_path}."
        )
    try:
        return ExportConfig(**raw)
    except ValidationError as exc:
        raise ValueError(
            f"BRIEF.export at {brief_path} failed schema validation: {exc}"
        ) from exc


__all__ = [
    "BRIEF_FILENAME",
    "DEFAULT_COVER_AS",
    "DEFAULT_OUT",
    "DEFAULT_STRIP",
    "EXPORT_FRONTMATTER_KEY",
    "ExportConfig",
    "load_export_config",
]
