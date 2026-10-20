"""Thread-level BRIEF.md helpers (issue #1121 split).

Part of the ``anvil.lib.project_brief`` package — see the package
``__init__.py`` docstring for the full module. This submodule owns three
independent thread-level (not project-level) surfaces:

- The freeform-prose thread ``BRIEF.md`` ``recommendation_target`` reader
  (issue #348, :func:`load_recommendation_target`) and its dual-surface
  resolver (issue #837, :func:`load_recommendation_target_resolved`).
- The ``pending_sources`` frontmatter companion knob for
  ``anvil/lib/pending_marker.py`` (issue #842, :class:`PendingSource` /
  :func:`resolve_pending_sources`).
- The body-filename helper (issue #295, :func:`body_filename_for`).

Split from the pre-#1121 monolithic ``anvil/lib/project_brief.py`` along its
existing "Thread-level BRIEF.md helpers" / "Thread-level ``pending_sources``
frontmatter" / "Body-filename helper" section boundaries (grouped into one
module — all three are thread-root-scoped helpers, as opposed to the
project-root-scoped parser in ``loader.py``). No behavior change.
"""

from __future__ import annotations

from pathlib import Path
from typing import Any, List, Literal, Optional, Tuple

from pydantic import BaseModel, ConfigDict, Field

from anvil.lib.frontmatter import extract_frontmatter as _extract_frontmatter
from anvil.lib.project_brief.loader import load_project_brief
from anvil.lib.project_brief.types import _RECOGNIZED_RECOMMENDATION_TARGETS
from anvil.lib.project_discovery import BRIEF_FILENAME

# ---------------------------------------------------------------------------
# Thread-level BRIEF.md helpers (issue #348)
# ---------------------------------------------------------------------------
#
# The thread-level ``<thread>/BRIEF.md`` is a SEPARATE on-disk surface from the
# project-level ``<project>/BRIEF.md`` parsed above. The thread-level BRIEF
# is intentionally **freeform prose** with optional YAML frontmatter — it
# documents the drafter's context (company / sector / stage / check_size)
# and the operator's recommendation posture. Recognized informal frontmatter
# keys are documented in ``anvil/skills/memo/commands/memo-draft.md`` step 3:
# ``company``, ``sector``, ``stage``, ``check_size``, and
# ``recommendation_target`` (one of ``invest`` / ``pass`` / ``conditional`` /
# ``undecided``).
#
# These keys are **purely informational passthrough** for most consumers; the
# drafter reads them into context but no structural module parses them.
# Issue #348 promotes the one structurally-load-bearing key —
# ``recommendation_target`` — into a typed signal so the reviewer can
# calibrate dim 1 (Recommendation clarity) appropriately when the operator
# explicitly declared the thread is in pre-decision mode
# (``recommendation_target: undecided``).
#
# The helper is intentionally **lenient** — every absence path returns
# ``None`` so callers can branch on ``is None`` without try/except. The
# contract mirrors :func:`load_rubric_overrides_for_slug` for the
# project-level surface.
# _RECOGNIZED_RECOMMENDATION_TARGETS moved to ``types.py`` (issue #1121
# split) — it is also consumed by ``fields.py::_validate_recommendation_target``,
# and a shared constant cannot live downstream of both its consumers
# without a circular import. See ``types.py`` for the full comment.




def load_recommendation_target(
    thread_dir: Path,
) -> Optional[Literal["invest", "pass", "conditional", "undecided"]]:
    """Read ``recommendation_target`` from a thread-level ``BRIEF.md``.

    Issue #348 promotes the informal-but-documented ``recommendation_target``
    frontmatter key (per ``memo-draft.md`` step 3 and
    ``templates/BRIEF.fresh.md.example``) into a typed signal that the
    reviewer can calibrate dim 1 (Recommendation clarity) against.

    Parameters
    ----------
    thread_dir
        The thread root directory (the directory holding ``BRIEF.md`` for
        the thread, e.g., ``<project>/<slug>/``). NOT a version directory.

    Returns
    -------
    Optional[Literal["invest", "pass", "conditional", "undecided"]]
        The verbatim ``recommendation_target`` value when present and in the
        closed set. ``None`` for every absence / malformed path:

        - ``<thread_dir>/BRIEF.md`` does not exist.
        - The file exists but has no YAML frontmatter (no opening ``---``
          delimiter, missing closing delimiter, malformed YAML).
        - The frontmatter is a parseable dict but contains no
          ``recommendation_target`` key.
        - The frontmatter value is not in the closed set
          (``invest`` / ``pass`` / ``conditional`` / ``undecided``) — e.g.,
          ``Undecided`` (capitalized), ``tbd``, ``maybe``, ``?``, an integer,
          a list, a null. The reviewer falls back to byte-identical
          pre-#348 behavior for these noise values.

    Notes
    -----
    Lenient by design — never raises. The contract mirrors
    :func:`load_rubric_overrides_for_slug`'s "empty / None on every absence
    path" lenient form so the reviewer's zero-impact backwards-compat is
    preserved exactly for any thread that pre-dates this helper or that
    chose not to set the field.

    The thread-level BRIEF is a SEPARATE surface from the project-level
    BRIEF parsed by :func:`load_project_brief`. The two share frontmatter
    extraction primitive (:func:`_extract_frontmatter`) but the schema
    contracts are distinct: project-level BRIEF is STRICT (typo in
    ``artifact_type`` raises); thread-level BRIEF is FREEFORM PROSE with
    informal frontmatter. This helper extracts only the one structured
    field; everything else is passed through to the drafter as
    informational context.
    """
    if not isinstance(thread_dir, Path):
        # Defensive: callers may inadvertently pass a string. The helper is
        # documented to take a Path; convert rather than raise to preserve
        # the lenient contract.
        try:
            thread_dir = Path(thread_dir)
        except Exception:
            return None

    brief_path = thread_dir / BRIEF_FILENAME
    if not brief_path.is_file():
        return None

    try:
        text = brief_path.read_text(encoding="utf-8")
    except OSError:
        return None

    fm = _extract_frontmatter(text)
    if fm is None:
        return None

    value = fm.get("recommendation_target")
    # Closed-set membership check. Anything not on the recognized list —
    # including booleans, ints, lists, dicts, None, and string typos —
    # falls through to None per the lenient contract.
    if isinstance(value, str) and value in _RECOGNIZED_RECOMMENDATION_TARGETS:
        return value  # type: ignore[return-value]
    return None


# ---------------------------------------------------------------------------
# Thread-level ``pending_sources`` frontmatter (issue #842)
# ---------------------------------------------------------------------------
#
# The optional companion knob for ``anvil/lib/pending_marker.py``: a thread
# MAY declare the pending-measurement sources it expects to resolve over its
# lifetime in ``<thread>/BRIEF.md`` YAML frontmatter. This is a REPORTING AID
# only — it has NO effect on the pending-marker gate itself (an undeclared
# marker still gates; a declared-but-never-written source is not a defect).
# The pending-marker critics use the declared source LABELS to report which
# declared sources are already resolved vs. still outstanding.
#
# The validator/resolver are modeled on the ``spec_ref`` / ``code_ref``
# companion-input pattern (:func:`_validate_companion_ref` /
# :func:`resolve_spec_ref`) — the parsing/validation lives HERE (the module
# that owns BRIEF frontmatter), not in a bespoke parser inside
# ``pending_marker.py``. Unlike the companion-ref string/glob shape, a
# pending source needs a small dedicated model — a bare label OR a
# ``{source, expected_by}`` mapping — so it carries its own Pydantic type.


class PendingSource(BaseModel):
    """One declared pending-measurement source (issue #842).

    A reporting-aid entry from a thread ``BRIEF.md``'s ``pending_sources``
    frontmatter. ``source`` is the label a ``[PENDING <source>]`` body
    marker names (a benchmark-run id, a vendor name, "Q3 earnings call");
    ``expected_by`` is an optional free-form note on when it is expected to
    resolve (a date, a milestone). Neither field gates anything.
    """

    model_config = ConfigDict(extra="forbid")

    source: str = Field(
        ...,
        description=(
            "The pending source label — matches the ``<source>`` of a "
            "``[PENDING <source>]`` body marker. Non-empty."
        ),
    )
    expected_by: Optional[str] = Field(
        None,
        description=(
            "Optional free-form note on when the value is expected to "
            "resolve (a date, a milestone). Purely informational."
        ),
    )


class PendingSourcesTypeError(ValueError):
    """Raised when ``pending_sources`` is declared with the wrong shape (issue #842).

    A distinguishable ``ValueError`` subclass mirroring
    :class:`CompanionRefTypeError`: it lets the lenient resolver
    (:func:`resolve_pending_sources`) tell "the whole BRIEF is
    structurally invalid" apart from "the ``pending_sources`` block itself
    is malformed" (a declared-but-broken reporting knob). Because it
    subclasses ``ValueError``, strict callers still treat a malformed
    ``pending_sources`` as a hard schema error.
    """


def _validate_pending_sources(
    raw: Any, field_path: str = "pending_sources"
) -> Optional[List[PendingSource]]:
    """Validate a raw ``pending_sources`` frontmatter value (issue #842).

    Accepts a YAML list whose elements are each EITHER a bare non-empty
    string (the common case — normalized to ``PendingSource(source=...)``)
    OR a mapping with a required non-empty ``source`` and an optional
    ``expected_by``. Normalizes to ``Optional[List[PendingSource]]``.

    Normalization rules (mirroring :func:`_validate_companion_ref`'s
    declared-but-broken posture):

    - ``raw is None`` → ``None`` (undeclared; reporting tier silent-off).
    - ``raw`` an empty list → ``None`` (declared-but-empty is off).
    - ``raw`` a list → one :class:`PendingSource` per element, preserving
      declaration order. A malformed element (empty string, a mapping with
      no/empty ``source``, an unknown key, or any non-str/non-mapping
      value) raises :class:`PendingSourcesTypeError` (the whole knob is
      poisoned, not the single element skipped).
    - ``raw`` any other type (string, int, dict, …) → raise
      :class:`PendingSourcesTypeError`.
    """
    if raw is None:
        return None
    if not isinstance(raw, list):
        raise PendingSourcesTypeError(
            f"BRIEF.{field_path} must be a list of source labels or "
            f"{{source, expected_by}} mappings; got "
            f"{type(raw).__name__}: {raw!r} — suggested fix: write it as a "
            f"YAML list, e.g. `pending_sources: [benchmark-run-2024-11, "
            f"vendor-quote-acme]`."
        )
    if len(raw) == 0:
        return None
    out: List[PendingSource] = []
    for j, item in enumerate(raw):
        if isinstance(item, str):
            if not item.strip():
                raise PendingSourcesTypeError(
                    f"BRIEF.{field_path}[{j}] is an empty source label — "
                    f"every entry must name a non-empty pending source."
                )
            out.append(PendingSource(source=item.strip()))
            continue
        if isinstance(item, dict):
            source = item.get("source")
            if not isinstance(source, str) or not source.strip():
                raise PendingSourcesTypeError(
                    f"BRIEF.{field_path}[{j}] must have a non-empty string "
                    f"`source` key; got {item!r}."
                )
            expected_by = item.get("expected_by")
            # ``expected_by`` is a free-form informational note. YAML parses
            # a bare date (``2026-08-15``) as a ``datetime.date`` and a bare
            # number as an int/float — coerce any scalar to its string form
            # rather than rejecting it; reject only collection types (a list
            # or mapping is a shape error, not a note).
            if isinstance(expected_by, (list, dict)):
                raise PendingSourcesTypeError(
                    f"BRIEF.{field_path}[{j}].expected_by must be a scalar "
                    f"note (a date, milestone, or string) when present; got "
                    f"{type(expected_by).__name__}."
                )
            unknown = set(item) - {"source", "expected_by"}
            if unknown:
                raise PendingSourcesTypeError(
                    f"BRIEF.{field_path}[{j}] has unknown key(s) "
                    f"{sorted(unknown)}; only `source` and `expected_by` "
                    f"are recognized."
                )
            out.append(
                PendingSource(
                    source=source.strip(),
                    expected_by=(
                        str(expected_by).strip()
                        if expected_by is not None
                        else None
                    ),
                )
            )
            continue
        raise PendingSourcesTypeError(
            f"BRIEF.{field_path}[{j}] must be a source label string or a "
            f"{{source, expected_by}} mapping; got "
            f"{type(item).__name__}: {item!r}."
        )
    return out


def resolve_pending_sources(thread_dir: Path) -> List[PendingSource]:
    """Read the optional ``pending_sources`` declarations for ``thread_dir``.

    The companion-input resolver for ``anvil/lib/pending_marker.py`` (issue
    #842), modeled on :func:`resolve_spec_ref`'s lenient posture. Reads
    ``<thread_dir>/BRIEF.md`` (the thread-level freeform-prose surface, the
    same one :func:`load_recommendation_target` reads), extracts its YAML
    frontmatter via the shared :func:`_extract_frontmatter`, and validates
    the ``pending_sources`` block via :func:`_validate_pending_sources`.

    Lenient by design — never raises. Returns ``[]`` on EVERY absence /
    malformed path (no BRIEF file, no frontmatter, no ``pending_sources``
    key, an empty list, OR a malformed declaration): ``pending_sources`` is
    a pure reporting aid, so a broken declaration degrades to "no declared
    sources" rather than crashing the pending-marker gate (which functions
    identically with or without declared sources). The distinguishable
    :class:`PendingSourcesTypeError` is still raised by
    :func:`_validate_pending_sources` for any strict caller that wants to
    surface a malformed knob.
    """
    if not isinstance(thread_dir, Path):
        try:
            thread_dir = Path(thread_dir)
        except Exception:
            return []
    brief_path = thread_dir / BRIEF_FILENAME
    if not brief_path.is_file():
        return []
    try:
        text = brief_path.read_text(encoding="utf-8")
    except OSError:
        return []
    fm = _extract_frontmatter(text)
    if fm is None:
        return []
    try:
        parsed = _validate_pending_sources(fm.get("pending_sources"))
    except PendingSourcesTypeError:
        # Declared-but-broken reporting knob — degrade to "no declared
        # sources" (the gate is unaffected either way).
        return []
    return parsed or []


def load_recommendation_target_resolved(
    thread_dir: Path,
    project_dir: Optional[Path] = None,
    slug: Optional[str] = None,
) -> Tuple[
    Optional[Literal["invest", "pass", "conditional", "undecided"]],
    Literal["thread", "project", "default"],
]:
    """Resolve ``recommendation_target`` across BOTH BRIEF surfaces (issue #837).

    :func:`load_recommendation_target` reads ONLY the legacy thread-level
    ``<thread_dir>/BRIEF.md`` surface. Under the post-#295/#296
    project-first layout there IS no thread-level ``BRIEF.md`` — per-
    thread config lives entirely in the project-root ``BRIEF.md``'s
    ``documents:`` frontmatter — so that helper unconditionally returns
    ``None`` for a migrated project and the #348 dim-1 calibration never
    fires. This resolver tries both surfaces, in precedence order, and
    reports WHICH surface (if any) supplied the value so the caller can
    record it for debuggability (the ``source`` half of the return
    tuple; see ``memo-review.md``'s ``_summary.md.recommendation_target_resolved.source``
    field).

    Precedence
    ----------
    1. **Thread** — ``<thread_dir>/BRIEF.md`` (the legacy freeform-prose
       surface read by :func:`load_recommendation_target`). Checked
       FIRST so a project still using the legacy per-thread shape
       resolves byte-identically to pre-#837 behavior — a value here
       always wins over a project-level declaration, even if both are
       present. This preserves the historical single-surface contract
       for any thread that hasn't migrated.
    2. **Project** — the project-root ``BRIEF.md``'s matching
       ``documents:`` entry (:func:`load_project_brief` +
       :meth:`ProjectBrief.document_for_slug`), read only when the
       thread-level surface resolved to ``None`` (absent file, no
       frontmatter, missing key, or an unrecognized value).
    3. **Default** — neither surface supplied a recognized value.
       Byte-identical to the pre-#837 "no calibration" behavior.

    Parameters
    ----------
    thread_dir
        The thread root directory (holds the thread-level ``BRIEF.md``,
        if any, and the ``<slug>.{N}/`` version dirs) — NOT a version
        subdirectory and NOT the project root.
    project_dir
        The project root (the directory containing the project-level
        ``BRIEF.md`` with the typed ``documents:`` schema). Defaults to
        ``thread_dir.parent`` — the standard project-first layout
        convention (mirrors ``load_rubric_overrides_for_slug``'s
        call-site convention documented in ``memo-review.md`` step 4i).
        Pass explicitly only when the on-disk layout diverges from this
        default.
    slug
        The document slug used to look up the matching ``documents:``
        entry. Defaults to ``thread_dir.name`` — the directory-name-
        echoes-slug convention enforced by
        :func:`_validate_slug_directory_divergence`. Pass explicitly
        only when the slug diverges from the thread directory name.

    Returns
    -------
    Tuple[Optional[str], str]
        ``(value, source)`` where ``value`` is one of ``"invest"`` /
        ``"pass"`` / ``"conditional"`` / ``"undecided"`` / ``None``, and
        ``source`` is one of ``"thread"`` / ``"project"`` / ``"default"``
        naming which surface (if any) supplied ``value``.

    Notes
    -----
    **Never raises** — mirrors the lenient contract of both underlying
    readers. A structurally invalid project-level BRIEF (the ONLY path
    that can raise inside :func:`load_project_brief`) degrades to
    ``(None, "default")`` for THIS resolver rather than propagating,
    the same "degrade to empty/default rather than break the reviewer"
    posture as :func:`load_rubric_overrides_for_slug`.
    """
    if not isinstance(thread_dir, Path):
        try:
            thread_dir = Path(thread_dir)
        except Exception:
            return None, "default"

    thread_value = load_recommendation_target(thread_dir)
    if thread_value is not None:
        return thread_value, "thread"

    resolved_project_dir = project_dir if project_dir is not None else thread_dir.parent
    resolved_slug = slug if slug is not None else thread_dir.name

    try:
        brief = load_project_brief(resolved_project_dir)
    except ValueError:
        # Structurally invalid project BRIEF. Lenient degrade — same
        # posture as load_rubric_overrides_for_slug: a malformed BRIEF
        # must not break the reviewer's dim-1 calibration lookup.
        return None, "default"

    if brief is None:
        return None, "default"

    doc = brief.document_for_slug(resolved_slug)
    if doc is None or doc.recommendation_target is None:
        return None, "default"

    return doc.recommendation_target, "project"


# ---------------------------------------------------------------------------
# Body-filename helper (issue #295)
# ---------------------------------------------------------------------------


def body_filename_for(slug: str) -> str:
    """Return the body markdown filename for a memo thread.

    Issue #295 (project-org model lock) pins the body filename
    convention: every version directory's body markdown **echoes the
    thread slug** as ``<slug>.md`` (e.g. ``investment-memo.1/`` carries
    ``investment-memo.md``, ``latency-wall.1/`` carries
    ``latency-wall.md``). This is the only recognized shape; there is
    no override mechanism.

    This helper is the single source of truth so a future shape change
    (vanishingly unlikely under the slug-echo contract) lands in one
    place. Lifecycle commands and lib modules that need to read or
    write the body file should call this helper rather than hard-coding
    ``f"{slug}.md"`` inline.

    Lives in ``project_brief.py`` after the issue #296 consolidation
    (its prior home, ``anvil_config.py``, was retired). The helper is a
    one-line ``f"{slug}.md"`` wrapper; placing it next to the project-
    config schema keeps every project / per-doc convention in one
    place.

    Parameters
    ----------
    slug
        The thread slug (the directory name under the project root that
        holds the thread's version dirs). Non-empty string required.

    Returns
    -------
    str
        ``f"{slug}.md"`` verbatim. Caller is responsible for combining
        with the version dir path (e.g. ``version_dir / body_filename_for(slug)``).
    """
    if not isinstance(slug, str) or not slug:
        raise ValueError(
            f"body_filename_for(slug) requires a non-empty string; "
            f"got {slug!r}"
        )
    return f"{slug}.md"
