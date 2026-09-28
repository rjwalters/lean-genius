"""BRIEF.md parsing entry points (issue #1121 split).

Part of the ``anvil.lib.project_brief`` package — see the package
``__init__.py`` docstring for the full module. This submodule owns the
slug-directory divergence validator (Open Question #1 resolution), the
lenient/strict parsing entry points (:func:`load_project_brief` /
:func:`load_project_brief_strict`), and the rubric-overrides convenience
wrapper (:func:`load_rubric_overrides_for_slug`).

Split from the pre-#1121 monolithic ``anvil/lib/project_brief.py`` along its
existing "Slug-directory divergence validation" / "Parsing entry points" /
"Rubric-overrides convenience API" section boundaries (grouped into one
module — they are one call chain: ``load_project_brief`` ->
``_parse_brief_body`` -> ``_validate_slug_directory_divergence``). No
behavior change.
"""

from __future__ import annotations

import re
import warnings
from pathlib import Path
from typing import Any, Dict, List, Optional

from pydantic import ValidationError

from anvil.lib.frontmatter import extract_frontmatter as _extract_frontmatter
from anvil.lib.project_brief.fields import (
    _normalize_ai_byline,
    _normalize_audience,
    _normalize_corpus_dirs,
    _normalize_documents,
    _normalize_string_list,
    _normalize_theme,
    _normalize_voice,
)
from anvil.lib.project_brief.models import ProjectBrief, RubricOverrides
from anvil.lib.project_brief.types import (
    consumer_overlay_dir_for,
    discover_consumer_artifact_types,
)
from anvil.lib.project_discovery import BRIEF_FILENAME, DOCUMENTS_FRONTMATTER_KEY

# ---------------------------------------------------------------------------
# Slug-directory divergence validation (Open Question #1 resolution)
# ---------------------------------------------------------------------------


def _on_disk_slug_dirs(project_dir: Path) -> List[str]:
    """Return the list of on-disk directory names that look like thread roots.

    A "thread-root-shaped" subdirectory of ``project_dir`` is one whose
    name appears as the stem of at least one ``<name>.<N>`` version dir
    immediately under it. This matches
    ``project_discovery._contains_version_dirs`` but inlined to avoid a
    circular-import shape (project_discovery is the caller of this
    parser in the wiring layer).

    Sibling directories that exist but have no version dirs (e.g.,
    ``research/``, an empty placeholder, a stray ``.cache/``) are NOT
    treated as thread roots — they're project-level infrastructure or
    pre-draft scaffolding. This narrows the on-disk-vs-BRIEF check to
    "started threads only".
    """
    version_re = re.compile(r"^(?P<stem>.+)\.(?P<num>\d+)$")
    out: List[str] = []
    try:
        children = list(project_dir.iterdir())
    except OSError:
        return out

    for child in children:
        if not child.is_dir():
            continue
        if child.name.startswith("."):
            # `.review/`, `.audit/`, `.<critic>/` siblings are review
            # output, not thread roots. Skip.
            continue
        try:
            grandchildren = list(child.iterdir())
        except OSError:
            continue
        for gc in grandchildren:
            if not gc.is_dir():
                continue
            m = version_re.match(gc.name)
            if m is None:
                continue
            if m.group("stem") == child.name:
                out.append(child.name)
                break
    return out


def _validate_slug_directory_divergence(
    brief: ProjectBrief, project_dir: Path
) -> None:
    """Apply the asymmetric slug-directory rule.

    - **Listed-but-missing** → ``warnings.warn(UserWarning)``. The draft
      hasn't started; this is the common case during early project setup.
    - **On-disk-but-unlisted** → ``ValueError``. Configuration drift
      that breaks overlay selection downstream.
    """
    brief_slugs = {doc.slug for doc in brief.documents}
    on_disk = set(_on_disk_slug_dirs(project_dir))

    # Listed-but-missing: warn but proceed.
    missing = sorted(brief_slugs - on_disk)
    if missing:
        warnings.warn(
            f"BRIEF.documents lists slugs with no matching directory under "
            f"{project_dir}: {missing}. A draft may not have been started "
            f"yet — proceeding. (To silence: remove the unstarted entries "
            f"from BRIEF.documents or create the matching directory.)",
            UserWarning,
            stacklevel=3,
        )

    # On-disk-but-unlisted: hard error.
    extra = sorted(on_disk - brief_slugs)
    if extra:
        raise ValueError(
            f"Configuration drift: directories present under {project_dir} "
            f"are not listed in BRIEF.documents: {extra}. Each thread "
            f"root must be acknowledged by the project BRIEF so the "
            f"reviewer can resolve its artifact_type. Suggested fix: add "
            f"matching `documents:` entries for {extra}, or remove the "
            f"directories if they are stale."
        )


# ---------------------------------------------------------------------------
# Parsing entry points (lenient + strict)
# ---------------------------------------------------------------------------


def _parse_brief_body(
    frontmatter: Dict[str, Any],
    project_dir: Path,
    consumer_root: Optional[Path] = None,
) -> ProjectBrief:
    """Parse a frontmatter dict into a :class:`ProjectBrief`.

    Raises ``ValueError`` on any schema violation. Recognized top-level
    keys: ``project``, ``audience``, ``hard_rules``, ``documents``,
    ``theme``, ``voice``, ``corpus``, ``ai_byline``, ``quarantine``.
    Other keys are ignored (forward-compat surface for project-level
    fields that may land later).

    The consumer artifact-type set (issue #394) is discovered ONCE per
    parse here and threaded down to the per-entry ``artifact_type``
    validator. ``consumer_root`` overrides the upward ``.anvil/``
    marker walk (testability from tmp dirs).
    """
    project_raw = frontmatter.get("project")
    if not isinstance(project_raw, str) or not project_raw.strip():
        raise ValueError(
            f"BRIEF.project is required and must be a non-empty string; "
            f"got {project_raw!r} at {project_dir / BRIEF_FILENAME}. "
            f"Suggested fix: add a `project:` key naming the project."
        )

    audience = _normalize_audience(frontmatter.get("audience"))
    hard_rules = _normalize_string_list(
        frontmatter.get("hard_rules"), "hard_rules"
    )
    consumer_overlay_dir = consumer_overlay_dir_for(project_dir, consumer_root)
    consumer_types = discover_consumer_artifact_types(
        project_dir, consumer_root
    )
    documents = _normalize_documents(
        frontmatter.get(DOCUMENTS_FRONTMATTER_KEY),
        consumer_types=consumer_types,
        consumer_overlay_dir=consumer_overlay_dir,
    )
    theme = _normalize_theme(frontmatter.get("theme"))
    voice = _normalize_voice(frontmatter.get("voice"))
    corpus = _normalize_corpus_dirs(frontmatter.get("corpus"))
    ai_byline = _normalize_ai_byline(frontmatter.get("ai_byline"))
    quarantine = _normalize_string_list(
        frontmatter.get("quarantine"), "quarantine"
    )

    try:
        return ProjectBrief(
            project=project_raw,
            audience=audience,
            hard_rules=hard_rules,
            documents=documents,
            theme=theme,
            voice=voice,
            corpus=corpus,
            ai_byline=ai_byline,
            quarantine=quarantine,
        )
    except ValidationError as exc:
        raise ValueError(
            f"BRIEF at {project_dir / BRIEF_FILENAME} failed schema "
            f"validation: {exc}"
        ) from exc


def load_project_brief(
    project_dir: Path,
    *,
    validate_dirs: bool = False,
    consumer_root: Optional[Path] = None,
) -> Optional[ProjectBrief]:
    """Lenient loader for ``<project_dir>/BRIEF.md``.

    Absence-tolerant entry point. Returns ``None`` when:

    - ``<project_dir>/BRIEF.md`` does not exist.
    - The file exists but has no YAML frontmatter.
    - The frontmatter is malformed YAML.

    Raises ``ValueError`` when the BRIEF is present and structurally
    wrong:

    - Missing required field (``project``, ``documents``).
    - Wrong type on any field.
    - Unknown ``artifact_type``.
    - Duplicate slug.
    - Empty ``documents`` list.
    - Malformed ``target_length`` / ``target_length_overrides`` /
      ``rubric_overrides`` shape.

    Parameters
    ----------
    project_dir
        Directory containing the project BRIEF. Typically the
        ``project_root`` field of a
        :class:`project_discovery.DiscoveryResult` for a
        ``LAYOUT_PROJECT_BRIEF`` match.
    validate_dirs
        When True, after parsing, validate the BRIEF's slug list against
        on-disk slug-shaped subdirectories under ``project_dir``. Listed-
        but-missing triggers a ``UserWarning``; on-disk-but-unlisted
        raises ``ValueError``. Default False — pure schema parsing only.
    consumer_root
        Optional explicit consumer root for the #394 consumer
        artifact-type tier. When ``None`` (default) the consumer root
        is discovered by walking upward from ``project_dir`` to the
        ``.anvil/`` install marker; when no marker exists the consumer
        tier is skipped (registered types only).

    Returns
    -------
    Optional[ProjectBrief]
        Parsed BRIEF, or ``None`` if no BRIEF is present.

    Raises
    ------
    ValueError
        On any schema violation. The exception message includes the
        offending field path and a suggested fix.
    """
    brief_path = project_dir / BRIEF_FILENAME
    if not brief_path.is_file():
        return None
    try:
        text = brief_path.read_text(encoding="utf-8")
    except OSError:
        return None
    fm = _extract_frontmatter(text)
    if fm is None:
        return None

    brief = _parse_brief_body(fm, project_dir, consumer_root=consumer_root)

    if validate_dirs:
        _validate_slug_directory_divergence(brief, project_dir)

    return brief


def load_project_brief_strict(
    project_dir: Path,
    *,
    validate_dirs: bool = False,
    consumer_root: Optional[Path] = None,
) -> ProjectBrief:
    """Strict loader for ``<project_dir>/BRIEF.md``.

    Raises on every failure mode the lenient form tolerates:

    - ``FileNotFoundError`` if ``<project_dir>/BRIEF.md`` does not exist.
    - ``ValueError`` if the file has no YAML frontmatter or the
      frontmatter is malformed.
    - ``ValueError`` (same as lenient) on schema violations.

    The strict form is what test fixtures use to assert specific
    failure modes; lifecycle commands should usually use the lenient
    :func:`load_project_brief` and check for ``None``.

    Parameters
    ----------
    project_dir
        Directory containing the project BRIEF.
    validate_dirs
        See :func:`load_project_brief`.
    consumer_root
        See :func:`load_project_brief`.

    Returns
    -------
    ProjectBrief
        Parsed BRIEF.

    Raises
    ------
    FileNotFoundError
        If ``<project_dir>/BRIEF.md`` is missing.
    ValueError
        On absent frontmatter, malformed YAML, or any schema violation.
    """
    brief_path = project_dir / BRIEF_FILENAME
    if not brief_path.is_file():
        raise FileNotFoundError(
            f"No BRIEF found at {brief_path}. Suggested fix: create a "
            f"`{BRIEF_FILENAME}` file at the project root with the "
            f"`project:`, `audience:`, `hard_rules:`, and `documents:` "
            f"frontmatter keys."
        )
    text = brief_path.read_text(encoding="utf-8")
    fm = _extract_frontmatter(text)
    if fm is None:
        raise ValueError(
            f"BRIEF at {brief_path} has no parseable YAML frontmatter. "
            f"Suggested fix: ensure the file opens with `---` on the "
            f"first non-blank line and closes the frontmatter with a "
            f"matching `---` line."
        )

    brief = _parse_brief_body(fm, project_dir, consumer_root=consumer_root)

    if validate_dirs:
        _validate_slug_directory_divergence(brief, project_dir)

    return brief


# ---------------------------------------------------------------------------
# Rubric-overrides convenience API (replaces anvil_config.load_rubric_overrides)
# ---------------------------------------------------------------------------


def load_rubric_overrides_for_slug(
    project_dir: Path, slug: str
) -> RubricOverrides:
    """Return the ``rubric_overrides`` for ``slug`` from ``<project_dir>/BRIEF.md``.

    Lenient convenience wrapper. Returns an empty
    :class:`RubricOverrides` for every absence path:

    - ``<project_dir>/BRIEF.md`` does not exist.
    - The BRIEF has no YAML frontmatter or the frontmatter is malformed.
    - The BRIEF parses but has no entry for ``slug``.
    - The matching entry has no ``rubric_overrides:`` block.

    Raises ``ValueError`` only on a structurally invalid BRIEF (the
    same conditions as :func:`load_project_brief`). This is the
    replacement for the retired
    ``anvil_config.load_rubric_overrides(thread_dir)`` API; the
    ``empty-on-absence`` contract is preserved exactly so the reviewer
    integration in ``rubric_overrides_suffix.py`` continues to work
    unchanged.

    Parameters
    ----------
    project_dir
        The project root (the directory containing ``BRIEF.md``). For
        threads under the project layout, this is the parent of the
        thread directory: ``thread_dir.parent``.
    slug
        The document slug (the name of the thread directory under the
        project root).

    Returns
    -------
    RubricOverrides
        Parsed overrides. Use ``RubricOverrides.is_empty`` to fast-path
        the no-overrides case.
    """
    try:
        brief = load_project_brief(project_dir)
    except ValueError:
        # The BRIEF exists but is structurally invalid. The lenient
        # contract says "degrade to empty"; propagating a ValueError
        # here would break the reviewer's pre-#296 zero-impact
        # behavior for legacy threads. So we swallow.
        return RubricOverrides()
    if brief is None:
        return RubricOverrides()

    doc = brief.document_for_slug(slug)
    if doc is None or doc.rubric_overrides is None:
        return RubricOverrides()
    return doc.rubric_overrides
