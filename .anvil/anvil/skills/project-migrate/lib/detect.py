"""Back-compat shim (issue #407): canonical module is ``anvil/lib/project_detect.py``.

Promoted from project-migrate-skill-local to the shared framework lib when
``anvil:project-scout`` (issue #407) became the second consumer of the
detector core (``inventory_project`` / ``detect_shape`` / ``_classify`` /
``_VERSION_DIR_RE``), firing the CLAUDE.md "wait for the second consumer
before generalizing" trigger — the same shape as the #382 promotion of
``project_discovery.py`` and the #393 promotion of
``rubric_overrides_suffix.py``.

This shim is **full-fidelity**: it re-exports the private surface the
sibling modules and tests consume (``plan`` imports ``_classify`` and
``_project_brief_slugs``; ``enroll`` imports ``_VERSION_DIR_RE`` /
``_extract_frontmatter`` / ``_has_project_brief``; ``verify`` imports
``_SKILL_FIXED_BODY_FILENAMES``; the test suite reads
``_RETAINED_BODY_FILENAMES``), not just ``__all__``. Every name is
imported explicitly — a wildcard import would drop the underscore names
and silently break the siblings.
"""

from anvil.lib.project_detect import (  # noqa: F401
    ANVIL_JSON_FILENAME,
    BRIEF_FILENAME,
    COUNSEL_MEMO_FILENAME,
    MEMO_BODY_FILENAME,
    PROVISIONAL_BODY_FILENAME,
    ProjectInventory,
    Shape,
    ThreadInventory,
    _FRONTMATTER_DELIM,
    _INFRASTRUCTURE_DIRS,
    _NON_THREAD_DIRNAME_PREFIXES,
    _OBSERVED_BODY_EXTENSIONS,
    _RETAINED_BODY_FILENAMES,
    _SKILL_FIXED_BODY_FILENAMES,
    _VERSION_DIR_RE,
    _classify,
    _extract_frontmatter,
    _hand_parse_minimal_yaml,
    _has_project_brief,
    _list_all_version_dirs,
    _list_subdirectories,
    _list_version_dirs,
    _observed_body_filenames,
    _observed_candidate_body_files,
    _observed_retained_body_filenames,
    _project_brief_slugs,
    detect_shape,
    has_counsel_memo_companion,
    has_native_provisional_body,
    inventory_project,
)


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
