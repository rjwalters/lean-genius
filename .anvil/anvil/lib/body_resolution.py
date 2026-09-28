"""Shared body-file resolution for version-dir-scoped verifiers (issue #1110).

``_body_path`` / ``_record_body_path`` were hand-maintained, near-identical
copies duplicated across three modules: :mod:`anvil.lib.pending_marker`,
:mod:`anvil.lib.numeric_consistency`, and :mod:`anvil.lib.evidence_check`.
Each docstring already pointed at its siblings ("Mirrors
``anvil/lib/numeric_consistency.py::_body_path``") — acknowledging the drift
risk without eliminating it. This module is the single canonical home,
following the :mod:`anvil.lib.atomic_write` precedent (issue #1104).

Public API:

- :func:`resolve_body_path` — locate a version dir's body file (slug-echo
  ``<slug>.md`` first, then a caller-supplied ``fallback_names`` chain), or
  resolve an explicit ``body`` override.
- :func:`record_body_path` — portfolio-relative path string for the
  result / sidecar (bare filename when inside ``version_dir``, else a path
  relative to the portfolio root, else absolute).
"""

from __future__ import annotations

from pathlib import Path
from typing import Optional, Sequence

DEFAULT_FALLBACK_NAMES: Sequence[str] = ("main.tex",)
"""Default single-name fallback chain (the paper shape).

``evidence_check.py`` passes its own extended ``FIXED_BODY_NAMES`` (issue
#475) instead of relying on this default.
"""


def resolve_body_path(
    version_dir: Path,
    *,
    body: Optional[Path] = None,
    fallback_names: Sequence[str] = DEFAULT_FALLBACK_NAMES,
    caller_name: str = "",
) -> Path:
    """Locate the body file inside a version directory.

    Detection order: ``<slug>.md`` (the #295 slug-echo shape — the slug is
    the parent dir name) first, then each name in ``fallback_names`` in
    order. Raises ``FileNotFoundError`` listing the full chain when none
    exists.

    When ``body`` is supplied (the adopted-in-place legacy-thread
    override — e.g. a ``paper.tex`` entry point outside
    ``fallback_names``), the discovery chain is skipped entirely: a
    relative override resolves against ``version_dir``, an absolute one is
    used as-is, and the resolved path must exist (``FileNotFoundError``
    naming the override, not the chain, otherwise).

    ``caller_name`` prefixes every raised message (e.g. ``"pending_marker"``)
    so each consumer's historical error text is preserved verbatim.
    """
    prefix = f"{caller_name}: " if caller_name else ""
    if body is not None:
        override = Path(body)
        if not override.is_absolute():
            override = version_dir / override
        if not override.is_file():
            raise FileNotFoundError(
                f"{prefix}--body override {override!s} does not exist or "
                f"is not a file."
            )
        return override
    slug_md = version_dir / f"{version_dir.parent.name}.md"
    if slug_md.is_file():
        return slug_md
    for name in fallback_names:
        candidate = version_dir / name
        if candidate.is_file():
            return candidate
    fallback_chain = ", ".join(repr(n) for n in fallback_names)
    raise FileNotFoundError(
        f"{prefix}no body file found in {version_dir!s} (looked for "
        f"{slug_md.name!r} per the #295 slug-echo convention, then "
        f"{fallback_chain})."
    )


def record_body_path(version_dir: Path, body: Path) -> str:
    """Portfolio-relative body-path string for the result / sidecar.

    For the common case (body lives inside ``version_dir``) this is the
    bare filename (``body.name``), byte-identical to the pre-#670
    contract. For an override that points outside ``version_dir`` (the
    adopted-in-place / scratch-staging case), records the path relative to
    the portfolio root (``version_dir.parent.parent`` under the
    post-#295/#296 canonical model), falling back to the absolute path
    when the body lives outside the portfolio tree entirely.
    """
    body = body.resolve()
    version_dir = version_dir.resolve()
    try:
        body.relative_to(version_dir)
        return body.name
    except ValueError:
        pass
    portfolio_root = version_dir.parent.parent
    try:
        return str(body.relative_to(portfolio_root))
    except ValueError:
        return str(body)


__all__ = ["resolve_body_path", "record_body_path"]
