"""Input-mode resolution for `anvil:diff` (issue #925).

Resolves the three documented input modes to a concrete pair of files to
diff, WITHOUT reading their content (that stays the CLI's job — this
module is filesystem-shape-only, mirroring ``anvil.lib.critics
.discover_critics``'s "discovery does not parse the payload" split):

1. **Version dirs** — ``resolve_version_pair`` resolves ``{thread}.{N}``
   vs ``{thread}.{N+1}`` through ``anvil.lib.latest_resolution
   .resolve_latest`` (so an operator's ``.latest`` pin is honored), then
   ``resolve_body_file`` locates each version dir's body file.
2. **A deslop run** — ``resolve_deslop_pair`` diffs an origin file against
   the ``emit/cleaned.txt`` a deslop thread wrote, surfacing
   ``emit/rationale.md`` when present.
3. **Two arbitrary files** — the escape hatch; the CLI just diffs two
   paths directly and never touches this module.

Read-only, non-mutating: every function here only stats/lists/reads
directory entries. Nothing is written, ever.
"""

from __future__ import annotations

import re
from pathlib import Path
from typing import List, Optional, Tuple

from anvil.lib.latest_resolution import resolve_latest

__all__ = [
    "VersionPairError",
    "resolve_body_file",
    "enumerate_versions",
    "resolve_version_pair",
    "resolve_deslop_pair",
]


class VersionPairError(ValueError):
    """Raised when a requested version-dir pair cannot be resolved.

    Always carries an operator-actionable message (which path is
    missing, or what flag to pass) -- this is a "clean error", not a
    crash; the CLI turns it into a one-line stderr message + exit 1.
    """


_VERSION_DIR_RE = re.compile(r"^(?P<slug>.+)\.(?P<n>\d+)$")


def _slug_from_version_dir(version_dir: Path) -> str:
    match = _VERSION_DIR_RE.match(version_dir.name)
    return match.group("slug") if match else version_dir.name


def resolve_body_file(
    version_dir: Path, slug: Optional[str] = None
) -> Optional[Path]:
    """Best-effort resolve the primary body file inside a version dir.

    Tries ``<slug>.md`` then ``<slug>.tex`` (the two body-file
    conventions documented in ``anvil/lib/snippets/version_layout.md``
    and CLAUDE.md), where ``slug`` defaults to the thread slug derived
    from the version dir's own name (``acme-seed.3`` -> ``acme-seed``)
    when not given explicitly. Falls back to the single largest ``.md``/
    ``.tex`` file directly inside the version dir when neither canonical
    name exists (a skill using a non-standard body filename). Returns
    ``None`` when nothing plausible is found -- the caller surfaces a
    clean "could not find a body file" error rather than guessing wrong.
    """

    version_dir = Path(version_dir)
    if slug is None:
        slug = _slug_from_version_dir(version_dir)

    for suffix in (".md", ".tex"):
        candidate = version_dir / f"{slug}{suffix}"
        if candidate.is_file():
            return candidate

    if not version_dir.is_dir():
        return None
    try:
        candidates = [
            p
            for p in version_dir.iterdir()
            if p.is_file()
            and p.suffix in (".md", ".tex")
            and not p.name.startswith("_")
        ]
    except OSError:
        return None
    if not candidates:
        return None
    candidates.sort(key=lambda p: p.stat().st_size, reverse=True)
    return candidates[0]


def enumerate_versions(thread_dir: Path, slug: str) -> List[int]:
    """List every ``<slug>.<N>`` integer version present in ``thread_dir``.

    Non-throwing: a missing/unreadable ``thread_dir`` returns ``[]``.
    """

    thread_dir = Path(thread_dir)
    out: List[int] = []
    try:
        if not thread_dir.is_dir():
            return out
        children = list(thread_dir.iterdir())
    except OSError:
        return out

    version_re = re.compile(rf"^{re.escape(slug)}\.(\d+)$")
    for child in children:
        try:
            if not child.is_dir():
                continue
        except OSError:
            continue
        match = version_re.match(child.name)
        if match:
            out.append(int(match.group(1)))
    return sorted(out)


def resolve_version_pair(
    thread_dir: Path,
    slug: str,
    *,
    from_n: Optional[int] = None,
    to_n: Optional[int] = None,
) -> Tuple[Path, Path]:
    """Resolve the ``(old_version_dir, new_version_dir)`` pair to diff.

    ``to_n`` defaults to the ``.latest``-resolved version (via
    :func:`anvil.lib.latest_resolution.resolve_latest`, so an operator
    pin to a non-highest version is honored, matching every other
    ``.latest`` consumer in the framework). ``from_n`` defaults to the
    version immediately preceding the resolved ``to`` version.

    Raises :class:`VersionPairError` -- never crashes with a bare
    filesystem exception -- when:

    - no version directories exist for ``slug`` under ``thread_dir``;
    - an explicitly-requested ``--from``/``--to`` version does not exist;
    - only one version exists and ``from_n`` was not given explicitly
      (the documented single-version-thread degrade-gracefully case --
      there is nothing to diff it against yet, so this asks the operator
      to be explicit once a second version exists rather than guessing).
    """

    thread_dir = Path(thread_dir)
    versions = enumerate_versions(thread_dir, slug)

    if to_n is not None:
        to_path = thread_dir / f"{slug}.{to_n}"
        if not to_path.is_dir():
            raise VersionPairError(f"version directory not found: {to_path}")
        to_resolved_n: Optional[int] = to_n
    else:
        latest = resolve_latest(thread_dir, slug)
        if latest is None:
            raise VersionPairError(
                f"no version directories found for slug {slug!r} under "
                f"{thread_dir} (expected {slug}.1, {slug}.2, ...)"
            )
        to_path = latest
        resolved_target = latest.resolve() if latest.is_symlink() else latest
        match = _VERSION_DIR_RE.match(resolved_target.name)
        if match:
            to_resolved_n = int(match.group("n"))
        elif versions:
            to_resolved_n = versions[-1]
        else:
            to_resolved_n = None

    if from_n is not None:
        from_path = thread_dir / f"{slug}.{from_n}"
        if not from_path.is_dir():
            raise VersionPairError(f"version directory not found: {from_path}")
    else:
        earlier = [
            v for v in versions if to_resolved_n is not None and v < to_resolved_n
        ]
        if not earlier:
            raise VersionPairError(
                f"only one version directory exists for slug {slug!r} "
                f"({to_path}); nothing to diff it against yet. Pass "
                "--from explicitly once a second version exists."
            )
        from_path = thread_dir / f"{slug}.{earlier[-1]}"

    return from_path, to_path


def resolve_deslop_pair(
    thread_dir: Path, origin: Path
) -> Tuple[Path, Path, Optional[Path]]:
    """Resolve ``(origin_file, cleaned_file, rationale_file_or_None)``.

    ``thread_dir`` is a deslop scratch thread directory -- the one
    ``anvil/skills/deslop/lib/orchestrate.py::emit()`` wrote
    ``emit/cleaned.txt`` (+ ``emit/rationale.md``, + ``emit/changes.diff``
    for file-origin inputs) under. ``origin`` is the source file path
    (deslop's ``emit()`` never persists the origin path to disk -- it is
    the operator's own input to the deslop run -- so it must be supplied
    here explicitly rather than inferred).

    Raises :class:`VersionPairError` when ``emit/cleaned.txt`` or
    ``origin`` does not exist.
    """

    thread_dir = Path(thread_dir)
    origin = Path(origin)

    cleaned = thread_dir / "emit" / "cleaned.txt"
    if not cleaned.is_file():
        raise VersionPairError(
            f"{cleaned} does not exist -- run the deslop `emit` step first"
        )
    if not origin.is_file():
        raise VersionPairError(f"origin file not found: {origin}")

    rationale = thread_dir / "emit" / "rationale.md"
    return origin, cleaned, (rationale if rationale.is_file() else None)
