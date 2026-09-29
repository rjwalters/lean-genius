"""Shared test-support helpers used across per-skill test suites (#1125).

Consolidates 11 distinct drifted variants of a directory-snapshot-hashing
helper (``_tree_hash`` / ``_tree_digest`` / ``_tree_hashes``) that had been
copy-pasted at module scope into 28 test files across 10 skills (``help``,
``ip-search``, ``project-book``, ``project-migrate``, ``project-photos``,
``project-scout``, ``project-share``, ``rubric-rebackport``). Every call
site uses the helper identically -- snapshot a tree before an operation,
run it, snapshot again, assert the two snapshots are equal (zero-mutation /
dry-run / idempotency guarantees) or unequal (an operation is expected to
write) -- so a single canonical implementation is a safe drop-in as long as
it preserves "same input tree -> equal snapshots, different tree -> unequal
snapshots" for existing ``==`` / ``!=`` assertions.

Also consolidates 10 byte-identical ``_parse_frontmatter(text) -> dict``
test helpers (issue #1133) that had been copy-pasted at module scope
across 10 skills' test suites (``memoir``, ``proposal``, ``installation``,
``essay``, ``spec``, ``primer``, ``ip-uspto-provisional``, ``ip-uspto``
(x2), ``datasheet``). Each copy was already a thin ``dict``-returning
adapter over the shared ``anvil.lib.frontmatter.extract_frontmatter``
primitive (issue #1083), which returns ``None`` where these call sites
want ``{}`` -- so, like ``tree_hash`` above, the wrapping itself should
have been shared too. Not absorbed: ``anvil/skills/deck/tests/
test_marp_smoke.py``'s same-named helper, which has a different signature
(``path: Path``), a hand-rolled stdlib-only parser (deliberately avoids
pyyaml per that suite's own dependency discipline), and a different
purpose (Marp-file ``key: value`` frontmatter, not general YAML) -- a
genuine lookalike, not a duplicate.

This module is test-support only -- it is imported by
``tests/`` and ``anvil/skills/*/tests/`` files, never by shipped skill code
(unlike the rest of ``anvil/lib/``, which is production-shared).

Also consolidates 99 byte-identical ``_read(p_or_path: Path) -> str``
test helpers (issue #1136) that had been copy-pasted at module scope
across the repo's test suites -- both a ``p: Path`` and a ``path: Path``
parameter-name variant of the exact same one-line
``return <param>.read_text(encoding="utf-8")`` body. A follow-up (issue
#1140) converted a further 78 files carrying the two closure variants --
the no-arg ``DOC``-closure (58 files, now ``_read =
functools.partial(read_text, DOC)``) and the relative-path
``_SKILL_ROOT``-closure (20 files, now ``_read = lambda rel:
read_text(_SKILL_ROOT / rel)``) -- binding the module-level constant at
the call site rather than baking a file-local default into this shared
helper. Still not absorbed: a handful of files whose ``_read`` has a
genuinely different body (an extra ``assert path.exists()``/``is_dir()``
branch, or a directory-vs-file dispatch), plus the ``self``-taking
method-scope variants -- those carry real behavior beyond the read and
are deliberately left alone.

Also consolidates 17 ``_assert_ok(result: subprocess.CompletedProcess[str])
-> None`` test helpers (issue #1144) that had been copy-pasted at module
scope across ``tests/scripts/test_install_*.py`` (16 files) and
``tests/scripts/test_resync_installed.py`` (1 file). 16 of the 17 were
byte-identical (failure message prefixed ``"installer exited
non-zero:"``); ``test_resync_installed.py``'s copy differed only in that
prefix (``"command exited non-zero:"``, since it invokes
``resync-installed.sh`` rather than the installer). The wording
difference is not load-bearing -- it only ever appears in a pytest
assertion-failure message, never asserted on by another test -- so this
consolidation folds both variants into a single ``"command exited
non-zero:"`` message rather than threading a ``context`` parameter
through all 17 call sites.
"""

from __future__ import annotations

import hashlib
import subprocess
from pathlib import Path

from anvil.lib.frontmatter import extract_frontmatter

__all__ = ["assert_ok", "parse_frontmatter", "read_text", "tree_hash"]

# Sentinel value recorded for directory entries. Distinct from any valid
# sha256 hex digest (which is exactly 64 lowercase hex characters), so a
# directory can never collide with a same-named file's hash.
_DIR_MARKER = "<dir>"


def tree_hash(root: Path, *, exclude: str | None = None) -> dict[str, str]:
    """Snapshot a directory tree as ``{relative_posix_path: content_hash}``.

    Walks every entry under ``root`` (files *and* directories, discovered
    via a sorted ``root.rglob("*")`` for determinism) and returns one dict
    entry per path:

    - Files map to the sha256 hex digest of their contents.
    - Directories map to a fixed marker (``"<dir>"``), so a directory-only
      structural change -- e.g. an empty subdirectory appearing or
      disappearing -- is visible in the returned mapping even though an
      empty directory has no content of its own to hash. (At least one of
      the pre-consolidation variants this helper replaces omitted
      directories entirely, so that class of change could go undetected --
      see issue #1125.)

    Two snapshots taken before/after an operation compare equal (``==``)
    iff the tree is byte-identical: same paths present, same file
    contents, same directory structure. This is the standard idiom used
    across the skill test suites to assert a command is read-only, a
    dry-run made no changes, or a re-run is idempotent.

    Args:
        root: directory to snapshot.
        exclude: optional path-component name to skip -- any entry whose
            relative path contains this component anywhere (e.g. a named
            subdirectory that the operation under test is *expected* to
            write into) is omitted from the snapshot. Matches the
            ``ip-search`` write-scope test's original ``exclude="prior-art"``
            usage: prove everything *outside* the one sanctioned write
            target is untouched.
    """

    out: dict[str, str] = {}
    for path in sorted(root.rglob("*")):
        rel_path = path.relative_to(root)
        if exclude is not None and exclude in rel_path.parts:
            continue
        rel = rel_path.as_posix()
        if path.is_file():
            out[rel] = hashlib.sha256(path.read_bytes()).hexdigest()
        elif path.is_dir():
            out[rel] = _DIR_MARKER
    return out


def read_text(path: Path) -> str:
    """Read a file as UTF-8 text.

    Thin wrapper over ``Path.read_text(encoding="utf-8")`` -- the exact
    one-line body copy-pasted as a module-scope ``_read`` helper across
    99 test files (issue #1136). Callers that closed over a module-level
    constant (``DOC``, ``_SKILL_ROOT``) instead of taking an explicit
    path argument bind it locally -- ``functools.partial(read_text, DOC)``
    for the no-arg form, ``lambda rel: read_text(_SKILL_ROOT / rel)`` for
    the relative-path form (issue #1140) -- rather than baking a
    file-local default into this shared helper.
    """
    return path.read_text(encoding="utf-8")


def parse_frontmatter(text: str) -> dict:
    """Parse a leading ``---``-delimited YAML frontmatter block.

    Thin ``dict``-returning adapter over the shared
    ``anvil.lib.frontmatter.extract_frontmatter`` primitive (issue
    #1083), which returns ``None`` where these call sites want ``{}``.
    """
    return extract_frontmatter(text) or {}


def assert_ok(result: subprocess.CompletedProcess[str]) -> None:
    """Assert a subprocess run succeeded, echoing stdout/stderr on failure.

    The exact ``_assert_ok`` body copy-pasted as a module-scope helper
    across 17 ``tests/scripts/test_install_*.py`` / ``test_resync_installed.py``
    files (issue #1144). See this module's docstring for why the two
    pre-consolidation failure-message wordings ("installer exited
    non-zero" vs. "command exited non-zero") were folded into one.
    """
    assert result.returncode == 0, (
        f"command exited non-zero:\n"
        f"--- stdout ---\n{result.stdout}\n--- stderr ---\n{result.stderr}"
    )
