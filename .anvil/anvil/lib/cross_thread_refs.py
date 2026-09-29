"""Cross-thread reference resolver for the memo skill (issue #287).

Sub-deliverable 4 of #283 — closes the **cross-thread half** of the
portfolio-shared evidence story. Sub-deliverable 3 (PR #281) already
shipped the *portfolio-level* half — ``resolve_refs_dirs`` in the
sibling :mod:`refs_resolver` module resolves ``<thread>/refs/`` plus a
sibling ``<portfolio>/research/`` for the reviewer's ``refs/`` back-check
(``commands/memo-review.md`` step 5 dim-3 sub-step). This module ships
the **cross-thread** half: native validation of references in ``memo.md``
that point at *sibling threads* under the same portfolio root, of the
form ``[[../<other-slug>/<other-slug>.latest]]`` or
``[[../<other-slug>/<other-slug>.N]]``.

Citation-token vocabulary
-------------------------

The shipped per-thread / portfolio patterns use ``[refs/<file>]`` and
``[research/<file>]`` as the verdict-tag prose surface (see
``rubric.md`` §"Refs back-check (dim 3)"). For cross-thread refs this
module documents the recommended companion token ``[<other-slug>/<file>]``
to match the existing pattern — the reviewer records
``-> <other-slug>/<file>`` in ``comments.md`` when verifying a
cross-thread ref. Other shapes the operator might consider
(``[../<other-slug>/<file>]`` to match the literal ``[[...]]`` form, or
a single ``[doc:<other-slug>]`` token) were considered and rejected per
the issue body's "Recommendation: ``[<other-slug>/<file>]``" — same
shape as the existing pattern; one less special case for the reviser
and downstream tooling to learn.

Public API
----------

``CrossThreadRef`` (dataclass)
    Typed parse result for a single ``[[../<other-slug>/<other-slug>.N]]``
    or ``[[../<other-slug>/<other-slug>.latest]]`` reference found in a
    body of text. Carries the source line, the raw reference text, the
    parsed ``other_slug``, the version specifier (``"latest"`` or an
    integer string), and the file inside the version dir when the
    reference points at a specific file (``memo.md`` body or any
    ``exhibits/<file>`` artifact) — ``None`` when the reference points at
    the version dir root.

``CrossThreadResolution`` (dataclass)
    Typed result of resolving a single :class:`CrossThreadRef` against
    on-disk state. Carries the original ref, the resolved target path
    (the version directory or the file inside it), a ``resolved`` bool,
    and a ``reason`` string when resolution failed (``"thread not
    found"`` / ``"version not found"`` / ``"file not found"`` /
    ``"latest unresolvable"``).

``find_cross_thread_refs(text: str) -> list[CrossThreadRef]``
    Permissive enumeration of cross-thread refs in a markdown body.
    Handles the two shipped shapes:

    - ``[[../<other-slug>/<other-slug>.latest]]``
    - ``[[../<other-slug>/<other-slug>.N]]``

    Both with optional ``/memo.md`` or ``/<file>`` suffixes for refs at
    the file level. Returns a list of :class:`CrossThreadRef` entries in
    source-line order.

``resolve_cross_thread_ref(ref: CrossThreadRef, portfolio_root: Path) -> CrossThreadResolution``
    Resolves a single ref against on-disk state. Walks
    ``<portfolio_root>/<other-slug>/`` to find the version dir
    (``<other-slug>.<N>/`` for explicit version, OR the ``.latest``
    target — symlink-or-walk-to-highest fallback per the issue body's AC
    on ``.latest`` tolerance). Returns a :class:`CrossThreadResolution`
    with ``resolved=True`` when the path exists, else ``resolved=False``
    with a short ``reason`` tag.

``resolve_cross_thread_refs(memo_text: str, portfolio_root: Path) -> list[CrossThreadResolution]``
    Convenience batch helper. Equivalent to::

        [resolve_cross_thread_ref(r, portfolio_root)
         for r in find_cross_thread_refs(memo_text)]

    Returns the per-ref resolution list. The caller (the reviewer's
    dim-3 back-check sub-step) iterates and tallies the unresolved count
    for the dim-3 deduction.

``.latest`` tolerance
---------------------

Per the AC: "must tolerate either a real directory like ``<slug>.3`` or
a ``.latest`` symlink pointing at one." Sub-deliverable 5 (#288) ships
the canonical resolver at
``anvil/skills/memo/lib/latest_resolution.py::resolve_latest`` and
**this module delegates** to it for the four-step rule (symlink wins;
real ``.latest/`` directory; walk-to-highest; ``None`` when nothing
matches). The fallback is permissive on purpose — the operator can ship
cross-thread refs to ``.latest`` regardless of whether they have
adopted the symlink convention.

Why a separate module from ``refs_resolver``
-------------------------------------------

``refs_resolver.resolve_refs_dirs`` has a single-thread + portfolio
research contract: given a thread dir, return ``[<thread>/refs/,
<portfolio>/research/]`` in order. Bolting cross-thread version dirs
onto that surface would conflate two distinct concepts: source-of-truth
evidence directories (refs / research) vs. sibling-thread *body
references* (cross-thread version dirs). Keep the surfaces separate
per the issue body's explicit guidance: "do NOT bolt onto
``resolve_refs_dirs`` whose contract is single-thread + portfolio
research". This module is the cross-thread sibling.

Promotion history
-----------------

Shipped skill-local under ``anvil/skills/memo/lib/`` per the CLAUDE.md
"skill-local first, lib promotion later" pattern (precedent:
``refs_resolver.py`` PR #281, ``rubric_overrides_suffix.py`` PR #265,
``project_discovery.py`` PR #290). Promoted to ``anvil/lib/`` under
issue #382 when ``anvil:deck`` / ``anvil:slides`` / ``anvil:proposal``
became the 2nd–4th consumers of the project-org primitives. The memo
path (``anvil/skills/memo/lib/cross_thread_refs.py``) remains as a
back-compat re-export shim.

No new Python deps
------------------

Standard library only (``re``, ``pathlib``, ``dataclasses``,
``typing``). The CLAUDE.md "Python deps: subprocess-only by default"
contract is preserved.
"""

from __future__ import annotations

import re
from dataclasses import dataclass
from pathlib import Path
from typing import List, Optional

# Re-export the canonical ``LATEST`` constant + resolver from the
# sibling ``latest_resolution`` module (sub-deliverable 5 of #283,
# issue #288). Local re-export preserves the historical import path
# (``cross_thread_refs.LATEST``) so downstream callers keep working
# unchanged.
from anvil.lib.latest_resolution import LATEST, resolve_latest

# Regex for the two shipped cross-thread reference shapes:
#
#   [[../<other-slug>/<other-slug>.latest]]
#   [[../<other-slug>/<other-slug>.N]]
#   [[../<other-slug>/<other-slug>.latest/<file>]]
#   [[../<other-slug>/<other-slug>.N/<file>]]
#
# Where ``<other-slug>`` is a directory name (slug shape — lowercase
# letters / digits / hyphens / underscores per the per-thread slug
# convention codified across the framework), the ``.N`` segment is
# either the literal string ``latest`` or a non-negative integer, and
# ``<file>`` is an optional path inside the version directory (e.g.,
# ``memo.md`` or ``exhibits/<file>``).
#
# The slug check is intentionally permissive (any non-``/`` character)
# — the on-disk discovery step at resolution time is the final gate.
# Over-matching here is safer than under-matching: a false-positive ref
# resolves to "thread not found" cleanly, while a false-negative ref
# would silently propagate as if the reviewer didn't see it.
_CROSS_THREAD_REF_RE = re.compile(
    r"""
    \[\[                                # opening [[
    \.\./                               # ../ — the cross-thread anchor
    (?P<other_slug>[^/\]]+)             # other thread slug
    /                                   # path separator
    (?P=other_slug)                     # repeated slug as version-dir stem
    \.(?P<version>latest|\d+)           # .latest OR .N (integer)
    (?:/(?P<file>[^\]]+))?              # optional /<file> suffix
    \]\]                                # closing ]]
    """,
    re.VERBOSE,
)


@dataclass(frozen=True)
class CrossThreadRef:
    """A single cross-thread reference parsed from ``memo.md``.

    Attributes
    ----------
    line
        1-based source line where the reference was found. Useful for
        the reviewer's ``comments.md`` cross-link and for the verdict's
        revision priorities.
    raw
        The verbatim ``[[...]]`` text, including the brackets. Surfaced
        so the reviewer can quote the exact ref text in ``comments.md``
        and the operator can grep for it.
    other_slug
        The sibling thread slug (the directory name under the portfolio
        root). E.g., ``"meridian-synthesis"`` for
        ``[[../meridian-synthesis/meridian-synthesis.latest]]``.
    version
        The version specifier — either the literal string ``"latest"``
        or a numeric string like ``"3"``. Kept as a string (not parsed
        to int) so the ``.latest`` symbolic form round-trips cleanly.
    file
        The file inside the version directory, when the reference points
        at a specific file (e.g., the body markdown ``"<other-slug>.md"``
        echoing the slug per #295, or ``"exhibits/figure.png"``).
        ``None`` when the reference points at the version dir root.
    """

    line: int
    raw: str
    other_slug: str
    version: str
    file: Optional[str]


@dataclass(frozen=True)
class CrossThreadResolution:
    """The result of resolving a :class:`CrossThreadRef` on-disk.

    Attributes
    ----------
    ref
        The original :class:`CrossThreadRef` this resolution was built
        from. Carried so callers don't need to maintain parallel lists.
    target_path
        The path the ref resolves to, when ``resolved=True``. For refs
        pointing at the version dir root this is the version directory
        itself; for refs with a ``file`` suffix this is the file inside
        the version directory. ``None`` when ``resolved=False``.
    resolved
        ``True`` when the target path exists on disk; ``False`` when
        any part of the resolution chain failed.
    reason
        Short tag explaining the failure when ``resolved=False``. One of:

        - ``"thread not found"`` — ``<portfolio>/<other-slug>/`` does
          not exist or is not a directory.
        - ``"version not found"`` — for explicit-N refs:
          ``<portfolio>/<other-slug>/<other-slug>.<N>/`` does not exist.
        - ``"latest unresolvable"`` — for ``.latest`` refs: neither a
          ``.latest`` symlink/directory nor any ``<other-slug>.<N>/``
          version dir exists under ``<portfolio>/<other-slug>/``.
        - ``"file not found"`` — the version dir resolves cleanly but
          the ``file`` suffix inside it does not exist.

        ``None`` when ``resolved=True``.
    """

    ref: CrossThreadRef
    target_path: Optional[Path]
    resolved: bool
    reason: Optional[str]


def find_cross_thread_refs(text: str) -> List[CrossThreadRef]:
    """Enumerate cross-thread references in a markdown body.

    Scans ``text`` for the two shipped reference shapes documented in
    the module docstring. Returns a list of :class:`CrossThreadRef`
    entries in source-line order. Each entry carries the 1-based line
    number, the raw ``[[...]]`` text, the parsed ``other_slug``, the
    version specifier (``"latest"`` or a numeric string), and the
    optional file suffix.

    Parameters
    ----------
    text
        The markdown body to scan. Typically the contents of
        ``<thread>.{N}/memo.md``.

    Returns
    -------
    list[CrossThreadRef]
        Parsed refs in source-line order. May be empty when ``text``
        contains no cross-thread refs (the common case — many threads
        do not cite siblings). The empty-list return is the backwards-
        compat anchor: a memo with no cross-thread refs produces zero
        findings, byte-identical to the pre-#287 behavior.

    Notes
    -----
    The function does NOT validate that ``other_slug`` is well-formed
    or that the referenced file path is plausible — those checks happen
    at resolution time (:func:`resolve_cross_thread_ref`). The
    enumeration is intentionally permissive so a typo'd slug surfaces
    as a "thread not found" finding rather than being silently dropped
    at parse time.
    """
    refs: List[CrossThreadRef] = []
    for line_idx, line_text in enumerate(text.splitlines(), start=1):
        for match in _CROSS_THREAD_REF_RE.finditer(line_text):
            refs.append(
                CrossThreadRef(
                    line=line_idx,
                    raw=match.group(0),
                    other_slug=match.group("other_slug"),
                    version=match.group("version"),
                    file=match.group("file"),
                )
            )
    return refs


def resolve_cross_thread_ref(
    ref: CrossThreadRef, portfolio_root: Path
) -> CrossThreadResolution:
    """Resolve a single :class:`CrossThreadRef` against on-disk state.

    Walks ``<portfolio_root>/<ref.other_slug>/`` to find the version
    directory (``<other_slug>.<N>/`` for explicit-N refs, OR the
    ``.latest`` symlink-or-walk-to-highest fallback for ``.latest``
    refs). When the ref carries a ``file`` suffix, checks that the file
    exists inside the resolved version dir.

    Parameters
    ----------
    ref
        The parsed cross-thread reference to resolve.
    portfolio_root
        The portfolio root directory under which sibling threads live.
        Typically ``thread_dir.parent`` (the directory containing the
        citing thread).

    Returns
    -------
    CrossThreadResolution
        Resolution result. ``resolved=True`` when every step of the
        chain succeeded; ``resolved=False`` with a short ``reason``
        otherwise.

    Notes
    -----
    The resolver is **non-throwing** on filesystem errors — any
    ``OSError`` during traversal degrades to a ``"thread not found"``
    or ``"latest unresolvable"`` reason rather than propagating. This
    mirrors the lenient-form precedent across the memo lib
    (``refs_resolver``, ``project_discovery``, ``project_brief``):
    consumer-friendly errors that surface as findings, not exceptions.
    """
    portfolio_root = Path(portfolio_root)
    other_thread_dir = portfolio_root / ref.other_slug

    if not other_thread_dir.is_dir():
        return CrossThreadResolution(
            ref=ref,
            target_path=None,
            resolved=False,
            reason="thread not found",
        )

    # Resolve the version directory.
    if ref.version == LATEST:
        # Delegate to the canonical resolver from latest_resolution.py
        # (sub-deliverable 5 / #288). Same four-step rule (symlink >
        # real .latest/ dir > walk-to-highest > None) the legacy
        # private helper implemented, now shared with intra-thread
        # callers.
        version_dir = resolve_latest(other_thread_dir, ref.other_slug)
        if version_dir is None:
            return CrossThreadResolution(
                ref=ref,
                target_path=None,
                resolved=False,
                reason="latest unresolvable",
            )
    else:
        # Explicit numeric version like .N — the regex guarantees
        # ``ref.version`` is a numeric string here.
        version_dir = other_thread_dir / f"{ref.other_slug}.{ref.version}"
        if not version_dir.is_dir():
            return CrossThreadResolution(
                ref=ref,
                target_path=None,
                resolved=False,
                reason="version not found",
            )

    # Optional file inside the version dir.
    if ref.file is None:
        return CrossThreadResolution(
            ref=ref,
            target_path=version_dir,
            resolved=True,
            reason=None,
        )

    target = version_dir / ref.file
    if not target.exists():
        return CrossThreadResolution(
            ref=ref,
            target_path=None,
            resolved=False,
            reason="file not found",
        )
    return CrossThreadResolution(
        ref=ref,
        target_path=target,
        resolved=True,
        reason=None,
    )


def resolve_cross_thread_refs(
    memo_text: str, portfolio_root: Path
) -> List[CrossThreadResolution]:
    """Convenience batch resolver — enumerate + resolve all refs.

    Equivalent to::

        [resolve_cross_thread_ref(r, portfolio_root)
         for r in find_cross_thread_refs(memo_text)]

    Returns the per-ref resolution list in source-line order. The
    caller (the reviewer's dim-3 back-check sub-step) iterates and
    tallies the unresolved count for the dim-3 deduction. The list is
    empty when ``memo_text`` contains no cross-thread refs — the
    backwards-compat anchor (byte-identical to pre-#287 behavior).
    """
    return [
        resolve_cross_thread_ref(ref, portfolio_root)
        for ref in find_cross_thread_refs(memo_text)
    ]


__all__ = [
    "CrossThreadRef",
    "CrossThreadResolution",
    "LATEST",
    "find_cross_thread_refs",
    "resolve_cross_thread_ref",
    "resolve_cross_thread_refs",
    # Re-exported from latest_resolution (sub-deliverable 5 / #288).
    # Kept on the public surface so callers that already import from
    # cross_thread_refs do not need to migrate.
    "resolve_latest",
]
