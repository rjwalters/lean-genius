"""Canonical ``.latest`` resolution for memo thread version directories
(issue #288, sub-deliverable 5 of #283).

This module ships the **single source of truth** for resolving a
``<slug>.latest`` reference to a concrete version directory on disk —
and, since issue #473, for **maintaining** the convenience symlinks
(:func:`update_latest_symlinks`, wired into the memo lifecycle via
``anvil/skills/memo/lib/latest_phase.py``). Issue #288's curator
recommendation — **option (c): pure tolerance** — originally left the
symlinks consumer-maintained; the studio canary surfaced that the
consumer-side convention was agent-invisible (#473), so the contract is
now *framework-maintained by default, consumer-pinnable* (see
``anvil/lib/snippets/version_layout.md`` §"Convenience ``.latest``
symlinks"). The **read side is unchanged**: every code path that has
to resolve a symbolic ``.latest`` reference goes through
:func:`resolve_latest`, which tolerates four on-disk shapes:

1. ``<thread_dir>/<slug>.latest`` exists as a **symlink** pointing at a
   ``<slug>.<N>/`` directory. The author pinned the symlink to a
   specific version (the load-bearing case for intentional pinning to a
   non-highest version — e.g., "publish ``.latest`` against the
   reviewed-and-AUDITED v3 even though v4 is in progress").
2. ``<thread_dir>/<slug>.latest`` exists as a **real directory** (no
   symlink). This is the rarer case — typically the operator hasn't
   migrated to the symlink convention yet, or is on a filesystem where
   symlinks are awkward (Windows without WSL).
3. No ``<slug>.latest`` of any shape, but one or more
   ``<slug>.<N>/`` sibling directories exist. The helper walks the
   children and returns the **highest-numbered** one. This is the
   walk-to-highest fallback — the load-bearing path for the "operator
   never created the symlink" case (the canary's common case today
   per #288's option (c) rationale).
4. None of the above — no symlink, no ``.latest/`` directory, no
   ``<slug>.<N>/`` siblings. The helper returns ``None``, leaving the
   caller to surface a clean "no version dirs" error to the operator.

Precedence is fixed: 1 > 2 > 3 > 4. **A pinned symlink always wins**
over walk-to-highest — an author who intentionally pins ``.latest`` to
v3 even though v4 exists gets v3 from this helper. This is the
load-bearing AC from the issue: "If ``<slug>.latest`` symlink exists, it
takes precedence (an author can pin ``.latest`` to a non-highest version
intentionally)."

Public API
----------

``resolve_latest(thread_dir: Path, slug: str) -> Optional[Path]``
    The canonical resolver. Returns the path to the resolved version
    directory (which may be the ``.latest`` symlink-or-directory itself,
    or the highest-numbered ``<slug>.<N>/``), or ``None`` when no
    resolution is possible. **Non-throwing**: filesystem errors during
    traversal degrade to ``None`` rather than propagating, mirroring the
    lenient-form precedent across the memo lib (``refs_resolver``,
    ``project_discovery``, ``project_brief``).

``update_latest_symlinks(thread_dir: Path, slug: str, *, force: bool = False) -> list[LatestSymlinkUpdate]``
    The canonical **writer** (issue #473). Creates or re-points the
    convenience symlinks ``<slug>.latest -> <slug>.{max_N}`` and
    ``<slug>.latest.review -> <slug>.{max_review_N}.review`` (plus any
    already-existing ``<slug>.latest.<tag>`` family) with **relative**
    targets — ``ln -sfn`` semantics. Each suffix family is handled
    independently. The steady-lifecycle stale link (still on the
    immediately-superseded version, set before the new highest existed)
    re-points freely; every other resolvable non-highest symlink is
    presumptively an operator **pin** and preserved by default — the
    #288 pin-honoring AC — re-pointed only under ``force=True``. A real
    ``.latest/`` *directory* (non-symlink) is never replaced, force or
    not. Non-throwing: per-family ``OSError`` degrades to a ``skipped``
    record rather than propagating.

``LatestSymlinkUpdate``
    The per-family outcome record returned by
    ``update_latest_symlinks`` (``link_name`` / ``target`` / ``action``
    / ``note``).

``LATEST``
    The literal string ``"latest"`` — the symbolic version specifier.
    Re-exported here as the single source of truth so callers that
    construct ``.latest`` paths (e.g., the cross-thread parser's regex)
    can reference one constant.

Relationship to ``cross_thread_refs``
-------------------------------------

Before this module shipped, the same walk-to-highest logic lived
privately inside ``cross_thread_refs._resolve_latest_version_dir`` (#287
/ PR #291). This module **extracts** that helper into a reusable public
surface so other call sites — intra-thread ``.latest`` resolution,
future ``memo-draft`` / ``memo-revise`` path resolution, downstream
tooling — can share the contract without re-implementing the regex or
the symlink-precedence rule. ``cross_thread_refs`` now delegates to
``resolve_latest`` to preserve a single source of truth.

Skill-local first
-----------------

Lives under ``anvil/skills/memo/lib/`` per the CLAUDE.md "skill-local
first, lib promotion later" pattern. Promotion to ``anvil/lib/`` is
queued for the second-consumer trigger (likely ``anvil:proposal`` —
which has its own portfolio shape — or ``anvil:paper``). Until then the
module has zero ``anvil.*`` runtime imports.

No new Python deps
------------------

Standard library only (``re``, ``pathlib``, ``typing``). The CLAUDE.md
"Python deps: subprocess-only by default" contract is preserved.
"""

from __future__ import annotations

import os
import re
from dataclasses import dataclass, field
from pathlib import Path
from typing import Dict, List, Optional


# The literal symbolic version specifier. Coupled to the consumer-side
# ``.latest`` symlink convention documented in
# ``anvil/lib/snippets/version_layout.md`` §"Convenience ``.latest``
# symlinks". Keeping the constant here (and re-exporting from
# ``cross_thread_refs``) ensures one source of truth for the literal.
LATEST = "latest"


def resolve_latest(thread_dir: Path, slug: str) -> Optional[Path]:
    """Resolve ``<slug>.latest`` to a concrete version directory on disk.

    The canonical four-step resolution rule per issue #288 option (c):

    1. If ``<thread_dir>/<slug>.latest`` exists as a **symlink** (whether
       resolvable or dangling-but-listed), return it. Symlink wins
       unconditionally — an author can pin ``.latest`` to a non-highest
       version intentionally.
    2. Else if ``<thread_dir>/<slug>.latest`` exists as a **real
       directory** (not a symlink), return it.
    3. Else, enumerate ``<thread_dir>/<slug>.<N>/`` for all integer ``N``,
       pick the highest, and return that directory.
    4. Else, return ``None``. No version dirs and no symlink — the
       caller should surface a clean "no version dirs" error.

    Parameters
    ----------
    thread_dir
        The parent directory that contains the thread's version dirs.
        For a thread at ``<portfolio>/investment-memo/`` with version
        dirs ``investment-memo.1/``, ``investment-memo.2/``, this is
        ``<portfolio>/investment-memo/``. For the cross-thread case,
        this is the sibling thread's directory under the portfolio root.
    slug
        The thread slug — the stem of the version dirs. For an
        ``investment-memo`` thread, slug is ``"investment-memo"`` and the
        helper looks for ``investment-memo.latest``,
        ``investment-memo.1``, ``investment-memo.2``, etc.

    Returns
    -------
    Path or None
        The resolved version directory path. **Note**: when steps 1 or 2
        fire, the return is the literal ``<thread_dir>/<slug>.latest``
        path (not the dereferenced target) — this matches the
        cross-thread resolver's pre-#288 behavior where the operator-
        visible path is what gets recorded in ``comments.md``. Callers
        that need the dereferenced target call ``.resolve()`` themselves.
        Returns ``None`` when no resolution is possible.

    Notes
    -----
    **Non-throwing**: any ``OSError`` during directory traversal (a
    symlink loop, a permission error, a vanished directory) degrades to
    ``None`` rather than propagating. The lenient-form precedent across
    the memo lib (``refs_resolver``, ``project_discovery``,
    ``project_brief``) is the consumer-friendly contract — errors surface
    as findings, not exceptions.

    **Symlink precedence**: a symlink at ``<slug>.latest`` wins even if
    its target does not exist (e.g., a dangling symlink left over from
    a deleted version dir). The caller is responsible for handling the
    case where the returned path's children do not exist — the
    cross-thread resolver, for example, surfaces such cases as
    ``"file not found"`` reasons on the higher-level resolution.

    Examples
    --------
    Symlink precedence (intentional pin to non-highest)::

        # On disk:
        #   <thread_dir>/<slug>.1/
        #   <thread_dir>/<slug>.2/
        #   <thread_dir>/<slug>.3/
        #   <thread_dir>/<slug>.latest -> <slug>.2  (pinned)
        # Returns: <thread_dir>/<slug>.latest (the symlink path)

    Walk-to-highest (no symlink)::

        # On disk:
        #   <thread_dir>/<slug>.1/
        #   <thread_dir>/<slug>.2/
        #   <thread_dir>/<slug>.7/
        # Returns: <thread_dir>/<slug>.7

    Real directory at ``.latest`` (no symlink)::

        # On disk:
        #   <thread_dir>/<slug>.1/
        #   <thread_dir>/<slug>.latest/    (real dir, not a symlink)
        # Returns: <thread_dir>/<slug>.latest

    No resolution::

        # On disk:
        #   <thread_dir>/   (empty)
        # Returns: None
    """
    thread_dir = Path(thread_dir)

    # Step 0: guard against the thread_dir itself not existing. A clean
    # ``None`` here lets the caller surface a "thread not found" error
    # at its preferred granularity (the cross-thread resolver has its
    # own dedicated error for this).
    try:
        if not thread_dir.is_dir():
            return None
    except OSError:
        return None

    latest_path = thread_dir / f"{slug}.{LATEST}"

    # Step 1: symlink wins. Use ``is_symlink`` (rather than ``exists``)
    # so dangling symlinks are also detected and returned — the operator
    # intentionally created the symlink, returning it is the right thing
    # even if the target has since been deleted.
    try:
        if latest_path.is_symlink():
            return latest_path
    except OSError:
        # Defensive: a permission error or weird filesystem state on
        # ``is_symlink``. Fall through to step 2.
        pass

    # Step 2: real directory at ``.latest`` (not a symlink).
    try:
        if latest_path.is_dir():
            return latest_path
    except OSError:
        pass

    # Step 3: walk-to-highest fallback.
    version_re = re.compile(rf"^{re.escape(slug)}\.(\d+)$")
    candidates: List[tuple[int, Path]] = []
    try:
        children = list(thread_dir.iterdir())
    except OSError:
        return None
    for child in children:
        try:
            if not child.is_dir():
                continue
        except OSError:
            # Skip children that vanished or that we can't stat. The
            # other children may still resolve cleanly.
            continue
        match = version_re.match(child.name)
        if match is None:
            continue
        try:
            n = int(match.group(1))
        except ValueError:
            # Defensive — the regex only matches digits, so int() should
            # not fail. Skip on the off-chance the platform / encoding
            # surfaces a surprising digit class.
            continue
        candidates.append((n, child))

    if not candidates:
        # Step 4: no resolution possible.
        return None
    candidates.sort(key=lambda pair: pair[0], reverse=True)
    return candidates[0][1]


# ---------------------------------------------------------------------------
# Writer half (issue #473): canonical ``.latest`` symlink maintenance
# ---------------------------------------------------------------------------

# ``action`` values on :class:`LatestSymlinkUpdate`.
ACTION_CREATED = "created"
ACTION_REPOINTED = "repointed"
ACTION_UNCHANGED = "unchanged"
ACTION_PINNED = "pinned"
ACTION_REFUSED_REAL_DIR = "refused-real-dir"
ACTION_SKIPPED = "skipped"


@dataclass(frozen=True)
class LatestSymlinkUpdate:
    """Per-family outcome record from :func:`update_latest_symlinks`.

    Attributes
    ----------
    link_name
        The symlink's basename inside the thread dir, e.g.
        ``"acme.latest"`` or ``"acme.latest.review"``.
    target
        The **relative** target the family should point at (the
        highest-N directory's basename, e.g. ``"acme.3"``), or ``None``
        when no target exists for the family (e.g., a dangling
        ``.latest.<tag>`` with no ``<slug>.<N>.<tag>/`` siblings).
    action
        One of ``created`` / ``repointed`` / ``unchanged`` / ``pinned``
        / ``refused-real-dir`` / ``skipped``.
    note
        Free-form human-readable detail (what was repaired, why a pin
        was preserved, the OSError text for ``skipped``, ...).
    """

    link_name: str
    target: Optional[str]
    action: str
    note: str = field(default="")


def _atomic_symlink(target: str, link_path: Path) -> None:
    """``ln -sfn`` semantics: (re)point ``link_path`` at ``target``.

    Creates the new symlink under a temporary leading-dot name in the
    same directory, then ``os.replace``s it over the final name — the
    final path atomically flips from old target to new target and is
    never absent in between.
    """
    tmp = link_path.parent / f".{link_path.name}.tmp-{os.getpid()}"
    try:
        if tmp.is_symlink() or tmp.exists():
            tmp.unlink()
        os.symlink(target, tmp)
        os.replace(tmp, link_path)
    except OSError:
        try:
            if tmp.is_symlink() or tmp.exists():
                tmp.unlink()
        except OSError:
            pass
        raise


def _update_one_family(
    thread_dir: Path,
    link_name: str,
    desired: Optional[str],
    second: Optional[str],
    *,
    force: bool,
) -> Optional[LatestSymlinkUpdate]:
    """Apply the update rule to one suffix family. May raise ``OSError``.

    ``desired`` is the highest-N member's basename (or ``None`` when the
    family has no enumerable members); ``second`` is the second-highest
    member's basename (used by the stale-vs-pin discrimination below).

    Returns ``None`` when there is nothing to record (no existing link
    and no target — the family does not exist on disk in any form).
    """
    link_path = thread_dir / link_name

    exists_as_symlink = link_path.is_symlink()
    if not exists_as_symlink and link_path.exists():
        # Shape 2 of the four-step rule: a real entry (directory — or,
        # degenerately, a file) at the ``.latest`` name. NEVER replaced,
        # force or not (issue #473 AC).
        kind = "directory" if link_path.is_dir() else "non-symlink entry"
        return LatestSymlinkUpdate(
            link_name=link_name,
            target=desired,
            action=ACTION_REFUSED_REAL_DIR,
            note=f"real {kind} exists at {link_name}; never replaced",
        )

    if exists_as_symlink:
        current_text = os.readlink(link_path)
        current_target = Path(current_text)
        if not current_target.is_absolute():
            current_target = thread_dir / current_text
        resolvable = False
        try:
            resolvable = current_target.is_dir()
        except OSError:
            resolvable = False

        if desired is None:
            # Existing link but no <slug>.<N>[.<tag>] targets on disk.
            if resolvable:
                # Resolvable with no enumerable family target — treat as
                # a pin (it points somewhere real the operator chose).
                return LatestSymlinkUpdate(
                    link_name=link_name,
                    target=None,
                    action=ACTION_PINNED,
                    note=(
                        f"resolvable symlink to {current_text} preserved; "
                        "no enumerable version-family target to re-point at"
                    ),
                )
            return LatestSymlinkUpdate(
                link_name=link_name,
                target=None,
                action=ACTION_SKIPPED,
                note=(
                    f"dangling symlink (was {current_text}) and no "
                    "version-family target exists to repair it with"
                ),
            )

        desired_path = thread_dir / desired
        if resolvable:
            points_at_desired = False
            try:
                points_at_desired = (
                    current_target.resolve() == desired_path.resolve()
                )
            except OSError:
                points_at_desired = False
            if points_at_desired:
                if current_text == desired:
                    return LatestSymlinkUpdate(
                        link_name=link_name,
                        target=desired,
                        action=ACTION_UNCHANGED,
                        note="already points at the highest version",
                    )
                # Same destination via a non-canonical (absolute / odd)
                # link text — normalize to the relative form. Not a pin:
                # it already points at the highest version.
                _atomic_symlink(desired, link_path)
                return LatestSymlinkUpdate(
                    link_name=link_name,
                    target=desired,
                    action=ACTION_REPOINTED,
                    note=f"normalized link text {current_text} -> {desired}",
                )
            # Resolvable but NOT the highest version. Two shapes share
            # this on-disk state and must be discriminated (#473 design
            # decision, flagged in the PR):
            #
            # 1. The **steady-lifecycle stale link**: a link that was
            #    tracking the highest version until the lifecycle wrote
            #    a new one moments ago (memo-draft step 9.6 /
            #    memo-revise step 9.8 run right after the version
            #    write). Signature: it points at the
            #    **immediately-superseded** (second-highest) member AND
            #    the link itself predates the new highest dir. This
            #    MUST re-point — it is the tracking path (#473 AC1).
            # 2. An **intentional operator pin** (#288's load-bearing
            #    AC — "publish .latest against the reviewed v3 even
            #    though v4 is in progress"). Signature: anything else —
            #    a link set *after* the newer version already existed
            #    (its own lstat mtime is >= the highest dir's mtime),
            #    or one lagging by more than one version, or one
            #    pointing outside the enumerable family. Preserved with
            #    a notice; ``force=True`` re-points.
            stale = False
            if not force and second is not None:
                points_at_second = False
                try:
                    points_at_second = (
                        current_target.resolve()
                        == (thread_dir / second).resolve()
                    )
                except OSError:
                    points_at_second = False
                if points_at_second:
                    try:
                        link_mtime = os.lstat(link_path).st_mtime
                        highest_mtime = (thread_dir / desired).stat().st_mtime
                        stale = link_mtime < highest_mtime
                    except OSError:
                        stale = False
            if force:
                _atomic_symlink(desired, link_path)
                return LatestSymlinkUpdate(
                    link_name=link_name,
                    target=desired,
                    action=ACTION_REPOINTED,
                    note=f"forced re-point from pinned target {current_text}",
                )
            if stale:
                _atomic_symlink(desired, link_path)
                return LatestSymlinkUpdate(
                    link_name=link_name,
                    target=desired,
                    action=ACTION_REPOINTED,
                    note=(
                        f"superseded tracking link (was {current_text}, "
                        f"set before {desired} existed)"
                    ),
                )
            return LatestSymlinkUpdate(
                link_name=link_name,
                target=desired,
                action=ACTION_PINNED,
                note=(
                    f"pinned to {current_text} (non-highest); "
                    "preserved — pass force=True to re-point"
                ),
            )

        # Dangling symlink: repair freely (the operator's target is
        # gone; pointing at the highest version is strictly better).
        _atomic_symlink(desired, link_path)
        return LatestSymlinkUpdate(
            link_name=link_name,
            target=desired,
            action=ACTION_REPOINTED,
            note=f"repaired dangling symlink (was {current_text})",
        )

    # No entry at the ``.latest`` name.
    if desired is None:
        return None
    _atomic_symlink(desired, link_path)
    return LatestSymlinkUpdate(
        link_name=link_name,
        target=desired,
        action=ACTION_CREATED,
        note="",
    )


def update_latest_symlinks(
    thread_dir: Path,
    slug: str,
    *,
    force: bool = False,
) -> List[LatestSymlinkUpdate]:
    """Create / re-point the ``<slug>.latest*`` convenience symlinks.

    The canonical writer half of the ``.latest`` convention (issue
    #473), wired into the memo lifecycle via the
    ``anvil/skills/memo/lib/latest_phase.py`` CLI. Each suffix family is
    handled **independently**:

    - ``<slug>.latest`` → the highest ``<slug>.{N}/`` version dir.
    - ``<slug>.latest.review`` → the highest ``<slug>.{N}.review/``
      critic sibling (maintained by default — the studio-canary pair;
      note it may lag ``<slug>.latest`` by one when the newest version
      has not been reviewed yet).
    - ``<slug>.latest.<tag>`` for any other tag → maintained **only
      when the symlink already exists** (the framework re-points what
      the operator opted into; it does not invent new tag families).

    Symlink targets are **relative** basenames (``acme.latest ->
    acme.3``), matching the documented ``ln -sfn`` idiom and keeping
    the links portable across repo moves/clones.

    Update rule per family (the #288/#473 pin-preservation contract):

    - **No entry** at the ``.latest`` name → create the symlink.
    - **Symlink already pointing at the highest** version → no-op
      (``unchanged``); a non-canonical link text to the same
      destination is normalized to the relative form.
    - **Symlink resolving to a real, non-highest** version dir → two
      shapes, discriminated by the steady-lifecycle signature:

      - the **superseded tracking link** — it points at the
        immediately-superseded (second-highest) member AND the symlink
        itself predates the new highest dir (lstat mtime comparison) —
        is re-pointed freely. This is the normal post-write shape and
        the #473 tracking AC.
      - **everything else** is presumptively an intentional operator
        pin (#288's load-bearing AC): a link set *after* a newer
        version already existed, or lagging by more than one version,
        or pointing outside the enumerable family. Preserved with a
        ``pinned`` record unless ``force=True``.

    - **Dangling symlink** → repaired freely (re-pointed at the
      highest version).
    - **Real directory (or any non-symlink entry)** at the ``.latest``
      name → never replaced (``refused-real-dir``), force or not.

    Returns the per-family outcome records; an **empty list** means the
    thread dir had no version dirs and no ``.latest`` entries (the
    empty-thread no-op). **Non-throwing**: a per-family ``OSError``
    degrades to a ``skipped`` record; a missing/unreadable
    ``thread_dir`` returns ``[]``.
    """
    thread_dir = Path(thread_dir)
    try:
        if not thread_dir.is_dir():
            return []
        children = sorted(os.listdir(thread_dir))
    except OSError:
        return []

    version_re = re.compile(rf"^{re.escape(slug)}\.(\d+)$")
    sibling_re = re.compile(rf"^{re.escape(slug)}\.(\d+)\.([a-zA-Z0-9-]+)$")
    latest_tag_re = re.compile(
        rf"^{re.escape(slug)}\.{LATEST}\.([a-zA-Z0-9-]+)$"
    )
    bare_latest_name = f"{slug}.{LATEST}"

    versions: Dict[int, str] = {}
    siblings: Dict[str, Dict[int, str]] = {}
    existing_latest_tags: List[str] = []
    bare_latest_exists = False

    for name in children:
        child = thread_dir / name
        m = version_re.match(name)
        if m is not None:
            try:
                if child.is_dir():
                    versions[int(m.group(1))] = name
            except OSError:
                pass
            continue
        m = sibling_re.match(name)
        if m is not None:
            try:
                if child.is_dir():
                    siblings.setdefault(m.group(2), {})[int(m.group(1))] = name
            except OSError:
                pass
            continue
        if name == bare_latest_name:
            bare_latest_exists = True
            continue
        m = latest_tag_re.match(name)
        if m is not None:
            existing_latest_tags.append(m.group(1))

    # Empty-thread no-op: nothing versioned and nothing to maintain.
    if not versions and not siblings and not bare_latest_exists and not existing_latest_tags:
        return []

    def _top_two(
        family: Dict[int, str],
    ) -> tuple[Optional[str], Optional[str]]:
        """(highest, second-highest) basenames for one family."""
        if not family:
            return None, None
        ordered = sorted(family, reverse=True)
        highest = family[ordered[0]]
        second = family[ordered[1]] if len(ordered) > 1 else None
        return highest, second

    # Family worklist: bare ``.latest`` and ``.latest.review`` are
    # maintained by default; every other tag only when an existing
    # ``<slug>.latest.<tag>`` entry opted the family in.
    families: List[tuple[str, Optional[str], Optional[str]]] = []
    if versions or bare_latest_exists:
        families.append((bare_latest_name, *_top_two(versions)))
    review_link_name = f"{bare_latest_name}.review"
    if siblings.get("review") or "review" in existing_latest_tags:
        families.append(
            (review_link_name, *_top_two(siblings.get("review", {})))
        )
    for tag in existing_latest_tags:
        if tag == "review":
            continue
        families.append(
            (f"{bare_latest_name}.{tag}", *_top_two(siblings.get(tag, {})))
        )

    updates: List[LatestSymlinkUpdate] = []
    for link_name, desired, second in families:
        try:
            record = _update_one_family(
                thread_dir, link_name, desired, second, force=force
            )
        except OSError as exc:
            record = LatestSymlinkUpdate(
                link_name=link_name,
                target=desired,
                action=ACTION_SKIPPED,
                note=f"filesystem error: {exc}",
            )
        if record is not None:
            updates.append(record)
    return updates


__all__ = [
    "ACTION_CREATED",
    "ACTION_PINNED",
    "ACTION_REFUSED_REAL_DIR",
    "ACTION_REPOINTED",
    "ACTION_SKIPPED",
    "ACTION_UNCHANGED",
    "LATEST",
    "LatestSymlinkUpdate",
    "resolve_latest",
    "update_latest_symlinks",
]
