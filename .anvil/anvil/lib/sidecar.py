"""Atomic sidecar directory writes via staging-then-rename (issue #350).

The Studio canary surfaced 13 critic-sibling directories (memo reviews,
audits, narratives) in **partial** state after mid-cycle interrupts: some
of the expected files (`verdict.md`, `scoring.md`, `comments.md`,
`_summary.md`, `_meta.json`, `_progress.json`) made it to disk, others
did not. The existing discovery contract in :mod:`anvil.lib.critics`
(specifically ``_has_recognizable_review``) treats any sibling dir with a
canonical ``_review.json`` OR a complete legacy file triple as a
valid critic — but the partial-write shapes from interrupted sessions
slip through: e.g., a directory with ``_review.json`` only (no
``_progress.json``, no ``_meta.json``) IS discovered and IS aggregated,
silently producing under-specified sidecars.

The file-level ``tmp + os.replace`` precedent — now consolidated in
:mod:`anvil.lib.atomic_write` (issue #1104; previously reimplemented
independently across :func:`anvil.lib.cite._cache_write`,
:mod:`anvil.skills.proposal.lib.synthesizer`,
:mod:`anvil.skills.project-migrate.lib.apply`,
:mod:`anvil.skills.deck.lib.imagegen`, and others) — gives correctness
at the **file** boundary; the studio failure mode is at the
**directory** boundary, where a fan-in of N file writes can be
interrupted after K files.

This module provides the directory-level analog:

1. The writer stages its files into a leading-dot sibling
   ``.<slug>.<N>.<tag>.tmp/`` directory.
2. On clean completion, the staged dir is renamed (atomically, per
   POSIX ``rename(2)`` on same-filesystem dir-to-dir) to its final name
   ``<slug>.<N>.<tag>/``.
3. On exception or missing-required-file, the staged dir is **left in
   place** so a forensic check can see what was produced, and the next
   per-critic sweep removes it.
4. A per-critic entry-step sweep (:func:`cleanup_one_staging`) targets
   only the *single* staging path that corresponds to the calling
   critic's intended ``final_dir``. It is the load-bearing surface for
   the critic-writing commands across all 11 artifact-class skills and
   is **parallel-safe**: concurrent critics writing different sidecars
   under the same portfolio root never sweep each other's in-flight
   staging dirs (issue #376).
5. An operator-facing portfolio-wide sweep
   (:func:`cleanup_stale_staging`) walks a parent directory for
   ``*.tmp/`` leading-dot dirs and removes them, logging the count. It
   is **NOT** safe to call from a per-critic entry step in a parallel
   fan-out workflow — it will sweep sibling critics' in-flight staging
   dirs. Reserve it for operator-time maintenance (e.g. a one-shot
   portfolio orphan-cleanup pass).

The leading-dot + ``.tmp`` suffix shape is **safe from accidental
discovery** by :func:`anvil.lib.critics.discover_critics`:

- ``discover_critics`` requires the candidate's name to start with
  ``<slug>.`` (no leading dot allowed; line 125 of ``critics.py``).
- The tag segment (everything after the last dot) cannot itself contain
  a dot (line 129) — so a hypothetical non-leading-dot stage name like
  ``<slug>.<N>.review.tmp/`` is also rejected because its tag
  ``review.tmp`` carries a dot.

Either disqualifier alone is sufficient; we ship both for belt-and-
suspenders robustness.

API
---

.. code-block:: python

    from anvil.lib.sidecar import (
        staged_sidecar,
        cleanup_one_staging,
        cleanup_stale_staging,
    )

    # Per-critic entry-step sweep: targets ONLY the staging path
    # corresponding to this critic's intended final_dir. Parallel-safe
    # under fan-out workflows (issue #376).
    cleanup_one_staging(Path("output/acme-seed.3.review"))

    # Stage + atomically rename a critic sibling directory.
    with staged_sidecar(
        final_dir=Path("output/acme-seed.3.review"),
        required_files=["verdict.md", "scoring.md", "comments.md",
                        "_summary.md", "_meta.json", "_progress.json"],
    ) as staging:
        (staging / "verdict.md").write_text(...)
        (staging / "scoring.md").write_text(...)
        # ... and so on for every required file.

    # Operator-facing portfolio-wide sweep — maintenance use only, NOT
    # safe to call from a per-critic entry step in a parallel fan-out
    # workflow (see issue #376).
    cleanup_stale_staging(Path("output"))

Binary/bulk-asset copy primitive (issue #1017)
-----------------------------------------------

A consumer hook that blocks every Bash-channel write into the checkout
(redirection, ``tee``, ``cp``, ``mv``, ``sed -i`` — a worktree-isolation
guard) leaves a manual/agent session with **no** sanctioned way to place
bytes it did not itself compose: a prior version's ``figures/*.pdf``
carried forward unchanged, a compiled ``main.pdf``, or the raw stdout/
stderr of a ``pdflatex`` compile pass destined for ``compile-log.txt``.
The agent's own editing tool is text-only and cannot hold a binary file's
bytes; re-typing a "summary" of a compile log or reconstructing a PDF by
hand is a fabrication risk, not a copy.

:func:`copy_bytes` is the byte-safe analog of the ``stage``/``commit`` CLI
shim above, extended from text to arbitrary bytes: a single file OR a
directory tree, landed via the same stage-then-atomic-rename shape
:func:`staged_sidecar` uses (so a crash mid-copy of a multi-file
``figures/`` tree never leaves ``dst`` partially written), with an
optional post-copy byte-identity verification (``(size, sha256)``
fingerprint per file, reusing :func:`_file_content_key`) rather than
trusting the underlying ``shutil`` copy silently. CLI shim::

    # Copy a single file (e.g. a scratch-captured compile log) into a
    # sidecar's staging dir:
    python -m anvil.lib.sidecar copy /tmp/compile.log \
        output/.thread.3.audit.tmp/compile-log.txt

    # Copy a whole directory (e.g. carrying figures/ forward unchanged
    # between versions):
    python -m anvil.lib.sidecar copy output/thread.2/figures \
        output/thread.3/figures

Refuses (nonzero exit) if the source is missing or the destination
already exists (``--force`` to overwrite deliberately) — the same
immutability-first default every other write primitive in this module
uses. This is a general-purpose byte-copy primitive, not scoped to
sidecar directories specifically: ``dst`` may be a version-dir path
(``figures/``) or a path inside an open sidecar staging dir
(``compile-log.txt``) — the caller decides, this function only guarantees
the copy itself is atomic and byte-verified.

CLI shim (issue #645)
---------------------

A manual or agent review session with no orchestrating Python driver
cannot hold the :func:`staged_sidecar` ``with`` block open across its
file writes (it writes files with its own editing tool between discrete
tool calls). The module therefore ships a ``python -m anvil.lib.sidecar``
entry point that decomposes the context manager into two commands sharing
the same atomicity guarantee — the manifest check + single
``Path.rename`` — enforced by code rather than re-derived in prose::

    # 1. Stage: create the staging dir, print its path to stdout.
    python -m anvil.lib.sidecar stage output/acme-seed.3.review
    #   -> output/.acme-seed.3.review.tmp

    # 2. Write every required file into the printed staging path with
    #    your own editing tool.

    # 3. Commit: verify the manifest, then atomically rename staging ->
    #    final. Nonzero exit (staging left in place) if any file missing.
    python -m anvil.lib.sidecar commit output/acme-seed.3.review \
        --required verdict.md,scoring.md,comments.md,_meta.json,_progress.json

    # Sweep a single leftover staging dir (parallel-safe, issue #376):
    python -m anvil.lib.sidecar cleanup output/acme-seed.3.review

    # Entry-step recovery for the replace surface (the .bak analog of
    # `cleanup`, issue #881) — run it next to `cleanup`:
    python -m anvil.lib.sidecar recover-replace output/acme-seed.3.review

The ``stage``/``commit`` pair maps to :func:`stage_enter` /
:func:`commit_staged`, which share every helper with
:func:`staged_sidecar` (``staging_path_for``, ``_missing_required_files``,
the ``FileExistsError`` refuse-to-overwrite guard,
:class:`SidecarIncompleteError`). When even ``python``/``uv`` is
unavailable, consuming command docs document a last-resort manual
``mv``-based fallback (see e.g. ``anvil/skills/paper/commands/paper-review.md``).

Migrated-corpus replace surface (issue #881)
---------------------------------------------

``stage_enter``/``staged_sidecar`` refuse (by design) when ``final_dir``
already exists — the immutability guarantee for a *recognizable* anvil
review (issue #350). But a corpus that has just gone through
``anvil:project-migrate --apply`` can leave the canonical
``<thread>.{N}.<tag>/`` path **occupied by foreign, pre-anvil content**
(e.g. a bare ``review.md`` from a hand-rolled pipeline) — a shape that is
NOT a real anvil review (it fails
``anvil.lib.critics._has_recognizable_review``), so the refusal is a false
positive: there is nothing anvil-recognized there yet to protect.

:func:`stage_replace` / :func:`commit_replace` / :func:`abort_replace`
generalize the move-aside/stage/swap recipe that
``anvil/skills/project-migrate/lib/adopt_review.py::_convert_one`` already
uses for the adjacent ``--adopt-review`` problem, so a critic-writing
command can land a *genuinely new* review into an occupied-but-unrecognized
final dir while preserving every pre-existing file (e.g. ``review.md``)
byte-identical alongside the new sidecar payload:

.. code-block:: python

    from anvil.lib.sidecar import stage_replace, commit_replace, abort_replace

    staging = stage_replace(final_dir)  # moves final_dir aside, copies its
                                         # contents into a fresh staging dir
    try:
        (staging / "verdict.md").write_text(...)
        # ... write every required file; foreign files (review.md) are
        # already present in `staging`, copied verbatim.
        commit_replace(final_dir, required_files=[...])
    except BaseException:
        abort_replace(final_dir)
        raise

:func:`stage_replace` refuses (``FileExistsError``) in the two cases where
replacement is NOT the right call: ``final_dir`` does not exist yet (use
:func:`stage_enter` instead), or ``final_dir`` already carries a
*recognizable* anvil review (the #350 guard stays intact — a real review is
never replaced). The CLI shim ships parallel subcommands
(``replace`` / ``commit-replace`` / ``abort-replace``) for non-Python-driver
sessions, mirroring ``stage``/``commit``/``cleanup``.

Cross-session crash recovery for the replace surface
----------------------------------------------------

The ``try``/``except`` recipe above only holds when the **same execution
context** survives to run the handler. The load-bearing consumer of this
surface — ``anvil/skills/essay/commands/essay-review.md`` — is a
*markdown-driven* command with no Python driver: the window between
``stage_replace`` and ``commit_replace`` spans many discrete agent tool
calls, and the session can die inside it (context exhaustion, process kill,
orchestrator timeout — first-class expected failure modes in this
framework). Nothing is left to call :func:`abort_replace`, and the original
content is sitting in a hidden ``.<name>.bak/`` while ``final_dir`` is
*absent*.

The ``.tmp`` crash path has always had an entry-side sweep
(:func:`cleanup_one_staging`, issue #376). The ``.bak`` crash path gets the
symmetric one:

- :func:`recover_interrupted_replace` is the **entry-step recovery sweep**
  for the replace surface. Call it at the top of any command that may use
  ``stage_replace``, right next to ``cleanup_one_staging``. It restores an
  orphaned backup when ``final_dir`` is absent, drops a provably-redundant
  backup when the commit-side rename already landed, and never guesses
  otherwise. CLI analog: ``recover-replace``.
- :func:`stage_enter` / :func:`commit_staged` — the split surface a
  driverless session drives across process boundaries — **refuse**
  (``FileExistsError``) while an orphaned backup is on disk, so a session
  that skips the entry sweep cannot commit a fresh sidecar over the gap and
  strand the only copy of the pre-existing content. This is the
  defense-in-depth half: recovery does not depend on a doc being followed.
  :func:`staged_sidecar` carries the same guard by default, with an explicit
  ``allow_orphaned_backup=True`` opt-out (issue #885) for the one live
  Python driver whose ``except`` path is guaranteed to run and that
  legitimately manages its own same-named ``.bak`` move-aside *around* the
  call — ``anvil/skills/project-migrate/lib/adopt_review.py``'s
  ``_convert_one`` and ``_rescore_one``. Every other caller is guarded.

Redundancy is content-aware, not name-only (issue #885): the shared
:func:`_unpreserved_backup_entries` helper — used by both
:func:`recover_interrupted_replace` and :func:`stage_replace`'s own
pre-move-aside check — recurses into subdirectories and compares each file's
size and content hash against its counterpart in ``final_dir``. A same-named
file with different bytes, or a file missing entirely, counts as
unpreserved; only a backup where every file is byte-identical to its
``final_dir`` counterpart is dropped without a trace left behind.

Contract
--------

- ``staged_sidecar(final_dir, required_files)`` returns a context
  manager. The body of the ``with`` block writes files into the yielded
  staging :class:`pathlib.Path`. On clean exit, the manager verifies
  every name in ``required_files`` exists in the staging dir, then
  ``Path.rename``\\ s the staging dir to ``final_dir``. On exception in
  the body, the staging dir is left in place (no rename, no cleanup) so
  forensic checks can inspect partial state. The exception propagates.
- If ``final_dir`` already exists when ``__enter__`` runs, we raise
  :class:`FileExistsError` immediately — atomic rename only works onto a
  non-existent target, and silently overwriting would defeat the
  immutability guarantee documented in ``anvil/lib/snippets/version_layout.md``.
- ``cleanup_one_staging(final_dir)`` removes exactly the staging path
  at ``staging_path_for(final_dir)`` if it exists and matches the
  leading-dot + ``.tmp`` shape this module owns. Returns ``True`` if a
  staging dir was removed, ``False`` otherwise. Idempotent and safe to
  call repeatedly. This is the per-critic entry-step sweep — it never
  touches sibling critics' staging dirs (issue #376).
- ``cleanup_stale_staging(parent)`` walks ``parent`` for direct children
  whose name starts with ``.`` AND ends with ``.tmp`` (the leading-dot
  + suffix shape this module owns) and removes them. It is idempotent
  and safe to call repeatedly. It logs the removed-dir names at INFO
  level via the :mod:`logging` standard library. **Operator-facing
  maintenance surface only** — calling this from a per-critic entry
  step in a parallel fan-out workflow will sweep sibling critics'
  in-flight staging dirs (issue #376).

Subprocess-only by default
--------------------------

This module uses only :mod:`os`, :mod:`pathlib`, :mod:`shutil`,
:mod:`contextlib`, :mod:`json`, and :mod:`logging` from the standard
library. :func:`write_critic_review_dir` (issue #1086) accepts an
already-built ``Review`` duck-typed on ``model_dump(mode="json")`` rather
than importing :class:`anvil.lib.review_schema.Review` at runtime — the
type is referenced only under ``TYPE_CHECKING`` — so this module still
introduces no new ``pyproject.toml`` dependency and the
"subprocess-only-by-default" contract documented at the top of
``CLAUDE.md`` is preserved.

Critic-sidecar writer consolidation (issue #1086)
--------------------------------------------------

Seven near-duplicate ``write_review_dir()`` / ``_write_review_dir()``
copies (``anvil/lib/pending_marker.py``, ``anvil/lib/numeric_consistency.py``,
``anvil/lib/hyperlink_resolver.py``, ``anvil/lib/figure_content.py``,
``anvil/skills/memo/lib/image_accessibility.py``,
``anvil/skills/memo/lib/citation_coverage.py``,
``anvil/skills/report/lib/claim_figure_grounding.py``) did the same three
steps in the same order — compute the sibling dir, build a typed
``Review`` via that critic's own ``to_review(...)``, write it (and, for
three of the seven, a ``_findings.json`` companion) into the sibling dir
— but had drifted into two behavioral camps: two used
:func:`staged_sidecar` (crash-safe), five used a plain
``mkdir(parents=True, exist_ok=True)`` + ``write_text`` (not crash-safe).
:func:`write_critic_review_dir` is the single canonical implementation
both camps now call: it takes the already-built ``Review`` (and optional
findings payload) rather than a critic-specific ``result`` object, so it
stays decoupled from each critic's ``to_review()``/``to_json()`` call
shape, and it defaults to the atomic (``staged_sidecar``) path — the five
previously-non-atomic writers gain crash-safety as a deliberate,
called-out side effect of the consolidation rather than a silent
behavior change.
"""

from __future__ import annotations

import hashlib
import json
import logging
import shutil
from contextlib import contextmanager
from pathlib import Path
from typing import (
    TYPE_CHECKING,
    Any,
    Dict,
    Iterable,
    Iterator,
    List,
    Optional,
    Sequence,
)

if TYPE_CHECKING:  # pragma: no cover - typing only, no runtime import
    from anvil.lib.review_schema import Review

__all__ = [
    "STAGING_SUFFIX",
    "SidecarIncompleteError",
    "SidecarCopyVerificationError",
    "staged_sidecar",
    "stage_enter",
    "commit_staged",
    "stage_replace",
    "commit_replace",
    "abort_replace",
    "recover_interrupted_replace",
    "copy_bytes",
    "staging_path_for",
    "backup_path_for",
    "cleanup_one_staging",
    "cleanup_stale_staging",
    "write_critic_review_dir",
    "main",
]


# ---------------------------------------------------------------------------
# Public constants
# ---------------------------------------------------------------------------


#: The suffix appended to a final-dir name to derive its staging-dir name.
#: Combined with the leading-dot prefix in :func:`staging_path_for`, the full
#: shape is ``.<final-name>.tmp/`` (e.g., ``.acme-seed.3.review.tmp/``).
STAGING_SUFFIX = ".tmp"


#: The dotted-name prefix.
_STAGING_PREFIX = "."


_log = logging.getLogger(__name__)


# ---------------------------------------------------------------------------
# Exceptions
# ---------------------------------------------------------------------------


class SidecarIncompleteError(RuntimeError):
    """The staged sidecar dir is missing one or more declared
    ``required_files`` at context exit. The staging directory is left in
    place so a forensic check can inspect what WAS produced.
    """


class SidecarCopyVerificationError(RuntimeError):
    """:func:`copy_bytes` completed a copy but post-copy byte-identity
    verification found the destination does not match the source. The
    staged copy is left in place (unrenamed) for forensic inspection; the
    caller must not treat the destination as landed.
    """


# ---------------------------------------------------------------------------
# Path helpers
# ---------------------------------------------------------------------------


def staging_path_for(final_dir: Path) -> Path:
    """Return the staging-dir path that corresponds to ``final_dir``.

    Naming shape: a leading-dot sibling of ``final_dir`` with the
    :data:`STAGING_SUFFIX` appended. For example::

        final_dir          = Path("output/acme-seed.3.review")
        staging_path_for() = Path("output/.acme-seed.3.review.tmp")

    The staging dir lives in the same parent as the final dir — required
    for ``rename(2)`` atomicity (POSIX guarantees atomic rename only when
    source and dest are on the same filesystem; same-parent is the
    natural way to satisfy that constraint).

    Parameters
    ----------
    final_dir:
        The intended final path for the sidecar directory.

    Returns
    -------
    The staging path. Does not touch the filesystem.
    """
    final_dir = Path(final_dir)
    parent = final_dir.parent
    staging_name = f"{_STAGING_PREFIX}{final_dir.name}{STAGING_SUFFIX}"
    return parent / staging_name


#: The suffix appended to a final-dir name to derive its move-aside backup
#: name, used by :func:`stage_replace` / :func:`commit_replace` /
#: :func:`abort_replace` (issue #881).
BACKUP_SUFFIX = ".bak"


def backup_path_for(final_dir: Path) -> Path:
    """Return the move-aside backup path :func:`stage_replace` uses.

    Naming shape mirrors :func:`staging_path_for`: a leading-dot sibling of
    ``final_dir`` with :data:`BACKUP_SUFFIX` appended, e.g.::

        final_dir         = Path("output/acme-seed.3.review")
        backup_path_for() = Path("output/.acme-seed.3.review.bak")

    Lives in the same parent as ``final_dir`` so the move-aside rename is a
    same-filesystem, atomic ``Path.rename``. Does not touch the filesystem.
    """
    final_dir = Path(final_dir)
    parent = final_dir.parent
    backup_name = f"{_STAGING_PREFIX}{final_dir.name}{BACKUP_SUFFIX}"
    return parent / backup_name


def _refuse_on_orphaned_backup(caller: str, final_dir: Path) -> None:
    """Raise :class:`FileExistsError` if an interrupted :func:`stage_replace`
    left its move-aside backup on disk for ``final_dir`` (issue #881).

    Guards every fresh-staging entry point (:func:`stage_enter`,
    :func:`commit_staged`, and — by default — :func:`staged_sidecar`, issue
    #885) against the cross-session crash path: when a replace dies between
    :func:`stage_replace` and :func:`commit_replace`, ``final_dir`` is absent
    (it was renamed to the backup), so every fresh-staging entry check passes
    and the next run happily commits a brand-new sidecar into the gap —
    permanently stranding the ONLY copy of the pre-existing content inside a
    hidden ``.bak`` sibling that no sweep recognizes.

    Refusing here makes that silent loss impossible even when the caller
    skips the documented :func:`recover_interrupted_replace` entry step.
    """
    backup = backup_path_for(final_dir)
    if not backup.exists() or not backup.is_dir():
        return
    raise FileExistsError(
        f"{caller}: refusing to stage a fresh sidecar for {final_dir!s}; an "
        f"interrupted stage_replace() left its move-aside backup at "
        f"{backup!s}, which currently holds the only copy of that "
        f"directory's pre-existing content. Committing a fresh sidecar here "
        f"would strand it. Run recover_interrupted_replace({final_dir!s}) "
        f"(CLI: `python -m anvil.lib.sidecar recover-replace {final_dir!s}`) "
        f"first, then re-run."
    )


def _file_content_key(path: Path) -> tuple:
    """Return a ``(size, sha256-hexdigest)`` content fingerprint for ``path``.

    Two files are provably identical iff their fingerprints match. Size is
    included (cheap, and gives a readable early-exit signal in a future
    diff) even though the hash alone already implies it.
    """
    data = path.read_bytes()
    return (len(data), hashlib.sha256(data).hexdigest())


def _unpreserved_backup_entries(backup: Path, final_dir: Path) -> List[str]:
    """Return the ``backup``-relative file paths NOT provably preserved in
    ``final_dir`` — the content-aware redundancy predicate (issue #885)
    shared by :func:`recover_interrupted_replace` and :func:`stage_replace`.

    Recurses into subdirectories (unlike the earlier top-level-name-only
    check) and requires byte-identical content — same size AND same content
    hash — at the same relative path, not merely that a same-named entry
    exists. An empty list means every file ``backup`` holds is proven to
    have a byte-identical twin in ``final_dir``, i.e. ``backup`` is safe to
    discard without losing anything undocumented elsewhere.

    A backup with no files at all (or that does not exist) trivially returns
    an empty list — there is nothing in it to lose.
    """
    if not backup.exists():
        return []
    unpreserved: List[str] = []
    for path in sorted(backup.rglob("*")):
        if not path.is_file():
            continue
        rel = path.relative_to(backup)
        counterpart = final_dir / rel
        if not counterpart.is_file():
            unpreserved.append(str(rel))
            continue
        if _file_content_key(path) != _file_content_key(counterpart):
            unpreserved.append(str(rel))
    return unpreserved


# ---------------------------------------------------------------------------
# Binary/bulk-asset copy primitive (issue #1017)
# ---------------------------------------------------------------------------


def _content_manifest(path: Path) -> dict:
    """Return a ``{relative-posix-path: (size, sha256)}`` content manifest
    for ``path`` — a single ``{"": key}`` entry when ``path`` is a file, or
    one entry per contained file (keyed by its path relative to ``path``,
    POSIX-separated for platform-stable comparison) when ``path`` is a
    directory. Shared verification helper for :func:`copy_bytes`.
    """
    if path.is_dir():
        return {
            str(p.relative_to(path).as_posix()): _file_content_key(p)
            for p in sorted(path.rglob("*"))
            if p.is_file()
        }
    return {"": _file_content_key(path)}


def copy_bytes(
    src: Path,
    dst: Path,
    *,
    overwrite: bool = False,
    verify: bool = True,
    parents: bool = True,
) -> Path:
    """Byte-safe copy of ``src`` to ``dst`` (issue #1017).

    The binary/bulk-asset analog of the ``stage``/``commit`` CLI shim: a
    manual/agent session whose editing tool is text-only (and whose Bash
    channel may be blocked by a consumer's worktree-isolation hook) has no
    other sanctioned way to place bytes it did not itself compose — a
    prior version's unchanged ``figures/*.pdf``, a compiled ``main.pdf``,
    or a raw compile-log capture destined for a sidecar's
    ``compile-log.txt``.

    Supports both a single file and a directory tree (recursively). The
    copy is staged into a same-parent leading-dot sibling
    (:func:`staging_path_for`) and landed with a single atomic
    ``Path.rename`` — the same stage-then-rename shape :func:`staged_sidecar`
    uses for critic directories — so a crash mid-copy of a large or
    multi-file payload never leaves ``dst`` partially written.

    Parameters
    ----------
    src:
        The source path (file or directory). Must exist.
    dst:
        The destination path. Its parent is created if missing (when
        ``parents`` is ``True``, the default).
    overwrite:
        When ``False`` (default), refuse (:class:`FileExistsError`) if
        ``dst`` already exists — the same immutability-first default every
        other write primitive in this module uses. When ``True``, the
        existing ``dst`` is removed immediately before the staged copy is
        renamed into place (CLI: ``--force``).
    verify:
        When ``True`` (default), after staging the copy, compare a
        ``(size, sha256)`` content manifest (:func:`_content_manifest`) of
        the staged copy against ``src``. Any mismatch or missing file
        raises :class:`SidecarCopyVerificationError` and leaves the
        staged (unrenamed) copy in place for forensic inspection — ``dst``
        is never landed with unverified content. This should be
        unreachable in practice (the underlying copy is either exact or
        raises), but exists as defense-in-depth for the "byte-identity
        verified" contract rather than trusting the copy silently.
    parents:
        Forwarded to ``dst.parent``'s :meth:`pathlib.Path.mkdir`.

    Returns
    -------
    ``dst`` on success.

    Raises
    ------
    FileNotFoundError
        If ``src`` does not exist.
    FileExistsError
        If ``dst`` already exists and ``overwrite`` is ``False``.
    SidecarCopyVerificationError
        If ``verify`` is ``True`` and the post-copy manifest does not match
        ``src``.
    """
    src = Path(src)
    dst = Path(dst)

    if not src.exists():
        raise FileNotFoundError(
            f"copy_bytes: source {src!s} does not exist; nothing to copy."
        )
    if dst.exists() and not overwrite:
        raise FileExistsError(
            f"copy_bytes: refusing to overwrite existing destination "
            f"{dst!s}. Pass overwrite=True (CLI: `--force`) if replacing "
            f"it is intended."
        )

    dst.parent.mkdir(parents=parents, exist_ok=True)

    # Stage into a same-parent leading-dot sibling of dst, then land with a
    # single atomic rename — mirrors staged_sidecar's contract so a crash
    # mid-copy (e.g. a multi-file figures/ tree) never leaves dst partially
    # written.
    staging = staging_path_for(dst)
    if staging.exists():
        if staging.is_dir():
            shutil.rmtree(staging)
        else:
            staging.unlink()

    if src.is_dir():
        shutil.copytree(src, staging)
    else:
        shutil.copy2(src, staging)

    if verify:
        src_manifest = _content_manifest(src)
        staged_manifest = _content_manifest(staging)
        if src_manifest != staged_manifest:
            missing = sorted(set(src_manifest) - set(staged_manifest))
            mismatched = sorted(
                rel
                for rel in set(src_manifest) & set(staged_manifest)
                if src_manifest[rel] != staged_manifest[rel]
            )
            raise SidecarCopyVerificationError(
                f"copy_bytes: post-copy verification of {dst!s} (staged at "
                f"{staging!s}) did not match source {src!s}. "
                f"missing={missing or 'none'} mismatched={mismatched or 'none'}. "
                f"The staged copy is left in place, unrenamed, for forensic "
                f"inspection."
            )

    if dst.exists():
        # Only reachable when overwrite=True (the exists-check above already
        # refused otherwise).
        if dst.is_dir():
            shutil.rmtree(dst)
        else:
            dst.unlink()

    staging.rename(dst)
    return dst


# ---------------------------------------------------------------------------
# Staged sidecar context manager
# ---------------------------------------------------------------------------


@contextmanager
def staged_sidecar(
    final_dir: Path,
    required_files: Sequence[str],
    *,
    parents: bool = True,
    allow_orphaned_backup: bool = False,
) -> Iterator[Path]:
    """Stage a critic sidecar directory; rename atomically on completion.

    Parameters
    ----------
    final_dir:
        The intended final path for the critic sibling directory, e.g.
        ``Path("output/acme-seed.3.review")``. Must NOT already exist —
        we refuse to overwrite to preserve the immutability guarantee
        documented in ``anvil/lib/snippets/version_layout.md``.
    required_files:
        The list of file names (NOT paths — just basenames relative to
        the staging dir) that MUST exist in the staging dir at clean
        context exit. If any is missing, the rename is skipped, the
        staging dir is left in place, and :class:`SidecarIncompleteError`
        is raised. Subdirectories under the staging dir (e.g.,
        ``perspective/``) are not validated by this manifest; the
        manifest is a flat top-level-file check.
    parents:
        Forwarded to :meth:`pathlib.Path.mkdir`. When ``True`` (default)
        any missing intermediate directories are created.
    allow_orphaned_backup:
        When ``False`` (default), refuses (:class:`FileExistsError`) if an
        orphaned :func:`stage_replace` backup is on disk for ``final_dir`` —
        the same :func:`_refuse_on_orphaned_backup` guard :func:`stage_enter`
        and :func:`commit_staged` carry (issue #881/#885). Set ``True`` only
        when the caller manages its OWN same-named ``.bak`` move-aside
        immediately around this call and is a live Python driver whose
        ``except`` handler is guaranteed to run (e.g.
        ``anvil/skills/project-migrate/lib/adopt_review.py``'s
        ``_convert_one`` / ``_rescore_one``) — passing ``True`` from any
        other caller reopens the cross-session stranding window this guard
        exists to close.

    Yields
    ------
    :class:`pathlib.Path`
        The staging directory. Write all files for the sidecar into this
        directory; do NOT write into ``final_dir`` directly.

    Raises
    ------
    FileExistsError
        If ``final_dir`` already exists on entry (we do not overwrite), or
        if ``allow_orphaned_backup`` is ``False`` and an orphaned
        :func:`stage_replace` backup is on disk for ``final_dir``.
    SidecarIncompleteError
        If clean context exit finds any name in ``required_files``
        missing from the staging dir. The staging dir is left in place
        for forensic inspection; the next per-critic invocation's
        :func:`cleanup_one_staging` call (or an operator-time
        :func:`cleanup_stale_staging` sweep) will remove it.
    Exception
        Anything raised in the context body propagates unchanged. The
        staging dir is left in place (no rename); the exception
        propagates after the staging dir is preserved.

    Examples
    --------
    Happy path::

        with staged_sidecar(
            Path("output/acme-seed.3.review"),
            required_files=["verdict.md", "scoring.md", "_progress.json"],
        ) as staging:
            (staging / "verdict.md").write_text("...")
            (staging / "scoring.md").write_text("...")
            (staging / "_progress.json").write_text("{}")
        # On block exit: staging dir is renamed to acme-seed.3.review/.

    Exception in body (e.g., a reviewer LLM error mid-write)::

        try:
            with staged_sidecar(final, required_files=[...]) as staging:
                (staging / "verdict.md").write_text("...")
                raise RuntimeError("LLM tool error")
        except RuntimeError:
            ...
        # The staging dir .<name>.tmp/ exists with verdict.md only; the
        # final dir was never created. The next entry-step
        # cleanup_one_staging(final_dir) call sweeps the .tmp/.
    """
    final_dir = Path(final_dir)
    staging = staging_path_for(final_dir)

    if final_dir.exists():
        raise FileExistsError(
            f"staged_sidecar: refusing to stage into {staging.name!r}; "
            f"final target {final_dir!s} already exists. "
            f"Caller is responsible for the resume/idempotency check "
            f"before invoking staged_sidecar."
        )

    # (issue #885) The orphaned-backup guard that stage_enter and
    # commit_staged carry applies here too by default. A driverless
    # (markdown/CLI) session skipping the entry sweep is the load-bearing
    # crash-exposed case, but a live Python driver can hit the same gap if a
    # PRIOR run's stage_replace()/commit_replace() cycle died before this
    # process started — nothing about being Python-driven rules that out.
    # allow_orphaned_backup=True is the narrow, explicit opt-out for callers
    # that manage their own same-named `.bak` move-aside immediately around
    # this call (adopt_review.py's _convert_one / _rescore_one).
    if not allow_orphaned_backup:
        _refuse_on_orphaned_backup("staged_sidecar", final_dir)

    # If a previous interrupt left a staging dir with the same name in
    # place, wipe it before we re-enter — otherwise our mkdir would fail
    # and we'd be unable to make forward progress. This is the only path
    # where staged_sidecar itself deletes; cleanup_one_staging is the
    # per-critic entry-step sweep and cleanup_stale_staging is the
    # operator-facing portfolio-wide sweep.
    if staging.exists():
        _log.info(
            "staged_sidecar: removing prior staging dir %s (interrupted "
            "previous attempt)",
            staging,
        )
        shutil.rmtree(staging)

    staging.mkdir(parents=parents, exist_ok=False)

    try:
        yield staging
    except BaseException:
        # Body errored. Leave the staging dir in place for forensics +
        # next-startup GC. Do NOT rename.
        _log.info(
            "staged_sidecar: exception in body; leaving staging dir %s "
            "for next-invocation cleanup_one_staging() sweep",
            staging,
        )
        raise

    # Clean body exit; verify the required-files manifest.
    missing = _missing_required_files(staging, required_files)
    if missing:
        _log.warning(
            "staged_sidecar: missing required files in %s: %s "
            "(staging dir left in place for forensics)",
            staging,
            ", ".join(missing),
        )
        raise SidecarIncompleteError(
            f"staged_sidecar: sidecar at {staging!s} is missing required "
            f"files: {', '.join(missing)}. The staging directory is left "
            f"in place; rename to {final_dir.name!r} has been skipped."
        )

    # Atomic rename: POSIX guarantees atomicity for same-filesystem
    # directory rename. By construction (staging_path_for places staging
    # in the same parent as final_dir) we satisfy that constraint.
    staging.rename(final_dir)


def _missing_required_files(
    staging: Path, required_files: Iterable[str]
) -> List[str]:
    """Return the subset of ``required_files`` that do not exist in
    ``staging``. Order-preserving.
    """
    missing: List[str] = []
    for name in required_files:
        if not (staging / name).exists():
            missing.append(name)
    return missing


# ---------------------------------------------------------------------------
# Per-critic entry-step sweep (parallel-safe)
# ---------------------------------------------------------------------------


def cleanup_one_staging(final_dir: Path) -> bool:
    """Remove only the staging dir corresponding to ``final_dir``.

    Computes ``staging_path_for(final_dir)`` and removes that single
    directory if (a) it exists, (b) it is a directory, and (c) its name
    matches the leading-dot + :data:`STAGING_SUFFIX` shape this module
    owns. Returns ``True`` iff a staging dir was actually removed.

    This is the **per-critic entry-step sweep** — the load-bearing
    surface for the critic-writing commands across all 11 artifact-class
    skills. It is
    **parallel-safe**: when two critics fan out concurrently under the
    same portfolio root with distinct ``final_dir`` values, each one
    targets only its own staging path and never disturbs the sibling's
    in-flight staging dir (issue #376).

    Idempotent: a second call on the same ``final_dir`` returns
    ``False`` because the first call already removed (or found absent)
    the target.

    Safe when:

    - The staging path does not exist (returns ``False``).
    - The parent directory does not exist (returns ``False``).
    - The path exists but is a file, not a directory (returns ``False``
      — this module never deletes files).
    - The staging name does not match the leading-dot + ``.tmp`` shape
      (returns ``False`` — defensive against external callers passing a
      ``final_dir`` whose derived staging name happens to be unusual).

    Logs at INFO level the removed path (one log line per removal).

    Parameters
    ----------
    final_dir:
        The intended final path for the critic sibling directory. The
        staging path is computed via :func:`staging_path_for`. The
        ``final_dir`` itself is NOT touched by this function.

    Returns
    -------
    ``True`` if a staging directory was removed, ``False`` otherwise.

    Examples
    --------
    Happy path — a leftover staging dir from a prior crash is swept::

        cleanup_one_staging(Path("output/thread.4.review"))
        # If output/.thread.4.review.tmp/ exists, it is removed.

    No-op — nothing to sweep::

        cleanup_one_staging(Path("output/thread.4.review"))
        # If output/.thread.4.review.tmp/ does not exist, returns False.

    Parallel-safety guarantee::

        # Critic A and Critic B fan out concurrently:
        cleanup_one_staging(Path("p/thread.4.perspective"))  # touches A only
        cleanup_one_staging(Path("p/thread.4.hyperlinks"))   # touches B only
        # Each call's scope is bounded to a single staging path.
    """
    final_dir = Path(final_dir)
    staging = staging_path_for(final_dir)

    if not staging.exists():
        return False
    if not staging.is_dir():
        return False
    if not _is_staging_dirname(staging.name):
        return False

    shutil.rmtree(staging)
    _log.info(
        "cleanup_one_staging: removed stale staging dir %s",
        staging,
    )
    return True


# ---------------------------------------------------------------------------
# Operator-facing portfolio-wide sweep
# ---------------------------------------------------------------------------


def cleanup_stale_staging(parent: Path) -> List[Path]:
    """Remove any leading-dot ``.tmp/`` staging dirs under ``parent``.

    Walks ``parent``'s direct children (NOT recursive — staging dirs are
    always siblings of the intended final dir, which is in the portfolio
    root) and removes every directory whose name matches the
    leading-dot + :data:`STAGING_SUFFIX` shape this module owns. Returns
    the list of removed paths (post-rmtree absolute paths) for the
    caller to log or surface in a startup message.

    Idempotent: a second call returns ``[]`` because the first call
    already deleted the matches. Safe to call on a directory that does
    not exist (returns ``[]``).

    Files (non-directories) and directories that don't match the shape
    (e.g., a hidden ``.git/`` or a non-tmp dot-dir like
    ``.archive-2026/``) are left alone.

    Logs at INFO level the count and names of removed dirs (one log line
    per call).

    **Operator-facing maintenance surface only.** This function sweeps
    *every* leading-dot ``.tmp/`` staging dir under ``parent`` — including
    staging dirs that belong to **other critics currently writing**.
    Calling this from a per-critic entry step in a parallel fan-out
    workflow (e.g. memo-perspective + memo-hyperlinks running
    concurrently) causes the second-starting critic to ``rmtree`` the
    first-starting critic's in-flight staging dir mid-write, producing
    silently-truncated final sidecars (issue #376). Per-critic entry
    steps MUST use :func:`cleanup_one_staging` instead; this function is
    reserved for operator-time portfolio-wide orphan cleanup.

    Parameters
    ----------
    parent:
        The directory to sweep. Typically the portfolio root (the
        directory that contains ``<thread>.{N}/`` version dirs and their
        critic siblings).

    Returns
    -------
    The list of removed staging-dir paths. Empty when nothing matched.
    """
    parent = Path(parent)
    if not parent.exists() or not parent.is_dir():
        return []

    removed: List[Path] = []
    for child in sorted(parent.iterdir()):
        if not child.is_dir():
            continue
        if not _is_staging_dirname(child.name):
            continue
        shutil.rmtree(child)
        removed.append(child)

    if removed:
        _log.info(
            "cleanup_stale_staging: removed %d stale .tmp staging dir(s) "
            "from %s: %s",
            len(removed),
            parent,
            ", ".join(p.name for p in removed),
        )
    return removed


def _is_staging_dirname(name: str) -> bool:
    """Return True iff ``name`` matches the leading-dot + ``.tmp`` shape
    this module owns. Conservative: we require BOTH the leading dot AND
    the trailing ``.tmp`` so we never delete an unrelated dotfile (e.g.,
    ``.git``, ``.archive-2026``).
    """
    if not name.startswith(_STAGING_PREFIX):
        return False
    if not name.endswith(STAGING_SUFFIX):
        return False
    # Require something between the dot and the .tmp — a name like
    # ".tmp" alone (no body) is suspicious and we leave it alone.
    inner = name[len(_STAGING_PREFIX) : -len(STAGING_SUFFIX)]
    return bool(inner)


def _is_backup_dirname(name: str) -> bool:
    """Return True iff ``name`` matches the leading-dot + :data:`BACKUP_SUFFIX`
    shape :func:`stage_replace` owns (issue #881). Same conservative rule as
    :func:`_is_staging_dirname`: both the leading dot AND the trailing
    ``.bak``, with a non-empty body between them, so an unrelated dotfile is
    never mistaken for a move-aside backup.
    """
    if not name.startswith(_STAGING_PREFIX):
        return False
    if not name.endswith(BACKUP_SUFFIX):
        return False
    inner = name[len(_STAGING_PREFIX) : -len(BACKUP_SUFFIX)]
    return bool(inner)


# ---------------------------------------------------------------------------
# Split stage/commit surface for CLI-driven (non-Python-driver) sessions
# ---------------------------------------------------------------------------
#
# The :func:`staged_sidecar` context manager assumes an orchestrating Python
# process that holds the ``with`` block open across all file writes. A manual
# or agent review session with no such driver can only shell out to discrete
# ``python -m anvil.lib.sidecar`` subcommands and write files with its own
# editing tool between invocations. The two functions below decompose the
# context manager's enter-side (``stage_enter``) and exit-side
# (``commit_staged``) so the CLI can offer the same atomicity guarantee — the
# manifest check + single ``Path.rename`` — across two process boundaries.
# They share every helper with :func:`staged_sidecar` (``staging_path_for``,
# ``_missing_required_files``, the ``FileExistsError`` refuse-to-overwrite
# check, ``SidecarIncompleteError``), so there is no second copy of the
# contract to drift.


def stage_enter(final_dir: Path, *, parents: bool = True) -> Path:
    """Create (and return) the staging dir for ``final_dir`` — the
    enter-side of :func:`staged_sidecar`, exposed for the CLI.

    Mirrors the ``__enter__`` half of :func:`staged_sidecar`: refuses if
    ``final_dir`` already exists (:class:`FileExistsError`), wipes any
    leftover staging dir from a prior interrupt, then ``mkdir``\\ s the
    staging path. Returns the staging :class:`pathlib.Path` for the
    caller to write files into.

    Unlike :func:`staged_sidecar`, this does NOT verify a required-files
    manifest or rename — that is :func:`commit_staged`'s job, invoked in a
    later process once the caller has finished writing files.

    Raises
    ------
    FileExistsError
        If ``final_dir`` already exists. (We do not overwrite — same
        immutability guarantee as :func:`staged_sidecar`.)
    """
    final_dir = Path(final_dir)
    staging = staging_path_for(final_dir)

    if final_dir.exists():
        raise FileExistsError(
            f"stage_enter: refusing to stage into {staging.name!r}; "
            f"final target {final_dir!s} already exists. "
            f"Caller is responsible for the resume/idempotency check "
            f"before invoking stage_enter."
        )

    # An interrupted stage_replace() leaves final_dir absent and its content
    # in a .bak sibling — the check above cannot see it (issue #881).
    _refuse_on_orphaned_backup("stage_enter", final_dir)

    if staging.exists():
        _log.info(
            "stage_enter: removing prior staging dir %s (interrupted "
            "previous attempt)",
            staging,
        )
        shutil.rmtree(staging)

    staging.mkdir(parents=parents, exist_ok=False)
    return staging


def commit_staged(final_dir: Path, required_files: Sequence[str]) -> Path:
    """Verify the manifest and atomically rename staging → ``final_dir``.

    The exit-side of :func:`staged_sidecar`, exposed for the CLI. Assumes
    a prior :func:`stage_enter` (or a manual ``mkdir`` of the staging
    path) already created ``staging_path_for(final_dir)`` and the caller
    has written files into it. Verifies every name in ``required_files``
    exists, then performs the single ``Path.rename`` to ``final_dir``.

    Returns the ``final_dir`` path on success.

    Raises
    ------
    FileNotFoundError
        If the staging dir does not exist (nothing to commit).
    FileExistsError
        If ``final_dir`` already exists — atomic rename only works onto a
        non-existent target (same guard as :func:`staged_sidecar`).
    SidecarIncompleteError
        If any name in ``required_files`` is missing from the staging
        dir. The staging dir is left in place for forensic inspection;
        the rename is skipped — identical to :func:`staged_sidecar`'s
        clean-exit manifest check.
    """
    final_dir = Path(final_dir)
    staging = staging_path_for(final_dir)

    if not staging.exists():
        raise FileNotFoundError(
            f"commit_staged: staging dir {staging!s} does not exist. "
            f"Run `stage` first (or the writer never created it)."
        )
    if final_dir.exists():
        raise FileExistsError(
            f"commit_staged: refusing to commit {staging.name!r}; final "
            f"target {final_dir!s} already exists. Atomic rename only "
            f"works onto a non-existent target."
        )

    # A backup on disk means this staging dir belongs to an in-flight (or
    # interrupted) stage_replace(); committing it via the fresh-staging path
    # would drop the preserved content on the floor. Use commit_replace()
    # (which swaps AND drops the backup) or recover first (issue #881).
    _refuse_on_orphaned_backup("commit_staged", final_dir)

    missing = _missing_required_files(staging, required_files)
    if missing:
        _log.warning(
            "commit_staged: missing required files in %s: %s "
            "(staging dir left in place for forensics)",
            staging,
            ", ".join(missing),
        )
        raise SidecarIncompleteError(
            f"commit_staged: sidecar at {staging!s} is missing required "
            f"files: {', '.join(missing)}. The staging directory is left "
            f"in place; rename to {final_dir.name!r} has been skipped."
        )

    staging.rename(final_dir)
    return final_dir


# ---------------------------------------------------------------------------
# Migrated-corpus replace surface (issue #881)
# ---------------------------------------------------------------------------
#
# stage_enter / staged_sidecar refuse whenever final_dir exists — correct
# when final_dir already carries a RECOGNIZABLE anvil review (the #350
# immutability guard), wrong when final_dir is merely occupied by foreign,
# pre-anvil content a migration left behind (issue #881: a bare `review.md`
# sitting at the canonical `<thread>.{N}.review/` path). The three
# functions below generalize the move-aside/stage/swap recipe
# `anvil/skills/project-migrate/lib/adopt_review.py::_convert_one` already
# uses for the adjacent `--adopt-review` problem: move the occupied dir
# aside, stage a fresh dir seeded with everything that was already there
# (verbatim), let the caller add the new required files, then atomically
# swap the staging dir into place and drop the backup.


def stage_replace(final_dir: Path, *, parents: bool = True) -> Path:
    """Move ``final_dir`` aside and open a staging dir seeded with its
    existing contents — the entry-side of the #881 replace recipe.

    Unlike :func:`stage_enter` (which refuses when ``final_dir`` exists),
    this function is specifically FOR the case where ``final_dir`` exists
    but does not carry a recognizable anvil review — replacement, not
    fresh staging, is what's needed.

    Refuses in the two cases where replacement is the wrong call:

    - ``final_dir`` does not exist at all — use :func:`stage_enter`
      instead (nothing to move aside).
    - ``final_dir`` already carries a *recognizable* anvil review per
      :func:`anvil.lib.critics._has_recognizable_review` (canonical
      ``_review.json``, or a complete legacy file triple) — the #350
      immutability guard stays intact; a real review is never replaced.

    On success: ``final_dir`` is renamed to :func:`backup_path_for`, every
    file/dir it contained is copied byte-identical into a fresh staging
    dir at :func:`staging_path_for`, and the staging path is returned for
    the caller to add the new required files into (alongside the copied
    foreign content). The backup is NOT removed here — :func:`commit_replace`
    removes it on success; :func:`abort_replace` restores it on failure.

    Parameters
    ----------
    final_dir:
        The occupied-but-unrecognized sidecar path to replace.
    parents:
        Forwarded to the staging dir's :meth:`pathlib.Path.mkdir`.

    Raises
    ------
    FileNotFoundError
        If ``final_dir`` does not exist.
    FileExistsError
        If ``final_dir`` already carries a recognizable anvil review, or if
        an existing backup at :func:`backup_path_for` holds content not
        provably preserved in ``final_dir`` (issue #885 — see below).

    Notes
    -----
    If a backup is already on disk at :func:`backup_path_for` (e.g. left
    over from a prior ``stage_replace``/``commit_replace`` cycle that this
    caller believes finished, or that :func:`recover_interrupted_replace`
    already vetted), it is dropped before the move-aside rename ONLY when
    every file it holds is provably preserved — byte-identical, recursively
    — in the CURRENT ``final_dir`` (the shared
    :func:`_unpreserved_backup_entries` predicate, issue #885). An
    unconditional ``rmtree`` here would silently destroy a backup that
    :func:`recover_interrupted_replace` deliberately left on disk with a
    WARNING because it could not prove the content was preserved elsewhere.
    """
    final_dir = Path(final_dir)

    if not final_dir.exists():
        backup = backup_path_for(final_dir)
        if backup.exists():
            # NOT a genuinely absent final_dir: a previous stage_replace was
            # interrupted before commit_replace, so the directory's only copy
            # is sitting in the backup. Steering the operator at stage_enter()
            # here is exactly how the content gets stranded (issue #881).
            raise FileNotFoundError(
                f"stage_replace: {final_dir!s} does not exist, but an "
                f"interrupted stage_replace() left its contents at "
                f"{backup!s}. This is NOT a genuinely absent final_dir — do "
                f"NOT fall through to stage_enter(), which would commit a "
                f"fresh sidecar over the gap and strand that backup. Run "
                f"recover_interrupted_replace({final_dir!s}) (CLI: `python -m "
                f"anvil.lib.sidecar recover-replace {final_dir!s}`) to restore "
                f"it first, then re-run."
            )
        raise FileNotFoundError(
            f"stage_replace: {final_dir!s} does not exist; nothing to "
            f"replace. Use stage_enter() for a genuinely absent final_dir."
        )

    # Lazy import: avoids a module-load-time dependency cycle (critics.py
    # does not import sidecar.py today, but importing at call time keeps
    # this module importable even if that ever changes).
    from anvil.lib.critics import _has_recognizable_review

    if _has_recognizable_review(final_dir):
        raise FileExistsError(
            f"stage_replace: refusing to replace {final_dir!s}; it already "
            f"carries a recognizable anvil review (the #350 immutability "
            f"guard). If you intended the idempotent-skip path, use that "
            f"instead of stage_replace()."
        )

    backup = backup_path_for(final_dir)
    if backup.exists():
        # An existing backup here is either genuinely stale (a completed
        # prior cycle whose caller forgot to clean it up) or the ONLY copy
        # of content a prior cycle failed to land (issue #885). Only drop it
        # when every file it holds is provably preserved in the CURRENT
        # final_dir — the same content-aware predicate
        # recover_interrupted_replace uses for its symmetric check.
        unpreserved = _unpreserved_backup_entries(backup, final_dir)
        if unpreserved:
            raise FileExistsError(
                f"stage_replace: refusing to replace {final_dir!s}; an "
                f"existing backup at {backup!s} holds {len(unpreserved)} "
                f"file(s) not provably preserved in {final_dir!s}: "
                f"{', '.join(unpreserved)}. Deleting this backup here would "
                f"strand that content. Run "
                f"recover_interrupted_replace({final_dir!s}) (CLI: `python "
                f"-m anvil.lib.sidecar recover-replace {final_dir!s}`) "
                f"first, then re-run."
            )
        _log.info(
            "stage_replace: dropping provably-redundant existing backup %s "
            "before move-aside (every file already present in %s)",
            backup,
            final_dir,
        )
        shutil.rmtree(backup)
    final_dir.rename(backup)

    staging = staging_path_for(final_dir)
    if staging.exists():
        shutil.rmtree(staging)
    staging.mkdir(parents=parents, exist_ok=False)

    for entry in sorted(backup.iterdir()):
        if entry.is_dir():
            shutil.copytree(entry, staging / entry.name)
        else:
            shutil.copy2(entry, staging / entry.name)

    return staging


def commit_replace(final_dir: Path, required_files: Sequence[str]) -> Path:
    """Verify the manifest, atomically swap staging → ``final_dir``, then
    drop the move-aside backup — the exit-side of :func:`stage_replace`.

    Assumes a prior :func:`stage_replace` moved ``final_dir`` aside and
    created the staging dir (seeded with the original contents), and the
    caller has since written the new required files into it. Verifies
    every name in ``required_files`` exists in the staging dir, renames it
    to ``final_dir``, then removes the backup.

    Returns the ``final_dir`` path on success.

    Raises
    ------
    FileNotFoundError
        If the staging dir does not exist (nothing to commit).
    FileExistsError
        If ``final_dir`` already exists (should not happen after a clean
        :func:`stage_replace` — defensive, mirrors :func:`commit_staged`).
    SidecarIncompleteError
        If any name in ``required_files`` is missing from the staging
        dir. The staging dir AND the backup are both left in place for
        forensic inspection; call :func:`abort_replace` to restore the
        original content, or fix the gap and re-``commit_replace``.
    """
    final_dir = Path(final_dir)
    staging = staging_path_for(final_dir)

    if not staging.exists():
        raise FileNotFoundError(
            f"commit_replace: staging dir {staging!s} does not exist. "
            f"Run stage_replace() first."
        )
    if final_dir.exists():
        raise FileExistsError(
            f"commit_replace: refusing to commit {staging.name!r}; final "
            f"target {final_dir!s} already exists. Atomic rename only "
            f"works onto a non-existent target."
        )

    missing = _missing_required_files(staging, required_files)
    if missing:
        _log.warning(
            "commit_replace: missing required files in %s: %s "
            "(staging dir and backup left in place for forensics)",
            staging,
            ", ".join(missing),
        )
        raise SidecarIncompleteError(
            f"commit_replace: sidecar at {staging!s} is missing required "
            f"files: {', '.join(missing)}. The staging directory (and its "
            f"backup at {backup_path_for(final_dir)!s}) are left in place; "
            f"rename to {final_dir.name!r} has been skipped."
        )

    staging.rename(final_dir)

    backup = backup_path_for(final_dir)
    if backup.exists():
        shutil.rmtree(backup)

    return final_dir


def abort_replace(final_dir: Path) -> bool:
    """Undo an in-progress :func:`stage_replace`: restore the backup,
    discard any staging dir.

    Call this from the caller's exception handler when writing the new
    required files (between :func:`stage_replace` and
    :func:`commit_replace`) fails partway through. Removes any staging dir
    at :func:`staging_path_for`, then — only if ``final_dir`` is still
    absent (i.e. :func:`commit_replace` never ran) — renames the backup at
    :func:`backup_path_for` back to ``final_dir``, restoring the original
    content byte-identical.

    Idempotent and safe to call even when there is nothing to abort (no
    backup, no staging dir): returns ``False`` in that case.

    Returns
    -------
    ``True`` if the backup was restored, ``False`` otherwise (nothing to
    restore, or ``final_dir`` already exists so restoring would clobber
    it — the latter should not happen after a clean :func:`stage_replace`
    but is left untouched defensively).
    """
    final_dir = Path(final_dir)
    staging = staging_path_for(final_dir)
    backup = backup_path_for(final_dir)

    if staging.exists():
        shutil.rmtree(staging)

    if backup.exists() and not final_dir.exists():
        backup.rename(final_dir)
        _log.info(
            "abort_replace: restored %s from backup %s",
            final_dir,
            backup,
        )
        return True

    return False


def recover_interrupted_replace(final_dir: Path) -> bool:
    """Entry-step recovery sweep for the replace surface — the ``.bak``
    analog of :func:`cleanup_one_staging` (issue #881).

    :func:`abort_replace` closes the *same-session* failure: the caller's
    ``except`` handler runs and undoes the move-aside. It cannot close the
    **cross-session** failure, where the process that called
    :func:`stage_replace` dies before reaching any handler — the load-bearing
    shape for ``essay-review``, a markdown-driven command whose
    stage→commit window spans many discrete agent tool calls. In that state
    ``final_dir`` is absent and the only copy of its former content sits in
    a hidden ``.<name>.bak/`` that no sweep recognizes
    (:func:`cleanup_one_staging` and :func:`cleanup_stale_staging` both match
    the ``.tmp`` shape only).

    Call this at command entry, alongside ``cleanup_one_staging(final_dir)``,
    before the idempotency check. Three outcomes:

    - **No backup on disk** → no-op, returns ``False``. (The overwhelmingly
      common case; this is a cheap ``stat``.)
    - **Backup present, ``final_dir`` absent** → an interrupted replace.
      Delegates to :func:`abort_replace`: the partial staging dir is
      discarded and the backup is renamed back into place, restoring the
      pre-existing content byte-identical. Returns ``True``. The command then
      proceeds normally — its idempotency check sees the restored dir and
      re-enters the replace path from a clean state.
    - **Backup present, ``final_dir`` present** → :func:`commit_replace`'s
      rename landed but its backup-drop did not (a kill inside that
      sub-millisecond window), or something recreated ``final_dir``. The
      backup is dropped **only** when every FILE it holds is provably
      preserved in ``final_dir`` — same relative path, same size, same
      content hash, recursing into subdirectories (the content-aware
      :func:`_unpreserved_backup_entries` predicate, issue #885; a same-named
      file with different bytes is NOT redundant just because a name
      matches). Otherwise the backup is left untouched with a warning naming
      every unpreserved file, because deleting content that is not
      demonstrably preserved is never this function's call to make.

    Idempotent and safe to call repeatedly, on any path, whether or not the
    replace surface was ever used. Never touches ``final_dir``'s contents.

    Returns
    -------
    ``True`` if the on-disk state was changed (backup restored, or a
    redundant backup dropped), ``False`` otherwise.
    """
    final_dir = Path(final_dir)
    backup = backup_path_for(final_dir)

    if not backup.exists():
        return False
    if not backup.is_dir():
        return False
    if not _is_backup_dirname(backup.name):
        return False

    if not final_dir.exists():
        restored = abort_replace(final_dir)
        if restored:
            _log.info(
                "recover_interrupted_replace: recovered %s from an "
                "interrupted stage_replace (backup %s restored)",
                final_dir,
                backup,
            )
        return restored

    # final_dir exists AND a backup exists. Drop the backup only if it is
    # provably redundant — every file it holds is byte-identical to its
    # counterpart in final_dir (content-aware + recursive, issue #885).
    unpreserved = _unpreserved_backup_entries(backup, final_dir)
    if unpreserved:
        _log.warning(
            "recover_interrupted_replace: leaving backup %s in place — it "
            "holds %d file(s) not provably preserved (byte-identical) in "
            "%s: %s. Resolve by hand; this function never deletes content "
            "it cannot prove is preserved.",
            backup,
            len(unpreserved),
            final_dir,
            ", ".join(unpreserved),
        )
        return False

    shutil.rmtree(backup)
    _log.info(
        "recover_interrupted_replace: dropped redundant backup %s (every "
        "file is byte-identical to its counterpart in %s)",
        backup,
        final_dir,
    )
    return True


# ---------------------------------------------------------------------------
# Critic-sidecar writer consolidation (issue #1086)
# ---------------------------------------------------------------------------


def write_critic_review_dir(
    version_dir: Path,
    suffix: str,
    review: "Review",
    *,
    findings_json: Optional[Dict[str, Any]] = None,
    atomic: bool = True,
    regenerate: bool = True,
) -> Path:
    """Write a critic's ``<version_dir>.<suffix>/_review.json`` (+ optional
    ``_findings.json``) sidecar — the single canonical implementation the
    seven pre-#1086 ``write_review_dir()``/``_write_review_dir()`` copies
    now share (``pending_marker``, ``numeric_consistency``,
    ``hyperlink_resolver``, ``figure_content``, ``image_accessibility``,
    ``citation_coverage``, ``claim_figure_grounding``).

    Every one of the seven did the same three things in the same order:
    compute the sibling dir name, build a typed ``Review`` via that
    critic's own ``to_review(...)`` call (whose keyword arguments differ
    slightly per critic — e.g. ``figure_content`` passes ``model=``,
    ``numeric_consistency`` passes ``blocking=``), then write it (and, for
    three of the seven, a ``_findings.json`` companion built from that
    critic's own ``result.to_json()``) into the sibling dir. This function
    takes the already-built ``review`` (and, optionally, an already-built
    ``findings_json`` payload) rather than a critic-specific ``result``
    object, so it stays decoupled from each critic's
    ``to_review()``/``to_json()`` call shape — every call site keeps its
    own ``to_review(...)``/``to_json()`` call locally and passes the
    outputs in here.

    Parameters
    ----------
    version_dir:
        The version directory being reviewed, e.g.
        ``Path("output/acme-seed.1")``. The sibling dir is computed as
        ``version_dir.parent / f"{version_dir.name}.{suffix}"`` — the
        same ``<version_dir>.<tag>/`` shape
        :func:`anvil.lib.critics.discover_critics` recognizes without
        code changes.
    suffix:
        The critic's sibling-dir tag, e.g. ``"hyperlinks"``,
        ``"citations"``, ``"claim-figure-grounding"`` — matches each
        critic's own ``*_SUFFIX`` / ``CRITIC_ID`` constant.
    review:
        An already-built :class:`anvil.lib.review_schema.Review` instance
        — or any duck-typed object exposing ``model_dump(mode="json")``,
        so this module does not need to import ``review_schema`` (and
        transitively ``pydantic``) at runtime. Dumped via
        ``json.dumps(review.model_dump(mode="json"), indent=2) + "\\n"``
        — byte-identical to every pre-#1086 copy's own dump: five of the
        seven already used exactly this call; the other two
        (``citation_coverage``, ``claim_figure_grounding``) used
        ``review.model_dump_json(indent=2)`` instead, which is
        byte-identical to ``json.dumps(model_dump(mode="json"), ...)``
        for the ASCII-only content this schema ever carries (verified by
        round-trip diff in the #1086 PR body — pydantic's own JSON
        encoder and stdlib ``json.dumps`` agree on key order, separators,
        and escaping for this payload shape).
    findings_json:
        Optional structured findings payload (a plain ``dict``,
        typically the critic's own ``result.to_json()``). When given, an
        additional ``_findings.json`` companion is written alongside
        ``_review.json`` — the three-of-seven companion-file convention
        (``image_accessibility``, ``citation_coverage``,
        ``claim_figure_grounding``). When omitted (the default), only
        ``_review.json`` is written — the four-of-seven single-file
        convention (``pending_marker``, ``numeric_consistency``,
        ``hyperlink_resolver``, ``figure_content``).
    atomic:
        When ``True`` (the default), stages every file into a leading-dot
        sibling via :func:`staged_sidecar` and lands the complete set with
        a single atomic ``Path.rename`` (issue #350) — crash-safe: a
        mid-write interrupt never leaves a partially-written sidecar at
        the final name. Two of the seven pre-#1086 copies
        (``pending_marker``, ``numeric_consistency``) already used this
        path; the other five (``hyperlink_resolver``, ``figure_content``,
        ``image_accessibility``, ``citation_coverage``,
        ``claim_figure_grounding``) gain crash-safety as a deliberate,
        called-out side effect of the #1086 consolidation — every
        consuming command's own markdown doc already mandates
        ``staged_sidecar`` for these critics, so this closes a doc/code
        drift, not just a dedup. ``atomic=False`` reproduces the old
        plain ``mkdir(parents=True, exist_ok=...)`` + ``write_text``
        shape; no call site in this repo passes it as of #1086.
    regenerate:
        When ``True`` (the default), an existing sibling dir from a prior
        run of THIS critic on THIS version is replaced by the fresh
        write — the deterministic-critic-rerun carve-out to the
        sidecar-immutability convention that ``pending_marker`` and
        ``numeric_consistency`` already documented pre-#1086 (a later
        deterministic pass supersedes an earlier one; the five
        previously-non-atomic writers had the same effective behavior via
        their ``exist_ok=True`` overwrite-in-place). Under
        ``atomic=True`` this also sweeps any leftover staging dir from a
        prior interrupted run (:func:`cleanup_one_staging`, issue #376)
        before staging fresh. When ``False``, a pre-existing sibling dir
        is left alone under ``atomic=False`` (mirroring
        ``exist_ok=False``) or raises :class:`FileExistsError` under
        ``atomic=True`` (:func:`staged_sidecar`'s own immutability
        default) — one-shot semantics for a caller that wants a rerun to
        be a hard error rather than a silent overwrite.

    Returns
    -------
    The path to the written ``_review.json`` (NOT the sibling dir itself)
    — matches every pre-#1086 copy's return contract.
    """
    version_dir = Path(version_dir)
    final = version_dir.parent / f"{version_dir.name}.{suffix}"

    files: Dict[str, str] = {
        "_review.json": json.dumps(review.model_dump(mode="json"), indent=2)
        + "\n"
    }
    if findings_json is not None:
        files["_findings.json"] = json.dumps(findings_json, indent=2) + "\n"

    if atomic:
        # Per-critic entry-step sweep (parallel-safe; issue #376).
        cleanup_one_staging(final)
        if regenerate and final.exists():
            shutil.rmtree(final)
        with staged_sidecar(final, required_files=list(files.keys())) as staging:
            for name, text in files.items():
                (staging / name).write_text(text, encoding="utf-8")
    else:
        final.mkdir(parents=True, exist_ok=regenerate)
        for name, text in files.items():
            (final / name).write_text(text, encoding="utf-8")

    return final / "_review.json"


# ---------------------------------------------------------------------------
# CLI entry point (non-Python-driver sessions — issue #645)
# ---------------------------------------------------------------------------
#
# Mirrors the ``if __name__ == "__main__":`` precedent shipped by seven
# sibling ``anvil/lib/*.py`` modules (evidence_check, numeric_consistency,
# figure_content, hyperlink_resolver, export_schema, vocab_reminder,
# inventorship_evidence). A manual or agent review session with no
# orchestrating Python driver cannot call the :func:`staged_sidecar` context
# manager directly; it CAN shell out to ``python -m anvil.lib.sidecar`` and
# get the exact same atomicity guarantee — the manifest check + single
# ``Path.rename`` — enforced by code rather than re-derived in prose. When
# even ``python``/``uv`` is unavailable, the consuming command docs document a
# last-resort manual ``mv``-based fallback (see e.g. paper-review.md).


def _build_cli_parser():
    import argparse

    p = argparse.ArgumentParser(
        prog="python -m anvil.lib.sidecar",
        description=(
            "Atomic sidecar directory writes via staging-then-rename "
            "(issue #350). CLI shim for manual/agent review sessions with "
            "no orchestrating Python driver: `stage` a staging dir, write "
            "the required files into the printed path with your own "
            "editing tool, then `commit` (verify manifest + atomic "
            "rename). `cleanup` sweeps a single leftover staging dir."
        ),
    )
    sub = p.add_subparsers(dest="subcommand", required=True)

    p_stage = sub.add_parser(
        "stage",
        help=(
            "Create the staging dir for FINAL_DIR and print its path to "
            "stdout. Refuses if FINAL_DIR already exists."
        ),
    )
    p_stage.add_argument(
        "final_dir",
        help="The intended final sidecar path, e.g. output/thread.3.review",
    )

    p_commit = sub.add_parser(
        "commit",
        help=(
            "Verify the required-files manifest in the staging dir, then "
            "atomically rename it to FINAL_DIR. Nonzero exit (leaving the "
            "staging dir in place) if any required file is missing."
        ),
    )
    p_commit.add_argument(
        "final_dir",
        help="The intended final sidecar path, e.g. output/thread.3.review",
    )
    p_commit.add_argument(
        "--required",
        required=True,
        metavar="NAMES",
        help=(
            "Comma-separated list of required file basenames that MUST "
            "exist in the staging dir (e.g. "
            "verdict.md,scoring.md,comments.md,_meta.json,_progress.json)."
        ),
    )

    p_cleanup = sub.add_parser(
        "cleanup",
        help=(
            "Remove the single leftover staging dir corresponding to "
            "FINAL_DIR (the parallel-safe per-critic sweep, issue #376). "
            "Idempotent no-op when absent."
        ),
    )
    p_cleanup.add_argument(
        "final_dir",
        help="The intended final sidecar path, e.g. output/thread.3.review",
    )

    p_replace = sub.add_parser(
        "replace",
        help=(
            "Move FINAL_DIR aside and open a staging dir seeded with its "
            "existing contents (issue #881: a migrated-corpus final dir "
            "occupied by foreign, non-anvil-recognizable content). Refuses "
            "if FINAL_DIR is absent (use `stage` instead) or already "
            "carries a recognizable anvil review (the #350 guard)."
        ),
    )
    p_replace.add_argument(
        "final_dir",
        help="The occupied-but-unrecognized sidecar path to replace.",
    )

    p_commit_replace = sub.add_parser(
        "commit-replace",
        help=(
            "Verify the required-files manifest in the staging dir opened "
            "by `replace`, atomically swap it into FINAL_DIR, then drop "
            "the move-aside backup."
        ),
    )
    p_commit_replace.add_argument(
        "final_dir",
        help="The intended final sidecar path, e.g. output/thread.3.review",
    )
    p_commit_replace.add_argument(
        "--required",
        required=True,
        metavar="NAMES",
        help=(
            "Comma-separated list of required file basenames that MUST "
            "exist in the staging dir (typically includes the preserved "
            "foreign file, e.g. review.md,verdict.md,scoring.md,...)."
        ),
    )

    p_abort_replace = sub.add_parser(
        "abort-replace",
        help=(
            "Undo an in-progress `replace`: discard the staging dir and "
            "restore FINAL_DIR from its move-aside backup. Idempotent "
            "no-op when there is nothing to abort."
        ),
    )
    p_abort_replace.add_argument(
        "final_dir",
        help="The intended final sidecar path, e.g. output/thread.3.review",
    )

    p_recover_replace = sub.add_parser(
        "recover-replace",
        help=(
            "Entry-step recovery sweep for the replace surface (issue #881) "
            "— the `.bak` analog of `cleanup`. Restores FINAL_DIR from an "
            "orphaned move-aside backup left by a `replace` whose session "
            "died before `commit-replace`; drops a provably-redundant backup "
            "when the swap already landed. Idempotent no-op otherwise. Run "
            "it at command entry, next to `cleanup`."
        ),
    )
    p_recover_replace.add_argument(
        "final_dir",
        help="The intended final sidecar path, e.g. output/thread.3.review",
    )

    p_copy = sub.add_parser(
        "copy",
        help=(
            "Byte-safe copy of SRC to DST (issue #1017) — a single file or "
            "a directory tree, staged then atomically renamed into place, "
            "with post-copy byte-identity verification by default. The "
            "sanctioned binary/bulk-asset channel for a session whose "
            "editing tool is text-only (compile logs, carried-forward "
            "figures/, compiled PDFs)."
        ),
    )
    p_copy.add_argument("src", help="Source path (file or directory). Must exist.")
    p_copy.add_argument(
        "dst",
        help=(
            "Destination path. Refused if it already exists unless --force "
            "is given."
        ),
    )
    p_copy.add_argument(
        "--force",
        action="store_true",
        help="Overwrite DST if it already exists (default: refuse).",
    )
    p_copy.add_argument(
        "--no-verify",
        action="store_true",
        help=(
            "Skip the post-copy byte-identity verification (default: "
            "verify)."
        ),
    )

    return p


def main(argv: "Sequence[str] | None" = None) -> int:
    """CLI entry point. Returns the process exit code.

    Subcommands:

    - ``stage FINAL_DIR`` — create the staging dir and print its path.
      Exit ``0`` on success; ``3`` if ``FINAL_DIR`` already exists.
    - ``commit FINAL_DIR --required a,b,c`` — verify the manifest and
      atomically rename staging → ``FINAL_DIR``. Exit ``0`` on success;
      ``1`` if a required file is missing (staging dir left in place);
      ``3`` if the staging dir is absent or ``FINAL_DIR`` already exists.
    - ``cleanup FINAL_DIR`` — sweep the single leftover staging dir. Exit
      ``0`` always (idempotent no-op when absent); prints whether a dir
      was removed.
    - ``replace FINAL_DIR`` — move FINAL_DIR aside and open a staging dir
      seeded with its existing contents (issue #881). Exit ``0`` on
      success (prints the staging path); ``3`` if FINAL_DIR is absent or
      already carries a recognizable anvil review.
    - ``commit-replace FINAL_DIR --required a,b,c`` — verify the manifest
      and atomically swap staging → FINAL_DIR, then drop the backup. Exit
      ``0`` on success; ``1`` if a required file is missing (staging dir
      AND backup left in place); ``3`` if the staging dir is absent or
      FINAL_DIR already exists.
    - ``abort-replace FINAL_DIR`` — undo an in-progress `replace`: discard
      the staging dir, restore FINAL_DIR from its backup. Exit ``0``
      always (idempotent no-op when nothing to abort).
    - ``recover-replace FINAL_DIR`` — the entry-step recovery sweep for the
      replace surface (issue #881; the ``.bak`` analog of ``cleanup``).
      Restores FINAL_DIR when a prior ``replace``'s session died before
      ``commit-replace``; drops a provably-redundant backup when the swap
      already landed; leaves an ambiguous backup alone. Exit ``0`` always.
    - ``copy SRC DST [--force] [--no-verify]`` — byte-safe copy of a file
      or directory tree (issue #1017), staged then atomically renamed into
      DST, with post-copy byte-identity verification by default. Exit
      ``0`` on success (prints DST); ``3`` if SRC is missing or DST
      already exists without ``--force``; ``1`` if ``--no-verify`` was NOT
      passed and post-copy verification finds a mismatch (staged copy left
      unrenamed for forensics).

    Exit-code contract mirrors the sibling ``anvil/lib/*.py`` CLIs: ``0``
    clean, ``1`` a contract failure the caller must act on
    (missing-required-file, the ``SidecarIncompleteError`` analog), and a
    distinct nonzero code (``3``) for invocation/precondition errors.
    """
    import sys

    parser = _build_cli_parser()
    args = parser.parse_args(argv)
    # `copy` takes src/dst, not final_dir — every other subcommand does.
    final_dir = Path(args.final_dir) if args.subcommand != "copy" else None

    if args.subcommand == "stage":
        try:
            staging = stage_enter(final_dir)
        except FileExistsError as exc:
            print(f"error: {exc}", file=sys.stderr)
            return 3
        print(str(staging))
        return 0

    if args.subcommand == "commit":
        required = [
            name.strip() for name in args.required.split(",") if name.strip()
        ]
        try:
            committed = commit_staged(final_dir, required)
        except (FileNotFoundError, FileExistsError) as exc:
            print(f"error: {exc}", file=sys.stderr)
            return 3
        except SidecarIncompleteError as exc:
            print(f"error: {exc}", file=sys.stderr)
            return 1
        print(str(committed))
        return 0

    if args.subcommand == "cleanup":
        removed = cleanup_one_staging(final_dir)
        staging = staging_path_for(final_dir)
        if removed:
            print(f"removed staging dir {staging}")
        else:
            print(f"no staging dir to remove at {staging}")
        return 0

    if args.subcommand == "replace":
        try:
            staging = stage_replace(final_dir)
        except (FileNotFoundError, FileExistsError) as exc:
            print(f"error: {exc}", file=sys.stderr)
            return 3
        print(str(staging))
        return 0

    if args.subcommand == "commit-replace":
        required = [
            name.strip() for name in args.required.split(",") if name.strip()
        ]
        try:
            committed = commit_replace(final_dir, required)
        except (FileNotFoundError, FileExistsError) as exc:
            print(f"error: {exc}", file=sys.stderr)
            return 3
        except SidecarIncompleteError as exc:
            print(f"error: {exc}", file=sys.stderr)
            return 1
        print(str(committed))
        return 0

    if args.subcommand == "abort-replace":
        restored = abort_replace(final_dir)
        if restored:
            print(f"restored {final_dir} from backup")
        else:
            print(f"nothing to restore for {final_dir}")
        return 0

    if args.subcommand == "recover-replace":
        backup = backup_path_for(final_dir)
        had_backup = backup.exists()
        final_existed = final_dir.exists()
        changed = recover_interrupted_replace(final_dir)
        if changed and not final_existed:
            print(f"recovered {final_dir} from an interrupted replace")
        elif changed:
            print(f"dropped redundant backup {backup} for {final_dir}")
        elif had_backup:
            print(
                f"backup {backup} left in place: it holds content not "
                f"present in {final_dir} — resolve by hand"
            )
        else:
            print(f"nothing to recover for {final_dir}")
        return 0

    if args.subcommand == "copy":
        try:
            landed = copy_bytes(
                Path(args.src),
                Path(args.dst),
                overwrite=args.force,
                verify=not args.no_verify,
            )
        except (FileNotFoundError, FileExistsError) as exc:
            print(f"error: {exc}", file=sys.stderr)
            return 3
        except SidecarCopyVerificationError as exc:
            print(f"error: {exc}", file=sys.stderr)
            return 1
        print(str(landed))
        return 0

    # argparse's required=True on the subparser guarantees we never fall
    # through, but return a distinct code defensively.
    return 3  # pragma: no cover


if __name__ == "__main__":
    raise SystemExit(main())
