"""Deterministic BRIEF/refs evidence-drift advisory (issue #857).

The problem
-----------

Version-dir immutability means a version's evidence is frozen at
draft/revise time, but ``<thread>/BRIEF.md`` and ``<thread>/refs/**`` are
mutable thread-root siblings that can change *after* a version was
drafted — including after a thread reaches a terminal state
(``READY``/``AUDITED``). The framework's state machine derives state
purely from sibling *existence*, so a terminal thread whose BRIEF or refs
changed yesterday looks byte-identical to one whose evidence is current.
Two censusapi incidents (issue #857) hit exactly this: an ``AUDITED``
paper thread whose refs were later found contaminated (nothing flagged
the drift; the correction pass was operator-initiated out-of-band), and a
``proposal`` thread whose ``BRIEF.md`` was updated after the v1 draft
(a claim the draft leaned on was retracted) with no mechanism to notice.

This module is a **read-only, advisory** detector: it compares the
current on-disk mtimes of a thread's ``BRIEF.md`` + ``refs/**`` against a
snapshot recorded at the latest version's draft/revise completion time,
and reports whether the thread-root evidence has since changed. It never
mutates on-disk state, never affects scoring, `advance`, or critical
flags, and never reopens the state machine — the same advisory posture as
the ``NEVER-VISION-CHECKED`` orchestrator note (`anvil/skills/paper/commands/
paper.md`) and, more directly, the ``pending_sources`` reporting aid
(`anvil/lib/project_brief.py::resolve_pending_sources`). Unlike the
`pending_marker` gate (issue #841/#842), evidence drift is **never**
wired through `anvil/lib/convergence.py`'s `CriticalFlag` machinery —
there is nothing to "resolve" here, only something for a reviewer/auditor
to re-weigh.

Two halves
----------

1. **Snapshot recording** (:func:`compute_evidence_snapshot`,
   :func:`record_evidence_snapshot`): called by a drafter/reviser command
   at draft/revise completion time. Computes the current BRIEF.md mtime
   and the max mtime across every file under ``refs/**``, and merges the
   result into the version dir's ``_progress.json`` as
   ``metadata.evidence_snapshot`` — a read-merge-write over the *file*
   only (the version dir itself is otherwise untouched), atomic via
   the shared :func:`anvil.lib.atomic_write.atomic_write_json` helper.
   This is the baseline a later review/audit pass compares against.

2. **Drift checking** (:func:`check_evidence_drift`,
   :func:`check_thread_evidence_drift`): called by a reviewer/auditor
   command. Reads the recorded snapshot from the latest version dir's
   ``_progress.json`` and compares it against the CURRENT on-disk state
   of the thread root. A newer ``BRIEF.md`` mtime or a newer max
   ``refs/**`` mtime than the recorded snapshot is reported as
   ``EVIDENCE-DRIFT``.

Bootstrap safety
-----------------

A thread whose latest version predates this feature (or whose
draft/revise command has not yet been updated to record a snapshot) has
no ``metadata.evidence_snapshot`` to compare against. This is explicitly
treated as ``NO-SNAPSHOT`` — reported as **not drifted** — never as a
false-positive drift signal. The very next draft/revise pass on that
thread starts recording a snapshot, and drift detection becomes active
from that point forward.

mtime vs. content hash
------------------------

This module compares mtimes, not content hashes. A checkout/clone/rsync
that touches mtimes without changing content is a known false-positive
source for mtime-based freshness checks (see
``anvil/skills/report/lib/data_contract.py``'s ``STALE`` freshness
check, which has the identical tradeoff) — accepted here because (a) the
signal is purely advisory (a false positive costs a reviewer one extra
sentence of re-weighing, not a blocked pipeline), and (b) the alternative
(hashing every file under ``refs/**`` on every review pass) is a real
cost for large reference corpora with no correctness benefit for the
common case (an author's local edit, not a bulk checkout). If mtime
noise proves disruptive in practice, a content-hash mode can be added
additively without changing this module's public contract.

CLI entry-point
----------------

``python -m anvil.lib.evidence_drift record <thread_dir> <version_dir>``
    Computes the current snapshot and merges it into
    ``<version_dir>/_progress.json`` as ``metadata.evidence_snapshot``.
    Prints the recorded snapshot as JSON. Exit code is always ``0``
    (invocation errors aside) — this subcommand mutates only the
    advisory snapshot field, never gates anything.

``python -m anvil.lib.evidence_drift check <thread_dir> <version_dir>``
    Reads the recorded snapshot from ``<version_dir>/_progress.json`` and
    compares it against the current state of ``<thread_dir>``. Prints the
    :class:`EvidenceDriftResult` as JSON. Exit code is **always ``0``**
    regardless of drift status — this tool is purely informational and
    MUST NOT be wired into any pass/fail gate.
"""

from __future__ import annotations

import json
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Dict, List, Optional

from anvil.lib.atomic_write import atomic_write_json

BRIEF_FILENAME = "BRIEF.md"
"""Thread-root brief filename whose mtime is tracked."""

REFS_DIRNAME = "refs"
"""Thread-root reference-material directory whose ``**`` max mtime is
tracked."""

STATUS_CLEAN = "CLEAN"
"""No drift: current thread-root evidence is unchanged since the
recorded snapshot."""

STATUS_DRIFT = "EVIDENCE-DRIFT"
"""``BRIEF.md`` and/or ``refs/**`` were modified after the latest
version's recorded evidence snapshot."""

STATUS_NO_SNAPSHOT = "NO-SNAPSHOT"
"""Bootstrap case: no prior snapshot recorded. Reported as clean/not-
drifted — never a false-positive drift signal (see module docstring)."""

DRIFT_TOLERANCE_SECONDS = 1e-3
"""Minimum mtime delta (seconds) treated as real drift, not float-precision
noise (issue #1018). A hand-recorded snapshot (a `record` invocation typed
by hand rather than run through the tool, e.g. under a Bash-write-blocking
hook) can lose sub-microsecond precision when the mtime float is
transcribed, which previously surfaced as a false-positive `EVIDENCE-DRIFT`
on a delta as small as 2e-7 seconds. 1ms is comfortably above that noise
floor and above common filesystem mtime granularity (e.g. 1-second
resolution on some filesystems truncated by intermediate tooling), while
staying far below the elapsed time of any real edit — the same "false
positive costs a sentence, not a blocked pipeline" tradeoff already
accepted for mtime-vs-content-hash above."""


# ---------------------------------------------------------------------------
# Snapshot computation
# ---------------------------------------------------------------------------


def _refs_max_mtime(thread_dir: Path) -> Optional[float]:
    """Max mtime across every file under ``<thread_dir>/refs/**``.

    ``None`` when ``refs/`` does not exist or contains no files (an
    empty/absent refs dir has nothing to drift).
    """
    refs_dir = Path(thread_dir) / REFS_DIRNAME
    if not refs_dir.is_dir():
        return None
    latest: Optional[float] = None
    for path in refs_dir.rglob("*"):
        if not path.is_file():
            continue
        try:
            mtime = path.stat().st_mtime
        except OSError:
            continue
        if latest is None or mtime > latest:
            latest = mtime
    return latest


def compute_evidence_snapshot(thread_dir: Path) -> Dict[str, Optional[float]]:
    """Compute the current thread-root evidence mtime snapshot.

    Returns ``{"brief_mtime": <float|None>, "refs_mtime": <float|None>}``
    — a plain JSON-serializable dict suitable for embedding verbatim as
    ``_progress.json``'s ``metadata.evidence_snapshot``.
    ``brief_mtime`` is ``None`` when ``<thread_dir>/BRIEF.md`` does not
    exist; ``refs_mtime`` is ``None`` when ``<thread_dir>/refs/`` does
    not exist or contains no files. Pure ``Path.stat()`` — no content
    hashing, no filesystem mutation.
    """
    thread_dir = Path(thread_dir)
    brief_path = thread_dir / BRIEF_FILENAME
    brief_mtime: Optional[float]
    try:
        brief_mtime = brief_path.stat().st_mtime if brief_path.is_file() else None
    except OSError:
        brief_mtime = None
    return {
        "brief_mtime": brief_mtime,
        "refs_mtime": _refs_max_mtime(thread_dir),
    }


# ---------------------------------------------------------------------------
# _progress.json read-merge-write (metadata.evidence_snapshot only)
# ---------------------------------------------------------------------------


def _read_progress(progress_path: Path) -> Dict[str, Any]:
    if not progress_path.is_file():
        return {}
    try:
        data = json.loads(progress_path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError):
        return {}
    return data if isinstance(data, dict) else {}


def record_evidence_snapshot(
    thread_dir: Path, version_dir: Path
) -> Dict[str, Optional[float]]:
    """Compute + persist the evidence snapshot for a just-completed version.

    Merges ``metadata.evidence_snapshot`` into
    ``<version_dir>/_progress.json``, preserving every other top-level
    and ``metadata`` field (the shallow-merge convention documented in
    ``anvil/lib/snippets/progress.md``). Atomic via the shared
    :func:`anvil.lib.atomic_write.atomic_write_json` helper. Creates
    ``_progress.json`` with the minimal shape if it does not already
    exist (defensive — in the normal flow the calling draft/revise
    command has already initialized it before this runs).

    Returns the recorded snapshot dict.
    """
    thread_dir = Path(thread_dir)
    version_dir = Path(version_dir)
    snapshot = compute_evidence_snapshot(thread_dir)

    progress_path = version_dir / "_progress.json"
    progress = _read_progress(progress_path)
    if not progress:
        progress = {"version": 1, "thread": thread_dir.name, "phases": {}}
    metadata = progress.get("metadata")
    if not isinstance(metadata, dict):
        metadata = {}
    metadata["evidence_snapshot"] = snapshot
    progress["metadata"] = metadata

    version_dir.mkdir(parents=True, exist_ok=True)
    atomic_write_json(progress_path, progress)
    return snapshot


def load_snapshot_from_progress(version_dir: Path) -> Optional[Dict[str, Any]]:
    """Read ``metadata.evidence_snapshot`` from a version dir's ``_progress.json``.

    Lenient by design (mirrors ``project_brief.py::resolve_pending_sources``):
    returns ``None`` for a missing/unreadable/malformed ``_progress.json``
    or an absent/malformed ``evidence_snapshot`` key — every one of these
    is the bootstrap case handled by :func:`check_evidence_drift`, never
    an error.
    """
    progress = _read_progress(Path(version_dir) / "_progress.json")
    metadata = progress.get("metadata")
    if not isinstance(metadata, dict):
        return None
    snapshot = metadata.get("evidence_snapshot")
    if not isinstance(snapshot, dict):
        return None
    return snapshot


# ---------------------------------------------------------------------------
# Drift check
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class EvidenceDriftResult:
    """Outcome of one :func:`check_evidence_drift` pass.

    Purely advisory — see module docstring. ``status`` is one of
    ``STATUS_CLEAN`` / ``STATUS_DRIFT`` / ``STATUS_NO_SNAPSHOT``.
    """

    status: str
    detail: str
    brief_drifted: bool = False
    refs_drifted: bool = False
    snapshot: Optional[Dict[str, Any]] = None
    current: Optional[Dict[str, Any]] = None

    @property
    def drifted(self) -> bool:
        """``True`` only for :data:`STATUS_DRIFT` — the sole gate a
        caller should branch on to decide whether to surface an advisory
        note. ``STATUS_NO_SNAPSHOT`` is deliberately NOT drifted."""
        return self.status == STATUS_DRIFT

    def changed_paths(self) -> List[str]:
        """Human-legible labels for the changed evidence, in a stable order."""
        changed: List[str] = []
        if self.brief_drifted:
            changed.append(BRIEF_FILENAME)
        if self.refs_drifted:
            changed.append(f"{REFS_DIRNAME}/**")
        return changed

    def to_json(self) -> Dict[str, Any]:
        return {
            "status": self.status,
            "detail": self.detail,
            "drifted": self.drifted,
            "brief_drifted": self.brief_drifted,
            "refs_drifted": self.refs_drifted,
            "changed_paths": self.changed_paths(),
            "snapshot": self.snapshot,
            "current": self.current,
        }


def check_evidence_drift(
    thread_dir: Path, snapshot: Optional[Dict[str, Any]]
) -> EvidenceDriftResult:
    """Compare current thread-root evidence mtimes against a recorded snapshot.

    ``snapshot`` is normally the return value of
    :func:`load_snapshot_from_progress` against the latest version dir.
    ``None`` (or a dict with both mtimes absent/``None``) is the
    bootstrap case (see module docstring "Bootstrap safety") — reported
    as :data:`STATUS_NO_SNAPSHOT`, which is NOT drifted.

    Never raises for a missing ``BRIEF.md``/``refs/``; never mutates any
    on-disk state; has no bearing on gating, scoring, or critical flags.
    """
    thread_dir = Path(thread_dir)
    current = compute_evidence_snapshot(thread_dir)

    if not snapshot or (
        snapshot.get("brief_mtime") is None and snapshot.get("refs_mtime") is None
    ):
        return EvidenceDriftResult(
            status=STATUS_NO_SNAPSHOT,
            detail=(
                "no evidence snapshot recorded in the latest version's "
                "_progress.json (pre-#857 thread, or no draft/revise pass "
                "has run since this feature was adopted) — treated as "
                "clean, not a drift signal. The next draft/revise pass "
                "on this thread will begin recording a snapshot."
            ),
            snapshot=snapshot,
            current=current,
        )

    prior_brief = snapshot.get("brief_mtime")
    prior_refs = snapshot.get("refs_mtime")

    brief_drifted = current["brief_mtime"] is not None and (
        prior_brief is None
        or current["brief_mtime"] - prior_brief > DRIFT_TOLERANCE_SECONDS
    )
    refs_drifted = current["refs_mtime"] is not None and (
        prior_refs is None
        or current["refs_mtime"] - prior_refs > DRIFT_TOLERANCE_SECONDS
    )

    if not brief_drifted and not refs_drifted:
        return EvidenceDriftResult(
            status=STATUS_CLEAN,
            detail=(
                f"{BRIEF_FILENAME} and {REFS_DIRNAME}/** are unchanged "
                "since the recorded evidence snapshot."
            ),
            snapshot=snapshot,
            current=current,
        )

    result = EvidenceDriftResult(
        status=STATUS_DRIFT,
        detail="",
        brief_drifted=brief_drifted,
        refs_drifted=refs_drifted,
        snapshot=snapshot,
        current=current,
    )
    changed = " and ".join(result.changed_paths())
    detail = (
        f"{changed} modified after the latest version's recorded evidence "
        "snapshot — the thread's evidence may have changed since this "
        "version was drafted/revised. Advisory only: does not change any "
        "on-disk state, score, or critical flag. Re-weigh the BRIEF/refs "
        "against the version under review."
    )
    return EvidenceDriftResult(
        status=STATUS_DRIFT,
        detail=detail,
        brief_drifted=brief_drifted,
        refs_drifted=refs_drifted,
        snapshot=snapshot,
        current=current,
    )


def check_thread_evidence_drift(
    thread_dir: Path, version_dir: Path
) -> EvidenceDriftResult:
    """Convenience wrapper: load the snapshot from ``version_dir`` and
    compare it against ``thread_dir``'s current on-disk state."""
    snapshot = load_snapshot_from_progress(version_dir)
    return check_evidence_drift(thread_dir, snapshot)


# ---------------------------------------------------------------------------
# CLI entry-point
# ---------------------------------------------------------------------------


def _build_cli_parser():
    import argparse

    p = argparse.ArgumentParser(
        prog="python -m anvil.lib.evidence_drift",
        description=(
            "Deterministic BRIEF.md/refs/** evidence-drift advisory "
            "(issue #857). Purely informational — never gates, never "
            "mutates artifact state."
        ),
    )
    sub = p.add_subparsers(dest="command", required=True)

    record_p = sub.add_parser(
        "record",
        help=(
            "Compute the current BRIEF/refs mtime snapshot and merge it "
            "into <version_dir>/_progress.json as "
            "metadata.evidence_snapshot."
        ),
    )
    record_p.add_argument("thread_dir", help="Path to the thread root (<thread>/ or <project>/<thread>/).")
    record_p.add_argument("version_dir", help="Path to the just-completed <thread>.{N}/ version dir.")

    check_p = sub.add_parser(
        "check",
        help=(
            "Compare the current thread-root evidence against the "
            "snapshot recorded in <version_dir>/_progress.json."
        ),
    )
    check_p.add_argument("thread_dir", help="Path to the thread root (<thread>/ or <project>/<thread>/).")
    check_p.add_argument("version_dir", help="Path to the latest <thread>.{N}/ version dir.")

    return p


def main(argv: Optional[List[str]] = None) -> int:
    """CLI entry point. Returns the process exit code.

    Always ``0`` on a successful invocation of either subcommand — this
    tool is purely advisory and MUST NOT be wired into a pass/fail gate
    by any caller. ``2`` on an invocation error (bad path, etc.).
    """
    parser = _build_cli_parser()
    args = parser.parse_args(argv)

    try:
        if args.command == "record":
            snapshot = record_evidence_snapshot(
                Path(args.thread_dir), Path(args.version_dir)
            )
            print(json.dumps(snapshot, indent=2))
            return 0
        if args.command == "check":
            result = check_thread_evidence_drift(
                Path(args.thread_dir), Path(args.version_dir)
            )
            print(json.dumps(result.to_json(), indent=2))
            return 0
    except OSError as exc:
        print(f"error: {exc}", file=sys.stderr)
        return 2

    return 2  # pragma: no cover - argparse enforces a valid subcommand


__all__ = [
    "BRIEF_FILENAME",
    "REFS_DIRNAME",
    "STATUS_CLEAN",
    "STATUS_DRIFT",
    "STATUS_NO_SNAPSHOT",
    "DRIFT_TOLERANCE_SECONDS",
    "EvidenceDriftResult",
    "compute_evidence_snapshot",
    "record_evidence_snapshot",
    "load_snapshot_from_progress",
    "check_evidence_drift",
    "check_thread_evidence_drift",
    "main",
]


if __name__ == "__main__":
    raise SystemExit(main())
