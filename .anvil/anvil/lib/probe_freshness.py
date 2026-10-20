"""Perishable-claim freshness advisory for audit siblings (issue #863).

The problem
-----------

``kind: tool_evidence`` verifications come in two flavors the audit
contract did not previously distinguish. A BOM subtotal that sums is
**durable** — verified once, true forever unless the document changes. A
live URL, an HTTP status, a version pin, the SHA of a served artifact is
**perishable** — verified once, true until the world moves. Both landed
on disk as an indistinguishable ``VERIFIED``, so a perishable claim's
implicit expiry was unrecorded and every downstream consumer (the next
auditor, the reviser, the operator deciding to send) inherited a
verification whose freshness was unknowable without redoing the probe.

The censusapi canary hit this one day apart on a partner-facing proposal:
a clean 44-row audit on 2026-08-01 had two of its 41 verified claims
false by 2026-08-02 (a cited paper advanced from "working draft v8" to
v10 at the same URL; a dataset host reported dead came back with HTTP
200). Both were correctly verified when the audit ran. Both were
trivially falsifiable by the recipient. Nothing on disk told the next
pass to look.

The contract
------------

An auditor records each **perishable** verification as a
:class:`~anvil.lib.review_schema.Probe` — target, method, observed value,
timestamp. Durable verifications record nothing; the *existence* of a
probe row is the perishability marker. See
``anvil/lib/snippets/audit.md`` §"Perishable vs durable verifications".

Two carriers, because the shipped audit commands have not all migrated to
``_review.json`` (``audit.md`` §"Migration status"): a schema-era critic
populates ``Review.probes``; a prose-era critic writes a standalone
``probes.json`` (a :class:`~anvil.lib.review_schema.ProbeLog`) next to its
``findings.md``. This module reads both and unions them, so the
perishability contract does not have to wait on the per-skill migration.

What this module reports
------------------------

:func:`check_probe_freshness` classifies every probed target across a
thread's critic siblings into a bounded re-probe checklist:

- ``FRESH`` — probed within the freshness budget, in the version under
  review.
- ``STALE`` — the newest probe of this target is older than its
  freshness budget (per-probe ``max_age_days``, else the caller's
  default).
- ``NOT-REPROBED`` — the target was verified against an *earlier*
  version and no pass since has re-probed it. This is the "surfaces
  which perishable claims have not been re-probed since their original
  verification" leg: the claim was carried forward into the current
  version on the strength of an older pass.

Plus ``unknown_freshness``: audit-class siblings carrying no probe record
at all. Every pre-#863 sibling lands here — tolerated by design, never a
defect, never an error. Unknown is honest; silence dressed as
``VERIFIED`` was the bug.

Advisory only
-------------

Like ``anvil/lib/evidence_drift.py`` (issue #857), this check is purely
informational. It never mutates on-disk state, never touches scoring,
``advance``, or critical flags, and the CLI always exits ``0``. A stale
probe is not a defect — it is a claim whose verification has expired and
which the next pass must re-run before the artifact ships.

CLI entry-point
---------------

``python -m anvil.lib.probe_freshness <version_dir> [--max-age-days N]``
    Reports probe freshness for ``<version_dir>``'s thread as JSON.
    ``--now`` pins the evaluation instant (ISO-8601) for reproducible
    output; ``--max-age-days`` sets the default freshness budget
    (default ``14``).
"""

from __future__ import annotations

import json
import re
import sys
from dataclasses import dataclass, field
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Dict, List, Optional

from anvil.lib.review_schema import Probe, parse_timestamp

PROBE_LOG_FILENAME = "probes.json"
"""Standalone re-probe list written by a prose-era audit sibling."""

REVIEW_FILENAME = "_review.json"
"""Schema-era carrier; ``probes[]`` is read off the ``Review`` payload."""

DEFAULT_MAX_AGE_DAYS = 14
"""Default freshness budget.

Deliberately a dumb heuristic — the issue's own framing is that "even a
dumb heuristic beats silence". Two weeks is roughly the observed gap
between a customer-facing artifact reaching ``AUDITED`` and a human
deciding to send it; a probe older than that has had time to rot
unnoticed. Callers override per-probe (``Probe.max_age_days``) when a
claim has a known expiry.
"""

STATUS_FRESH = "FRESH"
STATUS_STALE = "STALE"
STATUS_NOT_REPROBED = "NOT-REPROBED"

REPORT_CLEAN = "CLEAN"
"""Every recorded probe is fresh and re-probed against the current version."""

REPORT_NEEDS_REPROBE = "NEEDS-REPROBE"
"""At least one target is ``STALE`` or ``NOT-REPROBED``."""

REPORT_NO_PROBES = "NO-PROBES"
"""No probe record anywhere in the thread — the pre-#863 shape."""

# `<slug>.<N>.<tag>` — the critic-sibling naming contract from
# `anvil/lib/snippets/version_layout.md`. Group 1 is the version ordinal.
_CRITIC_DIR_RE = re.compile(r"\.(\d+)\.[^.]+$")
# `<slug>.<N>` — a version dir (no trailing tag).
_VERSION_DIR_RE = re.compile(r"\.(\d+)$")

# A sibling is audit-class (and therefore expected to carry probes) when
# its `_review.json` says `kind: tool_evidence`, or — for the prose-era
# auditors that write no `_review.json` at all — when its dir tag names an
# audit. The tag heuristic is deliberately loose: a false positive costs
# one honest "unknown freshness" line, a false negative silently drops a
# sibling out of the report.
_AUDIT_TAG_SUBSTRINGS = ("audit", "verify", "fact-check")


def _version_ordinal(dir_name: str) -> Optional[int]:
    match = _CRITIC_DIR_RE.search(dir_name) or _VERSION_DIR_RE.search(dir_name)
    return int(match.group(1)) if match else None


def _critic_tag(dir_name: str) -> Optional[str]:
    if not _CRITIC_DIR_RE.search(dir_name):
        return None
    return dir_name.rsplit(".", 1)[-1]


def _read_json(path: Path) -> Optional[Any]:
    try:
        return json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError):
        return None


# ---------------------------------------------------------------------------
# Collection
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class CollectedProbe:
    """One :class:`Probe` plus where it was found."""

    probe: Probe
    critic_dir: str
    version_dir: str
    version: Optional[int]

    def to_json(self) -> Dict[str, Any]:
        return {
            "critic_dir": self.critic_dir,
            "version_dir": self.version_dir,
            "version": self.version,
            **self.probe.model_dump(exclude_none=True),
        }


def _probes_from_dir(critic_dir: Path) -> Optional[List[Probe]]:
    """Union of both probe carriers in one critic sibling dir.

    ``None`` distinguishes "no probe record at all" (unknown freshness)
    from an empty list ("audited; nothing perishable"). Malformed rows are
    skipped individually rather than discarding the whole sibling — a
    partial re-probe list beats none, and this is an advisory path that
    must never raise on a hand-edited sidecar.
    """
    found = False
    probes: List[Probe] = []
    seen: set = set()

    for filename in (PROBE_LOG_FILENAME, REVIEW_FILENAME):
        payload = _read_json(critic_dir / filename)
        if not isinstance(payload, dict):
            continue
        rows = payload.get("probes")
        if not isinstance(rows, list):
            continue
        found = True
        for row in rows:
            try:
                probe = Probe.model_validate(row)
            except Exception:
                continue
            identity = (probe.target, probe.method, probe.checked_at)
            if identity in seen:
                continue
            seen.add(identity)
            probes.append(probe)

    return probes if found else None


def _is_audit_sibling(critic_dir: Path) -> bool:
    payload = _read_json(critic_dir / REVIEW_FILENAME)
    if isinstance(payload, dict) and payload.get("kind") == "tool_evidence":
        return True
    tag = _critic_tag(critic_dir.name) or ""
    return any(s in tag for s in _AUDIT_TAG_SUBSTRINGS)


def _iter_critic_dirs(thread_dir: Path) -> List[Path]:
    if not thread_dir.is_dir():
        return []
    return sorted(
        child
        for child in thread_dir.iterdir()
        if child.is_dir() and _CRITIC_DIR_RE.search(child.name)
    )


def collect_probes(thread_dir: Path) -> List[CollectedProbe]:
    """Every probe recorded by every critic sibling under a thread root.

    Walks *all* versions, not just the latest — a probe recorded during
    the v2 audit is exactly the record a v3 pass needs to notice it never
    re-ran. Never raises for a missing/malformed sidecar.
    """
    thread_dir = Path(thread_dir)
    collected: List[CollectedProbe] = []
    for critic_dir in _iter_critic_dirs(thread_dir):
        probes = _probes_from_dir(critic_dir)
        if not probes:
            continue
        version = _version_ordinal(critic_dir.name)
        version_dir = critic_dir.name.rsplit(".", 1)[0]
        for probe in probes:
            collected.append(
                CollectedProbe(
                    probe=probe,
                    critic_dir=critic_dir.name,
                    version_dir=version_dir,
                    version=version,
                )
            )
    return collected


def find_unknown_freshness_siblings(thread_dir: Path) -> List[str]:
    """Audit-class sibling dirs carrying no probe record.

    Backward compatibility (issue #863 AC5): every pre-#863 audit sibling
    lands here. It is reported, never treated as a defect, and never
    conflated with "nothing perishable" (which an auditor states by
    writing an empty ``probes`` list).
    """
    return [
        critic_dir.name
        for critic_dir in _iter_critic_dirs(Path(thread_dir))
        if _probes_from_dir(critic_dir) is None and _is_audit_sibling(critic_dir)
    ]


# ---------------------------------------------------------------------------
# Freshness classification
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class ProbeStatus:
    """One probed target's freshness verdict, newest probe wins."""

    target: str
    status: str
    detail: str
    probe: Probe
    critic_dir: str
    version: Optional[int]
    age_days: Optional[float]
    max_age_days: int

    def to_json(self) -> Dict[str, Any]:
        return {
            "target": self.target,
            "status": self.status,
            "detail": self.detail,
            "critic_dir": self.critic_dir,
            "version": self.version,
            "age_days": (
                None if self.age_days is None else round(self.age_days, 2)
            ),
            "max_age_days": self.max_age_days,
            "method": self.probe.method,
            "observed": self.probe.observed,
            "checked_at": self.probe.checked_at,
            "claim": self.probe.claim,
            "recheck_command": self.probe.recheck_command,
        }


@dataclass(frozen=True)
class ProbeFreshnessReport:
    """Outcome of one :func:`check_probe_freshness` pass. Advisory only."""

    status: str
    detail: str
    version_dir: str
    now: str
    default_max_age_days: int
    statuses: List[ProbeStatus] = field(default_factory=list)
    unknown_freshness: List[str] = field(default_factory=list)

    @property
    def needs_reprobe(self) -> List[ProbeStatus]:
        """The bounded checklist: every target a pass must re-run."""
        return [s for s in self.statuses if s.status != STATUS_FRESH]

    def to_json(self) -> Dict[str, Any]:
        return {
            "status": self.status,
            "detail": self.detail,
            "version_dir": self.version_dir,
            "now": self.now,
            "default_max_age_days": self.default_max_age_days,
            "probes": [s.to_json() for s in self.statuses],
            "needs_reprobe": [s.to_json() for s in self.needs_reprobe],
            "unknown_freshness": self.unknown_freshness,
        }


def _newest_per_target(
    collected: List[CollectedProbe],
) -> Dict[str, CollectedProbe]:
    """Keep the most recent probe per target.

    Ties (identical timestamps across two siblings) resolve to the higher
    version, then to the later-sorting critic dir — deterministic, so two
    runs over the same tree report identically.
    """
    newest: Dict[str, CollectedProbe] = {}
    for item in collected:
        current = newest.get(item.probe.target)
        if current is None:
            newest[item.probe.target] = item
            continue
        item_ts = parse_timestamp(item.probe.checked_at)
        current_ts = parse_timestamp(current.probe.checked_at)
        item_key = (
            item_ts or datetime.min.replace(tzinfo=timezone.utc),
            item.version or -1,
            item.critic_dir,
        )
        current_key = (
            current_ts or datetime.min.replace(tzinfo=timezone.utc),
            current.version or -1,
            current.critic_dir,
        )
        if item_key > current_key:
            newest[item.probe.target] = item
    return newest


def check_probe_freshness(
    version_dir: Path,
    now: Optional[datetime] = None,
    max_age_days: int = DEFAULT_MAX_AGE_DAYS,
    thread_dir: Optional[Path] = None,
) -> ProbeFreshnessReport:
    """Classify every probed target in ``version_dir``'s thread.

    ``version_dir`` is the version being revised or audited, e.g.
    ``<thread>/<thread>.3``. Its parent is the thread root unless
    ``thread_dir`` says otherwise. ``now`` defaults to the current UTC
    instant; pass it to pin output for tests or a reproducible report.

    Never raises for a missing thread dir, a malformed sidecar, or an
    unparseable timestamp; never mutates anything.
    """
    version_dir = Path(version_dir)
    root = Path(thread_dir) if thread_dir is not None else version_dir.parent
    now = now or datetime.now(timezone.utc)
    if now.tzinfo is None:
        now = now.replace(tzinfo=timezone.utc)

    current_version = _version_ordinal(version_dir.name)
    collected = collect_probes(root)
    unknown = find_unknown_freshness_siblings(root)

    statuses: List[ProbeStatus] = []
    for target, item in sorted(_newest_per_target(collected).items()):
        budget = (
            item.probe.max_age_days
            if item.probe.max_age_days is not None
            else max_age_days
        )
        checked_at = parse_timestamp(item.probe.checked_at)
        age_days = (
            None
            if checked_at is None
            else (
                now
                - (
                    checked_at
                    if checked_at.tzinfo
                    else checked_at.replace(tzinfo=timezone.utc)
                )
            ).total_seconds()
            / 86400.0
        )

        if age_days is not None and age_days > budget:
            status, detail = (
                STATUS_STALE,
                f"last probed {age_days:.1f}d ago (budget {budget}d) — "
                f"observed {item.probe.observed!r} at {item.probe.checked_at}; "
                "re-run before this artifact ships.",
            )
        elif (
            current_version is not None
            and item.version is not None
            and item.version < current_version
        ):
            status, detail = (
                STATUS_NOT_REPROBED,
                f"verified against version {item.version} and carried into "
                f"version {current_version} without a re-probe; observed "
                f"{item.probe.observed!r} at {item.probe.checked_at}.",
            )
        else:
            status, detail = (
                STATUS_FRESH,
                f"probed {item.probe.checked_at} (budget {budget}d).",
            )

        statuses.append(
            ProbeStatus(
                target=target,
                status=status,
                detail=detail,
                probe=item.probe,
                critic_dir=item.critic_dir,
                version=item.version,
                age_days=age_days,
                max_age_days=budget,
            )
        )

    if not statuses:
        return ProbeFreshnessReport(
            status=REPORT_NO_PROBES,
            detail=(
                "no perishable-claim probes recorded anywhere in this thread "
                "(pre-#863 thread, or no audit pass has adopted the probe "
                "contract yet) — freshness is unknown, not clean. The next "
                "audit pass should record a probes.json re-probe list per "
                "anvil/lib/snippets/audit.md."
            ),
            version_dir=version_dir.name,
            now=now.isoformat(),
            default_max_age_days=max_age_days,
            unknown_freshness=unknown,
        )

    stale_or_carried = [s for s in statuses if s.status != STATUS_FRESH]
    if stale_or_carried:
        targets = ", ".join(s.target for s in stale_or_carried)
        detail = (
            f"{len(stale_or_carried)} of {len(statuses)} perishable claims "
            f"need re-probing before this artifact ships: {targets}. "
            "Advisory only: does not change any on-disk state, score, or "
            "critical flag."
        )
        status = REPORT_NEEDS_REPROBE
    else:
        detail = (
            f"all {len(statuses)} perishable claims were re-probed against "
            "this version within their freshness budget."
        )
        status = REPORT_CLEAN

    return ProbeFreshnessReport(
        status=status,
        detail=detail,
        version_dir=version_dir.name,
        now=now.isoformat(),
        default_max_age_days=max_age_days,
        statuses=statuses,
        unknown_freshness=unknown,
    )


# ---------------------------------------------------------------------------
# CLI entry-point
# ---------------------------------------------------------------------------


def _build_cli_parser():
    import argparse

    p = argparse.ArgumentParser(
        prog="python -m anvil.lib.probe_freshness",
        description=(
            "Perishable-claim freshness advisory for audit siblings "
            "(issue #863). Purely informational — never gates, never "
            "mutates artifact state."
        ),
    )
    p.add_argument(
        "version_dir",
        help="Path to the <thread>.{N}/ version dir being revised or audited.",
    )
    p.add_argument(
        "--thread-dir",
        default=None,
        help="Thread root holding the critic siblings (default: version_dir's parent).",
    )
    p.add_argument(
        "--max-age-days",
        type=int,
        default=DEFAULT_MAX_AGE_DAYS,
        help=(
            "Default freshness budget in days, overridden per-probe by "
            f"Probe.max_age_days (default: {DEFAULT_MAX_AGE_DAYS})."
        ),
    )
    p.add_argument(
        "--now",
        default=None,
        help="ISO-8601 instant to evaluate against (default: now, UTC).",
    )
    return p


def main(argv: Optional[List[str]] = None) -> int:
    """CLI entry point. Returns the process exit code.

    Always ``0`` on a successful invocation regardless of staleness — this
    tool is advisory and MUST NOT be wired into a pass/fail gate by any
    caller. ``2`` on an invocation error.
    """
    parser = _build_cli_parser()
    args = parser.parse_args(argv)

    now: Optional[datetime] = None
    if args.now is not None:
        now = parse_timestamp(args.now)
        if now is None:
            print(f"error: --now is not an ISO-8601 instant: {args.now!r}", file=sys.stderr)
            return 2

    try:
        report = check_probe_freshness(
            Path(args.version_dir),
            now=now,
            max_age_days=args.max_age_days,
            thread_dir=Path(args.thread_dir) if args.thread_dir else None,
        )
    except OSError as exc:
        print(f"error: {exc}", file=sys.stderr)
        return 2

    print(json.dumps(report.to_json(), indent=2))
    return 0


__all__ = [
    "DEFAULT_MAX_AGE_DAYS",
    "PROBE_LOG_FILENAME",
    "REVIEW_FILENAME",
    "REPORT_CLEAN",
    "REPORT_NEEDS_REPROBE",
    "REPORT_NO_PROBES",
    "STATUS_FRESH",
    "STATUS_NOT_REPROBED",
    "STATUS_STALE",
    "CollectedProbe",
    "ProbeFreshnessReport",
    "ProbeStatus",
    "check_probe_freshness",
    "collect_probes",
    "find_unknown_freshness_siblings",
    "main",
]


if __name__ == "__main__":
    raise SystemExit(main())
