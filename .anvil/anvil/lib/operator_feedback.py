"""Operator-feedback critic sibling for post-READY defects (issue #1322).

The problem
-----------

The lifecycle reserves one gate for a human: the operator's read-through
of a thread the critics already converged on (READY / AUDITED). When
that read-through finds a defect, the reviser had no documented input to
receive it. ``paper-revise`` step 4 exits early once the latest review
advanced with no critical flag in ``.review/`` or ``.audit/``, so the only
workarounds were editing critic output (breaking sidecar immutability) or
bumping ``max_iterations`` and hand-writing a critic sibling in an
undocumented shape. A BRIEF amendment made after READY is detected by
``evidence_drift`` only as an advisory note, with the same dead end.

The path
--------

The operator writes one more critic sibling at the current version,
``<thread>.{N}.operator/``, using the existing schema unchanged:

- ``_review.json``: an ordinary :class:`~anvil.lib.review_schema.Review`
  with ``kind: judgment``, ``critic_id: "operator"``, ``verdict: BLOCK``,
  and one ``CriticalFlag`` per defect. ``critic_id`` and
  ``CriticalFlag.type`` are free-form, so no schema-version bump is
  needed. The conventional flag types are ``operator_defect`` (default)
  and ``brief_amendment`` (the BRIEF changed after READY and the text
  must follow it); the CLI's ``--flag`` recognizes only those two as a
  ``type:`` prefix and refuses ``pending_dependency:`` (non-blocking, so
  it would silently do nothing). The single ``Score`` is ``score=None``: the operator
  owns no rubric dimension and the /44 total is unchanged.
- ``_meta.json``: ``scorecard_kind: "human-verdict"``, the same template
  the reviewer's own sibling uses.
- ``operator.md``: the operator's free-text notes for the reviser.

Because the tag is a single segment, ``critics.discover_critics`` picks
the sibling up with no aggregator change, and because its flags are
ordinary (not ``pending_dependency``) they force ``Verdict.BLOCK`` in the
aggregate exactly like a ``.review`` or ``.audit`` flag.

``paper-revise`` step 4 consults :func:`revise_required_by_operator`
(or ``python -m anvil.lib.operator_feedback check``) as a third input
alongside ``.review/`` and ``.audit/``: blocking operator flags require
another revision even when the review advanced. The step 3 iteration cap
allows exactly one pass beyond ``max_iterations`` for a version whose
operator sibling carries a blocking flag. That is safe from runaway loops
because each extra pass needs a human to write a new sibling.

The sibling is **immutable** once written, like every critic sibling: a
second write to the same version raises ``FileExistsError`` (CLI exit
``2``). Feedback on the next version goes in that version's own sibling.

CLI
---

``python -m anvil.lib.operator_feedback write <version_dir> --flag
"[TYPE:] justification" [--flag ...] [--notes TEXT]``

``python -m anvil.lib.operator_feedback check <version_dir>`` prints a
JSON summary. Exit codes: ``0`` no blocking operator flag, ``1`` blocking
operator flag(s) present (revision required), ``2`` invocation error.
"""

from __future__ import annotations

import json
import re
import sys
from datetime import datetime, timezone
from pathlib import Path
from typing import List, Optional, Sequence

from anvil.lib.convergence import PENDING_DEPENDENCY_FLAG_TYPE, blocking_critical_flags
from anvil.lib.review_schema import CriticalFlag, Finding, Kind, Review, Score, Verdict
from anvil.lib.sidecar import cleanup_one_staging, staged_sidecar

CRITIC_ID = "operator"
"""``_review.json.critic_id`` for the operator sibling."""

OPERATOR_SUFFIX = "operator"
"""Sidecar dir tag: ``<thread>.{N}.operator/``."""

DEFAULT_FLAG_TYPE = "operator_defect"
"""Flag type for a defect found on the operator's read-through."""

BRIEF_AMENDMENT_FLAG_TYPE = "brief_amendment"
"""Flag type for a BRIEF change after READY that the text must follow."""

KNOWN_FLAG_TYPES = (DEFAULT_FLAG_TYPE, BRIEF_AMENDMENT_FLAG_TYPE)
"""Flag-type prefixes ``--flag`` recognizes; any other ``word:`` prefix is
kept as part of the justification (typed ``operator_defect``)."""

NOTES_FILENAME = "operator.md"
REQUIRED_FILES = ("_review.json", "_meta.json", NOTES_FILENAME)

_FLAG_TYPE_RE = re.compile(r"^\s*([a-z][a-z0-9_\-]*)\s*:\s*(.+)$", re.DOTALL)


def operator_dir(version_dir: Path) -> Path:
    """``<version_dir>.operator/`` for ``version_dir``."""
    version_dir = Path(version_dir)
    return version_dir.parent / f"{version_dir.name}.{OPERATOR_SUFFIX}"


def build_operator_review(
    version_dir_name: str,
    flags: Sequence[CriticalFlag],
    *,
    findings: Sequence[Finding] = (),
) -> Review:
    """Build the operator ``Review`` (``kind: judgment``).

    ``verdict`` is ``BLOCK`` when any flag is blocking, else ``None`` (the
    aggregator recomputes the verdict in any case).
    """
    flags = list(flags)
    return Review(
        schema_version="1",
        kind=Kind.JUDGMENT,
        version_dir=version_dir_name,
        critic_id=CRITIC_ID,
        scores=[
            Score(
                dimension="operator_read_through",
                score=None,
                max=1,
                justification=(
                    "Operator read-through after the critics converged; owns "
                    "no rubric dimension. Critical flags carry the feedback."
                ),
            )
        ],
        findings=list(findings),
        critical_flags=flags,
        verdict=Verdict.BLOCK if blocking_critical_flags(flags) else None,
    )


def _now() -> str:
    return datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")


def _render_notes(review: Review, notes: Optional[str]) -> str:
    lines = [f"# Operator feedback for {review.version_dir}", ""]
    if notes:
        lines += [notes.strip(), ""]
    if review.critical_flags:
        lines += ["## Critical flags (require another revise pass)", ""]
        for f in review.critical_flags:
            span = f" ({f.evidence_span})" if f.evidence_span else ""
            lines.append(f"- **{f.type}**{span}: {f.justification}")
        lines.append("")
    return "\n".join(lines)


def write_operator_review(
    version_dir: Path,
    review: Review,
    *,
    notes: Optional[str] = None,
) -> Path:
    """Atomically write ``<version_dir>.operator/`` and return its path.

    Uses ``staged_sidecar`` (issue #350). Raises ``FileExistsError`` when
    the sibling already exists: operator feedback is immutable once
    written, like every critic sibling.
    """
    final = operator_dir(version_dir)
    if final.exists():
        raise FileExistsError(
            f"operator_feedback: {final} already exists; critic siblings are "
            f"immutable. Put further feedback on the next version's sibling."
        )
    cleanup_one_staging(final)
    started = _now()
    with staged_sidecar(final, REQUIRED_FILES) as staging:
        (staging / "_review.json").write_text(
            json.dumps(review.model_dump(mode="json"), indent=2) + "\n",
            encoding="utf-8",
        )
        (staging / NOTES_FILENAME).write_text(_render_notes(review, notes), encoding="utf-8")
        meta = {
            "critic": CRITIC_ID,
            "scorecard_kind": "human-verdict",
            "started": started,
            "finished": _now(),
            "model": "human",
            "schema_version": "1",
        }
        (staging / "_meta.json").write_text(json.dumps(meta, indent=2) + "\n", encoding="utf-8")
    return final


def operator_blocking_flags(version_dir: Path) -> List[CriticalFlag]:
    """Blocking critical flags in ``<version_dir>.operator/`` (``[]`` if absent).

    ``pending_dependency``-typed flags are filtered out, as everywhere else
    (``convergence.blocking_critical_flags``).
    """
    d = operator_dir(version_dir)
    if not (d / "_review.json").is_file():
        return []
    from anvil.lib.critics import load_review

    review = load_review(d)
    return [f for f in blocking_critical_flags(review.critical_flags) if isinstance(f, CriticalFlag)]


def revise_required_by_operator(version_dir: Path) -> bool:
    """``True`` when the operator sibling requires another revise pass."""
    return bool(operator_blocking_flags(version_dir))


def _parse_flag(spec: str) -> CriticalFlag:
    """Parse one ``--flag`` value into a blocking :class:`CriticalFlag`.

    Only the known types (:data:`KNOWN_FLAG_TYPES`) are honoured as a
    ``type:`` prefix; ``"abstract: overclaims the bound"`` stays an
    ``operator_defect`` with the full text as justification. A
    ``pending_dependency:`` prefix raises :class:`ValueError`: that type is
    non-blocking everywhere (``check`` would report ``revise_required:
    false``), so the operator's feedback would silently do nothing.
    """
    m = _FLAG_TYPE_RE.match(spec)
    if m and m.group(1) == PENDING_DEPENDENCY_FLAG_TYPE:
        raise ValueError(
            f"--flag type {PENDING_DEPENDENCY_FLAG_TYPE!r} is non-blocking and "
            f"would not reopen the thread (check reports revise_required: "
            f"false). Use '{DEFAULT_FLAG_TYPE}:' or "
            f"'{BRIEF_AMENDMENT_FLAG_TYPE}:' (or no prefix) for feedback that "
            f"must be revised."
        )
    if m and m.group(1) in KNOWN_FLAG_TYPES:
        return CriticalFlag(type=m.group(1), justification=m.group(2).strip())
    return CriticalFlag(type=DEFAULT_FLAG_TYPE, justification=spec.strip())


def _build_cli_parser():
    import argparse

    p = argparse.ArgumentParser(
        prog="python -m anvil.lib.operator_feedback",
        description=(
            "Write or check the <thread>.{N}.operator/ critic sibling that "
            "feeds an operator's post-READY read-through back into revise."
        ),
    )
    sub = p.add_subparsers(dest="cmd", required=True)
    w = sub.add_parser("write", help="Write <version_dir>.operator/ (immutable).")
    w.add_argument("version_dir")
    w.add_argument(
        "--flag",
        action="append",
        required=True,
        metavar="[TYPE:] JUSTIFICATION",
        help=(
            f"One critical flag per use. A leading "
            f"'{BRIEF_AMENDMENT_FLAG_TYPE}:' or '{DEFAULT_FLAG_TYPE}:' sets "
            f"the flag type; otherwise '{DEFAULT_FLAG_TYPE}' (any other "
            f"'word:' prefix stays in the text). "
            f"'{PENDING_DEPENDENCY_FLAG_TYPE}:' is refused (exit 2): it is "
            f"non-blocking and would not reopen the thread."
        ),
    )
    w.add_argument("--notes", default=None, help="Free-text notes for operator.md.")
    c = sub.add_parser("check", help="Exit 1 when blocking operator flags exist.")
    c.add_argument("version_dir")
    return p


def main(argv: Optional[List[str]] = None) -> int:
    args = _build_cli_parser().parse_args(argv)
    version_dir = Path(args.version_dir)
    if not version_dir.is_dir():
        print(f"error: version_dir {version_dir} does not exist", file=sys.stderr)
        return 2
    if args.cmd == "write":
        try:
            flags = [_parse_flag(s) for s in args.flag]
        except ValueError as exc:
            print(f"error: {exc}", file=sys.stderr)
            return 2
        review = build_operator_review(version_dir.name, flags)
        try:
            out = write_operator_review(version_dir, review, notes=args.notes)
        except FileExistsError as exc:
            print(f"error: {exc}", file=sys.stderr)
            return 2
        print(f"wrote {out}", file=sys.stderr)
        return 0
    flags = operator_blocking_flags(version_dir)
    print(
        json.dumps(
            {
                "version_dir": version_dir.name,
                "operator_dir": operator_dir(version_dir).name,
                "revise_required": bool(flags),
                "blocking_flags": [f.model_dump(mode="json") for f in flags],
            },
            indent=2,
        )
    )
    return 1 if flags else 0


__all__ = [
    "CRITIC_ID",
    "OPERATOR_SUFFIX",
    "DEFAULT_FLAG_TYPE",
    "BRIEF_AMENDMENT_FLAG_TYPE",
    "KNOWN_FLAG_TYPES",
    "operator_dir",
    "build_operator_review",
    "write_operator_review",
    "operator_blocking_flags",
    "revise_required_by_operator",
    "main",
]


if __name__ == "__main__":
    raise SystemExit(main())
