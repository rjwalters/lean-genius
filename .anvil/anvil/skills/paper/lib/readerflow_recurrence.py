"""Recurrence measure for the ``paper-review`` reader-flow lens (issue #1419).

The lens (step 4j) is a fresh read, so its raw finding count does not fall on
a flow-revised version: the #1396 acceptance run saw 42 -> 31, 36 -> 39 and
41 -> 42 findings on three revised papers. What does move is how many of the
*previous* version's findings come back. This module computes that share:

    R = recurring / prior_total

``prior_total`` counts the ``major`` + ``minor`` findings of the previous
version's ``.readerflow/_review.json`` (``nit`` excluded). A prior finding
*recurs* when a current finding matches it, one-to-one (a current finding
satisfies at most one prior finding). New current findings are never part of
``R``.

Match rule, on whitespace- and case-folded ``evidence_span``:

1. ``difflib.SequenceMatcher`` ratio >= ``SIMILARITY_THRESHOLD``; else
2. same ``dimension`` and one span contained in the other.

Findings without a span cannot match. Advisory only: the result is recorded
by ``paper-review`` and never feeds the total, dim 7 or the class-1 cap.

The lens is briefed with no prior review, so this runs in the scoring pass
after the lens returns, never inside the subagent.
"""

from __future__ import annotations

import difflib
import re
from typing import Any, Mapping, Optional, Sequence

SIMILARITY_THRESHOLD = 0.8
COUNTED_SEVERITIES = frozenset({"major", "minor"})

_WS = re.compile(r"\s+")


def _get(finding: Any, key: str) -> Optional[str]:
    if isinstance(finding, Mapping):
        return finding.get(key)
    return getattr(finding, key, None)


def _norm(span: Optional[str]) -> str:
    return _WS.sub(" ", span or "").strip().casefold()


def _matches(prior: Any, current: Any) -> bool:
    a, b = _norm(_get(prior, "evidence_span")), _norm(_get(current, "evidence_span"))
    if not a or not b:
        return False
    if difflib.SequenceMatcher(None, a, b).ratio() >= SIMILARITY_THRESHOLD:
        return True
    dim_a, dim_b = _get(prior, "dimension"), _get(current, "dimension")
    return dim_a == dim_b and (a in b or b in a)


def recurrence(
    prior_findings: Sequence[Any], current_findings: Sequence[Any]
) -> Optional[dict]:
    """Return ``{prior_total, recurring, share}``, or ``None`` with no prior.

    ``None`` when the previous sidecar has no ``major``/``minor`` finding, so
    the caller omits the measure instead of reporting 0/0. ``share`` is
    rounded to 3 places.
    """
    prior = [f for f in prior_findings if _get(f, "severity") in COUNTED_SEVERITIES]
    if not prior:
        return None
    unused = list(current_findings)
    recurring = 0
    for p in prior:
        for i, c in enumerate(unused):
            if _matches(p, c):
                del unused[i]
                recurring += 1
                break
    return {
        "prior_total": len(prior),
        "recurring": recurring,
        "share": round(recurring / len(prior), 3),
    }
