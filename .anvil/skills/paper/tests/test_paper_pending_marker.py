"""End-to-end pending-marker lifecycle coverage for ``anvil:paper`` (issue #844).

Phase 3 of the #841 ``pending_marker`` adoption epic. The core lib primitive
(``anvil/lib/pending_marker.py``) and its wiring into ``paper-review`` (step
4g / step 7), ``paper-revise``, and ``paper-audit`` (step 6b) landed via PR
#847; ``tests/lib/test_pending_marker.py`` covers the primitive thoroughly but
is skill-agnostic. This module is the paper-specific gap: it exercises the full
lifecycle against a small in-repo/temp ``paper`` thread fixture (``main.tex``,
the paper body shape) to prove — for this skill — that

- a thread carrying an active ``[PENDING <source>]`` marker is **surfaced as an
  outstanding dependency** (the specially-resolved ``pending_dependency`` flag
  is visible in the aggregate),
- **without a dimension penalty** (the pending review contributes no score to
  the /44 total; the content total is unchanged),
- **without forcing ``Verdict.BLOCK``** (``convergence.blocking_critical_flags``
  filters the pending flag out, so a passing paper still ADVANCEs), yet
- the marker **holds the READY / AUDITED terminal transition**
  (``convergence.has_pending_dependency_flag`` is True — the separate terminal
  gate ``paper-review`` step 7 / ``paper-audit`` step 6b enforce), and
- **resolving the marker** (replacing it with the real value) lets READY be
  reached (no pending flag, terminal gate clears).

Plus a doc-coverage class pinning the SKILL.md state-table clause (the other
half of #844): the READY / AUDITED rows must name the pending-marker gate as a
condition distinct from "no unresolved critical flag" (since
``pending_dependency`` is deliberately excluded from
``convergence.blocking_critical_flags``).

This reuses ``anvil/lib/pending_marker.py`` directly against a temp fixture — it
does NOT require a full ``paper-review`` / ``paper-audit`` agent run. Distinct
filename per the #58 packaging convention; the ``paper/tests`` dir carries an
``__init__.py`` chain. Runs under ``pytest anvil/skills/paper/tests/`` or
``python -m unittest discover anvil/skills/paper/tests/``.
"""

from __future__ import annotations

import sys
import tempfile
import unittest
from pathlib import Path

_REPO_ROOT = Path(__file__).resolve().parents[4]
if str(_REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(_REPO_ROOT))

from anvil.lib.convergence import (  # noqa: E402
    PENDING_DEPENDENCY_FLAG_TYPE,
    blocking_critical_flags,
    has_pending_dependency_flag,
)
from anvil.lib.critics import aggregate, compute_verdict, discover_critics  # noqa: E402
from anvil.lib.pending_marker import (  # noqa: E402
    PENDING_SUFFIX,
    check_pending_markers,
    write_review_dir,
)
from anvil.lib.review_schema import Kind, Review, Score, Verdict  # noqa: E402

_SKILL_ROOT = Path(__file__).resolve().parent.parent

# The paper body carrying one honest, load-bearing pending measurement.
_BODY_WITH_MARKER = r"""\documentclass{anvil-paper}
\begin{document}
\section{Results}
The model reaches [PENDING benchmark-run-2024-11] accuracy on the held-out set,
a clear improvement over the prior state of the art.
\end{document}
"""

# The same body after the pending value genuinely resolved.
_BODY_RESOLVED = r"""\documentclass{anvil-paper}
\begin{document}
\section{Results}
The model reaches 87.3\% accuracy on the held-out set,
a clear improvement over the prior state of the art.
\end{document}
"""


def _content_review(version_dir: str, total: int = 40) -> Review:
    """A passing paper content review (no critical flags, >=35/44).

    A single aggregate dimension scored ``total``/44 stands in for a full
    9-dimension scoring pass — the pending-marker lifecycle does not depend on
    the dimension breakdown, only on the total clearing the /44 advance
    threshold and there being no ordinary critical flag.
    """
    return Review(
        schema_version="1",
        kind=Kind.JUDGMENT,
        version_dir=version_dir,
        critic_id="review",
        scores=[
            Score(
                dimension="content",
                score=total,
                max=44,
                justification="Passing content review for the lifecycle fixture.",
            )
        ],
        findings=[],
        critical_flags=[],
    )


class TestPaperPendingMarkerLifecycle(unittest.TestCase):
    """draft (marker present) -> review -> resolve -> READY, over a temp thread."""

    def _make_thread(self, tmp: Path, body: str) -> Path:
        """Create ``<tmp>/mythread/mythread.1/main.tex`` and return the version dir."""
        version_dir = tmp / "mythread" / "mythread.1"
        version_dir.mkdir(parents=True)
        (version_dir / "main.tex").write_text(body, encoding="utf-8")
        return version_dir

    def test_active_marker_surfaced_as_outstanding_dependency(self):
        with tempfile.TemporaryDirectory() as td:
            version_dir = self._make_thread(Path(td), _BODY_WITH_MARKER)
            result = check_pending_markers(version_dir)

            # The marker is detected as an active outstanding dependency.
            self.assertFalse(result.passed())
            self.assertEqual(result.outstanding_sources, ["benchmark-run-2024-11"])
            self.assertEqual(len(result.active_markers), 1)

            # It surfaces as exactly one specially-resolved pending_dependency flag.
            flags = result.to_critical_flags()
            self.assertEqual(len(flags), 1)
            self.assertEqual(flags[0].type, PENDING_DEPENDENCY_FLAG_TYPE)

    def test_marker_incurs_no_dimension_penalty(self):
        with tempfile.TemporaryDirectory() as td:
            version_dir = self._make_thread(Path(td), _BODY_WITH_MARKER)
            result = check_pending_markers(version_dir)
            pending_review = result.to_review(version_dir=version_dir.name)

            # The pending review's only Score is the no-dim placeholder (score=None):
            # it contributes 0 to the /44 total, so a paper scored 40/44 stays 40/44.
            self.assertTrue(all(s.score is None for s in pending_review.scores))

            agg = aggregate([_content_review(version_dir.name, total=40), pending_review])
            self.assertEqual(agg.total, 40)

    def test_pending_marker_does_not_force_block_but_holds_ready(self):
        with tempfile.TemporaryDirectory() as td:
            version_dir = self._make_thread(Path(td), _BODY_WITH_MARKER)
            result = check_pending_markers(version_dir)
            pending_review = result.to_review(version_dir=version_dir.name)
            agg = aggregate([_content_review(version_dir.name, total=40), pending_review])

            # The pending flag is VISIBLE in the aggregate ...
            self.assertTrue(has_pending_dependency_flag(agg.critical_flags))
            # ... but is filtered out of the BLOCK trigger, so a passing paper
            # still ADVANCEs on the verdict path (paper-review step 7).
            self.assertEqual(blocking_critical_flags(agg.critical_flags), [])
            self.assertEqual(compute_verdict(agg, threshold=35), Verdict.ADVANCE)

            # The SEPARATE terminal gate holds READY while the marker remains:
            # advance == true but has_pending_dependency_flag == true.
            advance = compute_verdict(agg, threshold=35) == Verdict.ADVANCE
            ready = advance and not has_pending_dependency_flag(agg.critical_flags)
            self.assertTrue(advance)
            self.assertFalse(ready)

    def test_resolving_marker_allows_ready(self):
        with tempfile.TemporaryDirectory() as td:
            tmp = Path(td)
            version_dir = self._make_thread(tmp, _BODY_WITH_MARKER)

            # Resolve: the drafter replaces the marker with the real value.
            (version_dir / "main.tex").write_text(_BODY_RESOLVED, encoding="utf-8")

            result = check_pending_markers(version_dir)
            self.assertTrue(result.passed())
            self.assertEqual(result.outstanding_sources, [])
            self.assertEqual(result.to_critical_flags(), [])

            pending_review = result.to_review(version_dir=version_dir.name)
            agg = aggregate([_content_review(version_dir.name, total=40), pending_review])

            # No pending flag now, so the terminal gate clears: READY is reachable.
            self.assertFalse(has_pending_dependency_flag(agg.critical_flags))
            advance = compute_verdict(agg, threshold=35) == Verdict.ADVANCE
            ready = advance and not has_pending_dependency_flag(agg.critical_flags)
            self.assertTrue(ready)

    def test_written_sidecar_is_auto_discovered(self):
        with tempfile.TemporaryDirectory() as td:
            version_dir = self._make_thread(Path(td), _BODY_WITH_MARKER)
            result = check_pending_markers(version_dir)
            out = write_review_dir(version_dir, result)

            # The sidecar lands at <thread>.{N}.pending/_review.json ...
            self.assertTrue(out.is_file())
            self.assertEqual(out.parent.name, f"{version_dir.name}.{PENDING_SUFFIX}")

            # ... and critics.discover_critics picks up the sibling dir with no
            # aggregator change (discovery is dir-level, not file-level).
            discovered = discover_critics(version_dir)
            self.assertIn(out.parent, discovered)


class TestPaperSkillStateTableClause(unittest.TestCase):
    """SKILL.md READY/AUDITED rows name the pending-marker gate (issue #844)."""

    def setUp(self):
        self.skill = (_SKILL_ROOT / "SKILL.md").read_text(encoding="utf-8")

    def test_ready_and_audited_rows_name_the_pending_gate(self):
        # Both terminal rows must mention the [PENDING <source>] marker gate.
        self.assertEqual(
            self.skill.count("no unresolved `[PENDING <source>]` marker"), 2
        )

    def test_gate_is_distinct_from_no_critical_flag(self):
        # The clause must explain the gate is NOT implied by the critical-flag
        # clause (pending_dependency is filtered out of blocking_critical_flags).
        self.assertIn("blocking_critical_flags", self.skill)
        self.assertIn("pending_dependency", self.skill)
        # The no-fabrication instruction is carried into the doc.
        self.assertIn("never fabricate", self.skill.lower())


if __name__ == "__main__":
    unittest.main()
