"""Doc-coverage tests for the ``anvil:paper`` evidence-drift advisory (issue #857).

These are **substring-assertion** tests over the shipped command files —
the same pattern as ``test_paper_command_coverage.py``'s
``NEVER-VISION-CHECKED`` coverage. They read the command markdown as text
and pin the evidence-drift wiring the #857 curation locked:

- ``paper-draft.md`` step 9b and ``paper-revise.md`` step 11b invoke
  ``anvil.lib.evidence_drift record`` to snapshot ``BRIEF.md``/``refs/**``
  mtimes into ``metadata.evidence_snapshot`` at draft/revise completion.
- ``paper-review.md`` documents the snapshot as an ``## Inputs`` entry,
  step 4h invokes ``anvil.lib.evidence_drift check``, and step 9 adds an
  advisory "Evidence drift" note to ``verdict.md`` — explicitly NOT
  gating ``advance``, score, or the terminal-state transition.
- ``paper/SKILL.md`` documents the mechanism, mirroring the
  ``NEVER-VISION-CHECKED`` documentation precedent.
- The bootstrap case (no recorded snapshot) is documented as "not
  drifted", never a false positive.

The module filename is deliberately distinct (``test_paper_evidence_drift``)
per the #58 packaging convention so it never collides with another skill's
``test_*`` module under pytest's default import mode. The tests read files
by path only — no cross-module imports — so no ``__init__.py`` is required
(matching the existing ``paper/tests`` layout).

Runs under ``pytest anvil/skills/paper/tests/`` or
``python -m unittest discover anvil/skills/paper/tests/``.
"""

from __future__ import annotations

import unittest
from pathlib import Path

from anvil.lib.testing import read_text

_SKILL_ROOT = Path(__file__).resolve().parent.parent

_read = lambda rel: read_text(_SKILL_ROOT / rel)


class TestPaperDraftRecordsSnapshot(unittest.TestCase):
    """paper-draft.md step 9b records the evidence-drift baseline."""

    def setUp(self):
        self.text = _read("commands/paper-draft.md")

    def test_step_invokes_evidence_drift_record(self):
        self.assertIn("anvil.lib.evidence_drift record", self.text)
        self.assertIn("evidence-drift baseline", self.text)

    def test_progress_json_snippet_documents_evidence_snapshot(self):
        self.assertIn("evidence_snapshot", self.text)

    def test_tooling_absent_is_fail_open(self):
        # The step must not fail the draft when uv is unavailable.
        idx = self.text.index("Record the evidence-drift baseline")
        window = self.text[idx : idx + 900]
        self.assertIn("skip this step", window)


class TestPaperReviseRecordsSnapshot(unittest.TestCase):
    """paper-revise.md step 11b re-baselines the evidence-drift snapshot."""

    def setUp(self):
        self.text = _read("commands/paper-revise.md")

    def test_step_invokes_evidence_drift_record(self):
        self.assertIn("anvil.lib.evidence_drift record", self.text)
        self.assertIn("evidence-drift baseline", self.text)

    def test_progress_json_snippet_documents_evidence_snapshot(self):
        self.assertIn("evidence_snapshot", self.text)


class TestPaperReviewChecksDrift(unittest.TestCase):
    """paper-review.md step 4h checks + verdict.md surfaces drift."""

    def setUp(self):
        self.text = _read("commands/paper-review.md")

    def test_inputs_documents_evidence_snapshot(self):
        self.assertIn("Evidence-drift snapshot", self.text)
        self.assertIn("metadata.evidence_snapshot", self.text)

    def test_step_invokes_evidence_drift_check(self):
        self.assertIn("anvil.lib.evidence_drift check", self.text)

    def test_check_is_never_routed_through_critical_flag_machinery(self):
        idx = self.text.index("Check BRIEF/refs evidence drift")
        window = self.text[idx : idx + 1200]
        self.assertIn("NEVER routed through", window)
        self.assertIn("CriticalFlag", window)

    def test_verdict_note_is_advisory_only(self):
        idx = self.text.index("Evidence drift (conditional")
        window = self.text[idx : idx + 900]
        self.assertIn("advisory only", window)
        self.assertIn("does NOT change `advance`", window)
        self.assertIn("does NOT gate the terminal transition", window)

    def test_bootstrap_case_documented(self):
        self.assertIn("NO-SNAPSHOT", self.text)


class TestSkillDocumentsEvidenceDrift(unittest.TestCase):
    """paper/SKILL.md documents the mechanism (mirrors NEVER-VISION-CHECKED)."""

    def setUp(self):
        self.skill = _read("SKILL.md")

    def test_skill_names_evidence_drift(self):
        self.assertIn("EVIDENCE-DRIFT", self.skill)
        self.assertIn("issue #857", self.skill)

    def test_skill_documents_advisory_posture(self):
        self.assertIn("purely advisory", self.skill.lower().replace("**", ""))
