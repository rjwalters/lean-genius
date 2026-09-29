"""Doc-coverage tests for the ``anvil:paper`` subject voice tier (issue #613).

These are **substring-assertion** tests over the shipped command files —
the same pattern as ``anvil/skills/essay/tests/test_essay_skeleton.py``
(the PR #604 pilot). They read the command markdown as text and pin the
subject-voice-tier wiring the #613 curation locked:

- ``paper-draft.md`` step 3c invokes ``resolve_subject_voice_docs`` and
  records ``metadata.subject_voice_exemplars`` (per-subject transcript map).
- ``paper-review.md`` step 4e resolves the tier; the dim 7 sub-pass, the
  ``subject_voice_grounding`` ``_summary.md`` block, and the conditional
  Misattribution critical flag (``≥2 subjects``) are all documented.
- The rubric stamps stay ``anvil-pub-v2`` / 44 / 35 — the flag is
  **additive**, not a rubric-total change.
- ``paper-revise.md`` is DELIBERATELY out of scope (AC12): it carries no
  subject voice tier wiring, and no ``subject_voice_grounding`` block.
- The byte-identical-when-absent contract is documented in both files.

Issue #732 extends this module with two more coverage classes:

- ``paper-revise.md`` now loads the ad hoc skill-local
  ``.anvil/skills/paper/voice.md`` override, symmetric with
  ``paper-draft.md`` (bug a) — while still staying out of the #613
  **subject** voice tier.
- ``rubric.md`` dim 7/9 and ``paper-review.md``'s D7/D9 guidance name the
  self-flattering / virtue-signaling adjective class as a **default**
  AI-tell check (bug b), fired for every consumer with no ``voice.md``
  required, with the STYLE_GUIDE semantic-work exception preserved and no
  rubric-total / weight change.

The module filename is deliberately distinct (``test_paper_command_coverage``)
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
_REPO_ROOT = _SKILL_ROOT.parent.parent.parent

RUBRIC_ID = "anvil-pub-v2"

_read = lambda rel: read_text(_SKILL_ROOT / rel)


def _read_repo(rel: str) -> str:
    return (_REPO_ROOT / rel).read_text(encoding="utf-8")


class TestPubDraftSubjectTier(unittest.TestCase):
    """paper-draft.md step 3c: drafter contract (AC1)."""

    def setUp(self):
        self.text = _read("commands/paper-draft.md")

    def test_step_3c_present(self):
        self.assertIn("3c.", self.text)

    def test_invokes_resolver(self):
        self.assertIn("resolve_subject_voice_docs", self.text)
        self.assertIn("voice_grounding.md", self.text)
        self.assertIn('"Subject voice tier"', self.text)

    def test_records_per_subject_exemplar_map(self):
        self.assertIn("subject_voice_exemplars", self.text)
        # The per-subject map shape is documented.
        self.assertIn('{"<name>": ["<transcript path>"', self.text)

    def test_byte_identical_when_absent(self):
        self.assertIn("no `subjects` list", self.text)
        self.assertIn("Byte-identical to pre-#613", self.text)

    def test_declared_but_missing_surfaces_major(self):
        self.assertIn("missing: true", self.text)
        self.assertIn("never raises", self.text)


class TestPubReviewSubjectTier(unittest.TestCase):
    """paper-review.md steps 4e / 5 / 6 / 10 (AC2–AC5)."""

    def setUp(self):
        self.text = _read("commands/paper-review.md")

    def test_step_4e_resolves_and_caches(self):
        self.assertIn("4e.", self.text)
        self.assertIn("resolve_subject_voice_docs", self.text)

    def test_dim_7_sub_pass_folds_in(self):
        # Paper folds the per-subject pass into dim 7 (Prose & structural
        # quality) — paper has no owned voice dimension.
        self.assertIn("Prose & structural quality (D7)", self.text)
        self.assertIn(
            "subject voice tier active — <N> subject(s) scored against "
            "transcript corpora, subject-voice deductions must quote transcripts",
            self.text,
        )
        # Quote-the-transcript deduction discipline.
        self.assertIn("MUST quote the transcript", self.text)
        self.assertIn("convergence-with-Claude", self.text)

    def test_misattribution_flag_conditional_on_two_subjects(self):
        self.assertIn("Misattribution", self.text)
        self.assertIn("≥2 subjects", self.text)
        self.assertIn("voice-identity failure", self.text)
        self.assertIn("cannot fire", self.text)

    def test_summary_block_name_and_shape(self):
        self.assertIn("subject_voice_grounding", self.text)
        self.assertIn("corpus_files_loaded", self.text)
        self.assertIn("voice_doc_loaded", self.text)
        self.assertIn("exemplars_quoted", self.text)
        self.assertIn("lines_flagged", self.text)
        # NOT emitted when inactive — no ran:false entry.
        self.assertIn("NOT emitted at all", self.text)

    def test_rubric_stamps_unchanged(self):
        # The flag is additive — rubric total/threshold do not move.
        self.assertIn(f'rubric_id: "{RUBRIC_ID}"', self.text)
        self.assertIn("rubric_total: 44", self.text)
        self.assertIn("advance_threshold: 35", self.text)
        # The additive-not-total-change promise is stated explicitly.
        self.assertIn("does NOT change the rubric total", self.text)


class TestPubReviseNotWired(unittest.TestCase):
    """paper-revise.md MUST NOT receive subject-tier wiring (AC12)."""

    def setUp(self):
        self.text = _read("commands/paper-revise.md")

    def test_no_subject_voice_resolver(self):
        self.assertNotIn("resolve_subject_voice_docs", self.text)

    def test_no_subject_voice_grounding_block(self):
        self.assertNotIn("subject_voice_grounding", self.text)

    def test_no_subject_voice_exemplars(self):
        self.assertNotIn("subject_voice_exemplars", self.text)


class TestPubReviseVoiceOverride(unittest.TestCase):
    """paper-revise.md loads the skill-local voice.md, symmetric with
    paper-draft.md (issue #732 bug a)."""

    def setUp(self):
        self.revise = _read("commands/paper-revise.md")
        self.draft = _read("commands/paper-draft.md")

    def test_draft_still_loads_voice_md(self):
        # Guard the symmetry anchor — draft has always loaded it.
        self.assertIn(".anvil/skills/paper/voice.md", self.draft)

    def test_revise_now_loads_voice_md(self):
        self.assertIn(".anvil/skills/paper/voice.md", self.revise)
        self.assertIn("Voice and style overrides", self.revise)

    def test_revise_voice_hook_is_ad_hoc_not_subject_tier(self):
        # Bug (a) is the simple skill-local override, NOT the #613 subject
        # voice tier — the deliberate out-of-scope contract still holds.
        self.assertNotIn("resolve_subject_voice_docs", self.revise)
        self.assertNotIn("subject_voice_grounding", self.revise)
        self.assertNotIn("subject_voice_exemplars", self.revise)


class TestPubDefaultAiTellCheck(unittest.TestCase):
    """Default self-flattering / virtue-signaling adjective check in the
    reviewer's D7/D9 guidance and the rubric rows (issue #732 bug b)."""

    def setUp(self):
        self.rubric = _read("rubric.md")
        self.review = _read("commands/paper-review.md")

    def test_rubric_dim7_names_the_tell_class(self):
        self.assertIn("self-flattering", self.rubric)
        self.assertIn("virtue-signaling", self.rubric)
        # Semantic-work exception preserved.
        self.assertIn("semantic work", self.rubric)

    def test_review_d7_default_check_no_voice_md_required(self):
        self.assertIn("default AI-tell check", self.review)
        self.assertIn("self-flattering", self.review)
        # Fires without a hand-authored voice.md.
        self.assertIn("does not require a hand-authored", self.review)

    def test_review_d9_mirrors_the_check(self):
        # The economy dimension also names the class + exception.
        self.assertIn("D9 economy failure", self.review)
        self.assertIn("semantic-work exception", self.review)

    def test_no_rubric_total_or_weight_change(self):
        # Additive scoring guidance — the /44 total and D7/D9 weights hold.
        self.assertIn("summing to **44**", self.rubric)
        self.assertIn("Advance threshold: ≥35", self.rubric)
        self.assertIn("| 7 | **Prose & structural quality** | 4 |", self.rubric)
        self.assertIn("| 9 | **Rhetorical economy** | 4 |", self.rubric)


class TestStructuralImportanceAnnouncementTellClass(unittest.TestCase):
    """The "load-bearing" AI-tell class (issue #997): STYLE_GUIDE §3 names
    it, and paper/rubric.md + paper-review.md's D7/D9 guidance extend the
    default AI-tell check to cover it, mirroring the self-flattering /
    virtue-signaling adjective class wired for issue #732."""

    def setUp(self):
        self.style_guide = _read_repo("anvil/templates/voice/STYLE_GUIDE.template.md")
        self.rubric = _read("rubric.md")
        self.review = _read("commands/paper-review.md")

    def test_style_guide_names_the_class_with_marker_terms(self):
        self.assertIn("structural-importance announcement", self.style_guide.lower())
        self.assertIn("load-bearing", self.style_guide)
        self.assertIn("load bearing", self.style_guide)
        # Semantic-work / engineering-referent exception carried over.
        self.assertIn("exempt", self.style_guide)

    def test_rubric_dim7_and_dim9_name_the_class(self):
        self.assertIn("structural-importance announcement", self.rubric.lower())
        self.assertIn("| 7 | **Prose & structural quality** | 4 |", self.rubric)
        self.assertIn("| 9 | **Rhetorical economy** | 4 |", self.rubric)

    def test_rubric_dim9_boilerplate_question_no_longer_says_load_bearing(self):
        # The literal "Is every paragraph load-bearing?" boilerplate is gone;
        # "load-bearing" only survives elsewhere in dim 9's prose (naming the
        # tell class itself and the pre-existing semantic-work exception).
        self.assertNotIn("Is every paragraph load-bearing?", self.rubric)

    def test_review_d7_and_d9_name_the_class(self):
        self.assertIn("structural-importance announcement", self.review.lower())
        self.assertIn("default AI-tell check", self.review)
        self.assertIn("D9 economy failure", self.review)

    def test_replacement_avoids_reserved_leak_words(self):
        # "earns its place" / "doing real work" are reserved for a future
        # corpus check (per issue #997) — the replacement boilerplate must
        # not reintroduce either as the new AI-tell.
        self.assertNotIn("earns its place", self.rubric)
        self.assertNotIn("doing real work", self.rubric)


class TestPaperVisionRecommendation(unittest.TestCase):
    """paper.md surfaces paper-vision at READY/AUDITED with figures (issue #731).

    The vision critic was wired on the consuming side (paper-revise) but never
    surfaced on the invoking side, so figures could reach terminal AUDITED
    without any visual review. These assertions pin the non-blocking
    orchestrator recommendation (Option 2) — a next-command table row and a
    ``NEVER-VISION-CHECKED`` anomaly bullet — plus the SKILL.md doc sentence.
    """

    def setUp(self):
        self.paper = _read("commands/paper.md")
        self.skill = _read("SKILL.md")

    def test_table_recommends_vision_at_ready_with_figures(self):
        # A READY thread with figures and no vision sibling routes to paper-vision.
        self.assertIn(
            "figures present, no `<thread>.{N}.vision/` sibling at this `N`",
            self.paper,
        )
        self.assertIn("`paper-vision <thread>` (then `paper-audit`)", self.paper)

    def test_table_recommends_vision_at_audited_with_figures(self):
        # AUDITED terminal with unchecked figures still surfaces paper-vision,
        # non-blocking (does not reopen the state machine).
        self.assertIn("terminal — but recommend `paper-vision <thread>`", self.paper)
        self.assertIn("does not reopen the state machine", self.paper)

    def test_no_figures_audited_is_byte_identical_terminal(self):
        # Text-only papers keep a plain terminal row (no vision prompt).
        self.assertIn(
            "| `AUDITED` (no critical flags in audit, no figures) | (terminal) |",
            self.paper,
        )

    def test_vision_sibling_present_routes_unchanged(self):
        # A thread that already has a vision sibling is not re-recommended.
        self.assertIn(
            "figures present, `<thread>.{N}.vision/` sibling exists) | "
            "`paper-audit <thread>` |",
            self.paper,
        )

    def test_anomaly_bullet_never_vision_checked(self):
        self.assertIn("NEVER-VISION-CHECKED", self.paper)
        self.assertIn("informational and non-blocking", self.paper)
        # No-figures threads never trigger the note.
        self.assertIn(
            "A thread with **no figures** at the latest `N` never triggers this note",
            self.paper,
        )

    def test_skill_documents_vision_is_optional_and_surfaced(self):
        self.assertIn("recommended-but-optional", self.skill)
        self.assertIn("NEVER-VISION-CHECKED", self.skill)
        # The mechanism (orchestrator surfacing) is named.
        self.assertIn("the portfolio orchestrator (`paper`) surfaces", self.skill)


class TestNatbibCiteCommandGuidance(unittest.TestCase):
    """Both drafter and reviser document the natbib author-year cite-command
    rule (issue #735).

    Under the default ``anvil-paper`` class natbib runs in author-year mode,
    where bare ``\\cite{key}`` aliases to ``\\citet{key}`` and prints
    "Author (Year)" — so ``Name~\\cite{key}`` doubles the author name in the
    rendered PDF. The fix is documentation-only: both ``paper-draft.md`` and
    ``paper-revise.md`` carry a decision-table rule steering the agent to
    ``\\citeyearpar`` / ``\\citet`` / ``\\citep`` and away from bare
    ``\\cite`` when the author is named in prose. These substring assertions
    pin that guidance so a future edit cannot silently drop it.
    """

    def setUp(self):
        self.draft = _read("commands/paper-draft.md")
        self.revise = _read("commands/paper-revise.md")

    def _assert_rule_present(self, text: str) -> None:
        # Anchors the natbib author-year mode + the aliasing root cause.
        self.assertIn("author-year", text)
        self.assertIn("authoryear", text)  # the cls option, quoted verbatim
        # The three sanctioned commands appear.
        self.assertIn(r"\citeyearpar{key}", text)
        self.assertIn(r"\citet{key}", text)
        self.assertIn(r"\citep{key}", text)
        # The bare-cite anti-pattern is called out.
        self.assertIn(r"\cite{key}", text)
        self.assertIn(r"Name~\cite{key}", text)
        # The doubling defect is named concretely.
        self.assertIn("doubles the author name", text)
        # The numeric-mode carve-out is stated.
        self.assertIn(r"\documentclass[numeric]{anvil-paper}", text)
        self.assertIn("unaffected", text)
        # The shared section heading is present in both files.
        self.assertIn("## Citation-command choice under natbib author-year", text)

    def test_draft_documents_cite_command_rule(self):
        self._assert_rule_present(self.draft)

    def test_revise_documents_cite_command_rule(self):
        self._assert_rule_present(self.revise)

    def test_draft_related_work_points_to_rule(self):
        # The Related Work body-writing bullet warns against Name~\cite.
        self.assertIn("do NOT write `Name~\\cite{key}`", self.draft)

    def test_revise_prose_rewrite_points_to_rule(self):
        # The reviser's refs.bib step warns against reintroducing the doubling.
        self.assertIn(
            "reintroduce `Name~\\cite{key}` author-name doubling", self.revise
        )


if __name__ == "__main__":
    unittest.main()
