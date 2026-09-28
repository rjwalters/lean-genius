"""Tests for `anvil:deslop`'s orchestrate module (issue #898).

Covers scratchpad-thread management, the deterministic lint pass (default
+ consumer-declared rhetoric rules), voice-grounding resolution, the
typed-review round trip through `anvil.lib.critics`, the
convergence-driven iterate loop, and the cleaned-text/rationale/diff
emission (never touching the ingested source).
"""

from __future__ import annotations

import json
import textwrap
from pathlib import Path

from _deslop_fixtures import CLEAN_MARKDOWN, PASTED_SLOPPY_TEXT, SLOPPY_MARKDOWN
from _deslop_skill_lib import ingest, orchestrate

from anvil.lib.review_schema import CriticalFlag, Verdict


# ---------------------------------------------------------------------------
# Scratchpad thread management
# ---------------------------------------------------------------------------


def test_slugify_derives_filesystem_safe_slug() -> None:
    assert orchestrate.slugify("Our Landing Page Copy.md") == "our-landing-page-copy"
    assert orchestrate.slugify("") == "prose"
    assert orchestrate.slugify("pasted-text-1") == "pasted-text-1"


def test_init_thread_write_read_version_roundtrip(tmp_path: Path) -> None:
    thread_dir = orchestrate.init_thread(tmp_path, "landing-copy")
    assert thread_dir == tmp_path / "landing-copy"
    assert thread_dir.is_dir()

    vdir = orchestrate.write_version(thread_dir, 1, SLOPPY_MARKDOWN)
    assert vdir == thread_dir / "landing-copy.1"
    assert (vdir / "landing-copy.md").read_text(encoding="utf-8") == SLOPPY_MARKDOWN
    assert orchestrate.read_version(thread_dir, 1) == SLOPPY_MARKDOWN
    assert orchestrate.version_dir_name(thread_dir, 1) == "landing-copy.1"


# ---------------------------------------------------------------------------
# Deterministic lint pass
# ---------------------------------------------------------------------------


def test_lint_body_flags_default_ai_tells_with_no_project() -> None:
    result = orchestrate.lint_body(SLOPPY_MARKDOWN, project_dir=None)
    rule_ids = {f.rule_id for f in result.findings}
    assert "no-important-to-note" in rule_ids


def test_lint_body_clean_text_has_no_findings() -> None:
    result = orchestrate.lint_body(CLEAN_MARKDOWN, project_dir=None)
    assert result.findings == []


def _write_project_with_voice_and_rules(
    project_dir: Path,
    *,
    disable_important_to_note: bool,
) -> None:
    project_dir.mkdir(parents=True, exist_ok=True)
    (project_dir / "VALUES.md").write_text("# Values\n\nDirectness.\n", encoding="utf-8")
    (project_dir / "STYLE_GUIDE.md").write_text(
        "# Style\n\nShort sentences.\n", encoding="utf-8"
    )
    (project_dir / "VOCABULARY.md").write_text("# Vocabulary\n\nship, ship it\n", encoding="utf-8")

    rules_payload = {"name": "consumer-tune", "rules": [], "disable": []}
    if disable_important_to_note:
        rules_payload["disable"] = ["no-important-to-note"]
    (project_dir / "rhetoric-rules.json").write_text(
        json.dumps(rules_payload), encoding="utf-8"
    )

    (project_dir / "BRIEF.md").write_text(
        textwrap.dedent(
            """\
            ---
            project: landing-copy
            documents:
              - slug: landing-copy
                artifact_type: essay
            voice:
              values: VALUES.md
              style_guide: STYLE_GUIDE.md
              vocabulary: VOCABULARY.md
              rhetoric_rules: rhetoric-rules.json
            ---

            # Landing copy cleanup project
            """
        ),
        encoding="utf-8",
    )


def test_lint_body_honors_consumer_declared_rhetoric_rules(tmp_path: Path) -> None:
    project_dir = tmp_path / "project"
    _write_project_with_voice_and_rules(project_dir, disable_important_to_note=True)

    result = orchestrate.lint_body(SLOPPY_MARKDOWN, project_dir=project_dir)
    rule_ids = {f.rule_id for f in result.findings}
    # The consumer's rule file disabled this default rule.
    assert "no-important-to-note" not in rule_ids


def test_lint_body_default_rules_still_apply_without_disable(tmp_path: Path) -> None:
    project_dir = tmp_path / "project"
    _write_project_with_voice_and_rules(project_dir, disable_important_to_note=False)

    result = orchestrate.lint_body(SLOPPY_MARKDOWN, project_dir=project_dir)
    rule_ids = {f.rule_id for f in result.findings}
    assert "no-important-to-note" in rule_ids


def test_lint_body_missing_project_falls_back_to_defaults_no_crash(tmp_path: Path) -> None:
    # No BRIEF.md at all under this directory: resolve_rhetoric_rules
    # returns None, never raises.
    result = orchestrate.lint_body(SLOPPY_MARKDOWN, project_dir=tmp_path)
    rule_ids = {f.rule_id for f in result.findings}
    assert "no-important-to-note" in rule_ids


# ---------------------------------------------------------------------------
# Voice-grounding resolution
# ---------------------------------------------------------------------------


def test_voice_context_inactive_with_no_project() -> None:
    assert orchestrate.voice_context(None) == []


def test_voice_context_inactive_with_project_but_no_brief(tmp_path: Path) -> None:
    assert orchestrate.voice_context(tmp_path) == []


def test_voice_context_resolves_declared_docs(tmp_path: Path) -> None:
    project_dir = tmp_path / "project"
    _write_project_with_voice_and_rules(project_dir, disable_important_to_note=False)

    resolved = orchestrate.voice_context(project_dir)
    kinds = {entry.kind for entry in resolved}
    assert {"values", "style_guide", "vocabulary"} <= kinds
    for entry in resolved:
        assert entry.missing is False


# ---------------------------------------------------------------------------
# Critic-review IO + aggregation (canonical _review.json)
# ---------------------------------------------------------------------------


def test_new_review_write_and_aggregate_roundtrip(tmp_path: Path) -> None:
    thread_dir = orchestrate.init_thread(tmp_path, "landing-copy")
    orchestrate.write_version(thread_dir, 1, SLOPPY_MARKDOWN)

    review = orchestrate.new_review(
        version_dir_name=orchestrate.version_dir_name(thread_dir, 1),
        rhetorical_economy=6,
        rhetorical_economy_justification="Opens with filler and a trope.",
        rhetorical_economy_fix="Cut 'it's important to note' and the movement trope.",
        voice_adherence=None,
        voice_adherence_justification="n/a — no voice docs declared.",
    )
    critic_dir = orchestrate.write_critic_review(thread_dir, 1, review)

    assert critic_dir == thread_dir / "landing-copy.1.critic"
    payload = json.loads((critic_dir / "_review.json").read_text(encoding="utf-8"))
    assert payload["critic_id"] == orchestrate.DEFAULT_CRITIC_TAG
    dims = {s["dimension"] for s in payload["scores"]}
    assert dims == {orchestrate.RHETORICAL_ECONOMY_DIM, orchestrate.VOICE_ADHERENCE_DIM}

    agg = orchestrate.aggregate_reviews(thread_dir, 1)
    assert agg.total == 6  # only rhetorical_economy is scored; voice_adherence is None
    # voice_adherence is unowned, so the default threshold scales down to
    # the rhetorical_economy-only bar rather than an unreachable 16/10.
    assert agg.threshold == orchestrate.RHETORICAL_ECONOMY_ONLY_THRESHOLD


def test_aggregate_with_two_critic_siblings_means_scores(tmp_path: Path) -> None:
    thread_dir = orchestrate.init_thread(tmp_path, "landing-copy")
    orchestrate.write_version(thread_dir, 1, SLOPPY_MARKDOWN)

    review_a = orchestrate.new_review(
        version_dir_name=orchestrate.version_dir_name(thread_dir, 1),
        critic_id="rhetoric",
        rhetorical_economy=6,
        voice_adherence=None,
    )
    review_b = orchestrate.new_review(
        version_dir_name=orchestrate.version_dir_name(thread_dir, 1),
        critic_id="voice",
        rhetorical_economy=8,
        voice_adherence=7,
    )
    orchestrate.write_critic_review(thread_dir, 1, review_a, tag="rhetoric")
    orchestrate.write_critic_review(thread_dir, 1, review_b, tag="voice")

    agg = orchestrate.aggregate_reviews(thread_dir, 1)
    # rhetorical_economy: mean(6, 8) = 7; voice_adherence: mean of non-null = 7.
    dims = {s.dimension: s.score for s in agg.scores}
    assert dims[orchestrate.RHETORICAL_ECONOMY_DIM] == 7
    assert dims[orchestrate.VOICE_ADHERENCE_DIM] == 7
    assert agg.total == 14


# ---------------------------------------------------------------------------
# Convergence-driven iterate loop
# ---------------------------------------------------------------------------


def test_decide_next_advances_when_threshold_met(tmp_path: Path) -> None:
    thread_dir = orchestrate.init_thread(tmp_path, "landing-copy")
    orchestrate.write_version(thread_dir, 1, CLEAN_MARKDOWN)
    review = orchestrate.new_review(
        version_dir_name=orchestrate.version_dir_name(thread_dir, 1),
        rhetorical_economy=9,
        voice_adherence=None,
    )
    orchestrate.write_critic_review(thread_dir, 1, review)
    agg = orchestrate.aggregate_reviews(thread_dir, 1)

    history = [agg.total]
    verdict, reason = orchestrate.decide_next(agg, history, iteration=1)
    assert verdict == Verdict.ADVANCE
    assert reason == "THRESHOLD_MET"


def test_decide_next_revises_below_threshold_under_cap(tmp_path: Path) -> None:
    thread_dir = orchestrate.init_thread(tmp_path, "landing-copy")
    orchestrate.write_version(thread_dir, 1, SLOPPY_MARKDOWN)
    review = orchestrate.new_review(
        version_dir_name=orchestrate.version_dir_name(thread_dir, 1),
        rhetorical_economy=4,
        voice_adherence=None,
    )
    orchestrate.write_critic_review(thread_dir, 1, review)
    agg = orchestrate.aggregate_reviews(thread_dir, 1)

    history = [agg.total]
    verdict, reason = orchestrate.decide_next(
        agg, history, iteration=1, max_iterations=4
    )
    assert verdict == Verdict.REVISE
    assert reason == ""


def test_decide_next_hits_max_iterations(tmp_path: Path) -> None:
    thread_dir = orchestrate.init_thread(tmp_path, "landing-copy")
    orchestrate.write_version(thread_dir, 1, SLOPPY_MARKDOWN)
    review = orchestrate.new_review(
        version_dir_name=orchestrate.version_dir_name(thread_dir, 1),
        rhetorical_economy=4,
        voice_adherence=None,
    )
    orchestrate.write_critic_review(thread_dir, 1, review)
    agg = orchestrate.aggregate_reviews(thread_dir, 1)

    history = [4, 5, 4, agg.total]
    verdict, reason = orchestrate.decide_next(
        agg, history, iteration=4, max_iterations=4
    )
    assert verdict == Verdict.REVISE
    assert reason == "MAX_ITERATIONS"


def test_decide_next_blocks_on_critical_flag(tmp_path: Path) -> None:
    thread_dir = orchestrate.init_thread(tmp_path, "landing-copy")
    orchestrate.write_version(thread_dir, 1, SLOPPY_MARKDOWN)
    review = orchestrate.new_review(
        version_dir_name=orchestrate.version_dir_name(thread_dir, 1),
        rhetorical_economy=9,
        voice_adherence=None,
        critical_flags=[
            CriticalFlag(type="fabricated_claim", justification="Invented a stat.")
        ],
    )
    orchestrate.write_critic_review(thread_dir, 1, review)
    agg = orchestrate.aggregate_reviews(thread_dir, 1)

    verdict, reason = orchestrate.decide_next(agg, [agg.total], iteration=1)
    assert verdict == Verdict.BLOCK
    assert reason == "CRITICAL_FLAG"


def test_decide_next_stalls_on_plateau() -> None:
    # STALLED doesn't need a real thread — it's a pure history check, but
    # exercised through decide_next's AggregatedReview-shaped call surface
    # via a minimal stand-in review/aggregate roundtrip.
    from anvil.lib.review_schema import AggregatedReview

    agg = AggregatedReview(
        version_dir="landing-copy.3",
        critic_ids=["critic"],
        scores=[],
        total=10,
        threshold=orchestrate.DEFAULT_THRESHOLD,
        verdict=Verdict.REVISE,
    )
    history = [9, 10, 10]
    verdict, reason = orchestrate.decide_next(
        agg, history, iteration=3, max_iterations=8
    )
    assert verdict == Verdict.STALLED
    assert reason == "STALLED"


# ---------------------------------------------------------------------------
# Emission: cleaned text + rationale + diff, never touching the source
# ---------------------------------------------------------------------------


def test_emit_writes_diff_for_markdown_file_input(tmp_path: Path) -> None:
    src = tmp_path / "copy.md"
    src.write_text(SLOPPY_MARKDOWN, encoding="utf-8")
    item = ingest.ingest_path(src)

    thread_dir = orchestrate.init_thread(tmp_path / "scratch", "copy")
    result = orchestrate.emit(
        thread_dir,
        item,
        CLEAN_MARKDOWN,
        ["Removed 'it's important to note' filler.", "Cut the movement trope."],
    )

    assert result.cleaned_text_path.read_text(encoding="utf-8") == CLEAN_MARKDOWN
    assert "Removed 'it's important to note'" in result.rationale_path.read_text(
        encoding="utf-8"
    )
    assert result.diff_path is not None
    diff_text = result.diff_path.read_text(encoding="utf-8")
    assert "-It's important to note" in diff_text or "-It's important" in diff_text
    assert "+Our product helps teams ship faster." in diff_text

    # The source file itself is untouched.
    assert src.read_text(encoding="utf-8") == SLOPPY_MARKDOWN


def test_emit_pasted_text_has_no_diff_path(tmp_path: Path) -> None:
    item = ingest.ingest_pasted(PASTED_SLOPPY_TEXT)
    thread_dir = orchestrate.init_thread(tmp_path / "scratch", "pasted-text-1")

    result = orchestrate.emit(thread_dir, item, "This paragraph is a demonstration.", [])

    assert result.diff_path is None
    assert result.diff == ""
    assert result.cleaned_text_path.exists()


def test_emit_html_diff_is_labeled_as_extracted_text(tmp_path: Path) -> None:
    from _deslop_fixtures import SLOPPY_HTML

    src = tmp_path / "index.html"
    src.write_text(SLOPPY_HTML, encoding="utf-8")
    item = ingest.ingest_path(src)

    thread_dir = orchestrate.init_thread(tmp_path / "scratch", "index")
    result = orchestrate.emit(thread_dir, item, "Our Product\n\nShips faster.\n", [])

    assert result.diff_path is not None
    assert "apply manually to the HTML source" in result.diff_path.read_text(
        encoding="utf-8"
    )
    # The HTML source itself is untouched.
    assert src.read_text(encoding="utf-8") == SLOPPY_HTML
