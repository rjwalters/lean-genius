"""Tests for `anvil:deslop`'s deterministic no-fabrication gate (issue #922).

Covers the three acceptance-criteria cases named in the issue — a clean
revision passes silently, a revision that invents a number/name/citation
is flagged, a revision that pulls a specific detail from a resolved
voice-grounding doc is NOT flagged — plus the fenced-code/HTML-comment/
inline-code exclusion scope, the explicit-operator-supplied-detail carve-
out, and the `orchestrate.check_no_fabrication` thread-reading wrapper.
"""

from __future__ import annotations

from pathlib import Path
from types import SimpleNamespace

from _deslop_skill_lib import no_fabrication, orchestrate

PRIOR = (
    "# Our Product\n\n"
    "Our product helps teams ship faster. It costs $29 per seat.\n"
)


# ---------------------------------------------------------------------------
# Clean revision: no new facts -> passes silently
# ---------------------------------------------------------------------------


def test_clean_revision_with_no_new_facts_is_not_flagged() -> None:
    revised = (
        "# Our Product\n\n"
        "Our product helps teams ship work faster. It still costs $29"
        " per seat.\n"
    )
    result = no_fabrication.diff_no_fabrication(PRIOR, revised)
    assert result.findings == []
    assert result.total == 0


def test_pure_rewording_with_zero_overlap_in_specifics_still_passes() -> None:
    # Rewording that drops a number entirely introduces nothing new, so it
    # must not be flagged either -- the gate only fires on introductions.
    revised = "# Our Product\n\nOur product helps teams ship faster.\n"
    result = no_fabrication.diff_no_fabrication(PRIOR, revised)
    assert result.findings == []


# ---------------------------------------------------------------------------
# Invented number / name / citation -> flagged
# ---------------------------------------------------------------------------


def test_invented_number_is_flagged() -> None:
    revised = PRIOR.replace("$29 per seat", "$29 per seat, used by 50,000 teams")
    result = no_fabrication.diff_no_fabrication(PRIOR, revised)
    kinds = {f.kind for f in result.findings}
    assert no_fabrication.KIND_NUMERAL in kinds
    tokens = {f.token for f in result.findings}
    assert "50,000" in tokens


def test_invented_name_is_flagged() -> None:
    revised = PRIOR + "Just ask Jane Whitfield how much time it saves.\n"
    result = no_fabrication.diff_no_fabrication(PRIOR, revised)
    proper_noun_findings = result.by_kind(no_fabrication.KIND_PROPER_NOUN)
    assert any(f.token == "Jane Whitfield" for f in proper_noun_findings)


def test_invented_citation_is_flagged() -> None:
    revised = PRIOR + 'As one review put it, "this changed everything for us."\n'
    result = no_fabrication.diff_no_fabrication(PRIOR, revised)
    citation_findings = result.by_kind(no_fabrication.KIND_CITATION)
    assert any(
        "this changed everything for us" in f.token for f in citation_findings
    )


def test_invented_url_and_bracket_ref_are_flagged() -> None:
    revised = (
        PRIOR
        + "See https://example.com/proof and note [1] for details.\n"
    )
    result = no_fabrication.diff_no_fabrication(PRIOR, revised)
    tokens = {f.token for f in result.by_kind(no_fabrication.KIND_CITATION)}
    assert "https://example.com/proof" in tokens
    assert "[1]" in tokens


def test_token_already_present_in_prior_is_not_flagged() -> None:
    # "Our" is a single leading capital (not chained) so the extracted
    # proper-noun token is "Jane Whitfield" in both the prior and revised
    # forms -- an unchanged specific must never be flagged.
    prior = PRIOR + "Our contact is Jane Whitfield.\n"
    revised = prior.replace(
        "Our contact is Jane Whitfield.", "Jane Whitfield is our contact."
    )
    result = no_fabrication.diff_no_fabrication(prior, revised)
    assert result.findings == []


def test_findings_are_deduplicated_by_kind_and_token() -> None:
    revised = PRIOR + "Ask Jane Whitfield. Seriously, ask Jane Whitfield again.\n"
    result = no_fabrication.diff_no_fabrication(PRIOR, revised)
    matches = [f for f in result.findings if f.token == "Jane Whitfield"]
    assert len(matches) == 1


# ---------------------------------------------------------------------------
# Voice-grounding-doc exception path -> NOT flagged
# ---------------------------------------------------------------------------


def test_specific_detail_from_voice_doc_is_not_flagged(tmp_path: Path) -> None:
    voice_doc = tmp_path / "VALUES.md"
    voice_doc.write_text(
        "# Values\n\nWe are proud our pilot ran with Acme Robotics"
        " for 18 months.\n",
        encoding="utf-8",
    )
    revised = PRIOR + "This is the same approach Acme Robotics trusted.\n"

    result = no_fabrication.diff_no_fabrication(
        PRIOR, revised, voice_doc_paths=[voice_doc]
    )
    assert result.findings == []


def test_detail_absent_from_voice_doc_is_still_flagged(tmp_path: Path) -> None:
    voice_doc = tmp_path / "VALUES.md"
    voice_doc.write_text("# Values\n\nDirectness above all.\n", encoding="utf-8")
    revised = PRIOR + "This is the same approach Acme Robotics trusted.\n"

    result = no_fabrication.diff_no_fabrication(
        PRIOR, revised, voice_doc_paths=[voice_doc]
    )
    proper_noun_tokens = {f.token for f in result.by_kind(no_fabrication.KIND_PROPER_NOUN)}
    assert "Acme Robotics" in proper_noun_tokens


def test_missing_voice_doc_path_is_skipped_gracefully(tmp_path: Path) -> None:
    missing = tmp_path / "does-not-exist.md"
    revised = PRIOR + "The team recommends Jane Whitfield for advice.\n"

    result = no_fabrication.diff_no_fabrication(
        PRIOR, revised, voice_doc_paths=[missing]
    )
    assert any(f.token == "Jane Whitfield" for f in result.findings)


# ---------------------------------------------------------------------------
# Explicit operator-supplied-detail exception path -> NOT flagged
# ---------------------------------------------------------------------------


def test_explicit_operator_supplied_token_is_not_flagged() -> None:
    revised = PRIOR.replace("$29 per seat", "$31 per seat")
    result = no_fabrication.diff_no_fabrication(
        PRIOR, revised, extra_allowed_tokens=["$31"]
    )
    assert result.findings == []


def test_unlisted_token_still_flagged_despite_other_extra_allowed_tokens() -> None:
    revised = PRIOR.replace("$29 per seat", "$31 per seat, per Jane Whitfield")
    result = no_fabrication.diff_no_fabrication(
        PRIOR, revised, extra_allowed_tokens=["$31"]
    )
    assert any(f.token == "Jane Whitfield" for f in result.findings)


# ---------------------------------------------------------------------------
# Exclusion scope: fenced code / HTML comments / inline code
# ---------------------------------------------------------------------------


def test_fenced_code_block_does_not_trigger_the_gate() -> None:
    revised = (
        PRIOR
        + "\n```bash\ncurl https://api.example.com/v2 --data 12345\n```\n"
    )
    result = no_fabrication.diff_no_fabrication(PRIOR, revised)
    assert result.findings == []


def test_inline_code_span_does_not_trigger_the_gate() -> None:
    revised = PRIOR + "\nRun `deploy.sh 42` to ship it.\n"
    result = no_fabrication.diff_no_fabrication(PRIOR, revised)
    assert result.findings == []


def test_html_comment_does_not_trigger_the_gate() -> None:
    revised = PRIOR + "\n<!-- internal note: revenue is $9,000,000 -->\n"
    result = no_fabrication.diff_no_fabrication(PRIOR, revised)
    assert result.findings == []


def test_code_sample_outside_fence_still_flagged() -> None:
    # Sanity check that the exclusion is scoped to the fence/comment/inline
    # markers themselves, not a blanket "anything code-shaped" carve-out.
    revised = PRIOR + "\nRun deploy.sh with build 99887 to ship it.\n"
    result = no_fabrication.diff_no_fabrication(PRIOR, revised)
    assert any(f.token == "99887" for f in result.by_kind(no_fabrication.KIND_NUMERAL))


# ---------------------------------------------------------------------------
# orchestrate.check_no_fabrication -- thread-reading wrapper
# ---------------------------------------------------------------------------


def test_orchestrate_check_no_fabrication_diffs_thread_versions(tmp_path: Path) -> None:
    thread_dir = orchestrate.init_thread(tmp_path, "landing-copy")
    orchestrate.write_version(thread_dir, 1, PRIOR)
    orchestrate.write_version(
        thread_dir, 2, PRIOR + "The team recommends Jane Whitfield for advice.\n"
    )

    result = orchestrate.check_no_fabrication(thread_dir, 1)
    assert any(f.token == "Jane Whitfield" for f in result.findings)


def test_orchestrate_check_no_fabrication_honors_voice_docs(tmp_path: Path) -> None:
    voice_doc = tmp_path / "VALUES.md"
    voice_doc.write_text(
        "# Values\n\nAcme Robotics is our flagship pilot.\n", encoding="utf-8"
    )

    thread_dir = orchestrate.init_thread(tmp_path / "scratch", "landing-copy")
    orchestrate.write_version(thread_dir, 1, PRIOR)
    orchestrate.write_version(
        thread_dir, 2, PRIOR + "Acme Robotics trusted this approach.\n"
    )

    # voice_context() normally returns ResolvedVoiceDoc objects; a
    # SimpleNamespace with a `.paths` attribute exercises the same
    # duck-typed flattening without standing up a full BRIEF.md project.
    voice_docs = [SimpleNamespace(paths=[str(voice_doc)])]

    result = orchestrate.check_no_fabrication(thread_dir, 1, voice_docs=voice_docs)
    assert result.findings == []


def test_orchestrate_check_no_fabrication_no_voice_docs_still_works(
    tmp_path: Path,
) -> None:
    thread_dir = orchestrate.init_thread(tmp_path, "landing-copy")
    orchestrate.write_version(thread_dir, 1, PRIOR)
    orchestrate.write_version(thread_dir, 2, PRIOR)  # byte-identical revision

    result = orchestrate.check_no_fabrication(thread_dir, 1)
    assert result.findings == []
    assert result.to_summary()["total"] == 0
