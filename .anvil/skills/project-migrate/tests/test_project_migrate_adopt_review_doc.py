"""Documentation pin tests for `--adopt-review` (issue #454 — Phase 3a).

Pins the `--adopt-review` flag, the "no LLM / no synthesized scores"
contract, the stub field set, and the Phase 3a/3b split in SKILL.md and
the command spec. These are load-bearing operator-facing guarantees — a
silent doc drift would let the honest-stub contract rot.
"""

from __future__ import annotations

from pathlib import Path

_SKILL_ROOT = Path(__file__).resolve().parents[1]
_SKILL_MD = _SKILL_ROOT / "SKILL.md"
_COMMAND_MD = _SKILL_ROOT / "commands" / "project-migrate.md"


def _skill_text() -> str:
    return _SKILL_MD.read_text(encoding="utf-8")


def _command_text() -> str:
    return _COMMAND_MD.read_text(encoding="utf-8")


class TestSkillMd:
    def test_flag_in_command_table(self):
        text = _skill_text()
        assert "--adopt-review" in text

    def test_no_llm_no_synthesized_scores_contract(self):
        text = _skill_text()
        assert "NO LLM" in text
        assert "NO score synthesis" in text or "NO synthesized scores" in text

    def test_stub_field_set_documented(self):
        text = _skill_text()
        # The honest unscored shape.
        assert "unscored" in text
        assert "foreign-adopted" in text
        assert "_review.json" in text
        assert "_meta.json" in text
        assert "byte-identical" in text

    def test_phase_3a_3b_split_documented(self):
        text = _skill_text()
        assert "Phase 3a" in text
        assert "Phase 3b" in text

    def test_rescore_flag_and_contract_documented(self):
        text = _skill_text()
        # Phase 3b ships as a --rescore flag (issue #507).
        assert "--rescore" in text
        assert "#507" in text
        # The honest-stub-vs-scored flip + lineage are documented.
        assert "rescored_from" in text
        assert "unscored: false" in text or "unscored=False" in text
        # The operator gate + honesty guard are recorded.
        assert "operator" in text.lower()
        assert "never guessed" in text.lower() or "never fabricates" in text.lower()

    def test_rubric_rebackport_scope_boundary(self):
        text = _skill_text()
        # The skill must record that rubric-rebackport does NOT apply here.
        assert "rubric-rebackport" in text


class TestCommandMd:
    def test_flag_and_synopsis(self):
        text = _command_text()
        assert "--adopt-review" in text
        assert "run_adopt_review" in text

    def test_no_llm_contract(self):
        text = _command_text()
        assert "NO LLM" in text

    def test_provenance_marker_shape_pinned(self):
        text = _command_text()
        assert "foreign-adopted" in text
        assert "anvil:project-migrate#454" in text
        assert "origin_filename" in text

    def test_phase_3b_rescore_documented(self):
        text = _command_text()
        assert "Phase 3b" in text
        # The --rescore flag, the operator LLM hand-off, and the --apply
        # gate are all documented (issue #507).
        assert "--rescore" in text
        assert "run_adopt_review" in text and "rescore=True" in text
        assert "slash-command runtime" in text
        assert "rescored_from: foreign-adopted" in text

    def test_rescore_apply_gate_documented(self):
        text = _command_text()
        # The operator gate is binding: rescore never runs silently.
        assert "operator gate is binding" in text
        assert "--apply" in text

    def test_dry_run_by_default(self):
        text = _command_text()
        assert "dry-run by default" in text or "dry-run (no mutations)" in text
