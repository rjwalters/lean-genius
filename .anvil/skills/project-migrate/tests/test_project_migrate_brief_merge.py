"""Migrate-mode surgical BRIEF merge tests (issue #415).

The load-bearing AC: a migrate-mode ``--apply`` over a project whose
BRIEF carries operator-authored config must preserve every byte the
migration does not intend to change. The old re-render path
(`render_project_brief`) was empirically shown (issue #406 curation,
PR #414) to drop top-level ``theme:``, per-doc ``render_*`` /
``latex_header_includes`` keys, every YAML comment (including #408's
TODO markers), quoting style, and entry order. Migrate now routes
through ``render_migrate_brief`` → ``_merge_brief_documents`` —
targeted text edits (append-entry / append-field-to-entry) instead of
a dict round-trip. These tests pin that contract against the same
tripwire-laden fixture BRIEF the #414 enroll tests use.

Per the #58 packaging convention this filename is unique across the
``anvil/skills/*/tests/`` tree.
"""

from __future__ import annotations

from pathlib import Path

from _fixtures import (
    ENROLL_OPERATOR_BRIEF,
    build_post_283_with_operator_brief,
)
from _project_migrate_skill_lib import (
    apply_mod,
    detect,
    orchestrate,
    plan as plan_mod,
)
from anvil.lib.testing import tree_hash as _tree_hash

_merge_brief_documents = apply_mod._merge_brief_documents
render_migrate_brief = apply_mod.render_migrate_brief
Shape = detect.Shape
BriefMergeOp = plan_mod.BriefMergeOp
DocumentPlan = plan_mod.DocumentPlan
Plan = plan_mod.Plan
run = orchestrate.run

# The single intended BRIEF delta for the fixture's zeta-memo thread:
# the `.anvil.json` target_length carried into the existing entry.
_ZETA_CARRY_LINE = "    target_length: { words: [5000, 8000] }\n"

_EXPECTED_AFTER_MIGRATE = ENROLL_OPERATOR_BRIEF.replace(
    "  - slug: alpha-memo\n",
    _ZETA_CARRY_LINE + "  - slug: alpha-memo\n",
)


def _make_migrate_plan(project_dir: Path, *, merges) -> Plan:
    """Assemble a minimal migrate-mode Plan carrying ``merges``."""
    p = Plan(project_dir=project_dir, shape=Shape.POST_283_ANVIL_JSON)
    for merge in merges:
        p.documents.append(
            DocumentPlan(
                slug=merge.slug,
                source_dir=project_dir / merge.slug,
                target_dir=project_dir / merge.slug,
                brief_merge=merge,
            )
        )
    return p


class TestMigrateApplyBytePreservation:
    def test_operator_brief_byte_preserved_except_intended_delta(
        self, tmp_path
    ):
        """The #414 tripwire fixture survives migrate-mode --apply
        byte-identically except the single intended delta (the carried
        target_length landing in the zeta entry)."""
        project = build_post_283_with_operator_brief(tmp_path)
        result = run(project, apply=True)
        assert result.success, result.report
        out = (project / "BRIEF.md").read_text(encoding="utf-8")
        assert out == _EXPECTED_AFTER_MIGRATE

    def test_tripwires_survive_explicitly(self, tmp_path):
        """Spell out the acceptance-criteria tripwires individually so
        a regression names the dropped byte class, not just a diff."""
        project = build_post_283_with_operator_brief(tmp_path)
        run(project, apply=True)
        out = (project / "BRIEF.md").read_text(encoding="utf-8")
        # Top-level theme + its comment.
        assert "theme: sphere-brand  # operator-pinned theme" in out
        # #408-style TODO marker on artifact_type.
        assert (
            "artifact_type: investment-memo  # TODO(operator): confirm"
            in out
        )
        # Per-doc render_* / latex_header_includes.
        assert "render_engine: xelatex" in out
        assert 'doc-type: "Investment Memo"' in out
        assert "latex_header_includes: |" in out
        assert "\\usepackage{xcolor}" in out
        # Quoting styles.
        assert '"Board of Directors"' in out
        assert "'No forward-looking statements'" in out
        # Entry order (zeta before alpha) + operator artifact_type kept.
        assert out.index("slug: zeta-memo") < out.index("slug: alpha-memo")
        assert "artifact_type: position-paper" in out
        # Body prose untouched.
        assert "Operator-authored prose that must survive" in out

    def test_unlisted_slug_entry_appended(self, tmp_path):
        project = build_post_283_with_operator_brief(
            tmp_path, extra_unlisted_slug="gamma-memo"
        )
        result = run(project, apply=True)
        assert result.success, result.report
        out = (project / "BRIEF.md").read_text(encoding="utf-8")
        # New entry appended at the END of the documents block.
        assert (
            "  - slug: gamma-memo\n    artifact_type: investment-memo\n"
            in out
        )
        assert (
            out.index("slug: zeta-memo")
            < out.index("slug: alpha-memo")
            < out.index("slug: gamma-memo")
        )
        # Inside the frontmatter, not the body.
        fm = out.split("\n---\n", 1)[0]
        assert "slug: gamma-memo" in fm
        # The zeta carry still lands too.
        assert _ZETA_CARRY_LINE in out

    def test_last_entry_carry_with_new_entry_appended(self, tmp_path):
        """Judge-found blocker (PR #416): when the LAST listed entry
        needs a field carry (its stop == end_idx) AND an unlisted slug
        appends a new entry in the same run, both insertions land at the
        same index. The carried field must attach to the LAST EXISTING
        entry, with the new entry spliced BELOW it — not above, where
        the carry would silently corrupt the new entry."""
        zeta_entry = (
            "  - slug: zeta-memo\n"
            "    artifact_type: investment-memo  # TODO(operator): confirm\n"
            "    render_engine: xelatex\n"
            "    render_metadata:\n"
            '      doc-type: "Investment Memo"\n'
            "    latex_header_includes: |\n"
            "      \\usepackage{xcolor}\n"
        )
        alpha_entry = (
            "  - slug: alpha-memo\n"
            "    artifact_type: position-paper\n"
        )
        # Alphabetical operator ordering: alpha first, zeta (the carry
        # target) LAST in the documents block.
        reordered = ENROLL_OPERATOR_BRIEF.replace(
            zeta_entry + alpha_entry, alpha_entry + zeta_entry
        )
        assert reordered != ENROLL_OPERATOR_BRIEF  # replace() fired
        project = build_post_283_with_operator_brief(
            tmp_path, extra_unlisted_slug="gamma-memo"
        )
        (project / "BRIEF.md").write_text(reordered, encoding="utf-8")

        result = run(project, apply=True)
        assert result.success, result.report
        out = (project / "BRIEF.md").read_text(encoding="utf-8")

        # Byte-level pin: zeta's carry lands inside zeta's entry span,
        # and the gamma entry follows AFTER it.
        expected = reordered.replace(
            "      \\usepackage{xcolor}\n"
            "---\n",
            "      \\usepackage{xcolor}\n"
            + _ZETA_CARRY_LINE
            + "  - slug: gamma-memo\n"
            "    artifact_type: investment-memo\n"
            "---\n",
        )
        assert expected != reordered  # replace() fired
        assert out == expected
        # Spell out the misattribution explicitly: the carry sits
        # between zeta's last field and the gamma entry.
        assert out.index("slug: zeta-memo") < out.index(_ZETA_CARRY_LINE)
        assert out.index(_ZETA_CARRY_LINE) < out.index("slug: gamma-memo")
        assert not (project / "zeta-memo" / ".anvil.json").exists()

    def test_reapply_is_byte_identical(self, tmp_path):
        project = build_post_283_with_operator_brief(tmp_path)
        first = run(project, apply=True)
        assert first.success
        before = _tree_hash(project)
        second = run(project, apply=True)
        assert second.success
        assert second.plan.is_noop
        assert _tree_hash(project) == before

    def test_dry_run_preview_matches_apply_write(self, tmp_path):
        """The dry-run 'Proposed BRIEF.md' block is byte-identical to
        what --apply writes (shared render_migrate_brief code path)."""
        project = build_post_283_with_operator_brief(tmp_path)
        dry = run(project, apply=False)
        assert dry.success
        preview = dry.report.split("````markdown\n", 1)[1]
        preview = preview.split("\n````", 1)[0] + "\n"
        run(project, apply=True)
        written = (project / "BRIEF.md").read_text(encoding="utf-8")
        assert preview == written

    def test_dry_run_does_not_mutate(self, tmp_path):
        project = build_post_283_with_operator_brief(tmp_path)
        before = _tree_hash(project)
        result = run(project, apply=False)
        assert result.success
        assert _tree_hash(project) == before


class TestMergeBriefDocumentsUnit:
    def test_existing_field_wins_on_conflict(self, tmp_path):
        """A carried value never clobbers an operator-set field; the
        conflict is surfaced as a note instead."""
        existing = ENROLL_OPERATOR_BRIEF.replace(
            "    render_engine: xelatex\n",
            "    target_length: { words: [9, 9] }  # operator-pinned\n"
            "    render_engine: xelatex\n",
        )
        merge = BriefMergeOp(
            slug="zeta-memo", target_length=(5000, 8000)
        )
        out, notes = _merge_brief_documents(
            existing, _make_migrate_plan(tmp_path, merges=[merge])
        )
        assert out == existing
        assert any("target_length" in n for n in notes)

    def test_iteration_cap_pair_skipped_together(self, tmp_path):
        """When the entry already carries max_iterations, neither half
        of the carried pair is appended (an unbalanced pair would fail
        the strict parser's paired-override contract)."""
        existing = ENROLL_OPERATOR_BRIEF.replace(
            "    render_engine: xelatex\n",
            "    max_iterations: 5\n"
            "    iteration_cap_rationale: operator says so\n"
            "    render_engine: xelatex\n",
        )
        merge = BriefMergeOp(
            slug="zeta-memo",
            max_iterations=7,
            iteration_cap_rationale="carried rationale",
        )
        out, notes = _merge_brief_documents(
            existing, _make_migrate_plan(tmp_path, merges=[merge])
        )
        assert out == existing
        assert any("iteration-cap" in n for n in notes)

    def test_missing_artifact_type_appended(self, tmp_path):
        existing = (
            "---\n"
            "project: p\n"
            "audience: []\n"
            "hard_rules: []\n"
            "documents:\n"
            "  - slug: solo\n"
            "---\n"
            "\nBody.\n"
        )
        merge = BriefMergeOp(slug="solo")
        out, _notes = _merge_brief_documents(
            existing, _make_migrate_plan(tmp_path, merges=[merge])
        )
        assert "  - slug: solo\n    artifact_type: investment-memo\n" in out

    def test_appended_fields_reindent_to_entry_indent(self, tmp_path):
        """An entry using a non-canonical field indent gets the carried
        field at ITS indent, keeping the entry's YAML self-consistent."""
        existing = (
            "---\n"
            "project: p\n"
            "audience: []\n"
            "hard_rules: []\n"
            "documents:\n"
            "    - slug: wide\n"
            "      artifact_type: investment-memo\n"
            "---\n"
            "\nBody.\n"
        )
        merge = BriefMergeOp(slug="wide", target_length=(100, 200))
        out, _notes = _merge_brief_documents(
            existing, _make_migrate_plan(tmp_path, merges=[merge])
        )
        assert "      target_length: { words: [100, 200] }\n" in out

    def test_no_documents_block_falls_back_to_render(self, tmp_path):
        """A per-thread BRIEF (frontmatter without documents:) takes the
        legacy render path — with an honest note about the fallback."""
        existing = (
            "---\n"
            "company: acme\n"
            "sector: TODO\n"
            "---\n"
            "\n# Brief\n\nProse body survives.\n"
        )
        merge = BriefMergeOp(slug="acme", target_length=(8000, 11000))
        text, notes = render_migrate_brief(
            _make_migrate_plan(tmp_path, merges=[merge]),
            existing_text=existing,
        )
        assert "documents:" in text
        assert "  - slug: acme\n" in text
        assert "Prose body survives." in text
        assert any("surgical merge not possible" in n for n in notes)

    def test_synthesis_path_unchanged_without_existing_brief(
        self, tmp_path
    ):
        merge = BriefMergeOp(slug="fresh")
        text, notes = render_migrate_brief(
            _make_migrate_plan(tmp_path, merges=[merge]),
            existing_text=None,
        )
        assert notes == []
        assert "  - slug: fresh\n" in text
