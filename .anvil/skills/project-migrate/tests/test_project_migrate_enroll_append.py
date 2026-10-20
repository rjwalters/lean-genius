"""Surgical-append unit tests for enrollment (issue #406).

The load-bearing AC: extending an existing operator-authored BRIEF must
preserve every pre-existing byte. The re-render path was empirically
shown (issue #406 curation) to drop top-level ``theme:``, per-doc
``render_*`` / ``latex_header_includes`` keys, every YAML comment
(including #408's TODO markers), quoting style, and entry order — so
``_append_brief_documents`` does raw-text insertion instead. These
tests pin that contract against a tripwire-laden fixture BRIEF.
"""

from __future__ import annotations

import pytest

from _fixtures import ENROLL_OPERATOR_BRIEF, build_loose_file_in_existing_project
from _project_migrate_skill_lib import apply_mod, detect, plan as plan_mod

_append_brief_documents = apply_mod._append_brief_documents
render_enroll_brief = apply_mod.render_enroll_brief
Shape = detect.Shape
BriefMergeOp = plan_mod.BriefMergeOp
DocumentPlan = plan_mod.DocumentPlan
Plan = plan_mod.Plan


def _make_enroll_plan(tmp_path, *, merges, logs=None):
    """Assemble a minimal append-mode Plan carrying ``merges``."""
    p = Plan(project_dir=tmp_path / "proj", shape=Shape.ENROLL)
    p.brief_mode = "append"
    for i, merge in enumerate(merges):
        doc = DocumentPlan(
            slug=merge.slug,
            source_dir=tmp_path,
            target_dir=tmp_path / "proj" / merge.slug,
            brief_merge=merge,
        )
        if logs:
            doc.enrollment_log.append(logs[i])
        p.documents.append(doc)
    return p


class TestAppendByteCompat:
    def test_frontmatter_prefix_is_byte_identical(self, tmp_path):
        merge = BriefMergeOp(
            slug="board-update",
            slug_comment="enrolled-from: 2026-05-19-board-update.md "
            "(date: 2026-05-19)",
            inferred=True,
            todo_comment="TODO(operator): confirm — memo-class default",
        )
        p = _make_enroll_plan(tmp_path, merges=[merge])
        out = _append_brief_documents(ENROLL_OPERATOR_BRIEF, p)

        # Everything BEFORE the closing delimiter that isn't ours must
        # be byte-identical: the original text up to the last entry
        # (i.e. up to the closing '---') is split around the insertion
        # point. The original frontmatter through its final pre-existing
        # line must be a byte-identical PREFIX of the result.
        original_fm_end = ENROLL_OPERATOR_BRIEF.index("\n---\n", 4)
        original_prefix = ENROLL_OPERATOR_BRIEF[:original_fm_end]
        assert out.startswith(original_prefix)

        # Tripwires survive verbatim.
        assert "theme: sphere-brand  # operator-pinned theme" in out
        assert "render_engine: xelatex" in out
        assert 'doc-type: "Investment Memo"' in out
        assert "latex_header_includes: |" in out
        assert "\\usepackage{xcolor}" in out
        assert '"Board of Directors"' in out
        assert "'No forward-looking statements'" in out
        assert (
            "artifact_type: investment-memo  # TODO(operator): confirm"
            in out
        )
        # Entry order preserved (zeta before alpha before the new one).
        assert (
            out.index("slug: zeta-memo")
            < out.index("slug: alpha-memo")
            < out.index("slug: board-update")
        )

    def test_body_prose_is_byte_identical_prefix(self, tmp_path):
        merge = BriefMergeOp(slug="board-update")
        p = _make_enroll_plan(
            tmp_path,
            merges=[merge],
            logs=["enrolled `x.md` as `board-update/board-update.1/"
                  "board-update.md` (version 1)"],
        )
        out = _append_brief_documents(ENROLL_OPERATOR_BRIEF, p)
        original_body = ENROLL_OPERATOR_BRIEF.split("\n---\n", 1)[1]
        out_body = out.split("\n---\n", 1)[1]
        assert out_body.startswith(original_body)
        assert "## Enrollment log" in out_body
        assert "- enrolled `x.md`" in out_body

    def test_new_entry_carries_provenance_comment(self, tmp_path):
        merge = BriefMergeOp(
            slug="board-update",
            slug_comment="enrolled-from: 2026-05-19-board-update.md "
            "(date: 2026-05-19)",
        )
        p = _make_enroll_plan(tmp_path, merges=[merge])
        out = _append_brief_documents(ENROLL_OPERATOR_BRIEF, p)
        assert (
            "  - slug: board-update  # enrolled-from: "
            "2026-05-19-board-update.md (date: 2026-05-19)" in out
        )

    def test_appended_brief_strict_parses(self, tmp_path):
        pytest.importorskip("anvil.lib.project_brief")
        from anvil.lib.project_brief import load_project_brief_strict

        project_dir = build_loose_file_in_existing_project(tmp_path)
        merge = BriefMergeOp(
            slug="board-update",
            slug_comment="enrolled-from: 2026-05-19-board-update.md "
            "(date: 2026-05-19)",
            inferred=True,
            todo_comment="TODO(operator): confirm",
        )
        p = _make_enroll_plan(tmp_path, merges=[merge])
        out = _append_brief_documents(ENROLL_OPERATOR_BRIEF, p)
        (project_dir / "BRIEF.md").write_text(out, encoding="utf-8")
        # The new slug has no dir yet (warns) — but the pre-existing
        # entries + appended entry must all parse strictly.
        with pytest.warns(UserWarning):
            brief = load_project_brief_strict(
                project_dir, validate_dirs=True
            )
        slugs = [d.slug for d in brief.documents]
        assert slugs == ["zeta-memo", "alpha-memo", "board-update"]
        # The preserved render_* fields parse back too.
        zeta = brief.documents[0]
        assert zeta.render_engine == "xelatex"
        assert zeta.render_metadata == {"doc-type": "Investment Memo"}
        assert zeta.latex_header_includes is not None
        assert brief.theme == "sphere-brand"

    def test_multiple_entries_appended_in_order(self, tmp_path):
        merges = [BriefMergeOp(slug="one"), BriefMergeOp(slug="two")]
        p = _make_enroll_plan(tmp_path, merges=merges)
        out = _append_brief_documents(ENROLL_OPERATOR_BRIEF, p)
        assert out.index("slug: one") < out.index("slug: two")

    def test_documents_block_boundary_not_fooled_by_block_scalar(
        self, tmp_path
    ):
        # `latex_header_includes: |` carries indented content; the
        # boundary scan must not stop inside it. Verified by the new
        # entry landing AFTER the alpha-memo entry (the block's end).
        merge = BriefMergeOp(slug="new-doc")
        p = _make_enroll_plan(tmp_path, merges=[merge])
        out = _append_brief_documents(ENROLL_OPERATOR_BRIEF, p)
        assert out.index("slug: alpha-memo") < out.index("slug: new-doc")
        # And the insertion stays inside the frontmatter.
        fm = out.split("\n---\n", 1)[0]
        assert "slug: new-doc" in fm


class TestAppendErrorCases:
    def test_no_frontmatter_refused(self, tmp_path):
        p = _make_enroll_plan(
            tmp_path, merges=[BriefMergeOp(slug="x")]
        )
        with pytest.raises(ValueError, match="frontmatter"):
            _append_brief_documents("# Just prose\n", p)

    def test_unterminated_frontmatter_refused(self, tmp_path):
        p = _make_enroll_plan(
            tmp_path, merges=[BriefMergeOp(slug="x")]
        )
        with pytest.raises(ValueError, match="unterminated"):
            _append_brief_documents("---\nproject: p\n", p)

    def test_missing_documents_key_refused(self, tmp_path):
        p = _make_enroll_plan(
            tmp_path, merges=[BriefMergeOp(slug="x")]
        )
        text = "---\nproject: p\naudience: []\n---\n\nBody.\n"
        with pytest.raises(ValueError, match="documents"):
            _append_brief_documents(text, p)

    def test_inline_documents_list_refused(self, tmp_path):
        p = _make_enroll_plan(
            tmp_path, merges=[BriefMergeOp(slug="x")]
        )
        text = "---\nproject: p\ndocuments: [a, b]\n---\n\nBody.\n"
        with pytest.raises(ValueError, match="documents"):
            _append_brief_documents(text, p)

    def test_render_enroll_brief_append_requires_existing_text(
        self, tmp_path
    ):
        p = _make_enroll_plan(
            tmp_path, merges=[BriefMergeOp(slug="x")]
        )
        with pytest.raises(ValueError, match="existing"):
            render_enroll_brief(p, existing_text=None)
