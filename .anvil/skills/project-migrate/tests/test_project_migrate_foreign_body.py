"""Tests for foreign (non-anvil) body filename rename + --artifact-type
on the bare-shape main mode (issue #878).

`anvil:essay` documents `anvil:project-migrate` as the supported path for
migrating a consumer's `post.md` corpus, but the bare-shape synthesis
defaulted every thread to `artifact_type: investment-memo` (the only value
the renamer's `_SKILL_FIXED_BODY_FILENAMES` scan could ever produce for a
plain `.md` body), and the correct declaration (`artifact_type: essay`)
would have to come from the very BRIEF the run is synthesizing — circular.
Separately, `post.md` matches no anvil skill's historical fixed name, so
the rename loop had nothing to match at all.

This suite covers the fix (composing options 1 + 2 of the issue's
suggested acceptance criteria):

1. Detection: `_foreign_md_body_candidates` / `_detect_foreign_md_body_filename`
   recognize a single consistent non-anvil `.md` body across a bare
   thread's version dirs.
2. Plan: the foreign body is renamed to `<slug>.md` in the dry-run plan
   (reviewable before apply) even with no `--artifact-type` given; the
   ambiguous multi-candidate case plans NO rename and surfaces a note
   instead of guessing.
3. `--artifact-type` on the main mode (`build_plan` / `orchestrate.run`)
   is applied to the synthesized `documents:` entry with no TODO marker,
   closing the circularity; an unregistered value is a plan-time refusal
   (`PlanError`) before any mutation.
4. End-to-end `--apply`: the body renames land, cross-thread refs (if
   any) rewrite, the BRIEF carries the declared type, and the migrated
   project passes `discover_thread_root` + `verify_migration`.
5. Idempotence: re-running after apply is a no-op.

Per the #58 packaging convention this filename is unique across the
``anvil/skills/*/tests/`` tree.
"""

from __future__ import annotations

import sys
import unittest
from pathlib import Path
from tempfile import TemporaryDirectory

_HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(_HERE))

from _project_migrate_skill_lib import (  # noqa: E402
    apply_mod,
    detect,
    orchestrate,
    plan,
    verify,
)
from _fixtures import (  # noqa: E402
    build_bare_ambiguous_md_body_threads,
    build_bare_foreign_md_body_threads,
    build_bare_version_dir_threads,
)

Shape = detect.Shape
inventory_project = detect.inventory_project
build_plan = plan.build_plan
PlanError = plan.PlanError
render_project_brief = apply_mod.render_project_brief
run = orchestrate.run
verify_migration = verify.verify_migration

SLUG = "wave-two-five-blocks"


class TestForeignBodyDetection(unittest.TestCase):
    """AC 1 — a single consistent non-anvil .md body is recognized."""

    def test_shape_stays_pre_283_classic_bare(self) -> None:
        """The definitional edge case from the issue: a foreign fixed
        body filename is still BARE — is_bare must not flip false just
        because *some* pipeline fixed the name."""
        with TemporaryDirectory() as td:
            project = build_bare_foreign_md_body_threads(Path(td))
            self.assertEqual(
                detect.detect_shape(project), Shape.PRE_283_CLASSIC
            )
            inv = inventory_project(project)
            self.assertTrue(inv.is_bare)
            self.assertEqual(len(inv.threads), 1)
            thread = inv.threads[0]
            self.assertEqual(thread.slug, SLUG)
            self.assertEqual(thread.body_filenames, ["post.md"])

    def test_single_foreign_candidate_detected(self) -> None:
        with TemporaryDirectory() as td:
            project = build_bare_foreign_md_body_threads(Path(td))
            inv = inventory_project(project)
            thread = inv.threads[0]
            self.assertEqual(
                plan._foreign_md_body_candidates(thread), ["post.md"]
            )
            self.assertEqual(
                plan._detect_foreign_md_body_filename(thread), "post.md"
            )

    def test_ambiguous_candidates_return_none(self) -> None:
        with TemporaryDirectory() as td:
            project = build_bare_ambiguous_md_body_threads(Path(td))
            inv = inventory_project(project)
            thread = inv.threads[0]
            self.assertEqual(
                plan._foreign_md_body_candidates(thread),
                ["draft.md", "post.md"],
            )
            self.assertIsNone(plan._detect_foreign_md_body_filename(thread))


class TestForeignBodyPlan(unittest.TestCase):
    """AC 2 — dry-run plan shows the body renames it would perform."""

    def test_plan_renames_foreign_body_to_slug_md(self) -> None:
        with TemporaryDirectory() as td:
            project = build_bare_foreign_md_body_threads(Path(td))
            p = build_plan(project)
            self.assertEqual(len(p.documents), 1)
            doc = p.documents[0]
            # Every version dir's post.md is planned for rename, alongside
            # the pre-283 directory-nesting move.
            body_renames = [
                r for r in doc.renames if r.source.name == "post.md"
            ]
            self.assertEqual(len(body_renames), 3)
            for r in body_renames:
                self.assertEqual(r.target.name, f"{SLUG}.md")
                # Body rename references the POST-MOVE version dir path
                # (the directory nesting move runs first).
                self.assertEqual(r.target.parent, r.source.parent)
                self.assertIn(f"{SLUG}/{SLUG}.", str(r.source))
            notes = "\n".join(doc.notes)
            self.assertIn("post.md", notes)
            self.assertIn("TODO(operator)", notes)
            self.assertTrue(
                any("post.md" in t for t in doc.operator_todos)
            )

    def test_ambiguous_plans_no_rename_but_notes(self) -> None:
        with TemporaryDirectory() as td:
            project = build_bare_ambiguous_md_body_threads(Path(td))
            p = build_plan(project)
            doc = p.documents[0]
            body_renames = [
                r for r in doc.renames
                if r.source.name in ("post.md", "draft.md")
            ]
            self.assertEqual(body_renames, [])
            notes = "\n".join(doc.notes)
            self.assertIn("ambiguous", notes)
            self.assertIn("post.md", notes)
            self.assertIn("draft.md", notes)

    def test_default_artifact_type_still_todo_marked_without_flag(
        self,
    ) -> None:
        """Without --artifact-type, the body rename still happens but the
        BRIEF entry keeps the honest memo-class default + TODO marker
        (never silently 'essay')."""
        with TemporaryDirectory() as td:
            project = build_bare_foreign_md_body_threads(Path(td))
            p = build_plan(project)
            doc = p.documents[0]
            self.assertEqual(
                doc.brief_merge.artifact_type, "investment-memo"
            )
            self.assertTrue(doc.brief_merge.inferred)
            self.assertIsNotNone(doc.brief_merge.todo_comment)

    def test_regular_bare_tex_thread_unaffected(self) -> None:
        """Regression: the pre-existing .tex-bodied bare fixture keeps
        its inference path untouched by the new .md detection."""
        with TemporaryDirectory() as td:
            project = build_bare_version_dir_threads(Path(td))
            p = build_plan(project)
            doc = p.documents[0]
            self.assertEqual(doc.brief_merge.artifact_type, "paper")
            body_renames = [
                r for r in doc.renames if r.target.suffix == ".md"
            ]
            self.assertEqual(body_renames, [])


class TestArtifactTypeFlag(unittest.TestCase):
    """AC 3 — --artifact-type on the main mode closes the circularity."""

    def test_artifact_type_applied_no_todo(self) -> None:
        with TemporaryDirectory() as td:
            project = build_bare_foreign_md_body_threads(Path(td))
            p = build_plan(project, artifact_type="essay")
            doc = p.documents[0]
            self.assertEqual(doc.brief_merge.artifact_type, "essay")
            self.assertFalse(doc.brief_merge.inferred)
            self.assertIsNone(doc.brief_merge.todo_comment)
            # The body rename still happens regardless of the flag.
            body_renames = [
                r for r in doc.renames if r.source.name == "post.md"
            ]
            self.assertEqual(len(body_renames), 3)

    def test_invalid_artifact_type_raises_planerror_pre_mutation(
        self,
    ) -> None:
        with TemporaryDirectory() as td:
            project = build_bare_foreign_md_body_threads(Path(td))
            before = sorted(p.name for p in project.rglob("*"))
            with self.assertRaises(PlanError):
                build_plan(project, artifact_type="not-a-real-type")
            after = sorted(p.name for p in project.rglob("*"))
            self.assertEqual(before, after)

    def test_orchestrate_run_threads_artifact_type(self) -> None:
        with TemporaryDirectory() as td:
            project = build_bare_foreign_md_body_threads(Path(td))
            result = run(project, apply=False, artifact_type="essay")
            self.assertTrue(result.success)
            self.assertIn("artifact_type: essay", result.report)
            self.assertNotIn(
                "artifact_type: essay  # TODO", result.report
            )

    def test_non_bare_project_ignores_artifact_type(self) -> None:
        """--artifact-type only applies to bare-synthesized entries; a
        non-bare thread's declared/legacy type is untouched."""
        with TemporaryDirectory() as td:
            from _fixtures import build_pre_283_classic

            project = build_pre_283_classic(Path(td))
            p = build_plan(project, artifact_type="essay")
            doc = p.documents[0]
            self.assertEqual(
                doc.brief_merge.artifact_type, "investment-memo"
            )


class TestForeignBodyApply(unittest.TestCase):
    """AC 4 — end-to-end apply lands the rename + declared type."""

    def test_apply_renames_bodies_and_writes_declared_type(self) -> None:
        with TemporaryDirectory() as td:
            project = build_bare_foreign_md_body_threads(Path(td))
            result = run(project, apply=True, artifact_type="essay")
            self.assertTrue(result.success, result.report)

            thread_root = project / SLUG
            for n in (1, 2, 3):
                version_dir = thread_root / f"{SLUG}.{n}"
                self.assertTrue(
                    (version_dir / f"{SLUG}.md").is_file(), version_dir
                )
                self.assertFalse((version_dir / "post.md").exists())

            brief = (project / "BRIEF.md").read_text(encoding="utf-8")
            self.assertIn("artifact_type: essay", brief)
            self.assertNotIn("artifact_type: essay  # TODO", brief)

    def test_post_apply_verify_and_discovery(self) -> None:
        try:
            from anvil.lib.project_discovery import discover_thread_root
        except ImportError:
            self.skipTest("anvil.lib not importable in this environment")
            return
        with TemporaryDirectory() as td:
            project = build_bare_foreign_md_body_threads(Path(td))
            result = run(project, apply=True, artifact_type="essay")
            self.assertTrue(result.success, result.report)

            vr = verify_migration(project)
            self.assertTrue(vr.ok, vr.to_report())

            deep_path = project / SLUG / f"{SLUG}.3" / f"{SLUG}.md"
            discovery = discover_thread_root(deep_path)
            self.assertIsNotNone(discovery)
            self.assertEqual(discovery.slug, SLUG)


class TestForeignBodyIdempotence(unittest.TestCase):
    """AC 5 — re-running after apply is a no-op."""

    def test_reapply_is_noop(self) -> None:
        with TemporaryDirectory() as td:
            project = build_bare_foreign_md_body_threads(Path(td))
            first = run(project, apply=True, artifact_type="essay")
            self.assertTrue(first.success, first.report)

            second = run(project, apply=True)
            self.assertTrue(second.success, second.report)
            self.assertEqual(second.shape, Shape.FULLY_MIGRATED)
            self.assertTrue(second.plan.is_noop)


if __name__ == "__main__":
    unittest.main()
