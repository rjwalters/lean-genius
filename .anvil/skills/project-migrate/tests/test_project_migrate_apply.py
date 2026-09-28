"""Tests for ``anvil.skills.project-migrate.lib.apply`` (issue #297).

Covers apply correctness:

- Pre-#283 → fully-migrated end-to-end (the studio-shaped acceptance
  criterion).
- Body filenames become `<slug>.md`.
- Version dirs become `<slug>/<slug>.N/`.
- `.anvil.json` files disappear from the project tree.
- BRIEF.md is written and lists every document.
- Cross-thread refs are rewritten in body markdown.
- Critic siblings are renamed.

Uses ``use_git=False`` to exercise the plain rename path; git integration
is tested separately.
"""

from __future__ import annotations

import sys
import unittest
from pathlib import Path
from tempfile import TemporaryDirectory

_HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(_HERE))

from _project_migrate_skill_lib import apply_mod, detect, plan  # noqa: E402
from _fixtures import (  # noqa: E402
    build_foundry_shaped,
    build_post_283_anvil_json,
    build_pre_283_classic,
)

ROLLBACK_SUBDIR = apply_mod.ROLLBACK_SUBDIR
apply_plan = apply_mod.apply_plan
Shape = detect.Shape
inventory_project = detect.inventory_project
build_plan = plan.build_plan


class TestApplyPre283(unittest.TestCase):
    def test_full_migration_produces_fully_migrated_shape(self) -> None:
        with TemporaryDirectory() as td:
            project = build_pre_283_classic(
                Path(td), project_name="acme", n_versions=2
            )
            plan = build_plan(project, Shape.PRE_283_CLASSIC)
            result = apply_plan(plan, use_git=False)

            self.assertFalse(
                result.failed_docs,
                f"expected no failures, got: {result.failed_docs}",
            )
            self.assertTrue(result.brief_written)

            # Inspect the resulting shape.
            inv = inventory_project(project)
            self.assertTrue(inv.has_project_brief)
            self.assertEqual(len(inv.threads), 1)
            thread = inv.threads[0]
            self.assertEqual(thread.slug, "acme")
            # Version dirs renamed to acme.N.
            for vd in thread.version_dirs:
                self.assertTrue(vd.name.startswith("acme."))
            # Body filename is acme.md.
            self.assertIn("acme.md", thread.body_filenames)
            self.assertNotIn("memo.md", thread.body_filenames)

    def test_anvil_json_removed_after_apply(self) -> None:
        with TemporaryDirectory() as td:
            project = build_pre_283_classic(Path(td), project_name="acme")
            plan = build_plan(project, Shape.PRE_283_CLASSIC)
            apply_plan(plan, use_git=False)
            anvil_jsons = list(project.rglob(".anvil.json"))
            # Ignore rollback dir if present.
            anvil_jsons = [
                p for p in anvil_jsons
                if ROLLBACK_SUBDIR not in p.parts
            ]
            self.assertEqual(anvil_jsons, [])

    def test_rollback_dir_removed_after_success(self) -> None:
        with TemporaryDirectory() as td:
            project = build_pre_283_classic(Path(td), project_name="acme")
            plan = build_plan(project, Shape.PRE_283_CLASSIC)
            apply_plan(plan, use_git=False)
            rollback = project / ROLLBACK_SUBDIR
            self.assertFalse(
                rollback.exists(),
                "rollback dir should be cleaned up on success",
            )

    def test_cross_thread_ref_actually_rewritten_in_body(self) -> None:
        with TemporaryDirectory() as td:
            project = build_pre_283_classic(
                Path(td), project_name="acme", n_versions=3
            )
            plan = build_plan(project, Shape.PRE_283_CLASSIC)
            apply_plan(plan, use_git=False)
            # Read the v3 body — should reference acme.2, not memo.2.
            v3_body = project / "acme" / "acme.3" / "acme.md"
            self.assertTrue(v3_body.is_file())
            text = v3_body.read_text()
            self.assertIn("acme.2", text)
            self.assertNotIn("memo.2", text)


class TestApplyPost283(unittest.TestCase):
    def test_renames_body_and_merges_anvil_json(self) -> None:
        with TemporaryDirectory() as td:
            project = build_post_283_anvil_json(Path(td))
            plan = build_plan(project, Shape.POST_283_ANVIL_JSON)
            result = apply_plan(plan, use_git=False)
            self.assertFalse(result.failed_docs)
            # Body files renamed to <slug>.md.
            for slug in ("investment-memo", "latency-wall"):
                expected_body = (
                    project / slug / f"{slug}.1" / f"{slug}.md"
                )
                self.assertTrue(
                    expected_body.is_file(),
                    f"missing {expected_body}",
                )
                old_body = (
                    project / slug / f"{slug}.1" / "memo.md"
                )
                self.assertFalse(
                    old_body.exists(),
                    f"unexpected legacy body {old_body}",
                )
            # No .anvil.json remains.
            anvil_jsons = [
                p for p in project.rglob(".anvil.json")
                if ROLLBACK_SUBDIR not in p.parts
            ]
            self.assertEqual(anvil_jsons, [])

    def test_brief_lists_every_document(self) -> None:
        with TemporaryDirectory() as td:
            project = build_post_283_anvil_json(Path(td))
            plan = build_plan(project, Shape.POST_283_ANVIL_JSON)
            apply_plan(plan, use_git=False)
            brief = (project / "BRIEF.md").read_text()
            self.assertIn("slug: investment-memo", brief)
            self.assertIn("slug: latency-wall", brief)
            # rubric_overrides merged from `.anvil.json`.
            self.assertIn("rubric_overrides:", brief)
            # memo_subtype may or may not be quoted depending on the YAML
            # emitter; accept either form.
            self.assertTrue(
                "memo_subtype: synthesis-brief" in brief
                or 'memo_subtype: "synthesis-brief"' in brief,
                f"expected memo_subtype synthesis-brief in BRIEF, got: {brief!r}",
            )


class TestApplyFoundry(unittest.TestCase):
    def test_critic_siblings_landed_correctly(self) -> None:
        with TemporaryDirectory() as td:
            project = build_foundry_shaped(Path(td))
            plan = build_plan(project, Shape.PRE_283_CLASSIC)
            apply_plan(plan, use_git=False)
            # The review siblings should now be at foundry/foundry.<n>.review/.
            for n in (1, 2, 3):
                review_dir = (
                    project / "foundry" / f"foundry.{n}.review"
                )
                self.assertTrue(
                    review_dir.is_dir(),
                    f"expected {review_dir} to exist",
                )
                verdict = review_dir / "verdict.md"
                self.assertTrue(
                    verdict.is_file(),
                    f"expected verdict at {verdict}",
                )
            # The audit sibling on memo.2 should land at
            # foundry/foundry.2.audit/.
            audit_dir = project / "foundry" / "foundry.2.audit"
            self.assertTrue(audit_dir.is_dir())


if __name__ == "__main__":
    unittest.main()
