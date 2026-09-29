"""Tests for ``anvil.skills.project-migrate.lib.plan`` (issue #297).

Covers per-shape plan generation:

- Pre-#283 plans rename memo.N → <slug>/<slug>.N and bring critic
  siblings along.
- Pre-#283 plans rewrite cross-thread refs (canary case: ``memo.2`` →
  ``<slug>.2``).
- Pre-#283 plans absorb root `.anvil.json` into the first thread's BRIEF
  merge.
- Post-#283 plans rename memo.md → <slug>.md and merge per-thread
  `.anvil.json` into BRIEF.
- Fully-migrated plans are no-ops.
"""

from __future__ import annotations

import sys
import unittest
from pathlib import Path
from tempfile import TemporaryDirectory

_HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(_HERE))

from _project_migrate_skill_lib import detect, plan  # noqa: E402
from _fixtures import (  # noqa: E402
    build_foundry_shaped,
    build_fully_migrated,
    build_post_283_anvil_json,
    build_pre_283_classic,
)

Shape = detect.Shape
build_plan = plan.build_plan


class TestPlanFullyMigrated(unittest.TestCase):
    def test_noop_plan(self) -> None:
        with TemporaryDirectory() as td:
            project = build_fully_migrated(Path(td))
            plan = build_plan(project, Shape.FULLY_MIGRATED)
            self.assertTrue(plan.is_noop)
            for doc in plan.documents:
                self.assertTrue(doc.is_noop)


class TestPlanPost283(unittest.TestCase):
    def test_renames_memo_md_to_slug_md(self) -> None:
        with TemporaryDirectory() as td:
            project = build_post_283_anvil_json(Path(td))
            plan = build_plan(project, Shape.POST_283_ANVIL_JSON)
            self.assertEqual(len(plan.documents), 2)
            for doc in plan.documents:
                renames = doc.renames
                target_filenames = {r.target.name for r in renames}
                self.assertIn(f"{doc.slug}.md", target_filenames)

    def test_merges_anvil_json_into_brief(self) -> None:
        with TemporaryDirectory() as td:
            project = build_post_283_anvil_json(Path(td))
            plan = build_plan(project, Shape.POST_283_ANVIL_JSON)
            for doc in plan.documents:
                self.assertIsNotNone(doc.brief_merge)
                self.assertIsNotNone(doc.anvil_json_to_delete)
                # `.anvil.json` carried target_length and rubric_overrides
                # in the fixture; both should land in the merge.
                self.assertEqual(
                    doc.brief_merge.target_length, (5000, 8000)
                )
                self.assertIsNotNone(doc.brief_merge.rubric_overrides)


class TestPlanPre283(unittest.TestCase):
    def test_renames_memo_n_to_slug_n(self) -> None:
        with TemporaryDirectory() as td:
            project = build_pre_283_classic(
                Path(td), project_name="acme", n_versions=2
            )
            plan = build_plan(project, Shape.PRE_283_CLASSIC)
            self.assertEqual(len(plan.documents), 1)
            doc = plan.documents[0]
            self.assertEqual(doc.slug, "acme")
            # Should have version-dir renames: memo.1 → acme/acme.1;
            # memo.2 → acme/acme.2. Body renames also fire (memo.md →
            # acme.md) but those source paths are inside the version
            # dirs and don't start with "memo." prefix at the parent
            # level — we filter to top-level version-dir renames here.
            project_resolved = project.resolve()
            top_level_version_renames = [
                r for r in doc.renames
                if r.source.parent == project_resolved
                and r.source.name.startswith("memo.")
            ]
            self.assertEqual(len(top_level_version_renames), 2)
            for r in top_level_version_renames:
                self.assertTrue(r.target.name.startswith("acme."))

    def test_promotes_anvil_json_to_brief_merge(self) -> None:
        with TemporaryDirectory() as td:
            project = build_pre_283_classic(Path(td), project_name="acme")
            plan = build_plan(project, Shape.PRE_283_CLASSIC)
            doc = plan.documents[0]
            self.assertIsNotNone(doc.brief_merge)
            self.assertEqual(
                doc.brief_merge.target_length, (8000, 11000)
            )

    def test_rewrites_cross_thread_refs(self) -> None:
        with TemporaryDirectory() as td:
            # Pre-#283 fixture writes "See memo.N for prior context."
            project = build_pre_283_classic(
                Path(td), project_name="acme", n_versions=3
            )
            plan = build_plan(project, Shape.PRE_283_CLASSIC)
            doc = plan.documents[0]
            # memo.2 → acme.2 should be rewritten in v2 and v3 bodies
            # (which both reference an earlier memo.N).
            rewritten = [
                r for r in doc.content_rewrites if "memo." in r.old_string
            ]
            self.assertGreater(
                len(rewritten),
                0,
                "expected at least one cross-thread ref rewrite",
            )
            for rw in rewritten:
                self.assertTrue(rw.old_string.startswith("memo."))
                self.assertTrue(rw.new_string.startswith("acme."))


class TestPlanFoundry(unittest.TestCase):
    def test_critic_siblings_renamed_alongside_version_dirs(self) -> None:
        with TemporaryDirectory() as td:
            project = build_foundry_shaped(Path(td))
            plan = build_plan(project, Shape.PRE_283_CLASSIC)
            doc = plan.documents[0]
            renames = doc.renames
            # Find renames where the source name contains ".review" or
            # ".audit" — those are critic siblings.
            critic_renames = [
                r for r in renames
                if any(k in r.source.name for k in (".review", ".audit"))
            ]
            self.assertGreater(
                len(critic_renames),
                0,
                "expected critic siblings to be planned for rename",
            )
            for r in critic_renames:
                self.assertTrue(r.target.name.startswith("foundry."))

    def test_canary_memo_2_cross_ref_rewritten(self) -> None:
        with TemporaryDirectory() as td:
            project = build_foundry_shaped(Path(td))
            plan = build_plan(project, Shape.PRE_283_CLASSIC)
            doc = plan.documents[0]
            # foundry/memo.3/memo.md references "memo.2" — should be
            # rewritten to "foundry.2".
            rewrites = [
                r for r in doc.content_rewrites
                if r.old_string == "memo.2" and r.new_string == "foundry.2"
            ]
            self.assertGreater(len(rewrites), 0)


if __name__ == "__main__":
    unittest.main()
