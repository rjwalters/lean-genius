"""Tests for ``anvil.skills.project-migrate.lib.detect`` (issue #297).

Coverage map:

- Pre-#283 classic projects classify as ``Shape.PRE_283_CLASSIC``.
- Post-#283 projects with `.anvil.json` classify as
  ``Shape.POST_283_ANVIL_JSON``.
- Fully-migrated projects classify as ``Shape.FULLY_MIGRATED``.
- Empty / non-anvil directories classify as ``Shape.UNKNOWN``.
- The foundry-shaped canary fixture classifies as PRE_283_CLASSIC.
- Inventory walks correctly enumerate per-thread `.anvil.json` files,
  skill-fixed body filenames, and version dirs.

Distinct filename per the #58 packaging convention. Lives next to the
skill rather than under ``tests/skills/project-migrate/`` so the skill is
self-contained.
"""

from __future__ import annotations

import sys
import unittest
from pathlib import Path
from tempfile import TemporaryDirectory

_HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(_HERE))

from _project_migrate_skill_lib import detect  # noqa: E402
from _fixtures import (  # noqa: E402
    build_foundry_shaped,
    build_fully_migrated,
    build_post_283_anvil_json,
    build_pre_283_classic,
)

Shape = detect.Shape
detect_shape = detect.detect_shape
inventory_project = detect.inventory_project


class TestDetectShape(unittest.TestCase):
    def test_pre_283_classic_classifies(self) -> None:
        with TemporaryDirectory() as td:
            project = build_pre_283_classic(Path(td))
            self.assertEqual(detect_shape(project), Shape.PRE_283_CLASSIC)

    def test_post_283_anvil_json_classifies(self) -> None:
        with TemporaryDirectory() as td:
            project = build_post_283_anvil_json(Path(td))
            self.assertEqual(detect_shape(project), Shape.POST_283_ANVIL_JSON)

    def test_fully_migrated_classifies(self) -> None:
        with TemporaryDirectory() as td:
            project = build_fully_migrated(Path(td))
            self.assertEqual(detect_shape(project), Shape.FULLY_MIGRATED)

    def test_foundry_shaped_classifies(self) -> None:
        with TemporaryDirectory() as td:
            project = build_foundry_shaped(Path(td))
            self.assertEqual(detect_shape(project), Shape.PRE_283_CLASSIC)

    def test_empty_dir_unknown(self) -> None:
        with TemporaryDirectory() as td:
            empty = Path(td) / "empty-project"
            empty.mkdir()
            self.assertEqual(detect_shape(empty), Shape.UNKNOWN)

    def test_nonexistent_unknown(self) -> None:
        with TemporaryDirectory() as td:
            missing = Path(td) / "does-not-exist"
            self.assertEqual(detect_shape(missing), Shape.UNKNOWN)


class TestInventory(unittest.TestCase):
    def test_pre_283_inventory_finds_threads(self) -> None:
        with TemporaryDirectory() as td:
            project = build_pre_283_classic(
                Path(td), project_name="acme", n_versions=3
            )
            inv = inventory_project(project)
            self.assertFalse(inv.has_project_brief)
            # Single thread (project_slug = "acme") with three memo.N versions.
            self.assertEqual(len(inv.threads), 1)
            thread = inv.threads[0]
            self.assertEqual(thread.slug, "acme")
            self.assertEqual(len(thread.version_dirs), 3)
            self.assertIn("memo.md", thread.body_filenames)
            # Extra .anvil.json at project root is recorded.
            self.assertEqual(len(inv.extra_anvil_jsons), 1)

    def test_post_283_inventory_finds_per_thread_anvil_jsons(self) -> None:
        with TemporaryDirectory() as td:
            project = build_post_283_anvil_json(Path(td))
            inv = inventory_project(project)
            self.assertTrue(inv.has_project_brief)
            # Two threads (investment-memo, latency-wall).
            slugs = sorted(t.slug for t in inv.threads)
            self.assertEqual(slugs, ["investment-memo", "latency-wall"])
            for thread in inv.threads:
                self.assertIsNotNone(thread.anvil_json_path)
                self.assertIn("memo.md", thread.body_filenames)

    def test_fully_migrated_inventory(self) -> None:
        with TemporaryDirectory() as td:
            project = build_fully_migrated(Path(td))
            inv = inventory_project(project)
            self.assertTrue(inv.has_project_brief)
            for thread in inv.threads:
                # Body filename equals slug.
                self.assertIn(f"{thread.slug}.md", thread.body_filenames)
                # No anvil.json.
                self.assertIsNone(thread.anvil_json_path)
            self.assertEqual(inv.extra_anvil_jsons, [])

    def test_foundry_shaped_inventory(self) -> None:
        with TemporaryDirectory() as td:
            project = build_foundry_shaped(Path(td))
            inv = inventory_project(project)
            self.assertEqual(len(inv.threads), 1)
            thread = inv.threads[0]
            self.assertEqual(thread.slug, "foundry")
            self.assertEqual(len(thread.version_dirs), 3)
            self.assertIn("memo.md", thread.body_filenames)


if __name__ == "__main__":
    unittest.main()
