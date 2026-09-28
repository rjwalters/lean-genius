"""Tests for `anvil:project-share` dry-run no-mutation contract (issue #396).

`--dry-run` must be SHA-256-verifiably side-effect-free: snapshot every
file in the project tree, run `orchestrate.run(project, dry_run=True)`,
snapshot again, and assert byte-identity (mirrors the
rubric-rebackport dry-run suite).
"""

from __future__ import annotations

import sys
import unittest
from pathlib import Path
from tempfile import TemporaryDirectory
from anvil.lib.testing import tree_hash as _tree_hash

_HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(_HERE))

from _project_share_skill_lib import orchestrate  # noqa: E402
from _share_fixtures import (  # noqa: E402
    build_full_project,
    build_project_with_unstarted_slug,
)


class TestDryRunNoMutations(unittest.TestCase):
    def test_dry_run_byte_identical(self) -> None:
        with TemporaryDirectory() as td:
            project = build_full_project(Path(td))
            before = _tree_hash(project)
            result = orchestrate.run(project, dry_run=True)
            self.assertTrue(result.success)
            after = _tree_hash(project)
            self.assertEqual(
                before, after, "dry-run mutated the project tree"
            )
            self.assertFalse((project / "SHARE").exists())

    def test_dry_run_with_zip_flag_writes_nothing(self) -> None:
        with TemporaryDirectory() as td:
            project = build_full_project(Path(td))
            before = _tree_hash(project)
            orchestrate.run(project, dry_run=True, zip_output=True)
            after = _tree_hash(project)
            self.assertEqual(before, after)
            self.assertEqual(list(project.glob("*.zip")), [])

    def test_dry_run_over_foreign_out_dir_writes_nothing(self) -> None:
        with TemporaryDirectory() as td:
            project = build_full_project(Path(td))
            foreign = project / "SHARE"
            foreign.mkdir()
            (foreign / "precious.txt").write_text("keep me\n")
            before = _tree_hash(project)
            orchestrate.run(project, dry_run=True)
            after = _tree_hash(project)
            self.assertEqual(before, after)
            self.assertTrue((foreign / "precious.txt").is_file())

    def test_dry_run_with_failed_doc_reports_failure(self) -> None:
        with TemporaryDirectory() as td:
            project = build_project_with_unstarted_slug(Path(td))
            before = _tree_hash(project)
            result = orchestrate.run(project, dry_run=True)
            after = _tree_hash(project)
            self.assertEqual(before, after)
            # The unresolved doc surfaces as a failure even in dry-run.
            self.assertFalse(result.success)
            self.assertIn("unstarted-deck", result.report)


class TestDryRunReport(unittest.TestCase):
    def test_report_carries_plan_details(self) -> None:
        with TemporaryDirectory() as td:
            project = build_full_project(Path(td))
            result = orchestrate.run(project, dry_run=True)
            self.assertIn("dry-run", result.report)
            self.assertIn("00-series-a-deck", result.report)
            self.assertIn("pinned-symlink", result.report)
            self.assertIn("walk-to-highest", result.report)
            self.assertIsNone(result.apply_result)
            self.assertIsNone(result.verify_result)


class TestDryRunWithCover(unittest.TestCase):
    """Issue #757: dry-run reports the planned cover copy, writes nothing."""

    def test_cover_reported_and_no_writes(self) -> None:
        with TemporaryDirectory() as td:
            project = build_full_project(
                Path(td),
                export_block="export:\n  cover: SHARE-README.md\n",
            )
            (project / "SHARE-README.md").write_text(
                "# Welcome\n", encoding="utf-8"
            )
            before = _tree_hash(project)
            result = orchestrate.run(project, dry_run=True)
            after = _tree_hash(project)
            self.assertEqual(before, after)
            self.assertTrue(result.success, result.report)
            self.assertIn("Cover note", result.report)
            self.assertIn("README.md", result.report)
            self.assertFalse((project / "SHARE").exists())


if __name__ == "__main__":
    unittest.main()
