"""Tests for `anvil:project-migrate` idempotence (issue #297).

Re-running `--apply` on a fully-migrated project must be a zero-diff
no-op. This is the safety-net for operators who lose track of which
projects they've already migrated, AND for the validation step that
re-runs the planner on the post-apply tree.

Acceptance criterion: re-running --apply on a migrated project is
zero-diff.
"""

from __future__ import annotations

import sys
import unittest
from pathlib import Path
from tempfile import TemporaryDirectory
from anvil.lib.testing import tree_hash as _tree_hash

_HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(_HERE))

from _project_migrate_skill_lib import orchestrate  # noqa: E402
from _fixtures import (  # noqa: E402
    build_fully_migrated,
    build_post_283_anvil_json,
    build_pre_283_classic,
)

run = orchestrate.run


class TestIdempotence(unittest.TestCase):
    def test_fully_migrated_apply_is_noop(self) -> None:
        with TemporaryDirectory() as td:
            project = build_fully_migrated(Path(td))
            before = _tree_hash(project)
            result = run(project, apply=True)
            self.assertTrue(result.success)
            after = _tree_hash(project)
            self.assertEqual(
                before,
                after,
                "apply on fully-migrated project mutated the tree",
            )

    def test_double_apply_pre_283_is_idempotent(self) -> None:
        """After applying once, re-applying must be byte-identical."""
        with TemporaryDirectory() as td:
            project = build_pre_283_classic(Path(td), project_name="acme")
            # First apply: pre-#283 → fully migrated.
            first = run(project, apply=True)
            self.assertTrue(first.success)
            tree_after_first = _tree_hash(project)
            # Second apply: should be a no-op.
            second = run(project, apply=True)
            self.assertTrue(second.success)
            tree_after_second = _tree_hash(project)
            self.assertEqual(
                tree_after_first,
                tree_after_second,
                "second apply mutated a fully-migrated project",
            )

    def test_double_apply_post_283_is_idempotent(self) -> None:
        with TemporaryDirectory() as td:
            project = build_post_283_anvil_json(Path(td))
            first = run(project, apply=True)
            self.assertTrue(first.success)
            tree_after_first = _tree_hash(project)
            second = run(project, apply=True)
            self.assertTrue(second.success)
            tree_after_second = _tree_hash(project)
            self.assertEqual(tree_after_first, tree_after_second)


if __name__ == "__main__":
    unittest.main()
