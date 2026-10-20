"""Composed-skill smoke tests for `anvil:project-scout` (issue #407, AC 5).

Scout's recommended-action strings must point at sibling capabilities
that actually accept the named dir/file:

- LEGACY_MIGRATABLE / BARE_THREADS clusters: ``detect_shape`` on the
  recommended dir returns the expected non-UNKNOWN shape (the dir is a
  valid `/anvil:project-migrate <dir>` input).
- LOOSE_DOCUMENTS files: #406's enroll plan builds for the named file
  (dry-run planning is pure, so this is a real end-to-end composition
  check with zero mutations).

Project-migrate's lib is loaded via ITS OWN unique-package helper
(``_project_migrate_skill_lib`` → ``project_migrate_lib``), which is
idempotent — safe whichever suite loads it first in a combined pytest
run.
"""

from __future__ import annotations

import sys
import unittest
from pathlib import Path
from tempfile import TemporaryDirectory

_HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(_HERE))

# Load project-migrate's lib through its own loader (idempotent).
_MIGRATE_TESTS = (
    _HERE.parents[1] / "project-migrate" / "tests"
)
if str(_MIGRATE_TESTS) not in sys.path:
    sys.path.insert(0, str(_MIGRATE_TESTS))

from _project_migrate_skill_lib import detect, enroll  # noqa: E402
from _project_scout_skill_lib import cluster, orchestrate  # noqa: E402
from _scout_fixtures import build_mega_tree  # noqa: E402


class TestComposedSmoke(unittest.TestCase):
    def test_migratable_cluster_dirs_are_valid_migrate_inputs(self) -> None:
        with TemporaryDirectory() as td:
            root = Path(td).resolve()
            build_mega_tree(root)
            result = orchestrate.run(root)
            expected_shapes = {
                cluster.BUCKET_LEGACY_MIGRATABLE: detect.Shape.PRE_283_CLASSIC,
                cluster.BUCKET_BARE_THREADS: detect.Shape.PRE_283_CLASSIC,
            }
            checked = 0
            for entry in result.data["clusters"]:
                if entry["bucket"] not in expected_shapes:
                    continue
                # The recommended command names the dir relative to root.
                cmd = entry["recommended_command"]
                self.assertTrue(cmd.startswith("/anvil:project-migrate "))
                rel = cmd.split(" ", 1)[1]
                target = root / rel
                self.assertTrue(target.is_dir(), target)
                shape = detect.detect_shape(target)
                self.assertIs(shape, expected_shapes[entry["bucket"]])
                self.assertIsNot(shape, detect.Shape.UNKNOWN)
                checked += 1
            self.assertGreaterEqual(checked, 2)

    def test_bare_cluster_synthesis_substate_via_migrate(self) -> None:
        """The BARE_THREADS note promises automatic BRIEF synthesis —
        verify migrate's own is_bare predicate agrees on the named dir."""
        with TemporaryDirectory() as td:
            root = Path(td).resolve()
            build_mega_tree(root)
            result = orchestrate.run(root)
            bare = [
                c
                for c in result.data["clusters"]
                if c["bucket"] == cluster.BUCKET_BARE_THREADS
            ]
            self.assertEqual(len(bare), 1)
            rel = bare[0]["recommended_command"].split(" ", 1)[1]
            inv = detect.inventory_project(root / rel)
            self.assertTrue(inv.is_bare)

    def test_loose_document_builds_enroll_plan(self) -> None:
        with TemporaryDirectory() as td:
            root = Path(td).resolve()
            build_mega_tree(root)
            result = orchestrate.run(root)
            enrollable = [
                d
                for d in result.data["loose_documents"]
                if d["recommended_command"]
            ]
            self.assertTrue(enrollable)
            # Take one outside-cluster candidate and one in-cluster one.
            outside = [
                d for d in enrollable if d["enclosing_cluster"] is None
            ][0]
            inside = [
                d
                for d in enrollable
                if d["enclosing_cluster"] is not None
            ][0]
            for entry in (outside, inside):
                rel = entry["recommended_command"].split("--enroll ", 1)[1]
                target = root / rel
                self.assertTrue(target.is_file(), target)
                # Dry-run planning is pure — building the plan IS the
                # smoke test that enroll accepts the path.
                plan = enroll.build_enroll_plan([target])
                self.assertIs(plan.shape, detect.Shape.ENROLL)
                self.assertEqual(len(plan.documents), 1)

    def test_already_migrated_and_foreign_get_no_command(self) -> None:
        with TemporaryDirectory() as td:
            root = Path(td).resolve()
            build_mega_tree(root)
            result = orchestrate.run(root)
            for entry in result.data["clusters"]:
                if entry["bucket"] in (
                    cluster.BUCKET_ALREADY_MIGRATED,
                    cluster.BUCKET_FOREIGN_GRAMMAR,
                ):
                    self.assertIsNone(entry["recommended_command"])


if __name__ == "__main__":
    unittest.main()
