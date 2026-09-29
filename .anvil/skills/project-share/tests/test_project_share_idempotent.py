"""Tests for `anvil:project-share` rebuild idempotence (issue #396).

Two runs over the same inputs (with a pinned build timestamp) produce
byte-identical export trees; a doc dropped between runs disappears from
the rebuilt export (no stale folders — blow-away rebuild contract).
"""

from __future__ import annotations

import sys
import unittest
from datetime import datetime, timezone
from pathlib import Path
from tempfile import TemporaryDirectory
from anvil.lib.testing import tree_hash as _tree_hash

_HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(_HERE))

from _project_share_skill_lib import orchestrate  # noqa: E402
from _share_fixtures import brief_text, build_full_project  # noqa: E402

NOW = datetime(2026, 6, 9, 12, 0, 0, tzinfo=timezone.utc)


class TestIdempotentRebuild(unittest.TestCase):
    def test_two_runs_pinned_timestamp_byte_identical(self) -> None:
        with TemporaryDirectory() as td:
            project = build_full_project(Path(td))
            r1 = orchestrate.run(project, now=NOW)
            self.assertTrue(r1.success, r1.report)
            first = _tree_hash(project / "SHARE")
            r2 = orchestrate.run(project, now=NOW)
            self.assertTrue(r2.success, r2.report)
            second = _tree_hash(project / "SHARE")
            self.assertEqual(first, second)

    def test_timestamp_is_the_only_diff_without_pinning(self) -> None:
        with TemporaryDirectory() as td:
            project = build_full_project(Path(td))
            orchestrate.run(
                project,
                now=datetime(2026, 6, 8, 9, 0, 0, tzinfo=timezone.utc),
            )
            first = _tree_hash(project / "SHARE")
            orchestrate.run(
                project,
                now=datetime(2026, 6, 9, 9, 0, 0, tzinfo=timezone.utc),
            )
            second = _tree_hash(project / "SHARE")
            differing = {
                rel
                for rel in set(first) | set(second)
                if first.get(rel) != second.get(rel)
            }
            self.assertEqual(differing, {"EXPORT.md"})

    def test_stale_doc_folder_disappears_on_rebuild(self) -> None:
        """First export all three docs; then narrow `export.order` to
        two and re-run — the dropped doc's folder must be gone."""
        with TemporaryDirectory() as td:
            project = build_full_project(Path(td))
            r1 = orchestrate.run(project, now=NOW)
            self.assertTrue(r1.success, r1.report)
            self.assertTrue(
                (project / "SHARE" / "02-market-analysis").is_dir()
            )
            # Narrow the export via export.order.
            block = (
                "export:\n"
                "  order: [series-a-deck, investment-memo]\n"
            )
            (project / "BRIEF.md").write_text(
                brief_text(export_block=block), encoding="utf-8"
            )
            r2 = orchestrate.run(project, now=NOW)
            self.assertTrue(r2.success, r2.report)
            share = project / "SHARE"
            self.assertFalse(
                any("market-analysis" in p.name for p in share.iterdir())
            )
            self.assertTrue((share / "00-series-a-deck").is_dir())
            self.assertTrue((share / "01-investment-memo").is_dir())


if __name__ == "__main__":
    unittest.main()
