"""Tests for `anvil:project-share` marker guard (issue #396).

A non-empty out dir WITHOUT the `EXPORT.md` marker is a hard refusal
with no deletion; the marker (or an empty/absent out dir) authorizes
the blow-away rebuild.
"""

from __future__ import annotations

import sys
import unittest
from datetime import datetime, timezone
from pathlib import Path
from tempfile import TemporaryDirectory

_HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(_HERE))

from _project_share_skill_lib import orchestrate  # noqa: E402
from _share_fixtures import build_full_project  # noqa: E402

NOW = datetime(2026, 6, 9, 12, 0, 0, tzinfo=timezone.utc)


class TestForeignDirRefusal(unittest.TestCase):
    def test_refuses_and_deletes_nothing(self) -> None:
        with TemporaryDirectory() as td:
            project = build_full_project(Path(td))
            foreign = project / "SHARE"
            (foreign / "deep").mkdir(parents=True)
            (foreign / "precious.txt").write_text("user data\n")
            (foreign / "deep" / "more.txt").write_text("more user data\n")

            result = orchestrate.run(project, now=NOW)

            self.assertFalse(result.success)
            assert result.apply_result is not None
            self.assertTrue(result.apply_result.refused)
            self.assertIn(
                "EXPORT.md", result.apply_result.refusal_reason or ""
            )
            self.assertIn("REFUSED", result.report)
            # Nothing deleted, nothing written.
            self.assertEqual(
                (foreign / "precious.txt").read_text(), "user data\n"
            )
            self.assertEqual(
                (foreign / "deep" / "more.txt").read_text(),
                "more user data\n",
            )
            self.assertFalse((foreign / "EXPORT.md").exists())
            self.assertFalse((foreign / "00-series-a-deck").exists())
            self.assertIsNone(result.verify_result)

    def test_refusal_with_zip_flag_writes_no_zip(self) -> None:
        with TemporaryDirectory() as td:
            project = build_full_project(Path(td))
            foreign = project / "SHARE"
            foreign.mkdir()
            (foreign / "precious.txt").write_text("user data\n")
            result = orchestrate.run(project, zip_output=True, now=NOW)
            self.assertFalse(result.success)
            self.assertEqual(list(project.glob("*.zip")), [])


class TestMarkerAuthorizedRebuild(unittest.TestCase):
    def test_marker_plus_stray_file_rebuilds_cleanly(self) -> None:
        """A previous-export dir (marker present) is rebuilt even when
        stray files accumulated — they disappear with the rebuild."""
        with TemporaryDirectory() as td:
            project = build_full_project(Path(td))
            previous = project / "SHARE"
            previous.mkdir()
            (previous / "EXPORT.md").write_text("# old export\n")
            (previous / "stale-doc-folder").mkdir()
            (previous / "stale-doc-folder" / "old.md").write_text("old\n")

            result = orchestrate.run(project, now=NOW)

            self.assertTrue(result.success, result.report)
            self.assertFalse((previous / "stale-doc-folder").exists())
            self.assertTrue((previous / "00-series-a-deck").is_dir())
            text = (previous / "EXPORT.md").read_text(encoding="utf-8")
            self.assertNotIn("old export", text)

    def test_empty_out_dir_proceeds(self) -> None:
        with TemporaryDirectory() as td:
            project = build_full_project(Path(td))
            (project / "SHARE").mkdir()
            result = orchestrate.run(project, now=NOW)
            self.assertTrue(result.success, result.report)
            self.assertTrue((project / "SHARE" / "EXPORT.md").is_file())

    def test_absent_out_dir_proceeds(self) -> None:
        with TemporaryDirectory() as td:
            project = build_full_project(Path(td))
            result = orchestrate.run(project, now=NOW)
            self.assertTrue(result.success, result.report)


if __name__ == "__main__":
    unittest.main()
