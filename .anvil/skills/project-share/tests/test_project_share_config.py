"""Tests for `anvil:project-share` config parsing (issue #396).

The ``export:`` BRIEF frontmatter block is skill-local: parsed by
``lib/config.py::ExportConfig``, never by the shared ``ProjectBrief``
model. Zero-config (no ``export:`` block) must yield full defaults.
"""

from __future__ import annotations

import sys
import unittest
from pathlib import Path
from tempfile import TemporaryDirectory

_HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(_HERE))

from _project_share_skill_lib import config as config_mod  # noqa: E402
from _share_fixtures import build_full_project  # noqa: E402

ExportConfig = config_mod.ExportConfig
load_export_config = config_mod.load_export_config
DEFAULT_STRIP = config_mod.DEFAULT_STRIP
DEFAULT_OUT = config_mod.DEFAULT_OUT
DEFAULT_COVER_AS = config_mod.DEFAULT_COVER_AS


class TestZeroConfigDefaults(unittest.TestCase):
    def test_no_export_block_yields_defaults(self) -> None:
        with TemporaryDirectory() as td:
            project = build_full_project(Path(td))
            cfg = load_export_config(project)
            self.assertIsNone(cfg.order)
            self.assertTrue(cfg.include_research)
            self.assertTrue(cfg.include_refs)
            self.assertTrue(cfg.include_assets)
            self.assertEqual(cfg.strip, list(DEFAULT_STRIP))
            self.assertEqual(cfg.out, DEFAULT_OUT)
            self.assertIsNone(cfg.cover)
            self.assertEqual(cfg.cover_as, DEFAULT_COVER_AS)

    def test_default_strip_covers_bookkeeping(self) -> None:
        self.assertIn("_progress.json", DEFAULT_STRIP)
        self.assertIn("changelog.md", DEFAULT_STRIP)
        self.assertIn("_*.json", DEFAULT_STRIP)
        self.assertIn(".tmp*", DEFAULT_STRIP)

    def test_default_strip_covers_bytecode_and_os_droppings(self) -> None:
        """Issue #756: Python bytecode caches and macOS `.DS_Store` files
        must never reach an outside recipient by default."""
        self.assertIn("__pycache__", DEFAULT_STRIP)
        self.assertIn("*.pyc", DEFAULT_STRIP)
        self.assertIn(".DS_Store", DEFAULT_STRIP)


class TestExportBlockParsing(unittest.TestCase):
    def test_full_block_parses(self) -> None:
        block = (
            "export:\n"
            "  order: [investment-memo, series-a-deck]\n"
            "  include_research: false\n"
            "  include_refs: false\n"
            "  include_assets: false\n"
            "  strip: [\"*.secret\"]\n"
            "  out: DATAROOM\n"
            "  cover: SHARE-README.md\n"
            "  cover_as: OVERVIEW.md\n"
        )
        with TemporaryDirectory() as td:
            project = build_full_project(Path(td), export_block=block)
            cfg = load_export_config(project)
            self.assertEqual(
                cfg.order, ["investment-memo", "series-a-deck"]
            )
            self.assertFalse(cfg.include_research)
            self.assertFalse(cfg.include_refs)
            self.assertFalse(cfg.include_assets)
            self.assertEqual(cfg.strip, ["*.secret"])
            self.assertEqual(cfg.out, "DATAROOM")
            self.assertEqual(cfg.cover, "SHARE-README.md")
            self.assertEqual(cfg.cover_as, "OVERVIEW.md")

    def test_partial_block_keeps_other_defaults(self) -> None:
        block = "export:\n  include_research: false\n"
        with TemporaryDirectory() as td:
            project = build_full_project(Path(td), export_block=block)
            cfg = load_export_config(project)
            self.assertFalse(cfg.include_research)
            self.assertTrue(cfg.include_refs)
            self.assertEqual(cfg.out, DEFAULT_OUT)
            self.assertEqual(cfg.strip, list(DEFAULT_STRIP))


class TestMalformedExportBlock(unittest.TestCase):
    def _project_with(self, block: str, td: str) -> Path:
        return build_full_project(Path(td), export_block=block)

    def test_non_mapping_export_block_raises(self) -> None:
        with TemporaryDirectory() as td:
            project = self._project_with("export: just-a-string\n", td)
            with self.assertRaisesRegex(ValueError, "must be a mapping"):
                load_export_config(project)

    def test_unknown_key_raises(self) -> None:
        with TemporaryDirectory() as td:
            project = self._project_with(
                "export:\n  include_briefs: true\n", td
            )
            with self.assertRaises(ValueError):
                load_export_config(project)

    def test_out_with_path_separator_raises(self) -> None:
        with TemporaryDirectory() as td:
            project = self._project_with(
                "export:\n  out: nested/SHARE\n", td
            )
            with self.assertRaisesRegex(ValueError, "path separators"):
                load_export_config(project)

    def test_out_dotdot_raises(self) -> None:
        with TemporaryDirectory() as td:
            project = self._project_with("export:\n  out: '..'\n", td)
            with self.assertRaises(ValueError):
                load_export_config(project)

    def test_order_non_string_entry_raises(self) -> None:
        with TemporaryDirectory() as td:
            project = self._project_with(
                "export:\n  order:\n    - 42\n", td
            )
            with self.assertRaises(ValueError):
                load_export_config(project)

    def test_order_duplicate_entry_raises(self) -> None:
        with TemporaryDirectory() as td:
            project = self._project_with(
                "export:\n  order: [a-doc, a-doc]\n", td
            )
            with self.assertRaisesRegex(ValueError, "more than once"):
                load_export_config(project)

    def test_missing_brief_raises_file_not_found(self) -> None:
        with TemporaryDirectory() as td:
            empty = Path(td) / "no-brief"
            empty.mkdir()
            with self.assertRaises(FileNotFoundError):
                load_export_config(empty)

    def test_cover_leading_slash_raises(self) -> None:
        with TemporaryDirectory() as td:
            project = self._project_with(
                "export:\n  cover: /etc/passwd\n", td
            )
            with self.assertRaisesRegex(ValueError, "leading path separator"):
                load_export_config(project)

    def test_cover_dotdot_component_raises(self) -> None:
        with TemporaryDirectory() as td:
            project = self._project_with(
                "export:\n  cover: ../outside-project/note.md\n", td
            )
            with self.assertRaisesRegex(ValueError, "path-traversal"):
                load_export_config(project)

    def test_cover_empty_string_raises(self) -> None:
        with TemporaryDirectory() as td:
            project = self._project_with("export:\n  cover: ''\n", td)
            with self.assertRaises(ValueError):
                load_export_config(project)

    def test_cover_as_with_path_separator_raises(self) -> None:
        with TemporaryDirectory() as td:
            project = self._project_with(
                "export:\n  cover: SHARE-README.md\n"
                "  cover_as: notes/README.md\n",
                td,
            )
            with self.assertRaisesRegex(ValueError, "path separators"):
                load_export_config(project)

    def test_cover_as_empty_raises(self) -> None:
        with TemporaryDirectory() as td:
            project = self._project_with(
                "export:\n  cover: SHARE-README.md\n  cover_as: ''\n", td
            )
            with self.assertRaises(ValueError):
                load_export_config(project)


class TestCoverDefaults(unittest.TestCase):
    def test_cover_unset_is_none_cover_as_defaults(self) -> None:
        with TemporaryDirectory() as td:
            project = build_full_project(Path(td))
            cfg = load_export_config(project)
            self.assertIsNone(cfg.cover)
            self.assertEqual(cfg.cover_as, "README.md")

    def test_cover_nested_relative_path_allowed(self) -> None:
        with TemporaryDirectory() as td:
            project = build_full_project(
                Path(td),
                export_block="export:\n  cover: refs/cover-note.md\n",
            )
            cfg = load_export_config(project)
            self.assertEqual(cfg.cover, "refs/cover-note.md")


if __name__ == "__main__":
    unittest.main()
