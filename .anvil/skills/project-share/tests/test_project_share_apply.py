"""Tests for `anvil:project-share` apply + verify + EXPORT.md (issue #396).

End-to-end layout assertions over the canonical full-project fixture,
EXPORT.md provenance contents (resolved version names, resolution
modes, PDF SHA-256), the `--zip` flag, per-doc failure tolerance
(AC 9), and the AC-8 regression: the created `SHARE/` dir does not
break `load_project_brief_strict` slug-divergence validation.
"""

from __future__ import annotations

import hashlib
import sys
import unittest
import warnings
import zipfile
from datetime import datetime, timezone
from pathlib import Path
from tempfile import TemporaryDirectory

_HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(_HERE))

from _project_share_skill_lib import orchestrate  # noqa: E402
from _share_fixtures import (  # noqa: E402
    build_full_project,
    build_project_with_unstarted_slug,
)

from anvil.lib.project_brief import load_project_brief_strict  # noqa: E402

NOW = datetime(2026, 6, 9, 12, 0, 0, tzinfo=timezone.utc)


class TestFullExportLayout(unittest.TestCase):
    def _export(self, td: str) -> Path:
        project = build_full_project(Path(td))
        result = orchestrate.run(project, now=NOW)
        self.assertTrue(result.success, result.report)
        return project

    def test_layout(self) -> None:
        with TemporaryDirectory() as td:
            project = self._export(td)
            share = project / "SHARE"
            # Marker / index.
            self.assertTrue((share / "EXPORT.md").is_file())
            # Deck doc: body + pdf + speaker notes + exhibits ride along.
            deck = share / "00-series-a-deck"
            self.assertTrue((deck / "deck.md").is_file())
            self.assertTrue((deck / "deck.pdf").is_file())
            self.assertTrue((deck / "speaker-notes.md").is_file())
            self.assertTrue((deck / "exhibits" / "market.png").is_file())
            # Memo doc: body + figures + thread-root refs.
            memo = share / "01-investment-memo"
            self.assertTrue((memo / "investment-memo.md").is_file())
            self.assertTrue((memo / "figures" / "traction.png").is_file())
            self.assertTrue(
                (memo / "refs" / "competitor-filing.pdf").is_file()
            )
            self.assertTrue((memo / "refs" / "notes.md").is_file())
            # Pinned doc: content comes from the PINNED v2, not v3.
            ma = share / "02-market-analysis"
            body = (ma / "market-analysis.md").read_text(encoding="utf-8")
            self.assertIn("Body v2", body)
            # Shared research pool, once at the export root.
            self.assertTrue(
                (share / "research" / "industry-notes.md").is_file()
            )
            self.assertTrue(
                (
                    share / "research" / "sources" / "robotics-survey.pdf"
                ).is_file()
            )

    def test_strip_and_structural_exclusions(self) -> None:
        with TemporaryDirectory() as td:
            project = self._export(td)
            share = project / "SHARE"
            names = {p.name for p in share.rglob("*")}
            self.assertNotIn("_progress.json", names)
            self.assertNotIn("changelog.md", names)
            self.assertNotIn("_meta.json", names)
            self.assertNotIn("BRIEF.md", names)
            self.assertFalse(any(n.startswith(".tmp") for n in names))
            self.assertFalse(any(".review" in n for n in names))
            self.assertFalse(any(".audit" in n for n in names))
            # Only the resolved version's content — no version-dir names
            # appear inside the export at all.
            self.assertFalse(
                any(p.name == "investment-memo.3" for p in share.rglob("*"))
            )

    def test_export_md_provenance(self) -> None:
        with TemporaryDirectory() as td:
            project = self._export(td)
            text = (project / "SHARE" / "EXPORT.md").read_text(
                encoding="utf-8"
            )
            self.assertIn("Brains for Robots", text)
            self.assertIn("2026-06-09T12:00:00Z", text)
            self.assertIn("`documents:` (BRIEF default)", text)
            # Concrete (dereferenced) version names + resolution modes.
            self.assertIn("`series-a-deck.2`", text)
            self.assertIn("walk-to-highest", text)
            self.assertIn("`market-analysis.2`", text)
            self.assertIn("pinned-symlink", text)
            # PDF sha256 present for deck; "no rendered PDF" for memo.
            deck_pdf = (
                project / "series-a-deck" / "series-a-deck.2" / "deck.pdf"
            ).read_bytes()
            self.assertIn(hashlib.sha256(deck_pdf).hexdigest(), text)
            self.assertIn("(no rendered PDF)", text)

    def test_verify_passes(self) -> None:
        with TemporaryDirectory() as td:
            project = build_full_project(Path(td))
            result = orchestrate.run(project, now=NOW)
            assert result.verify_result is not None
            self.assertTrue(result.verify_result.ok)
            self.assertGreater(result.verify_result.checks_run, 0)


class TestZip(unittest.TestCase):
    def test_zip_flag_produces_datestamped_archive(self) -> None:
        with TemporaryDirectory() as td:
            project = build_full_project(Path(td))
            result = orchestrate.run(project, zip_output=True, now=NOW)
            self.assertTrue(result.success, result.report)
            assert result.apply_result is not None
            zip_path = result.apply_result.zip_path
            assert zip_path is not None
            self.assertEqual(
                zip_path.name, "smart-actuators-share-20260609.zip"
            )
            # plan.project_dir is resolved; compare resolved paths
            # (macOS tmpdirs live behind the /var → /private/var link).
            self.assertEqual(zip_path.parent, project.resolve())
            with zipfile.ZipFile(zip_path) as zf:
                names = zf.namelist()
            self.assertIn("SHARE/EXPORT.md", names)
            self.assertIn("SHARE/00-series-a-deck/deck.pdf", names)

    def test_no_zip_by_default(self) -> None:
        with TemporaryDirectory() as td:
            project = build_full_project(Path(td))
            result = orchestrate.run(project, now=NOW)
            assert result.apply_result is not None
            self.assertIsNone(result.apply_result.zip_path)
            self.assertEqual(list(project.glob("*.zip")), [])


class TestPerDocFailureTolerance(unittest.TestCase):
    def test_unstarted_slug_is_finding_not_crash(self) -> None:
        with TemporaryDirectory() as td:
            project = build_project_with_unstarted_slug(Path(td))
            result = orchestrate.run(project, now=NOW)
            # Nonzero-exit signal: success is False...
            self.assertFalse(result.success)
            # ...but the resolvable doc still exported.
            share = project / "SHARE"
            self.assertTrue(
                (share / "00-investment-memo" / "investment-memo.md").is_file()
            )
            # The failed doc's folder does not exist.
            self.assertFalse((share / "01-unstarted-deck").exists())
            # Finding recorded in the report AND in EXPORT.md.
            self.assertIn("unstarted-deck", result.report)
            export_text = (share / "EXPORT.md").read_text(encoding="utf-8")
            self.assertIn("## Findings", export_text)
            self.assertIn("unstarted-deck", export_text)


class TestDivergenceRegression(unittest.TestCase):
    def test_share_dir_does_not_trip_slug_divergence(self) -> None:
        """AC 8: post-export, `load_project_brief_strict(...,
        validate_dirs=True)` still succeeds — `SHARE/` contains no
        `SHARE.<N>` version dirs, so `_on_disk_slug_dirs` ignores it."""
        with TemporaryDirectory() as td:
            project = build_full_project(Path(td))
            result = orchestrate.run(project, now=NOW)
            self.assertTrue(result.success, result.report)
            with warnings.catch_warnings():
                warnings.simplefilter("error")
                brief = load_project_brief_strict(
                    project, validate_dirs=True
                )
            self.assertEqual(len(brief.documents), 3)

    def test_zip_artifact_does_not_trip_divergence_either(self) -> None:
        with TemporaryDirectory() as td:
            project = build_full_project(Path(td))
            orchestrate.run(project, zip_output=True, now=NOW)
            brief = load_project_brief_strict(project, validate_dirs=True)
            self.assertEqual(len(brief.documents), 3)


class TestCoverNote(unittest.TestCase):
    """Issue #757: `export.cover` survives the marker-guarded rebuild."""

    def _project_with_cover(self, td: str, *, cover_as: str = "") -> Path:
        block = "export:\n  cover: SHARE-README.md\n"
        if cover_as:
            block += f"  cover_as: {cover_as}\n"
        project = build_full_project(Path(td), export_block=block)
        (project / "SHARE-README.md").write_text(
            "# Welcome\n\nRead the memo first, then the deck.\n",
            encoding="utf-8",
        )
        return project

    def test_cover_copied_with_default_name(self) -> None:
        with TemporaryDirectory() as td:
            project = self._project_with_cover(td)
            result = orchestrate.run(project, now=NOW)
            self.assertTrue(result.success, result.report)
            readme = project / "SHARE" / "README.md"
            self.assertTrue(readme.is_file())
            self.assertEqual(
                readme.read_text(encoding="utf-8"),
                (project / "SHARE-README.md").read_text(encoding="utf-8"),
            )

    def test_cover_copied_with_cover_as_override(self) -> None:
        with TemporaryDirectory() as td:
            project = self._project_with_cover(td, cover_as="OVERVIEW.md")
            result = orchestrate.run(project, now=NOW)
            self.assertTrue(result.success, result.report)
            self.assertTrue((project / "SHARE" / "OVERVIEW.md").is_file())
            self.assertFalse((project / "SHARE" / "README.md").exists())

    def test_cover_survives_rebuild(self) -> None:
        """The exact regression this issue reports: a hand-written
        `SHARE/README.md` used to be destroyed on every re-export."""
        with TemporaryDirectory() as td:
            project = self._project_with_cover(td)
            orchestrate.run(project, now=NOW)
            readme = project / "SHARE" / "README.md"
            before = readme.read_bytes()
            # Rebuild (second apply run over the marker-guarded out dir).
            result = orchestrate.run(project, now=NOW)
            self.assertTrue(result.success, result.report)
            self.assertTrue(readme.is_file())
            self.assertEqual(readme.read_bytes(), before)

    def test_cover_lands_in_zip(self) -> None:
        with TemporaryDirectory() as td:
            project = self._project_with_cover(td)
            result = orchestrate.run(project, zip_output=True, now=NOW)
            self.assertTrue(result.success, result.report)
            assert result.apply_result is not None
            zip_path = result.apply_result.zip_path
            assert zip_path is not None
            with zipfile.ZipFile(zip_path) as zf:
                names = zf.namelist()
            self.assertIn("SHARE/README.md", names)

    def test_no_cover_configured_no_readme_written(self) -> None:
        with TemporaryDirectory() as td:
            project = build_full_project(Path(td))
            result = orchestrate.run(project, now=NOW)
            self.assertTrue(result.success, result.report)
            self.assertFalse((project / "SHARE" / "README.md").exists())


class TestGitignoreSuggestion(unittest.TestCase):
    def test_suggests_when_in_repo_and_uncovered(self) -> None:
        with TemporaryDirectory() as td:
            project = build_full_project(Path(td))
            (project / ".git").mkdir()
            result = orchestrate.run(project, now=NOW)
            assert result.apply_result is not None
            note = result.apply_result.gitignore_note
            assert note is not None
            self.assertIn("SHARE/", note)

    def test_silent_when_covered(self) -> None:
        with TemporaryDirectory() as td:
            project = build_full_project(Path(td))
            (project / ".git").mkdir()
            (project / ".gitignore").write_text("SHARE/\n", encoding="utf-8")
            result = orchestrate.run(project, now=NOW)
            assert result.apply_result is not None
            self.assertIsNone(result.apply_result.gitignore_note)

    def test_silent_outside_git_repo(self) -> None:
        with TemporaryDirectory() as td:
            project = build_full_project(Path(td))
            result = orchestrate.run(project, now=NOW)
            assert result.apply_result is not None
            self.assertIsNone(result.apply_result.gitignore_note)


if __name__ == "__main__":
    unittest.main()
