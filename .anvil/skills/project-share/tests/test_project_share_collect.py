"""Tests for `anvil:project-share` per-doc collection (issue #396).

Pins the resolution contract: `.latest` precedence (pinned symlink >
real `.latest` dir > walk-to-highest), the **dereference** caveat
(`resolve_latest` returns the `.latest` path itself; the collector must
record the concrete version-dir name), refs detection, and PDF
SHA-256 fingerprints.
"""

from __future__ import annotations

import hashlib
import sys
import unittest
from pathlib import Path
from tempfile import TemporaryDirectory

_HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(_HERE))

from _project_share_skill_lib import collect  # noqa: E402
from _share_fixtures import (  # noqa: E402
    build_dangling_symlink_project,
    build_full_project,
    build_project_with_unstarted_slug,
    build_real_latest_dir_project,
)


class TestResolutionModes(unittest.TestCase):
    def test_walk_to_highest(self) -> None:
        with TemporaryDirectory() as td:
            project = build_full_project(Path(td))
            doc = collect.collect_doc(project, "investment-memo")
            self.assertFalse(doc.failed)
            self.assertEqual(doc.resolved_name, "investment-memo.3")
            self.assertEqual(
                doc.resolution_mode, collect.RESOLUTION_WALK_TO_HIGHEST
            )

    def test_pinned_symlink_honored_and_dereferenced(self) -> None:
        """A pin to a non-highest version wins, and provenance records
        the CONCRETE version-dir name, not `.latest`."""
        with TemporaryDirectory() as td:
            project = build_full_project(Path(td))
            doc = collect.collect_doc(project, "market-analysis")
            self.assertFalse(doc.failed)
            self.assertEqual(
                doc.resolution_mode, collect.RESOLUTION_PINNED_SYMLINK
            )
            # v3 exists; the pin to v2 must win — and be dereferenced.
            self.assertEqual(doc.resolved_name, "market-analysis.2")
            assert doc.resolved_dir is not None
            self.assertFalse(doc.resolved_dir.is_symlink())

    def test_real_latest_dir(self) -> None:
        with TemporaryDirectory() as td:
            project = build_real_latest_dir_project(Path(td))
            doc = collect.collect_doc(project, "memo-thread")
            self.assertFalse(doc.failed)
            self.assertEqual(
                doc.resolution_mode, collect.RESOLUTION_REAL_DIR
            )
            self.assertEqual(doc.resolved_name, "memo-thread.latest")


class TestResolutionFailures(unittest.TestCase):
    def test_unstarted_thread_is_failure_not_crash(self) -> None:
        with TemporaryDirectory() as td:
            project = build_project_with_unstarted_slug(Path(td))
            doc = collect.collect_doc(project, "unstarted-deck")
            self.assertTrue(doc.failed)
            self.assertIn("unstarted-deck", doc.failure or "")

    def test_no_version_dirs_is_failure(self) -> None:
        with TemporaryDirectory() as td:
            project = build_full_project(Path(td))
            empty_thread = project / "empty-thread"
            empty_thread.mkdir()
            doc = collect.collect_doc(project, "empty-thread")
            self.assertTrue(doc.failed)
            self.assertIn("no version directories", doc.failure or "")

    def test_dangling_symlink_is_failure(self) -> None:
        with TemporaryDirectory() as td:
            project = build_dangling_symlink_project(Path(td))
            doc = collect.collect_doc(project, "ghost")
            self.assertTrue(doc.failed)
            self.assertIn("dangling", doc.failure or "")


class TestRefsDetection(unittest.TestCase):
    def test_refs_detected_when_non_empty(self) -> None:
        with TemporaryDirectory() as td:
            project = build_full_project(Path(td))
            doc = collect.collect_doc(project, "investment-memo")
            self.assertIsNotNone(doc.refs_dir)

    def test_no_refs_dir_yields_none(self) -> None:
        with TemporaryDirectory() as td:
            project = build_full_project(Path(td))
            doc = collect.collect_doc(project, "series-a-deck")
            self.assertIsNone(doc.refs_dir)

    def test_empty_refs_dir_yields_none(self) -> None:
        with TemporaryDirectory() as td:
            project = build_full_project(Path(td))
            (project / "series-a-deck" / "refs").mkdir()
            doc = collect.collect_doc(project, "series-a-deck")
            self.assertIsNone(doc.refs_dir)


class TestPdfFingerprints(unittest.TestCase):
    def test_pdf_sha256_matches_bytes(self) -> None:
        with TemporaryDirectory() as td:
            project = build_full_project(Path(td))
            doc = collect.collect_doc(project, "series-a-deck")
            self.assertEqual(len(doc.pdfs), 1)
            pdf = doc.pdfs[0]
            self.assertEqual(pdf.filename, "deck.pdf")
            on_disk = (
                project / "series-a-deck" / "series-a-deck.2" / "deck.pdf"
            ).read_bytes()
            self.assertEqual(
                pdf.sha256, hashlib.sha256(on_disk).hexdigest()
            )

    def test_no_pdf_yields_empty_list(self) -> None:
        with TemporaryDirectory() as td:
            project = build_full_project(Path(td))
            doc = collect.collect_doc(project, "investment-memo")
            self.assertEqual(doc.pdfs, [])

    def test_pinned_doc_pdf_comes_from_pinned_version(self) -> None:
        with TemporaryDirectory() as td:
            project = build_full_project(Path(td))
            doc = collect.collect_doc(project, "market-analysis")
            self.assertEqual(len(doc.pdfs), 1)
            v2_bytes = (
                project
                / "market-analysis"
                / "market-analysis.2"
                / "market-analysis.pdf"
            ).read_bytes()
            self.assertEqual(
                doc.pdfs[0].sha256,
                hashlib.sha256(v2_bytes).hexdigest(),
            )


class TestResearchCollection(unittest.TestCase):
    def test_research_detected(self) -> None:
        with TemporaryDirectory() as td:
            project = build_full_project(Path(td))
            self.assertIsNotNone(collect.collect_research(project))

    def test_absent_research_yields_none(self) -> None:
        with TemporaryDirectory() as td:
            project = build_project_with_unstarted_slug(Path(td))
            self.assertIsNone(collect.collect_research(project))


if __name__ == "__main__":
    unittest.main()
