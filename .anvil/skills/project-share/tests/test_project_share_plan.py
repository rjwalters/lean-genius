"""Tests for `anvil:project-share` planning (issue #396).

Ordering semantics (`export.order` as authoritative include-list +
ordering; unknown slug = hard error), strip filtering, include toggles,
and the out-name collision guard.
"""

from __future__ import annotations

import sys
import unittest
from pathlib import Path
from tempfile import TemporaryDirectory

_HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(_HERE))

from _project_share_skill_lib import config as config_mod  # noqa: E402
from _project_share_skill_lib import plan as plan_mod  # noqa: E402
from _share_fixtures import build_full_project  # noqa: E402

from anvil.lib.project_brief import load_project_brief_strict  # noqa: E402


def _plan_for(project: Path, **config_kwargs):
    cfg = config_mod.ExportConfig(**config_kwargs)
    brief = load_project_brief_strict(project)
    return plan_mod.build_plan(project, brief, cfg)


def _target_rels(share_plan) -> list:
    return [str(fp.target_rel) for fp in share_plan.all_file_plans]


class TestOrdering(unittest.TestCase):
    def test_default_ordering_follows_documents(self) -> None:
        with TemporaryDirectory() as td:
            project = build_full_project(Path(td))
            share_plan = _plan_for(project)
            self.assertEqual(
                share_plan.ordering_source, plan_mod.ORDERING_DOCUMENTS
            )
            self.assertEqual(
                [d.target_dirname for d in share_plan.docs],
                [
                    "00-series-a-deck",
                    "01-investment-memo",
                    "02-market-analysis",
                ],
            )
            self.assertEqual(share_plan.excluded_slugs, [])

    def test_export_order_reorders_and_excludes(self) -> None:
        with TemporaryDirectory() as td:
            project = build_full_project(Path(td))
            share_plan = _plan_for(
                project, order=["investment-memo", "series-a-deck"]
            )
            self.assertEqual(
                share_plan.ordering_source, plan_mod.ORDERING_EXPORT_ORDER
            )
            self.assertEqual(
                [d.target_dirname for d in share_plan.docs],
                ["00-investment-memo", "01-series-a-deck"],
            )
            self.assertEqual(
                share_plan.excluded_slugs, ["market-analysis"]
            )
            self.assertTrue(
                any("market-analysis" in n for n in share_plan.notes)
            )

    def test_unknown_order_slug_is_hard_error_naming_slug(self) -> None:
        with TemporaryDirectory() as td:
            project = build_full_project(Path(td))
            with self.assertRaisesRegex(ValueError, "no-such-doc"):
                _plan_for(project, order=["no-such-doc"])


class TestStripFiltering(unittest.TestCase):
    def test_bookkeeping_never_planned(self) -> None:
        with TemporaryDirectory() as td:
            project = build_full_project(Path(td))
            rels = _target_rels(_plan_for(project))
            joined = "\n".join(rels)
            self.assertNotIn("_progress.json", joined)
            self.assertNotIn("changelog.md", joined)
            self.assertNotIn("_meta.json", joined)
            self.assertNotIn(".tmp-staging", joined)

    def test_brief_structurally_excluded(self) -> None:
        with TemporaryDirectory() as td:
            project = build_full_project(Path(td))
            # Even a custom empty strip list never exports BRIEF.md.
            rels = _target_rels(_plan_for(project, strip=["nothing-real"]))
            self.assertFalse(any("BRIEF.md" in r for r in rels))

    def test_only_resolved_version_planned(self) -> None:
        """No version history, no critic siblings, no `.latest` literal."""
        with TemporaryDirectory() as td:
            project = build_full_project(Path(td))
            share_plan = _plan_for(project)
            for fp in share_plan.all_file_plans:
                s = str(fp.source)
                self.assertNotIn(".review", s)
                self.assertNotIn(".audit", s)
                self.assertNotIn(".latest", s)
                self.assertNotIn("investment-memo.1", s)
                self.assertNotIn("investment-memo.2", s)
                self.assertNotIn("market-analysis.3", s)

    def test_pinned_doc_files_come_from_pinned_version(self) -> None:
        with TemporaryDirectory() as td:
            project = build_full_project(Path(td))
            share_plan = _plan_for(project)
            ma = next(
                d for d in share_plan.docs if d.slug == "market-analysis"
            )
            self.assertTrue(ma.files)
            for fp in ma.files:
                self.assertIn("market-analysis.2", str(fp.source))


class TestIncludeToggles(unittest.TestCase):
    def test_include_assets_false_top_level_only(self) -> None:
        with TemporaryDirectory() as td:
            project = build_full_project(Path(td))
            share_plan = _plan_for(project, include_assets=False)
            deck = next(
                d for d in share_plan.docs if d.slug == "series-a-deck"
            )
            rels = [str(fp.target_rel) for fp in deck.files]
            self.assertIn("00-series-a-deck/deck.md", rels)
            self.assertIn("00-series-a-deck/deck.pdf", rels)
            self.assertFalse(any("exhibits" in r for r in rels))

    def test_include_refs_false_drops_refs(self) -> None:
        with TemporaryDirectory() as td:
            project = build_full_project(Path(td))
            rels = _target_rels(_plan_for(project, include_refs=False))
            self.assertFalse(any("/refs/" in r for r in rels))

    def test_include_refs_true_plans_refs_under_doc_dir(self) -> None:
        with TemporaryDirectory() as td:
            project = build_full_project(Path(td))
            rels = _target_rels(_plan_for(project))
            self.assertIn(
                "01-investment-memo/refs/competitor-filing.pdf", rels
            )

    def test_include_research_false_drops_research(self) -> None:
        with TemporaryDirectory() as td:
            project = build_full_project(Path(td))
            share_plan = _plan_for(project, include_research=False)
            self.assertEqual(share_plan.research_files, [])

    def test_research_planned_once_at_export_root(self) -> None:
        with TemporaryDirectory() as td:
            project = build_full_project(Path(td))
            share_plan = _plan_for(project)
            rels = [str(fp.target_rel) for fp in share_plan.research_files]
            self.assertIn("research/industry-notes.md", rels)
            self.assertIn("research/sources/robotics-survey.pdf", rels)


class TestGuards(unittest.TestCase):
    def test_out_colliding_with_slug_raises(self) -> None:
        with TemporaryDirectory() as td:
            project = build_full_project(Path(td))
            with self.assertRaisesRegex(ValueError, "source-of-truth"):
                _plan_for(project, out="investment-memo")

    def test_out_colliding_with_research_raises(self) -> None:
        with TemporaryDirectory() as td:
            project = build_full_project(Path(td))
            with self.assertRaisesRegex(ValueError, "source-of-truth"):
                _plan_for(project, out="research")

    def test_failed_doc_carried_in_plan(self) -> None:
        with TemporaryDirectory() as td:
            project = build_full_project(Path(td))
            # Add an unstarted slug to the BRIEF via export.order? No —
            # simulate by removing a thread dir wholesale.
            import shutil

            shutil.rmtree(project / "market-analysis")
            share_plan = _plan_for(project)
            failed = share_plan.failed_docs
            self.assertEqual([d.slug for d in failed], ["market-analysis"])
            # Other docs still planned.
            ok_docs = [d for d in share_plan.docs if not d.failed]
            self.assertEqual(len(ok_docs), 2)


class TestCover(unittest.TestCase):
    def test_no_cover_configured_yields_no_cover_file(self) -> None:
        with TemporaryDirectory() as td:
            project = build_full_project(Path(td))
            share_plan = _plan_for(project)
            self.assertIsNone(share_plan.cover_file)

    def test_cover_resolved_and_folded_into_all_file_plans(self) -> None:
        with TemporaryDirectory() as td:
            project = build_full_project(Path(td))
            cover_source = project / "SHARE-README.md"
            cover_source.write_text("# Read me first\n", encoding="utf-8")
            share_plan = _plan_for(project, cover="SHARE-README.md")
            assert share_plan.cover_file is not None
            self.assertEqual(
                share_plan.cover_file.source, cover_source.resolve()
            )
            self.assertEqual(
                share_plan.cover_file.target_rel, Path("README.md")
            )
            self.assertIn("README.md", _target_rels(share_plan))

    def test_cover_as_override_used_as_target_name(self) -> None:
        with TemporaryDirectory() as td:
            project = build_full_project(Path(td))
            (project / "SHARE-README.md").write_text(
                "# Read me\n", encoding="utf-8"
            )
            share_plan = _plan_for(
                project, cover="SHARE-README.md", cover_as="OVERVIEW.md"
            )
            assert share_plan.cover_file is not None
            self.assertEqual(
                share_plan.cover_file.target_rel, Path("OVERVIEW.md")
            )

    def test_cover_as_colliding_with_export_md_marker_raises(self) -> None:
        with TemporaryDirectory() as td:
            project = build_full_project(Path(td))
            (project / "SHARE-README.md").write_text(
                "# Read me\n", encoding="utf-8"
            )
            with self.assertRaisesRegex(ValueError, "EXPORT.md"):
                _plan_for(
                    project, cover="SHARE-README.md", cover_as="EXPORT.md"
                )

    def test_cover_as_colliding_with_research_dirname_raises(self) -> None:
        with TemporaryDirectory() as td:
            project = build_full_project(Path(td))
            (project / "SHARE-README.md").write_text(
                "# Read me\n", encoding="utf-8"
            )
            with self.assertRaises(ValueError):
                _plan_for(
                    project, cover="SHARE-README.md", cover_as="research"
                )

    def test_cover_as_colliding_with_doc_target_dirname_raises(self) -> None:
        with TemporaryDirectory() as td:
            project = build_full_project(Path(td))
            (project / "SHARE-README.md").write_text(
                "# Read me\n", encoding="utf-8"
            )
            with self.assertRaises(ValueError):
                _plan_for(
                    project,
                    cover="SHARE-README.md",
                    cover_as="00-series-a-deck",
                )

    def test_missing_cover_source_raises_at_plan_time(self) -> None:
        with TemporaryDirectory() as td:
            project = build_full_project(Path(td))
            with self.assertRaisesRegex(ValueError, "does not resolve"):
                _plan_for(project, cover="does-not-exist.md")


class TestInspectOutDir(unittest.TestCase):
    def test_states(self) -> None:
        with TemporaryDirectory() as td:
            base = Path(td)
            self.assertEqual(
                plan_mod.inspect_out_dir(base / "missing"),
                plan_mod.OUT_ABSENT,
            )
            empty = base / "empty"
            empty.mkdir()
            self.assertEqual(
                plan_mod.inspect_out_dir(empty), plan_mod.OUT_EMPTY
            )
            marked = base / "marked"
            marked.mkdir()
            (marked / plan_mod.MARKER_FILENAME).write_text("# marker\n")
            self.assertEqual(
                plan_mod.inspect_out_dir(marked), plan_mod.OUT_MARKER
            )
            foreign = base / "foreign"
            foreign.mkdir()
            (foreign / "user-data.txt").write_text("precious\n")
            self.assertEqual(
                plan_mod.inspect_out_dir(foreign), plan_mod.OUT_FOREIGN
            )


if __name__ == "__main__":
    unittest.main()
