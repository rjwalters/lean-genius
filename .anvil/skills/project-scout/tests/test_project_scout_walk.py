"""Walk + filter tests for `anvil:project-scout` (issue #407, AC 6).

``--include`` / ``--exclude`` glob handling, default excludes, and the
honest-coverage rule: every pruned subtree — default OR operator flag —
is named, never silently dropped.
"""

from __future__ import annotations

import sys
import unittest
from pathlib import Path
from tempfile import TemporaryDirectory

_HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(_HERE))

from _project_scout_skill_lib import orchestrate, walk  # noqa: E402
from _scout_fixtures import _write, build_mega_tree  # noqa: E402


class TestDefaultExcludes(unittest.TestCase):
    def test_node_modules_pruned_and_named(self) -> None:
        with TemporaryDirectory() as td:
            root = Path(td).resolve()
            build_mega_tree(root)
            wr = walk.walk_tree(root)
            pruned = {
                p.path.relative_to(root).as_posix(): p.reason
                for p in wr.pruned_subtrees
            }
            self.assertEqual(
                pruned.get("node_modules"), walk.REASON_DEFAULT_EXCLUDE
            )
            # Nothing under a pruned subtree is a candidate.
            self.assertFalse(
                any(
                    "node_modules" in f.relative_to(root).as_posix()
                    for f in wr.candidate_files
                )
            )

    def test_default_exclude_list_pins_issue_requirements(self) -> None:
        for required in (".git", "node_modules", ".anvil", ".loom", "build"):
            self.assertIn(required, walk.DEFAULT_EXCLUDES)

    def test_dotdirs_pruned_and_named(self) -> None:
        with TemporaryDirectory() as td:
            root = Path(td).resolve()
            _write(root / ".hidden" / "secret.md", "# hidden\n")
            _write(root / "open.md", "# open\n\nprose body\n")
            wr = walk.walk_tree(root)
            pruned = {
                p.path.relative_to(root).as_posix(): p.reason
                for p in wr.pruned_subtrees
            }
            self.assertEqual(pruned.get(".hidden"), walk.REASON_DOTDIR)


class TestExcludeGlobs(unittest.TestCase):
    def test_exclude_glob_prunes_and_reports(self) -> None:
        with TemporaryDirectory() as td:
            root = Path(td).resolve()
            build_mega_tree(root)
            result = orchestrate.run(root, exclude=("docs-site",))
            pruned = {
                p["path"]: p["reason"]
                for p in result.data["filters"]["pruned_subtrees"]
            }
            self.assertEqual(
                pruned.get("docs-site"), walk.REASON_EXCLUDE_GLOB
            )
            # The pruned tree's files are gone from every count.
            self.assertFalse(
                any(
                    d["path"].startswith("docs-site/")
                    for d in result.data["loose_documents"]
                )
            )
            self.assertFalse(
                any(
                    c["path"].startswith("docs-site")
                    for c in result.data["clusters"]
                )
            )
            # And the report names the exclude in effect.
            self.assertIn("`docs-site`", result.markdown)

    def test_exclude_glob_matches_relative_paths(self) -> None:
        with TemporaryDirectory() as td:
            root = Path(td).resolve()
            _write(root / "a" / "skipme" / "x.md", "# x\n\nprose\n")
            _write(root / "keep.md", "# keep\n\nprose body here\n")
            wr = walk.walk_tree(root, exclude=("a/skipme",))
            pruned = [
                p.path.relative_to(root).as_posix()
                for p in wr.pruned_subtrees
            ]
            self.assertIn("a/skipme", pruned)


class TestIncludeGlobs(unittest.TestCase):
    def test_include_filters_candidate_files_only(self) -> None:
        with TemporaryDirectory() as td:
            root = Path(td).resolve()
            _write(root / "notes" / "a-2026-01-01.md", "# a\n\nprose\n")
            _write(root / "notes" / "b.tex", "\\documentclass{article}\n")
            wr = walk.walk_tree(root, include=("*.md",))
            rels = [
                f.relative_to(root).as_posix() for f in wr.candidate_files
            ]
            self.assertEqual(rels, ["notes/a-2026-01-01.md"])

    def test_include_does_not_hide_cluster_evidence(self) -> None:
        """Clusters stay visible even when include scopes files away —
        honest coverage for structure, file filter for content."""
        with TemporaryDirectory() as td:
            root = Path(td).resolve()
            for n in (1, 2):
                _write(root / "proj" / f"memo.{n}" / "memo.md", f"v{n}\n")
            wr = walk.walk_tree(root, include=("*.tex",))
            self.assertEqual(wr.candidate_files, [])
            self.assertEqual(len(wr.family_sites), 1)
            self.assertEqual(wr.family_sites[0].stem, "memo")


class TestEvidenceCollection(unittest.TestCase):
    def test_family_site_versions_and_sidecars(self) -> None:
        with TemporaryDirectory() as td:
            root = Path(td).resolve()
            for n in (1, 3, 7):
                _write(root / "p" / f"draft.{n}" / "draft.md", "x\n")
            _write(root / "p" / "draft.3.review" / "verdict.md", "x\n")
            wr = walk.walk_tree(root)
            self.assertEqual(len(wr.family_sites), 1)
            fam = wr.family_sites[0]
            self.assertEqual(fam.stem, "draft")
            self.assertEqual(fam.version_numbers, [1, 3, 7])
            self.assertEqual(fam.sidecar_dir_names, ["draft.3.review"])

    def test_brief_and_anvil_json_sites(self) -> None:
        with TemporaryDirectory() as td:
            root = Path(td).resolve()
            _write(
                root / "p" / "BRIEF.md",
                "---\ndocuments:\n  - slug: x\n---\n",
            )
            _write(root / "q" / ".anvil.json", "{}\n")
            # A BRIEF.md without documents: is NOT a project BRIEF.
            _write(root / "r" / "BRIEF.md", "# just notes\n")
            wr = walk.walk_tree(root)
            self.assertEqual(
                [b.relative_to(root).as_posix() for b in wr.brief_sites],
                ["p"],
            )
            self.assertEqual(
                [a.relative_to(root).as_posix() for a in wr.anvil_json_sites],
                ["q"],
            )


if __name__ == "__main__":
    unittest.main()
