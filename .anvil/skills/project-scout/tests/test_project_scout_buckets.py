"""Per-bucket classification tests for `anvil:project-scout` (issue #407).

Each taxonomy bucket has a fixture tree and a classification test
(FOREIGN_GRAMMAR has its own dedicated regression-lock file). Also pins:

- BARE_THREADS classifies via the #408 ``ProjectInventory.is_bare``
  sub-state — scout ships NO second bare predicate (grep-level check).
- Recommended-action strings name real commands: plain
  ``/anvil:project-migrate <dir>`` for BARE_THREADS (no
  ``--synthesize-brief`` flag exists post-#411), ``--enroll`` for
  LOOSE_DOCUMENTS.
- The version-gap bare-thread shape ({1,3,4,5,6,7}) is inventoried
  faithfully.
"""

from __future__ import annotations

import sys
import unittest
from pathlib import Path
from tempfile import TemporaryDirectory

_HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(_HERE))

from _project_scout_skill_lib import cluster, orchestrate  # noqa: E402
from _scout_fixtures import (  # noqa: E402
    build_bare_threads,
    build_classic_project,
    build_loose_docs_dir,
    build_migrated_project,
)


def _single_cluster(root: Path):
    result = orchestrate.run(root)
    clusters = result.classification.clusters
    return result, clusters


class TestAlreadyMigrated(unittest.TestCase):
    def test_migrated_project_buckets_already_migrated(self) -> None:
        with TemporaryDirectory() as td:
            root = Path(td)
            build_migrated_project(root)
            result, clusters = _single_cluster(root)
            self.assertEqual(len(clusters), 1)
            c = clusters[0]
            self.assertEqual(c.bucket, cluster.BUCKET_ALREADY_MIGRATED)
            self.assertEqual(c.detected_shape, "fully_migrated")
            self.assertIsNone(c.recommended_command)
            self.assertEqual(
                c.threads, [{"slug": "alpha-memo", "versions": [1, 2]}]
            )


class TestLegacyMigratable(unittest.TestCase):
    def test_classic_project_buckets_legacy(self) -> None:
        with TemporaryDirectory() as td:
            root = Path(td)
            build_classic_project(root)
            result, clusters = _single_cluster(root)
            self.assertEqual(len(clusters), 1)
            c = clusters[0]
            self.assertEqual(c.bucket, cluster.BUCKET_LEGACY_MIGRATABLE)
            self.assertEqual(c.detected_shape, "pre_283_classic")
            self.assertFalse(c.is_bare)
            self.assertEqual(
                c.recommended_command,
                "/anvil:project-migrate classic-project",
            )


class TestBareThreads(unittest.TestCase):
    def test_bare_version_gap_shape_buckets_bare(self) -> None:
        with TemporaryDirectory() as td:
            root = Path(td)
            build_bare_threads(root)
            result, clusters = _single_cluster(root)
            bare = [
                c for c in clusters
                if c.bucket == cluster.BUCKET_BARE_THREADS
            ]
            self.assertEqual(len(bare), 1)
            c = bare[0]
            self.assertTrue(c.is_bare)
            self.assertEqual(c.detected_shape, "pre_283_classic")
            # Version gaps inventoried faithfully (no `.2`).
            self.assertEqual(
                c.threads,
                [
                    {
                        "slug": "bispectral-imaging",
                        "versions": [1, 3, 4, 5, 6, 7],
                    }
                ],
            )

    def test_bare_action_string_is_plain_migrate(self) -> None:
        """No --synthesize-brief flag exists (post-#411: synthesis is
        automatic when is_bare). The action string must be the plain
        command, with the synthesis note alongside."""
        with TemporaryDirectory() as td:
            root = Path(td)
            build_bare_threads(root)
            result, clusters = _single_cluster(root)
            c = [
                x for x in clusters
                if x.bucket == cluster.BUCKET_BARE_THREADS
            ][0]
            self.assertEqual(
                c.recommended_command, "/anvil:project-migrate bare-paper"
            )
            self.assertNotIn("--synthesize-brief", result.markdown)
            self.assertIn("BRIEF will be synthesized", "\n".join(c.notes))

    def test_scout_has_no_second_bare_predicate(self) -> None:
        """Grep-level AC: scout delegates to #408's is_bare — it must not
        reimplement the predicate."""
        lib_dir = _HERE.parent / "lib"
        for py in sorted(lib_dir.glob("*.py")):
            text = py.read_text(encoding="utf-8")
            self.assertNotIn(
                "def is_bare", text,
                f"{py.name} reimplements the bare predicate",
            )
        # And the delegation point exists.
        cluster_src = (lib_dir / "cluster.py").read_text(encoding="utf-8")
        self.assertIn("inv.is_bare", cluster_src)


class TestLooseDocuments(unittest.TestCase):
    def test_loose_docs_dir_splits_loose_vs_not_document(self) -> None:
        with TemporaryDirectory() as td:
            root = Path(td)
            build_loose_docs_dir(root)
            result = orchestrate.run(root)
            cls = result.classification
            loose_rels = {d.rel for d in cls.loose_documents}
            self.assertEqual(
                loose_rels,
                {
                    "corp-docs/2026-05-19-board-update.md",
                    "corp-docs/competitive-landscape-2026-05-20.md",
                    "corp-docs/analysis/tam-analysis.md",
                },
            )
            nd_rels = {d.rel for d in cls.not_document_files}
            self.assertEqual(
                nd_rels,
                {
                    "corp-docs/README.md",
                    "corp-docs/CHANGELOG.md",
                    "corp-docs/adr/0001-use-postgres.md",
                },
            )

    def test_loose_documents_clusters_group_by_directory(self) -> None:
        with TemporaryDirectory() as td:
            root = Path(td)
            build_loose_docs_dir(root)
            result = orchestrate.run(root)
            loose_clusters = [
                c
                for c in result.classification.clusters
                if c.bucket == cluster.BUCKET_LOOSE_DOCUMENTS
            ]
            self.assertEqual(
                {c.rel for c in loose_clusters},
                {"corp-docs", "corp-docs/analysis"},
            )

    def test_enroll_action_string(self) -> None:
        with TemporaryDirectory() as td:
            root = Path(td)
            build_loose_docs_dir(root)
            result = orchestrate.run(root)
            by_rel = {
                d.rel: d for d in result.classification.loose_documents
            }
            doc = by_rel["corp-docs/2026-05-19-board-update.md"]
            self.assertEqual(
                doc.recommended_command,
                "/anvil:project-migrate --enroll "
                "corp-docs/2026-05-19-board-update.md",
            )
            # Outside any cluster: enroll proposes a new project root.
            self.assertTrue(
                any("new project root" in n for n in doc.notes)
            )

    def test_batch_form_surfaced_for_multi_candidate_dir(self) -> None:
        with TemporaryDirectory() as td:
            root = Path(td)
            build_loose_docs_dir(root)
            result = orchestrate.run(root)
            corp = [
                c
                for c in result.classification.clusters
                if c.bucket == cluster.BUCKET_LOOSE_DOCUMENTS
                and c.rel == "corp-docs"
            ][0]
            self.assertTrue(
                any(
                    "--enroll corp-docs/*.md" in n for n in corp.notes
                )
            )


class TestNotDocument(unittest.TestCase):
    def test_not_document_counted_not_listed_by_default(self) -> None:
        with TemporaryDirectory() as td:
            root = Path(td)
            build_loose_docs_dir(root)
            quiet = orchestrate.run(root)
            self.assertNotIn("corp-docs/README.md", quiet.markdown)
            self.assertEqual(quiet.data["not_document"]["count"], 3)
            self.assertEqual(quiet.data["not_document"]["paths"], [])
            loud = orchestrate.run(root, verbose=True)
            self.assertIn("corp-docs/README.md", loud.markdown)
            self.assertEqual(
                len(loud.data["not_document"]["paths"]), 3
            )


if __name__ == "__main__":
    unittest.main()
