"""Cluster-boundary tests for `anvil:project-scout` (issue #407, AC 7).

Evidence nominates project roots; BRIEF anchors merging; each cluster
classifies independently at its root:

- slug-nested family nominates the grandparent;
- two flat families under one parent → one cluster;
- descendant family under a BRIEF-bearing root merges upward;
- descendant under a BRIEF-less candidate does NOT merge;
- a loose file inside a cluster's subtree lists under that cluster with
  the auto-resolve ``--enroll`` form.
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
    _write,
    build_briefless_nest,
    build_migrated_project,
    build_nested_under_brief,
)


class TestRootNomination(unittest.TestCase):
    def test_slug_nested_family_nominates_grandparent(self) -> None:
        with TemporaryDirectory() as td:
            root = Path(td)
            build_migrated_project(root)  # <p>/alpha-memo/alpha-memo.N
            result = orchestrate.run(root)
            clusters = result.classification.clusters
            self.assertEqual(len(clusters), 1)
            # The cluster root is the PROJECT (grandparent of the
            # version dirs), not the thread dir.
            self.assertEqual(clusters[0].rel, "migrated-project")

    def test_two_flat_families_one_parent_coalesce(self) -> None:
        with TemporaryDirectory() as td:
            root = Path(td)
            project = root / "two-families"
            for n in (1, 2):
                _write(project / f"memo-a.{n}" / "memo-a.md", f"v{n}\n")
                _write(project / f"memo-b.{n}" / "memo-b.md", f"v{n}\n")
            result = orchestrate.run(root)
            clusters = result.classification.clusters
            self.assertEqual(len(clusters), 1)
            self.assertEqual(clusters[0].rel, "two-families")
            slugs = {t["slug"] for t in clusters[0].threads}
            self.assertEqual(slugs, {"memo-a", "memo-b"})


class TestBriefAnchoredMerge(unittest.TestCase):
    def test_descendant_merges_into_brief_bearing_ancestor(self) -> None:
        with TemporaryDirectory() as td:
            root = Path(td)
            build_nested_under_brief(root)
            result = orchestrate.run(root)
            clusters = result.classification.clusters
            self.assertEqual(len(clusters), 1)
            c = clusters[0]
            self.assertEqual(c.rel, "brief-anchored")
            # The merge is evidence-visible.
            evidence = "\n".join(c.evidence)
            self.assertIn("brief-anchored/sub", evidence)
            self.assertIn("merged descendant", evidence)

    def test_descendant_under_briefless_candidate_does_not_merge(self) -> None:
        with TemporaryDirectory() as td:
            root = Path(td)
            build_briefless_nest(root)
            result = orchestrate.run(root)
            clusters = result.classification.clusters
            rels = sorted(c.rel for c in clusters)
            self.assertEqual(
                rels, ["briefless-outer", "briefless-outer/inner"]
            )


class TestLooseInsideCluster(unittest.TestCase):
    def test_loose_file_lists_under_enclosing_cluster(self) -> None:
        with TemporaryDirectory() as td:
            root = Path(td)
            project = build_migrated_project(root)
            _write(
                project / "2026-06-01-followup.md",
                "# Followup\n\n" + ("Prose. " * 60) + "\n",
            )
            result = orchestrate.run(root)
            clusters = result.classification.clusters
            self.assertEqual(len(clusters), 1)
            c = clusters[0]
            self.assertEqual(c.bucket, cluster.BUCKET_ALREADY_MIGRATED)
            self.assertEqual(len(c.loose_documents), 1)
            doc = c.loose_documents[0]
            self.assertEqual(
                doc.rel, "migrated-project/2026-06-01-followup.md"
            )
            self.assertEqual(
                doc.enclosing_cluster, "migrated-project"
            )
            # Auto-resolve form: plain --enroll <file> (project resolves
            # by BRIEF walk-up; no new-project-root note).
            self.assertEqual(
                doc.recommended_command,
                "/anvil:project-migrate --enroll "
                "migrated-project/2026-06-01-followup.md",
            )
            self.assertFalse(
                any("new project root" in n for n in doc.notes)
            )

    def test_cluster_machinery_files_are_claimed_not_loose(self) -> None:
        """Version-dir bodies, sidecar files, BRIEF.md, and
        infrastructure-dir files never surface as enroll candidates."""
        with TemporaryDirectory() as td:
            root = Path(td)
            build_migrated_project(root)
            result = orchestrate.run(root)
            cls = result.classification
            self.assertEqual(cls.loose_documents, [])
            self.assertEqual(cls.not_document_files, [])
            # All candidates claimed: BRIEF.md, 2 bodies, 1 verdict.md,
            # research/notes.md.
            self.assertEqual(cls.coverage.candidate_files, 5)
            self.assertEqual(cls.coverage.in_clusters, 5)


class TestUnknownNominationDiagnostic(unittest.TestCase):
    def test_anvil_json_only_site_surfaces_as_diagnostic(self) -> None:
        """A nominated root that detect calls UNKNOWN is never dropped
        silently — it lands in diagnostics and its files flow through
        the loose path."""
        with TemporaryDirectory() as td:
            root = Path(td)
            stray = root / "stray"
            _write(stray / ".anvil.json", "{}\n")
            _write(
                stray / "notes-2026-05-01.md",
                "# Notes\n\n" + ("Prose words here. " * 30) + "\n",
            )
            result = orchestrate.run(root)
            self.assertTrue(
                any("UNKNOWN" in d for d in result.classification.diagnostics)
            )
            # The file is still accounted for.
            self.assertTrue(result.classification.coverage.identity_holds)
            self.assertEqual(
                {d.rel for d in result.classification.loose_documents},
                {"stray/notes-2026-05-01.md"},
            )


if __name__ == "__main__":
    unittest.main()
