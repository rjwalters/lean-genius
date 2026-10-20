"""Report + coverage tests for `anvil:project-scout` (issue #407, AC 4/6).

- The coverage identity ``candidate_files == in_clusters +
  loose_classified + not_document`` holds on the mixed mega fixture.
- Output is deterministic (two runs byte-identical — no timestamps).
- The JSON sidecar is versioned (``schema_version``) and carries the
  filters block + per-bucket entries.
- All recommended-action strings name commands that exist at merge
  time; no command string references a flag that does not exist.
"""

from __future__ import annotations

import json
import sys
import unittest
from pathlib import Path
from tempfile import TemporaryDirectory

_HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(_HERE))

from _project_scout_skill_lib import cluster, orchestrate, report  # noqa: E402
from _scout_fixtures import build_mega_tree  # noqa: E402


class TestCoverageIdentity(unittest.TestCase):
    def test_identity_holds_on_mega_tree(self) -> None:
        with TemporaryDirectory() as td:
            root = Path(td)
            build_mega_tree(root)
            result = orchestrate.run(root)
            cov = result.data["coverage"]
            self.assertEqual(
                cov["candidate_files"],
                cov["in_clusters"]
                + cov["loose_classified"]
                + cov["not_document"],
            )
            self.assertTrue(result.success)
            self.assertIn("holds", result.markdown)

    def test_identity_holds_under_filters(self) -> None:
        with TemporaryDirectory() as td:
            root = Path(td)
            build_mega_tree(root)
            for kwargs in (
                {"exclude": ("docs-site",)},
                {"include": ("*.md",)},
                {"verbose": True},
            ):
                with self.subTest(kwargs=kwargs):
                    result = orchestrate.run(root, **kwargs)
                    self.assertTrue(
                        result.classification.coverage.identity_holds
                    )

    def test_every_bucket_present_on_mega_tree(self) -> None:
        with TemporaryDirectory() as td:
            root = Path(td)
            build_mega_tree(root)
            result = orchestrate.run(root)
            buckets = {c["bucket"] for c in result.data["clusters"]}
            self.assertEqual(
                buckets,
                {
                    cluster.BUCKET_ALREADY_MIGRATED,
                    cluster.BUCKET_LEGACY_MIGRATABLE,
                    cluster.BUCKET_BARE_THREADS,
                    cluster.BUCKET_LOOSE_DOCUMENTS,
                    cluster.BUCKET_FOREIGN_GRAMMAR,
                },
            )
            self.assertGreater(result.data["not_document"]["count"], 0)


class TestDeterminism(unittest.TestCase):
    def test_two_runs_byte_identical(self) -> None:
        with TemporaryDirectory() as td:
            root = Path(td)
            build_mega_tree(root)
            first = orchestrate.run(root, verbose=True)
            second = orchestrate.run(root, verbose=True)
            self.assertEqual(first.markdown, second.markdown)
            self.assertEqual(
                json.dumps(first.data, sort_keys=True),
                json.dumps(second.data, sort_keys=True),
            )


class TestJsonSidecar(unittest.TestCase):
    def test_schema_version_and_filters_block(self) -> None:
        with TemporaryDirectory() as td:
            root = Path(td)
            build_mega_tree(root)
            result = orchestrate.run(
                root, include=("*.md", "*.tex"), exclude=("docs-site",)
            )
            data = result.data
            self.assertEqual(data["schema_version"], report.SCHEMA_VERSION)
            self.assertEqual(
                data["filters"]["include"], ["*.md", "*.tex"]
            )
            self.assertEqual(data["filters"]["exclude"], ["docs-site"])
            self.assertIn(
                "node_modules", data["filters"]["default_excludes"]
            )
            pruned_paths = {
                p["path"] for p in data["filters"]["pruned_subtrees"]
            }
            self.assertIn("docs-site", pruned_paths)
            self.assertIn("node_modules", pruned_paths)

    def test_cluster_entries_carry_contract_fields(self) -> None:
        with TemporaryDirectory() as td:
            root = Path(td)
            build_mega_tree(root)
            result = orchestrate.run(root)
            for entry in result.data["clusters"]:
                for key in (
                    "path",
                    "bucket",
                    "detected_shape",
                    "is_bare",
                    "threads",
                    "recommended_command",
                    "confidence",
                    "evidence",
                    "loose_documents",
                ):
                    self.assertIn(key, entry)

    def test_json_file_write_when_requested(self) -> None:
        with TemporaryDirectory() as td_tree, TemporaryDirectory() as td_out:
            root = Path(td_tree)
            build_mega_tree(root)
            json_path = Path(td_out) / "scout.json"
            md_path = Path(td_out) / "scout.md"
            result = orchestrate.run(
                root, report_path=md_path, json_path=json_path
            )
            self.assertEqual(
                json.loads(json_path.read_text(encoding="utf-8")),
                result.data,
            )
            self.assertEqual(
                md_path.read_text(encoding="utf-8"), result.markdown
            )


class TestActionStrings(unittest.TestCase):
    def test_no_nonexistent_flags_anywhere(self) -> None:
        """AC: action strings name real commands that exist at merge
        time. --synthesize-brief never shipped (synthesis is automatic
        when is_bare, post-#411)."""
        with TemporaryDirectory() as td:
            root = Path(td)
            build_mega_tree(root)
            result = orchestrate.run(root, verbose=True)
            self.assertNotIn("--synthesize-brief", result.markdown)
            self.assertNotIn(
                "--synthesize-brief", json.dumps(result.data)
            )
            commands = [
                c["recommended_command"]
                for c in result.data["clusters"]
                if c["recommended_command"]
            ] + [
                d["recommended_command"]
                for d in result.data["loose_documents"]
                if d["recommended_command"]
            ]
            for cmd in commands:
                self.assertTrue(
                    cmd.startswith("/anvil:project-migrate"),
                    cmd,
                )

    def test_bucket_command_shapes(self) -> None:
        with TemporaryDirectory() as td:
            root = Path(td)
            build_mega_tree(root)
            result = orchestrate.run(root)
            by_bucket = {}
            for c in result.data["clusters"]:
                by_bucket.setdefault(c["bucket"], []).append(c)
            self.assertEqual(
                by_bucket[cluster.BUCKET_LEGACY_MIGRATABLE][0][
                    "recommended_command"
                ],
                "/anvil:project-migrate classic-project",
            )
            self.assertEqual(
                by_bucket[cluster.BUCKET_BARE_THREADS][0][
                    "recommended_command"
                ],
                "/anvil:project-migrate bare-paper",
            )
            self.assertIsNone(
                by_bucket[cluster.BUCKET_FOREIGN_GRAMMAR][0][
                    "recommended_command"
                ]
            )
            self.assertIsNone(
                by_bucket[cluster.BUCKET_ALREADY_MIGRATED][0][
                    "recommended_command"
                ]
            )
            enroll_cmds = [
                d["recommended_command"]
                for d in result.data["loose_documents"]
                if d["recommended_command"]
            ]
            self.assertTrue(enroll_cmds)
            for cmd in enroll_cmds:
                self.assertIn("--enroll", cmd)


if __name__ == "__main__":
    unittest.main()
