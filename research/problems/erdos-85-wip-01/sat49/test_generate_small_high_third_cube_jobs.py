#!/usr/bin/env python3

import json
import tempfile
import unittest
from pathlib import Path

import generate_small_high_third_cube_jobs as third


class SmallHighThirdCubeJobsTest(unittest.TestCase):
    def fixture(self, root: Path) -> tuple[Path, Path, Path]:
        base = root / "base.cnf"
        base.write_text("c fixture\np cnf 500 2\n1 0\n-2 0\n")
        parent = root / "parent.json"
        parent.write_text(json.dumps({
            "schema": "erdos85-small-high-nested-cube-jobs-v1",
            "leaves": {
                "source": {
                    "cell": "h3_b1",
                    "base": str(base),
                    "base_sha256": third.sha256(base),
                    "variables": 500,
                    "base_clauses": 2,
                    "parent_units": [142, 142],
                    "jobs": [
                        {"id": "h3_b1.cube-0-0.nested.cover-left",
                         "kind": "cover-left", "units": [-162]},
                        {"id": "h3_b1.cube-0-0.nested.cube-0-0",
                         "kind": "cube", "units": [162, 163]},
                        {"id": "h3_b1.cube-0-0.nested.cube-0-1",
                         "kind": "cube", "units": [162, 209]},
                    ],
                },
                "unsupported": {
                    "cell": "h3_c2",
                    "base": str(base),
                    "base_sha256": third.sha256(base),
                    "variables": 500,
                    "base_clauses": 2,
                    "parent_units": [100],
                    "jobs": [{"id": "h3_c2.nested.cube-0-0",
                              "kind": "cube", "units": [101, 102]}],
                },
            },
        }, indent=2) + "\n")
        hard = root / "hard.txt"
        hard.write_text("# canonical slow canary\n"
                        "h3_b1.cube-0-0.nested.cube-0-0\n")
        manifest = root / "third.json"
        return parent, hard, manifest

    def test_manifest_and_materialization(self) -> None:
        with tempfile.TemporaryDirectory() as temporary_name:
            root = Path(temporary_name)
            parent, hard, manifest_path = self.fixture(root)
            third.write_manifest(parent, hard, manifest_path)
            manifest = json.loads(manifest_path.read_text())
            self.assertEqual(manifest["hard_nested_cube_jobs"], 1)
            self.assertEqual(manifest["positive_cube_jobs"], 64)
            self.assertEqual(manifest["negative_cover_jobs"], 2)
            self.assertEqual(manifest["parent_manifest_sha256"], third.sha256(parent))
            self.assertEqual(manifest["hard_jobs_sha256"], third.sha256(hard))

            leaf = manifest["leaves"]["h3_b1.cube-0-0.nested.cube-0-0"]
            self.assertEqual(leaf["parent_units"], [142, 142, 162, 163])
            self.assertEqual(leaf["left"], list(third.LEFT))
            self.assertEqual(leaf["right"], list(third.RIGHT))
            self.assertEqual(len(leaf["jobs"]), 66)

            cube = root / "cube.cnf"
            third.materialize(
                manifest_path,
                "h3_b1.cube-0-0.nested.cube-0-0.third.cube-7-7",
                cube,
            )
            self.assertEqual(third.inspect_dimacs(cube), (500, 8))
            self.assertEqual(
                cube.read_text().splitlines()[-6:],
                ["142 0", "142 0", "162 0", "163 0", "488 0", "489 0"],
            )

            cover = root / "cover.cnf"
            third.materialize(
                manifest_path,
                "h3_b1.cube-0-0.nested.cube-0-0.third.cover-left",
                cover,
            )
            self.assertEqual(third.inspect_dimacs(cover), (500, 14))
            self.assertEqual(
                cover.read_text().splitlines()[-8:],
                [f"-{literal} 0" for literal in third.LEFT],
            )

    def test_json_hard_list_and_all_supported_jobs(self) -> None:
        with tempfile.TemporaryDirectory() as temporary_name:
            root = Path(temporary_name)
            parent, hard, manifest_path = self.fixture(root)
            hard.write_text(json.dumps([
                "h3_b1.cube-0-0.nested.cube-0-1",
                "h3_b1.cube-0-0.nested.cube-0-0",
            ]))
            third.write_manifest(parent, hard, manifest_path)
            manifest = json.loads(manifest_path.read_text())
            self.assertEqual(manifest["hard_nested_cube_jobs"], 2)
            self.assertEqual(list(manifest["leaves"]), [
                "h3_b1.cube-0-0.nested.cube-0-0",
                "h3_b1.cube-0-0.nested.cube-0-1",
            ])

            all_manifest = root / "all.json"
            third.write_manifest(parent, None, all_manifest)
            self.assertEqual(
                json.loads(all_manifest.read_text())["hard_nested_cube_jobs"], 2
            )

    def test_rejects_duplicate_unknown_and_non_cube_hard_jobs(self) -> None:
        with tempfile.TemporaryDirectory() as temporary_name:
            root = Path(temporary_name)
            parent, hard, manifest = self.fixture(root)
            job = "h3_b1.cube-0-0.nested.cube-0-0"
            hard.write_text(f"{job}\n{job}\n")
            with self.assertRaisesRegex(ValueError, "duplicate ids"):
                third.write_manifest(parent, hard, manifest)
            for bad in ("missing", "h3_b1.cube-0-0.nested.cover-left",
                        "h3_c2.nested.cube-0-0"):
                hard.write_text(bad + "\n")
                with self.assertRaisesRegex(ValueError, "unknown, non-cube, or unsupported"):
                    third.write_manifest(parent, hard, manifest)

    def test_materialize_rejects_tampered_dependencies_and_preserves_output(self) -> None:
        with tempfile.TemporaryDirectory() as temporary_name:
            root = Path(temporary_name)
            parent, hard, manifest = self.fixture(root)
            third.write_manifest(parent, hard, manifest)
            output = root / "existing.cnf"
            output.write_text("preserve me\n")
            hard.write_text("tampered\n")
            with self.assertRaisesRegex(ValueError, "hard-job file hash mismatch"):
                third.materialize(
                    manifest,
                    "h3_b1.cube-0-0.nested.cube-0-0.third.cover-right",
                    output,
                )
            self.assertEqual(output.read_text(), "preserve me\n")

    def test_rejects_parent_and_base_hash_tampering(self) -> None:
        with tempfile.TemporaryDirectory() as temporary_name:
            root = Path(temporary_name)
            parent, hard, manifest = self.fixture(root)
            third.write_manifest(parent, hard, manifest)
            parent.write_text(parent.read_text() + "\n")
            with self.assertRaisesRegex(ValueError, "parent manifest hash mismatch"):
                third.materialize(manifest, "irrelevant", root / "out.cnf")

            parent, hard, manifest = self.fixture(root)
            third.write_manifest(parent, hard, manifest)
            base = root / "base.cnf"
            base.write_text(base.read_text() + "c tampered\n")
            with self.assertRaisesRegex(ValueError, "base CNF hash mismatch"):
                third.materialize(
                    manifest,
                    "h3_b1.cube-0-0.nested.cube-0-0.third.cover-right",
                    root / "out.cnf",
                )

    def test_queue_receipt_binds_exact_manifest_order(self) -> None:
        with tempfile.TemporaryDirectory() as temporary_name:
            root = Path(temporary_name)
            parent, hard, manifest = self.fixture(root)
            hard.write_text(json.dumps([
                "h3_b1.cube-0-0.nested.cube-0-1",
                "h3_b1.cube-0-0.nested.cube-0-0",
            ]))
            third.write_manifest(parent, hard, manifest)
            queue, receipt = root / "queue.txt", root / "queue.receipt.json"
            third.write_queue(manifest, queue, receipt)
            ids = queue.read_text().splitlines()
            self.assertEqual(len(ids), 132)
            self.assertEqual(
                ids[0],
                "h3_b1.cube-0-0.nested.cube-0-0.third.cover-left",
            )
            self.assertEqual(
                ids[66],
                "h3_b1.cube-0-0.nested.cube-0-1.third.cover-left",
            )
            data = json.loads(receipt.read_text())
            self.assertEqual(data["schema"],
                             "erdos85-small-high-third-queue-receipt-v1")
            self.assertEqual(data["manifest_sha256"], third.sha256(manifest))
            self.assertEqual(data["queue_sha256"], third.sha256(queue))
            self.assertEqual(data["jobs"], 132)
            self.assertEqual(data["positive_cube_jobs"], 128)
            self.assertEqual(data["negative_cover_jobs"], 4)
            third.validate_queue_receipt(receipt, third.sha256(receipt))

    def test_queue_rejects_tampered_dependencies_and_metadata(self) -> None:
        with tempfile.TemporaryDirectory() as temporary_name:
            root = Path(temporary_name)
            parent, hard, manifest = self.fixture(root)
            third.write_manifest(parent, hard, manifest)
            hard.write_text("tampered\n")
            with self.assertRaisesRegex(ValueError, "hard-job file hash mismatch"):
                third.write_queue(manifest, root / "queue", root / "receipt")

            parent, hard, manifest = self.fixture(root)
            third.write_manifest(parent, hard, manifest)
            data = json.loads(manifest.read_text())
            data["positive_cube_jobs"] += 1
            manifest.write_text(json.dumps(data))
            with self.assertRaisesRegex(ValueError, "count metadata mismatch"):
                third.write_queue(manifest, root / "queue", root / "receipt")

    def test_queue_validator_rejects_queue_and_receipt_tampering(self) -> None:
        with tempfile.TemporaryDirectory() as temporary_name:
            root = Path(temporary_name)
            parent, hard, manifest = self.fixture(root)
            third.write_manifest(parent, hard, manifest)
            queue, receipt = root / "queue.txt", root / "queue.receipt.json"
            third.write_queue(manifest, queue, receipt)
            queue.write_text(queue.read_text() + "extra\n")
            with self.assertRaisesRegex(ValueError, "queue hash mismatch"):
                third.validate_queue_receipt(receipt, third.sha256(receipt))

            third.write_queue(manifest, queue, receipt)
            data = json.loads(receipt.read_text())
            data["jobs"] += 1
            receipt.write_text(json.dumps(data))
            with self.assertRaisesRegex(ValueError, "metadata mismatch"):
                third.validate_queue_receipt(receipt, third.sha256(receipt))

            third.write_queue(manifest, queue, receipt)
            data = json.loads(receipt.read_text())
            data["unexpected"] = True
            receipt.write_text(json.dumps(data))
            with self.assertRaisesRegex(ValueError, "receipt fields"):
                third.validate_queue_receipt(receipt, third.sha256(receipt))

    def test_queue_validator_requires_external_receipt_pin(self) -> None:
        with tempfile.TemporaryDirectory() as temporary_name:
            root = Path(temporary_name)
            parent, hard, manifest = self.fixture(root)
            third.write_manifest(parent, hard, manifest)
            queue, receipt = root / "queue.txt", root / "queue.receipt.json"
            third.write_queue(manifest, queue, receipt)
            with self.assertRaisesRegex(ValueError, "receipt hash mismatch"):
                third.validate_queue_receipt(receipt, "0" * 64)
            with self.assertRaisesRegex(ValueError, "64 lowercase hex"):
                third.validate_queue_receipt(receipt, "not-a-sha")


if __name__ == "__main__":
    unittest.main()
