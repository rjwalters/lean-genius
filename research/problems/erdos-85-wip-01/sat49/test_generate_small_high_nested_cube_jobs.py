#!/usr/bin/env python3

import json
import tempfile
import unittest
from pathlib import Path

import generate_small_high_nested_cube_jobs as nested


class SmallHighNestedCubeJobsTest(unittest.TestCase):
    def fixture(self, root: Path) -> tuple[Path, Path, Path]:
        base = root / "base.cnf"
        base.write_text("c fixture\np cnf 500 2\n1 0\n-2 0\n")
        parent = root / "parent.json"
        cells = {}
        for cell_name in ("h3_b1", "h5_t1"):
            cells[cell_name] = {
                "base": str(base),
                "base_sha256": nested.sha256(base),
                "variables": 500,
                "base_clauses": 2,
                "jobs": [
                    {"id": f"{cell_name}.cover-left", "kind": "cover-left",
                     "units": [-10]},
                    {"id": f"{cell_name}.cube-0-0", "kind": "cube",
                     "units": [20, 21]},
                ],
            }
        parent.write_text(json.dumps({
            "schema": "erdos85-small-high-cube-jobs-v1",
            "cells": cells,
        }, indent=2) + "\n")
        hard = root / "hard.txt"
        hard.write_text("# pilot\nh3_b1.cube-0-0\n")
        return parent, hard, root / "nested.json"

    def test_manifest_and_materialization(self) -> None:
        with tempfile.TemporaryDirectory() as temporary_name:
            root = Path(temporary_name)
            parent, hard, manifest_path = self.fixture(root)
            nested.write_manifest(parent, hard, manifest_path)
            manifest = json.loads(manifest_path.read_text())
            self.assertEqual(manifest["hard_parent_jobs"], 1)
            self.assertEqual(manifest["positive_cube_jobs"], 64)
            self.assertEqual(manifest["negative_cover_jobs"], 2)
            self.assertEqual(manifest["parent_manifest_sha256"], nested.sha256(parent))
            leaf = manifest["leaves"]["h3_b1.cube-0-0"]
            self.assertEqual(leaf["parent_units"], [20, 21])
            self.assertEqual(leaf["left"], list(nested.SELECTORS["h3_b1"][0]))
            self.assertEqual(leaf["right"], list(nested.SELECTORS["h3_b1"][1]))
            self.assertEqual(len(leaf["jobs"]), 66)

            cube = root / "cube.cnf"
            nested.materialize(
                manifest_path, "h3_b1.cube-0-0.nested.cube-7-7", cube
            )
            self.assertEqual(nested.inspect_dimacs(cube), (500, 6))
            self.assertEqual(
                cube.read_text().splitlines()[-4:],
                ["20 0", "21 0", "486 0", "487 0"],
            )

            cover = root / "cover.cnf"
            nested.materialize(
                manifest_path, "h3_b1.cube-0-0.nested.cover-left", cover
            )
            self.assertEqual(nested.inspect_dimacs(cover), (500, 12))
            self.assertEqual(
                cover.read_text().splitlines()[-8:],
                [f"-{literal} 0" for literal in nested.SELECTORS["h3_b1"][0]],
            )

    def test_variable_width_grid_and_json_hard_list(self) -> None:
        with tempfile.TemporaryDirectory() as temporary_name:
            root = Path(temporary_name)
            parent, hard, manifest_path = self.fixture(root)
            hard.write_text(json.dumps(["h5_t1.cube-0-0"]))
            nested.write_manifest(parent, hard, manifest_path)
            manifest = json.loads(manifest_path.read_text())
            self.assertEqual(manifest["positive_cube_jobs"], 56)
            self.assertEqual(manifest["negative_cover_jobs"], 2)
            leaf = manifest["leaves"]["h5_t1.cube-0-0"]
            self.assertEqual(len(leaf["left"]), 8)
            self.assertEqual(len(leaf["right"]), 7)
            self.assertEqual(len(leaf["jobs"]), 58)

    def test_rejects_duplicate_unknown_and_non_cube_parent_jobs(self) -> None:
        with tempfile.TemporaryDirectory() as temporary_name:
            root = Path(temporary_name)
            parent, hard, manifest = self.fixture(root)
            hard.write_text("h3_b1.cube-0-0\nh3_b1.cube-0-0\n")
            with self.assertRaisesRegex(ValueError, "duplicate ids"):
                nested.write_manifest(parent, hard, manifest)
            hard.write_text("missing\n")
            with self.assertRaisesRegex(ValueError, "unknown parent job"):
                nested.write_manifest(parent, hard, manifest)
            hard.write_text("h3_b1.cover-left\n")
            with self.assertRaisesRegex(ValueError, "positive parent cube"):
                nested.write_manifest(parent, hard, manifest)

    def test_materialize_rejects_parent_tamper_and_preserves_output(self) -> None:
        with tempfile.TemporaryDirectory() as temporary_name:
            root = Path(temporary_name)
            parent, hard, manifest = self.fixture(root)
            nested.write_manifest(parent, hard, manifest)
            output = root / "existing.cnf"
            output.write_text("preserve me\n")
            parent.write_text(parent.read_text() + "\n")
            with self.assertRaisesRegex(ValueError, "parent manifest hash mismatch"):
                nested.materialize(
                    manifest, "h3_b1.cube-0-0.nested.cover-right", output
                )
            self.assertEqual(output.read_text(), "preserve me\n")

    def test_rejects_base_hash_and_metadata_tampering(self) -> None:
        with tempfile.TemporaryDirectory() as temporary_name:
            root = Path(temporary_name)
            parent, hard, manifest = self.fixture(root)
            data = json.loads(parent.read_text())
            data["cells"]["h3_b1"]["base_clauses"] = 3
            parent.write_text(json.dumps(data))
            with self.assertRaisesRegex(ValueError, "base CNF metadata mismatch"):
                nested.write_manifest(parent, hard, manifest)

            parent, hard, manifest = self.fixture(root)
            nested.write_manifest(parent, hard, manifest)
            (root / "base.cnf").write_text("p cnf 500 2\n1 0\n-2 0\nc changed\n")
            with self.assertRaisesRegex(ValueError, "base CNF hash mismatch"):
                nested.materialize(
                    manifest, "h3_b1.cube-0-0.nested.cover-right", root / "out.cnf"
                )


if __name__ == "__main__":
    unittest.main()
