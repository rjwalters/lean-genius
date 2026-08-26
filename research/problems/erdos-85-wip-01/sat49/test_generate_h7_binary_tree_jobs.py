#!/usr/bin/env python3

import json
import tempfile
import unittest
from pathlib import Path

from generate_h7_binary_tree_jobs import materialize, write_manifest
from generate_h7_t0_cube_one_cover_jobs import inspect_dimacs, sha256


class BinaryTreeJobsTest(unittest.TestCase):
    def setUp(self) -> None:
        self.temporary = tempfile.TemporaryDirectory()
        self.root = Path(self.temporary.name)
        self.base = self.root / "base.cnf"
        self.base.write_text("c fixture\np cnf 8 2\n1 2 0\n-1 3 0\n")
        self.parent = self.root / "parent.json"
        self.parent.write_text(json.dumps({
            "schema": "erdos85-h7-t0-cube1-cover-v1",
            "base": str(self.base.resolve()),
            "base_sha256": sha256(self.base),
            "variables": 8,
            "base_clauses": 2,
            "jobs": [{"id": "cube-0", "kind": "cube", "units": [4, -5]}],
        }))
        self.manifest = self.root / "tree.json"
        write_manifest(self.parent, "cube-0", (6, 7), self.manifest)

    def tearDown(self) -> None:
        self.temporary.cleanup()

    def test_complete_ordered_tree_and_exact_materialization(self) -> None:
        manifest = json.loads(self.manifest.read_text())
        self.assertEqual(manifest["leaf_count"], 4)
        self.assertEqual(
            [(leaf["id"], leaf["path_units"]) for leaf in manifest["leaves"]],
            [("cube-0.binary.leaf-00", [-6, -7]),
             ("cube-0.binary.leaf-01", [-6, 7]),
             ("cube-0.binary.leaf-10", [6, -7]),
             ("cube-0.binary.leaf-11", [6, 7])])
        output = self.root / "leaf.cnf"
        materialize(self.manifest, "cube-0.binary.leaf-01", output)
        self.assertEqual(inspect_dimacs(output), (8, 6))
        self.assertEqual(output.read_text().splitlines()[-4:],
                         ["4 0", "-5 0", "-6 0", "7 0"])

    def test_materializer_rejects_tampered_leaf(self) -> None:
        manifest = json.loads(self.manifest.read_text())
        manifest["leaves"][0]["path_units"] = [6, 7]
        self.manifest.write_text(json.dumps(manifest))
        with self.assertRaisesRegex(ValueError, "leaf enumeration"):
            materialize(self.manifest, "cube-0.binary.leaf-00",
                        self.root / "bad.cnf")


if __name__ == "__main__":
    unittest.main()
