#!/usr/bin/env python3

import importlib.util
import json
import tempfile
import unittest
from pathlib import Path


SCRIPT = Path(__file__).with_name("generate_small_high_cube_jobs.py")
SPEC = importlib.util.spec_from_file_location("small_high_cube_jobs", SCRIPT)
MODULE = importlib.util.module_from_spec(SPEC)
assert SPEC.loader is not None
SPEC.loader.exec_module(MODULE)


class SmallHighCubeJobsTest(unittest.TestCase):
    def test_manifest_and_materialization(self) -> None:
        with tempfile.TemporaryDirectory() as temporary_name:
            root = Path(temporary_name)
            bases = root / "bases"
            bases.mkdir()
            for filename in MODULE.DEFAULT_FILENAMES.values():
                (bases / filename).write_text(
                    "c fixture\np cnf 300 2\n1 0\n-2 0\n"
                )
            manifest_path = root / "manifest.json"
            MODULE.write_manifest(bases, manifest_path)
            manifest = json.loads(manifest_path.read_text())
            self.assertEqual(manifest["positive_cube_jobs"], 392)
            self.assertEqual(manifest["negative_cover_jobs"], 14)
            self.assertEqual(len(manifest["cells"]), 7)
            self.assertEqual(
                manifest["cells"]["h3_b1"]["base"],
                str((bases / "b1.lean-emitted.cnf").resolve()),
            )
            self.assertTrue(all(
                len(cell["jobs"]) == 58
                for cell in manifest["cells"].values()
            ))

            output = root / "cube.cnf"
            MODULE.materialize(manifest_path, "h3_b1.cube-0-0", output)
            self.assertEqual(MODULE.inspect_dimacs(output), (300, 4))
            self.assertEqual(
                output.read_text().splitlines()[-2:], ["142 0", "142 0"]
            )

            cover = root / "cover.cnf"
            MODULE.materialize(manifest_path, "h5_t2.cover-left", cover)
            self.assertEqual(MODULE.inspect_dimacs(cover), (300, 9))
            self.assertEqual(
                cover.read_text().splitlines()[-7:],
                ["-231 0", "-236 0", "-237 0", "-238 0",
                 "-239 0", "-240 0", "-241 0"],
            )

    def test_rejects_bad_clause_count(self) -> None:
        with tempfile.TemporaryDirectory() as temporary_name:
            path = Path(temporary_name) / "bad.cnf"
            path.write_text("p cnf 3 2\n1 0\n")
            with self.assertRaisesRegex(ValueError, "declares 2 clauses"):
                MODULE.inspect_dimacs(path)

    def test_rejects_literal_beyond_declared_variable_top(self) -> None:
        with tempfile.TemporaryDirectory() as temporary_name:
            root = Path(temporary_name)
            for name, contents, message in (
                ("high.cnf", "p cnf 3 1\n4 0\n", "exceeds variable header"),
                ("zero.cnf", "p cnf 3 1\n1 0 0\n", "unterminated clause"),
                ("early.cnf", "1 0\np cnf 3 1\n", "precedes header"),
            ):
                with self.subTest(name=name):
                    path = root / name
                    path.write_text(contents)
                    with self.assertRaisesRegex(ValueError, message):
                        MODULE.inspect_dimacs(path)

    def test_rejects_unknown_and_duplicated_job_ids(self) -> None:
        with tempfile.TemporaryDirectory() as temporary_name:
            root = Path(temporary_name)
            bases = root / "bases"
            bases.mkdir()
            for filename in MODULE.DEFAULT_FILENAMES.values():
                (bases / filename).write_text("p cnf 300 1\n1 0\n")
            manifest_path = root / "manifest.json"
            MODULE.write_manifest(bases, manifest_path)
            with self.assertRaisesRegex(ValueError, "unknown or duplicated"):
                MODULE.materialize(manifest_path, "missing", root / "out.cnf")

            manifest = json.loads(manifest_path.read_text())
            duplicate = dict(manifest["cells"]["h3_b1"]["jobs"][0])
            manifest["cells"]["h3_c1"]["jobs"].append(duplicate)
            manifest_path.write_text(json.dumps(manifest))
            with self.assertRaisesRegex(ValueError, "unknown or duplicated"):
                MODULE.materialize(manifest_path, duplicate["id"], root / "out.cnf")

    def test_rejects_base_hash_tamper_and_preserves_output(self) -> None:
        with tempfile.TemporaryDirectory() as temporary_name:
            root = Path(temporary_name)
            bases = root / "bases"
            bases.mkdir()
            for filename in MODULE.DEFAULT_FILENAMES.values():
                (bases / filename).write_text("p cnf 300 1\n1 0\n")
            manifest_path = root / "manifest.json"
            MODULE.write_manifest(bases, manifest_path)
            output = root / "out.cnf"
            output.write_text("preserve me\n")
            (bases / "b1.lean-emitted.cnf").write_text(
                "p cnf 300 1\n1 0\nc tampered\n"
            )
            with self.assertRaisesRegex(ValueError, "base CNF hash mismatch"):
                MODULE.materialize(manifest_path, "h3_b1.cube-0-0", output)
            self.assertEqual(output.read_text(), "preserve me\n")

    def test_metadata_tamper_fails_atomically(self) -> None:
        with tempfile.TemporaryDirectory() as temporary_name:
            root = Path(temporary_name)
            bases = root / "bases"
            bases.mkdir()
            for filename in MODULE.DEFAULT_FILENAMES.values():
                (bases / filename).write_text("p cnf 300 1\n1 0\n")
            manifest_path = root / "manifest.json"
            MODULE.write_manifest(bases, manifest_path)
            manifest = json.loads(manifest_path.read_text())
            manifest["cells"]["h3_b1"]["base_clauses"] = 2
            manifest_path.write_text(json.dumps(manifest))
            output = root / "out.cnf"
            output.write_text("preserve me\n")
            with self.assertRaisesRegex(ValueError, "declares 4 clauses"):
                MODULE.materialize(manifest_path, "h3_b1.cube-0-0", output)
            self.assertEqual(output.read_text(), "preserve me\n")


if __name__ == "__main__":
    unittest.main()
