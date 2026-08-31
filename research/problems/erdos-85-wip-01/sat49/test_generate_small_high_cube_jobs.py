#!/usr/bin/env python3

import importlib.util
import hashlib
import json
import subprocess
import tempfile
import unittest
from pathlib import Path


SCRIPT = Path(__file__).with_name("generate_small_high_cube_jobs.py")
SPEC = importlib.util.spec_from_file_location("small_high_cube_jobs", SCRIPT)
MODULE = importlib.util.module_from_spec(SPEC)
assert SPEC.loader is not None
SPEC.loader.exec_module(MODULE)


class SmallHighCubeJobsTest(unittest.TestCase):
    def freight_receipt(self, bases: Path) -> Path:
        commit = subprocess.check_output(
            ["git", "rev-parse", "HEAD"], cwd=MODULE.REPO, text=True).strip()
        builder_bytes = subprocess.check_output(
            ["git", "show", f"{commit}:{MODULE.FREIGHT_BUILDER_SOURCE}"],
            cwd=MODULE.REPO)
        emitter_bytes = subprocess.check_output(
            ["git", "show", f"{commit}:{MODULE.EMITTER_SOURCE}"], cwd=MODULE.REPO)
        rows = []
        for cell, filename in MODULE.DEFAULT_FILENAMES.items():
            path = bases / filename
            variables, clauses = MODULE.inspect_dimacs(path)
            maximum = max(abs(int(value)) for line in path.read_text().splitlines()
                          if line and not line.startswith(("c", "p"))
                          for value in line.split()[:-1])
            rows.append({
                "cell": cell, "path": filename, "sha256": MODULE.sha256(path),
                "bytes": path.stat().st_size, "variables": variables,
                "clauses": clauses, "max_literal": maximum,
            })
        receipt = {
            "schema": MODULE.FREIGHT_SCHEMA, "git_commit": commit,
            "freight_builder_source": MODULE.FREIGHT_BUILDER_SOURCE,
            "freight_builder_sha256": hashlib.sha256(builder_bytes).hexdigest(),
            "emitter_source": MODULE.EMITTER_SOURCE,
            "emitter_sha256": hashlib.sha256(emitter_bytes).hexdigest(),
            "emitter_build_command": [
                "lake", "build", "Proofs.Erdos85OrderFortyNineSmallHighCnfEmit"],
            "emitter_command": ["lake", "env", "lean", "--run",
                                "/repo/" + MODULE.EMITTER_SOURCE, "<cell>"],
            "lean_version": "Lean fixture", "cells": rows,
        }
        path = bases / "receipt.json"
        path.write_bytes(MODULE.canonical_json(receipt))
        return path

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
            receipt_path = self.freight_receipt(bases)
            MODULE.write_manifest(
                bases, receipt_path, MODULE.sha256(receipt_path), manifest_path)
            manifest = json.loads(manifest_path.read_text())
            self.assertEqual(manifest["positive_cube_jobs"], 392)
            self.assertEqual(manifest["negative_cover_jobs"], 14)
            self.assertEqual(len(manifest["cells"]), 7)
            self.assertEqual(
                manifest["cells"]["h3_b1"]["base"],
                str((bases / "h3_b1.cnf").resolve()),
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

    def test_manifest_publication_is_create_only(self) -> None:
        with tempfile.TemporaryDirectory() as temporary_name:
            root = Path(temporary_name)
            bases = root / "bases"
            bases.mkdir()
            for filename in MODULE.DEFAULT_FILENAMES.values():
                (bases / filename).write_text("p cnf 300 1\n1 0\n")
            receipt = self.freight_receipt(bases)
            output = root / "manifest.json"
            output.write_bytes(b"preserve manifest\n")
            with self.assertRaisesRegex(FileExistsError, "refusing to replace"):
                MODULE.write_manifest(
                    bases, receipt, MODULE.sha256(receipt), output)
            self.assertEqual(output.read_bytes(), b"preserve manifest\n")
            self.assertEqual(list(root.glob(".manifest.json.*.tmp")), [])

    def test_materialization_publication_is_create_only(self) -> None:
        with tempfile.TemporaryDirectory() as temporary_name:
            root = Path(temporary_name)
            bases = root / "bases"
            bases.mkdir()
            for filename in MODULE.DEFAULT_FILENAMES.values():
                (bases / filename).write_text("p cnf 300 1\n1 0\n")
            receipt = self.freight_receipt(bases)
            manifest = root / "manifest.json"
            MODULE.write_manifest(bases, receipt, MODULE.sha256(receipt), manifest)
            output = root / "cube.cnf"
            output.write_bytes(b"preserve cube\n")
            with self.assertRaisesRegex(FileExistsError, "refusing to replace"):
                MODULE.materialize(manifest, "h3_b1.cube-0-0", output)
            self.assertEqual(output.read_bytes(), b"preserve cube\n")
            self.assertEqual(list(root.glob(".cube.cnf.*.tmp")), [])

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

    def test_freight_receipt_is_canonical_and_binds_actual_bases(self) -> None:
        with tempfile.TemporaryDirectory() as temporary_name:
            bases = Path(temporary_name)
            for filename in MODULE.DEFAULT_FILENAMES.values():
                (bases / filename).write_text("p cnf 300 1\n1 0\n")
            receipt_path = self.freight_receipt(bases)
            with self.assertRaisesRegex(ValueError, "external pin"):
                MODULE.load_freight_receipt(bases, receipt_path, "0" * 64)
            receipt = json.loads(receipt_path.read_text())
            receipt["cells"][0]["sha256"] = "f" * 64
            receipt_path.write_bytes(MODULE.canonical_json(receipt))
            with self.assertRaisesRegex(ValueError, "does not bind actual base"):
                MODULE.load_freight_receipt(
                    bases, receipt_path, MODULE.sha256(receipt_path))
            receipt["cells"][0]["sha256"] = MODULE.sha256(
                bases / MODULE.DEFAULT_FILENAMES["h3_b1"])
            receipt_path.write_text(json.dumps(receipt, indent=2) + "\n")
            with self.assertRaisesRegex(ValueError, "not canonical"):
                MODULE.load_freight_receipt(
                    bases, receipt_path, MODULE.sha256(receipt_path))
            original = self.freight_receipt(bases).read_bytes()
            for key, value, message in (
                ("emitter_source", "proofs/Proofs/Wrong.lean", "wrong emitter source"),
                ("emitter_sha256", "f" * 64, "differs from commit bytes"),
                ("git_commit", "0" * 40, "commit/source is unavailable"),
            ):
                with self.subTest(key=key):
                    mutated = json.loads(original)
                    mutated[key] = value
                    receipt_path.write_bytes(MODULE.canonical_json(mutated))
                    with self.assertRaisesRegex(ValueError, message):
                        MODULE.load_freight_receipt(
                            bases, receipt_path, MODULE.sha256(receipt_path))

    def test_rejects_unknown_and_duplicated_job_ids(self) -> None:
        with tempfile.TemporaryDirectory() as temporary_name:
            root = Path(temporary_name)
            bases = root / "bases"
            bases.mkdir()
            for filename in MODULE.DEFAULT_FILENAMES.values():
                (bases / filename).write_text("p cnf 300 1\n1 0\n")
            manifest_path = root / "manifest.json"
            receipt = self.freight_receipt(bases)
            MODULE.write_manifest(bases, receipt, MODULE.sha256(receipt), manifest_path)
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
            receipt = self.freight_receipt(bases)
            MODULE.write_manifest(bases, receipt, MODULE.sha256(receipt), manifest_path)
            output = root / "out.cnf"
            output.write_text("preserve me\n")
            (bases / "h3_b1.cnf").write_text(
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
            receipt = self.freight_receipt(bases)
            MODULE.write_manifest(bases, receipt, MODULE.sha256(receipt), manifest_path)
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
