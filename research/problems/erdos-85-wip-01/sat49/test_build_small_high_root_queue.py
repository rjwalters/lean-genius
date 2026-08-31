#!/usr/bin/env python3

import hashlib
import importlib.util
import json
import tempfile
import unittest
from pathlib import Path
from unittest import mock


SOURCE = Path(__file__).with_name("build_small_high_root_queue.py")
SPEC = importlib.util.spec_from_file_location("build_small_high_root_queue", SOURCE)
MODULE = importlib.util.module_from_spec(SPEC)
assert SPEC.loader is not None
SPEC.loader.exec_module(MODULE)


def sample_manifest() -> dict:
    cells = {}
    for cell in MODULE.CELLS:
        left, right = MODULE.SELECTORS[cell]
        jobs = [
            {"id": f"{cell}.cover-left", "kind": "cover-left",
             "units": [-value for value in left]},
            {"id": f"{cell}.cover-right", "kind": "cover-right",
             "units": [-value for value in right]},
        ]
        for i, left_literal in enumerate(left):
            for j, right_literal in enumerate(right):
                jobs.append({"id": f"{cell}.cube-{i}-{j}", "kind": "cube",
                             "left_index": i, "right_index": j,
                             "units": [left_literal, right_literal]})
        cells[cell] = {"left": list(left), "right": list(right), "jobs": jobs}
    return {
        "schema": "erdos85-small-high-cube-jobs-v1",
        "lean_commit": MODULE.APPROVED_ROOT_COMMIT,
        "freight_receipt_sha256": MODULE.APPROVED_FREIGHT_RECEIPT_SHA256,
        "positive_cube_jobs": 392,
        "negative_cover_jobs": 14,
        "cells": cells,
    }


class RootQueueBuilderTest(unittest.TestCase):
    def write_manifest(self, root: Path, value: dict | None = None) -> Path:
        path = root / "manifest.json"
        path.write_text(json.dumps(value or sample_manifest()))
        return path

    def validate_with_actual_pin(self, path: Path):
        digest = hashlib.sha256(path.read_bytes()).hexdigest()
        with mock.patch.object(MODULE, "APPROVED_ROOT_MANIFEST_SHA256", digest):
            return MODULE.validate_root_manifest(path, digest)

    def test_exact_406_job_cover(self) -> None:
        with tempfile.TemporaryDirectory() as name:
            _, jobs = self.validate_with_actual_pin(
                self.write_manifest(Path(name)))
            self.assertEqual(len(jobs), 406)
            self.assertEqual(len(set(jobs)), 406)
            self.assertEqual(jobs[0], "h3_b1.cover-left")
            self.assertEqual(jobs[-1], "h5_t2.cube-6-7")

    def test_rejects_wrong_external_pin(self) -> None:
        with tempfile.TemporaryDirectory() as name:
            path = self.write_manifest(Path(name))
            with self.assertRaisesRegex(ValueError, "approved root manifest pin"):
                MODULE.validate_root_manifest(path, "0" * 64)

    def test_rejects_duplicate_or_missing_job(self) -> None:
        with tempfile.TemporaryDirectory() as name:
            root = Path(name)
            value = sample_manifest()
            value["cells"]["h5_t2"]["jobs"][-1] = dict(
                value["cells"]["h5_t2"]["jobs"][-2])
            with self.assertRaisesRegex(ValueError, "semantic job mapping|unique 406-job cover"):
                self.validate_with_actual_pin(self.write_manifest(root, value))

    def test_rejects_malformed_units(self) -> None:
        with tempfile.TemporaryDirectory() as name:
            root = Path(name)
            value = sample_manifest()
            value["cells"]["h3_b1"]["jobs"][0]["units"] = [1, 0]
            with self.assertRaisesRegex(ValueError, "semantic job mapping|malformed DIMACS unit"):
                self.validate_with_actual_pin(self.write_manifest(root, value))

    def test_rejects_wrong_selector_or_semantic_units(self) -> None:
        mutations = (
            lambda value: value["cells"]["h3_b1"]["left"].__setitem__(0, 999),
            lambda value: value["cells"]["h3_b1"]["jobs"][2]["units"].__setitem__(0, 999),
            lambda value: value["cells"]["h3_b1"]["jobs"][0]["units"].reverse(),
        )
        for mutate in mutations:
            with self.subTest(mutate=mutate), tempfile.TemporaryDirectory() as name:
                root = Path(name)
                value = sample_manifest()
                mutate(value)
                with self.assertRaisesRegex(ValueError, "selector mismatch|semantic job mapping"):
                    self.validate_with_actual_pin(self.write_manifest(root, value))

    def test_rejects_bool_as_dimacs_integer(self) -> None:
        with tempfile.TemporaryDirectory() as name:
            root = Path(name)
            value = sample_manifest()
            value["cells"]["h3_b1"]["jobs"][10]["left_index"] = True
            with self.assertRaisesRegex(ValueError, "malformed cube indices"):
                self.validate_with_actual_pin(self.write_manifest(root, value))

    def test_publish_is_create_only_and_cleans_staging(self) -> None:
        with tempfile.TemporaryDirectory() as name:
            root = Path(name)
            output = root / "queue"
            output.mkdir()
            (output / "sentinel").write_bytes(b"preserve")
            with mock.patch.object(MODULE, "require_clean_repo", return_value="a" * 40), \
                 mock.patch.object(MODULE, "require_clean_tracked_source",
                                   return_value=("a" * 40, "builder.py")), \
                 mock.patch.object(MODULE, "validate_root_manifest",
                                   return_value=({}, [f"job-{i}" for i in range(406)])):
                with self.assertRaisesRegex(FileExistsError, "refusing to replace"):
                    MODULE.build(root / "manifest", MODULE.APPROVED_ROOT_MANIFEST_SHA256,
                                 output, root, SOURCE)
            self.assertEqual((output / "sentinel").read_bytes(), b"preserve")
            self.assertEqual(list(root.glob(".queue.*")), [])

    def test_receipt_is_canonical_and_published_last(self) -> None:
        with tempfile.TemporaryDirectory() as name:
            root = Path(name)
            output = root / "queue"
            jobs = [f"job-{i}" for i in range(406)]
            with mock.patch.object(MODULE, "require_clean_repo", return_value="a" * 40), \
                 mock.patch.object(MODULE, "require_clean_tracked_source",
                                   return_value=("a" * 40, "builder.py")), \
                 mock.patch.object(MODULE, "validate_root_manifest",
                                   return_value=({}, jobs)):
                receipt = MODULE.build(root / "manifest",
                                       MODULE.APPROVED_ROOT_MANIFEST_SHA256,
                                       output, root, SOURCE)
            raw = (output / "receipt.json").read_bytes()
            self.assertEqual(raw, MODULE.canonical_json(json.loads(raw)))
            self.assertEqual(sorted(p.name for p in output.iterdir()),
                             ["jobs.txt", "receipt.json"])
            self.assertEqual((output / "jobs.txt").read_text().splitlines(), jobs)
            self.assertEqual(receipt["queue_sha256"],
                             MODULE.sha256_file(output / "jobs.txt"))


if __name__ == "__main__":
    unittest.main()
