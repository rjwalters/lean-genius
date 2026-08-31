#!/usr/bin/env python3

import hashlib
import importlib.util
import json
import os
import tempfile
import unittest
from pathlib import Path
from unittest import mock


SOURCE = Path(__file__).with_name("run_tierA_root_queue.py")
SPEC = importlib.util.spec_from_file_location("run_tierA_root_queue", SOURCE)
MODULE = importlib.util.module_from_spec(SPEC)
assert SPEC.loader is not None
SPEC.loader.exec_module(MODULE)


class RootControllerTest(unittest.TestCase):
    def test_lineage_marker_has_exact_shared_contract(self) -> None:
        marker = MODULE.lineage_marker("a" * 40, MODULE.CONTROLLER_REPO_PATH, "b" * 64)
        self.assertEqual(set(marker), {
            "schema", "work_root", "worker_sha256", "worker_receipt_sha256",
            "queue_receipt_sha256", "queue_sha256", "root_manifest_sha256",
            "freight_receipt_sha256", "controller_git_commit",
            "controller_source", "controller_sha256",
        })
        self.assertEqual(marker["controller_source"], MODULE.CONTROLLER_REPO_PATH)
        self.assertEqual(marker["queue_sha256"], MODULE.QUEUE_SHA256)

    def test_canonical_pin_loader_rejects_wrong_or_noncanonical(self) -> None:
        with tempfile.TemporaryDirectory() as name:
            path = Path(name) / "receipt.json"
            path.write_bytes(MODULE.canonical_json({"schema": "x"}))
            digest = MODULE.sha256_file(path)
            self.assertEqual(MODULE.load_canonical_pinned(path, digest, "test")["schema"], "x")
            with self.assertRaisesRegex(ValueError, "SHA mismatch"):
                MODULE.load_canonical_pinned(path, "0" * 64, "test")
            path.write_text(json.dumps({"schema": "x"}, indent=2) + "\n")
            digest = MODULE.sha256_file(path)
            with self.assertRaisesRegex(ValueError, "canonical"):
                MODULE.load_canonical_pinned(path, digest, "test")

    def test_worker_preflight_requires_exact_output_for_every_job(self) -> None:
        jobs = ["h3_b1.cover-left", "h5_t2.cube-6-7"]
        class Result:
            returncode = 0
            stdout = ""
        def fake_run(command, **kwargs):
            result = Result()
            result.stdout = (
                f"PREFLIGHT VERIFIED job={command[1]} mode=quick kind=root "
                f"manifest_sha256={MODULE.ROOT_MANIFEST_SHA256}\n")
            self.assertEqual(kwargs["env"]["TIERA_PREFLIGHT_ONLY"], "1")
            return result
        with mock.patch.object(MODULE.subprocess, "run", side_effect=fake_run):
            digest = MODULE.run_worker_preflights(Path("worker"), jobs, 2)
        expected = MODULE.sha256_bytes(MODULE.canonical_json([
            [job, (f"PREFLIGHT VERIFIED job={job} mode=quick kind=root "
                   f"manifest_sha256={MODULE.ROOT_MANIFEST_SHA256}\n")]
            for job in jobs
        ]))
        self.assertEqual(digest, expected)

    def test_worker_preflight_rejects_drift_and_parallelism(self) -> None:
        with self.assertRaisesRegex(ValueError, "parallelism"):
            MODULE.run_worker_preflights(Path("worker"), ["job"], 0)
        result = mock.Mock(returncode=0, stdout="unexpected\n")
        with mock.patch.object(MODULE.subprocess, "run", return_value=result):
            with self.assertRaisesRegex(ValueError, "preflight failed"):
                MODULE.run_worker_preflights(Path("worker"), ["job"], 1)

    def test_publish_is_create_only_and_cleans_temp(self) -> None:
        with tempfile.TemporaryDirectory() as name:
            root = Path(name)
            output = root / "receipt.json"
            output.write_bytes(b"preserve")
            with self.assertRaisesRegex(FileExistsError, "refusing to replace"):
                MODULE.publish_create_only(b"new", output)
            self.assertEqual(output.read_bytes(), b"preserve")
            self.assertEqual(list(root.glob(".receipt.json.*.tmp")), [])

    def test_preflight_rejects_outputs_in_protected_trees_before_subprocess(self) -> None:
        with tempfile.TemporaryDirectory() as name:
            campaign = Path(name) / "campaign"
            work_root = campaign / "fresh-root"
            legacy_root = campaign / "tierA"
            for output in (work_root, work_root / "receipt.json",
                           legacy_root / "h3_b1.cover-left" / "receipt.json"):
                with self.subTest(output=output), \
                     mock.patch.object(MODULE, "WORK_ROOT", work_root), \
                     mock.patch.object(MODULE, "require_clean_controller") as git_check:
                    with self.assertRaisesRegex(ValueError, "protected evidence tree"):
                        MODULE.preflight(
                            Path("queue-receipt"), Path("worker-receipt"),
                            Path("worker"), output, 1)
                    git_check.assert_not_called()
                    self.assertFalse(os.path.lexists(work_root))
                    self.assertFalse(os.path.lexists(legacy_root))

    def test_output_ancestry_resolves_symlinked_parent(self) -> None:
        with tempfile.TemporaryDirectory() as name:
            root = Path(name)
            protected = root / "protected"
            protected.mkdir()
            alias = root / "alias"
            alias.symlink_to(protected, target_is_directory=True)
            with self.assertRaisesRegex(ValueError, "protected evidence tree"):
                MODULE.reject_protected_output(
                    alias / "receipt.json", (protected,))

    def test_legacy_snapshot_detects_metadata_change(self) -> None:
        with tempfile.TemporaryDirectory() as name:
            root = Path(name)
            job = "h3_b1.cover-left"
            path = root / job
            path.mkdir(parents=True)
            artifact = path / "receipt.json"
            artifact.write_bytes(b"old")
            before, entries = MODULE.legacy_snapshot(root, [job])
            artifact.write_bytes(b"changed")
            after, entries_after = MODULE.legacy_snapshot(root, [job])
            self.assertEqual(entries, entries_after)
            self.assertNotEqual(before, after)


if __name__ == "__main__":
    unittest.main()
