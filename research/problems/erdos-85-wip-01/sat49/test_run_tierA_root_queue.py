#!/usr/bin/env python3

import hashlib
import importlib.util
import json
import os
import tempfile
import unittest
from datetime import datetime, timedelta, timezone
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

    def test_h7_state_requires_inactive_preserved_canonical_state(self) -> None:
        with tempfile.TemporaryDirectory() as name:
            path = Path(name) / "h7.json"
            state = {
                "schema": MODULE.H7_STATE_SCHEMA,
                "captured_at": "2099-01-01T00:00:00Z",
                "active": False,
                "preservation_complete": True,
                "free_bytes": MODULE.FREE_FLOOR_BYTES + 10**9,
                "guard_floor_bytes": 105 * 1024**3,
                "artifact_receipt_sha256": "a" * 64,
            }
            path.write_bytes(MODULE.canonical_json(state))
            digest = MODULE.sha256_file(path)
            self.assertFalse(MODULE.validate_h7_state(path, digest)["active"])
            state["active"] = True
            path.write_bytes(MODULE.canonical_json(state))
            digest = MODULE.sha256_file(path)
            with self.assertRaisesRegex(ValueError, "active"):
                MODULE.validate_h7_state(path, digest)

    def test_operator_authorization_is_exact_pinned_and_unexpired(self) -> None:
        with tempfile.TemporaryDirectory() as name:
            path = Path(name) / "authorization.json"
            prepared_sha = "c" * 64
            prepared = {"h7_state_sha256": "d" * 64, "parallelism": 1}
            authorization = {
                "schema": MODULE.AUTHORIZATION_SCHEMA,
                "authorized": True,
                "authorized_by": "operator",
                "authorization_id": "reviewed-test",
                "prepared_receipt_sha256": prepared_sha,
                "h7_state_sha256": prepared["h7_state_sha256"],
                "work_root": str(MODULE.WORK_ROOT),
                "mode": "quick",
                "cap_seconds": MODULE.CAP_SECONDS,
                "parallelism": 1,
                "free_floor_bytes": MODULE.FREE_FLOOR_BYTES,
                "expires_at": (datetime.now(timezone.utc) + timedelta(hours=1)
                               ).strftime("%Y-%m-%dT%H:%M:%SZ"),
            }
            path.write_bytes(MODULE.canonical_json(authorization))
            digest = MODULE.sha256_file(path)
            with self.assertRaisesRegex(ValueError, "not enabled"):
                MODULE.validate_authorization(path, digest, prepared_sha, prepared)
            with mock.patch.object(
                    MODULE, "APPROVED_OPERATOR_AUTHORIZATION_SHA256", digest):
                MODULE.validate_authorization(path, digest, prepared_sha, prepared)
                authorization["authorized_by"] = "agent"
                path.write_bytes(MODULE.canonical_json(authorization))
                wrong_digest = MODULE.sha256_file(path)
                with self.assertRaisesRegex(ValueError, "approved immutable hash"):
                    MODULE.validate_authorization(
                        path, wrong_digest, prepared_sha, prepared)

    def test_namespace_reservation_is_create_only_and_resume_exact(self) -> None:
        with tempfile.TemporaryDirectory() as name:
            work_root = Path(name) / "fresh"
            marker = {"schema": "test", "value": "bound"}
            with mock.patch.object(MODULE, "WORK_ROOT", work_root):
                MODULE.reserve_or_validate_namespace(marker, False)
                self.assertEqual((work_root / "lineage.json").read_bytes(),
                                 MODULE.canonical_json(marker))
                MODULE.reserve_or_validate_namespace(marker, True)
                with self.assertRaisesRegex(ValueError, "initial launch"):
                    MODULE.reserve_or_validate_namespace(marker, False)
                (work_root / "lineage.json").write_bytes(b"wrong\n")
                with self.assertRaisesRegex(ValueError, "exact existing"):
                    MODULE.reserve_or_validate_namespace(marker, True)

    def test_floor_stops_before_scheduling_any_job(self) -> None:
        usage = mock.Mock(free=MODULE.FREE_FLOOR_BYTES)
        with tempfile.TemporaryDirectory() as name, \
             mock.patch.object(MODULE, "WORK_ROOT", Path(name) / "fresh"), \
             mock.patch.object(MODULE.shutil, "disk_usage", return_value=usage), \
             mock.patch.object(MODULE.subprocess, "run") as run:
            self.assertEqual(MODULE.launch_jobs(Path("worker"), ["job"], 1),
                             (0, 0, True))
            run.assert_not_called()

    def test_floor_reserves_budget_for_every_running_job(self) -> None:
        usage = mock.Mock(
            free=MODULE.FREE_FLOOR_BYTES + 2 * MODULE.PER_JOB_BUDGET_BYTES)
        result = mock.Mock(returncode=0)
        with tempfile.TemporaryDirectory() as name, \
             mock.patch.object(MODULE, "WORK_ROOT", Path(name) / "fresh"), \
             mock.patch.object(MODULE.shutil, "disk_usage", return_value=usage), \
             mock.patch.object(MODULE.subprocess, "run", return_value=result) as run:
            completed, failures, stopped = MODULE.launch_jobs(
                Path("worker"), [f"job-{i}" for i in range(4)], 4)
            self.assertEqual((completed, failures, stopped), (2, 0, True))
            self.assertEqual(run.call_count, 2)


if __name__ == "__main__":
    unittest.main()
