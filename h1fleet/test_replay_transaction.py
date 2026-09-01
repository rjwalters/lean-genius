#!/usr/bin/env python3
"""Local end-to-end and fail-closed tests for the replay transaction."""

from __future__ import annotations

import gzip
import json
import subprocess
import sys
import tempfile
import time
import unittest
from dataclasses import replace
from types import SimpleNamespace
from unittest.mock import patch
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))

from replay_common import (
    AwsCliObjectStore, LocalObjectStore, NATIVE_AXIOM_PATTERN, ObjectInfo,
    PRODUCTION_COMPILE_COMMAND, PRODUCTION_ENVIRONMENT_ALLOWLIST,
    RECEIPT_INTEGRITY_SCHEME, ReplayError, SCHEMA, canonical_json, load_manifest,
    run_command, seal_receipt_integrity, sha256_bytes, sha256_file,
    validate_command_receipts, validate_receipt_integrity,
)
from audit_replay_leaf import parse_axioms
from build_replay_manifest import (
    generator_identity_fields, publish_validated_manifest,
    validate_queue_build_receipt,
)
import build_replay_manifest as manifest_builder
from capacity_queue import (
    CAPACITY_PROFILE_COUNTS, load_capacity_index, table_serialization_tag,
    validate_queue_capacity, validate_queue_tables,
)
from replay_worker import (
    command_values, validate_compact_lrat, validate_existing_receipt, validate_job,
    validate_production_compile_contract,
    validate_production_environment,
    validate_production_manifest,
)
import replay_worker as replay_worker_module
from run_replay_queue import acquire_single_writer_lock, load_queue
import validate_replay_receipt as replay_receipt_validator
from validate_replay_receipt import validate_production_backend_binding


WORKER = HERE / "replay_worker.py"
VALIDATOR = HERE / "validate_replay_receipt.py"
DISPATCHER = HERE / "run_replay_queue.py"
MANIFEST_BUILDER = HERE / "build_replay_manifest.py"
ZERO_SHA = "0" * 64


HELPER = r'''#!/usr/bin/env python3
import json, shutil, sys
from pathlib import Path

mode = sys.argv[1]
if mode == "generate":
    Path(sys.argv[2]).write_text("theorem checked : True := by trivial\n")
elif mode == "compile":
    Path(sys.argv[2]).write_bytes(b"OLEAN-V1")
elif mode == "audit":
    axioms = ["evil.axiom"] if Path("emit-evil").exists() else ["propext", "Classical.choice", "Quot.sound"]
    Path(sys.argv[2]).write_text(json.dumps({
        "schema":"erdos85-h1-replay-axiom-audit-v1", "sorry_ax":False,
        "source_scan":"PASS", "axioms":axioms}, sort_keys=True))
elif mode == "zstd":
    shutil.copyfile(sys.argv[2], sys.argv[3])
else:
    raise SystemExit(9)
'''


class ReplayTransactionTest(unittest.TestCase):
    def setUp(self) -> None:
        self.temporary = tempfile.TemporaryDirectory()
        self.root = Path(self.temporary.name).resolve()
        self.store_root = self.root / "store"
        self.store = LocalObjectStore(self.store_root)
        self.state = self.root / "state"
        self.helper = self.root / "helper.py"
        self.helper.write_text(HELPER)
        self.tag = "0123456789abcdef"
        compact = b"1 1 0 0\n2 0 1 0\n"
        compressed = gzip.compress(compact, mtime=0)
        self.certificate_key = f"sat49/campaign-20260825/h1/{self.tag}.compact.lrat.gz"
        certificate = self.root / "certificate.gz"
        certificate.write_bytes(compressed)
        self.store.put_immutable(
            self.certificate_key, certificate,
            {"cnf-sha256": "2" * 64, "tag": self.tag,
             "simulate-head-without-sha256": "true"},
        )
        self.job = self.root / "job.json"
        table_serialization = "test-table-row-v1"
        self.job.write_bytes(canonical_json({
            "tag": self.tag, "profile": 0, "local_index": 3,
            "certificate_key": self.certificate_key,
            "certificate_gzip_sha256": sha256_bytes(compressed),
            "compact_lrat_sha256": sha256_bytes(compact),
            "cnf_sha256": "2" * 64,
            "table_serialization": table_serialization,
            "table_sha256": sha256_bytes(table_serialization.encode()),
        }))
        self.queue = self.root / "queue.jsonl"
        self.queue.write_bytes(self.job.read_bytes())
        self.capacity_index = self.root / "capacity-index.tsv"
        self.capacity_index.write_text(
            "orbit\tprofile\tlocalIndex\n"
            f"{self.tag}\tBBBB\t3\n"
        )
        self.capacity_reindex_receipt = self.root / "capacity-reindex-receipt.json"
        self.capacity_reindex_receipt.write_bytes(canonical_json({
            "schema": "erdos85-h1-v2-capacity-reindex-v1",
            "inventory_sha256": ZERO_SHA,
            "output_sha256": sha256_file(self.capacity_index),
            "emitted_rows": 1,
            "dropped_outside_capacity_tags": [],
            "require_complete": False,
        }))
        self.queue_build_receipt = self.root / "queue-build-receipt.json"
        self.terminal_index = self.root / "terminal-index.tsv"
        self.terminal_index.write_text("reviewed terminal index fixture\n")
        terminal_index_sha = sha256_file(self.terminal_index)
        self.queue_build_receipt.write_bytes(canonical_json({
            "schema": "erdos85-h1-replay-queue-build-v1",
            "inventory_sha256": ZERO_SHA,
            "certificate_index_sha256": sha256_file(self.capacity_index),
            "terminal_index_sha256": terminal_index_sha,
            "output_sha256": sha256_file(self.queue),
            "emitted_jobs": 1,
            "require_complete": False,
        }))
        self.manifest = self.root / "manifest.json"
        self.manifest.write_bytes(canonical_json({
            "schema": SCHEMA,
            "campaign_prefix": "sat49/campaign-20260825/h1-replay/",
            "repository_commit": "test-commit", "inventory_sha256": ZERO_SHA,
            "coverage_sha256": "1" * 64, "toolchain_identity": "lean-test",
            "overlay_builder_sha256": "2" * 64,
            "overlay_project_manifest_sha256": "3" * 64,
            "overlay_build_receipt_sha256": "4" * 64,
            "overlay_manifest_sha256": "5" * 64,
            "overlay_identity_sha256": "6" * 64,
            "overlay_archive_sha256": "7" * 64,
            "generator_sha256": "3" * 64,
            "template_sha256": "4" * 64, "cnf_emitter_sha256": "d" * 64,
            "worker_sha256": sha256_file(WORKER),
            "validator_sha256": "6" * 64, "zstd_identity": "copy-test",
            "receipt_schema_sha256": "8" * 64,
            "aggregate_generator_sha256": "9" * 64,
            "stub_generator_sha256": "e" * 64,
            "capacity_exporter_sha256": "f" * 64,
            "capacity_reindexer_sha256": "0" * 64,
            "capacity_queue_validator_sha256": "1" * 64,
            "queue_builder_sha256": "4" * 64,
            "queue_build_receipt_sha256": "5" * 64,
            "terminal_index_sha256": terminal_index_sha,
            "capacity_index_sha256": "2" * 64,
            "capacity_reindex_receipt_sha256": "3" * 64,
            "axiom_auditor_sha256": "a" * 64, "common_sha256": "b" * 64,
            "dispatcher_sha256": "c" * 64,
            "aws_cli_identity": "local-backend-not-used",
            "worker_image_digest": "test-image@sha256:" + "7" * 64,
            "worker_ami_id": "local-test-ami",
            "worker_instance_type": "local-test", "ebs_shape": "local-test",
            "instance_role": "local-test", "s3_bucket": "local-test",
            "aws_region": "local-test",
            "receipt_integrity_scheme": RECEIPT_INTEGRITY_SCHEME,
            "single_writer_lock_path": str((self.root / "single-writer.lock").resolve()),
            "queue_sha256": sha256_file(self.queue), "expected_jobs": 1,
            "max_parallelism": 1, "single_dispatcher": True,
            "complete_capacity_queue": False,
            "allowed_axioms": ["propext", "Classical.choice", "Quot.sound"],
            "commands": {
                "generate": [sys.executable, str(self.helper), "generate", "{source}"],
                "compile": [sys.executable, str(self.helper), "compile", "{olean}"],
                "axiom_audit": [sys.executable, str(self.helper), "audit", "{audit_json}"],
                "zstd": [sys.executable, str(self.helper), "zstd", "{input}", "{output}"],
            },
        }))
        self.overlay_project_manifest = self.root / "project-overlay.sha256.tsv"
        self.overlay_project_manifest.write_text("1" * 64 + "\tFoo.olean\n")
        overlay_entries = [{"bytes": 5, "path": "Foo.olean", "sha256": "1" * 64}]
        overlay_identity = sha256_bytes(canonical_json(overlay_entries))
        self.overlay_manifest = self.root / "overlay-manifest.json"
        self.overlay_manifest.write_bytes(canonical_json({
            "entry_count": 1, "entries": overlay_entries,
            "identity_sha256": overlay_identity,
            "included_extensions": [".ir", ".olean", ".olean.private", ".olean.server"],
            "schema": manifest_builder.OVERLAY_SCHEMA,
        }))
        self.overlay_archive = self.root / "complete-overlay.tar.zst"
        self.overlay_archive.write_bytes(b"archive-fixture")
        self.overlay_receipt = self.root / "overlay-receipt.json"
        source_commit = subprocess.run(
            ["git", "rev-parse", "HEAD"], cwd=HERE.parent, text=True,
            capture_output=True, check=True,
        ).stdout.strip()
        self.overlay_receipt.write_bytes(canonical_json({
            "control_files": [
                {"blob_oid": str(index) * 40, "bytes": 1, "path": path,
                 "sha256": str(index) * 64}
                for index, path in enumerate((
                    "proofs/lean-toolchain", "proofs/lakefile.toml",
                    "proofs/lake-manifest.json"), 1)
            ],
            "entry_count": 1,
            "git_path": "/usr/bin/git", "git_sha256": "8" * 64,
            "manifest_path": "manifest.json",
            "manifest_sha256": sha256_file(self.overlay_manifest),
            "overlay_identity_sha256": overlay_identity,
            "packages": [{
                "build_root": "/tmp/pkg/.lake/build/lib/lean",
                "facade": "/tmp/repo/proofs/.lake/packages/pkg",
                "head": "9" * 40, "manifest_url": "https://github.com/x/pkg",
                "name": "pkg", "normalized_remote": "github.com/x/pkg",
                "rev": "9" * 40,
            }],
            "producer_path": str(HERE / "build_replay_overlay.py"),
            "producer_sha256": sha256_file(HERE / "build_replay_overlay.py"),
            "project_manifest_path": str(self.overlay_project_manifest),
            "project_manifest_sha256": sha256_file(self.overlay_project_manifest),
            "project_root": "/tmp/project", "repo": "/tmp/repo",
            "schema": manifest_builder.OVERLAY_RECEIPT_SCHEMA,
            "source_commit": source_commit,
        }))

    def test_compact_lrat_accepts_deletion_lines(self) -> None:
        certificate = self.root / "with-deletions.compact.lrat"
        certificate.write_text(
            "610405 -184 -201 -501 0 1 4568 0\n"
            "610405 d 4568 0\n"
            "610406 0 610405 0\n"
        )
        validate_compact_lrat(certificate)

    def test_compact_lrat_rejects_malformed_deletion_lines(self) -> None:
        for index, contents in enumerate((
            "1 d\n2 0 1 0\n",
            "1 d not-an-id 0\n2 0 1 0\n",
            "1 d 7\n2 0 1 0\n",
        )):
            certificate = self.root / f"bad-deletion-{index}.compact.lrat"
            certificate.write_text(contents)
            with self.subTest(contents=contents), self.assertRaises(ReplayError):
                validate_compact_lrat(certificate)

    def tearDown(self) -> None:
        self.temporary.cleanup()

    def test_command_values_use_unique_canonical_compact_basename(self) -> None:
        first = command_values(self.state / "first", {
            "tag": self.tag, "profile": 0, "local_index": 3,
        })
        second = command_values(self.state / "second", {
            "tag": "fedcba9876543210", "profile": 0, "local_index": 4,
        })
        self.assertEqual(
            Path(first["compact_lrat"]).name,
            "Erdos85H1V2CertP0I00003.compact.lrat",
        )
        self.assertEqual(
            Path(second["compact_lrat"]).name,
            "Erdos85H1V2CertP0I00004.compact.lrat",
        )
        self.assertNotEqual(
            Path(first["compact_lrat"]).name,
            Path(second["compact_lrat"]).name,
        )

    def test_production_compile_contract_is_direct_offline_lean(self) -> None:
        compile_command = [
            "/usr/bin/docker", "run", "--rm", "--network", "none",
            "--mount", "type=bind,src=/opt/replay/repo,dst=/opt/replay/repo,readonly",
            "--mount", "type=bind,src=/opt/replay/state,dst=/opt/replay/state",
            "--mount", "type=bind,src=/opt/replay/overlay,dst=/opt/replay/overlay,readonly",
            "--env", "LEAN_PATH=/opt/replay/overlay", "lean4-arm64:v4.31.0",
            "/root/.elan/bin/lean", "-R", "{work}", "-o", "{olean}", "{source}",
        ]
        manifest = {
            "commands": {"compile": compile_command},
            "environment_allowlist": ["HOME", "LEAN_PATH"],
        }
        validate_production_compile_contract(manifest)
        mutations = []
        for extra in ("--network", "host", "--env", "LEAN_PATH=evil", "--entrypoint", "/bin/sh"):
            mutations.append({"commands": {"compile": compile_command + [extra]},
                              "environment_allowlist": ["HOME", "LEAN_PATH"]})
        mutations.extend((
            {"commands": {"compile": ["/root/.elan/bin/lake" if value == "/root/.elan/bin/lean"
                                        else value for value in compile_command]},
             "environment_allowlist": ["HOME", "LEAN_PATH"]},
            {"commands": {"compile": compile_command}, "environment_allowlist": ["HOME"]},
            {"commands": {"compile": ["LEAN_PATH=evil" if value.startswith("LEAN_PATH=") else value
                                        for value in compile_command]},
             "environment_allowlist": ["HOME", "LEAN_PATH"]},
        ))
        for mutation in mutations:
            with self.subTest(mutation=mutation), self.assertRaises(ReplayError):
                validate_production_compile_contract(mutation)
        with patch.dict(__import__("os").environ, {"LEAN_PATH": "/opt/replay/overlay"}):
            validate_production_environment()
        with patch.dict(__import__("os").environ, {"LEAN_PATH": "poison"}):
            with self.assertRaisesRegex(ReplayError, "frozen overlay root"):
                validate_production_environment()

    def worker(self) -> subprocess.CompletedProcess[str]:
        return subprocess.run([
            sys.executable, str(WORKER), "--manifest", str(self.manifest),
            "--job", str(self.job), "--tag", self.tag,
            "--state-dir", str(self.state), "--object-store-root", str(self.store_root),
        ], text=True, capture_output=True, check=False)

    def receipt_path(self) -> Path:
        return self.store.objects / (
            f"sat49/campaign-20260825/h1-replay/receipts/{self.tag}.json"
        )

    def validate_receipt(self) -> subprocess.CompletedProcess[str]:
        return subprocess.run([
            sys.executable, str(VALIDATOR), "--manifest", str(self.manifest),
            "--receipt", str(self.receipt_path()),
            "--object-store-root", str(self.store_root),
        ], text=True, capture_output=True, check=False)

    def validator_args(self, receipt: Path | None = None) -> SimpleNamespace:
        return SimpleNamespace(
            manifest=self.manifest, receipt=receipt or self.receipt_path(),
            object_store_root=self.store_root, s3_bucket=None, aws="aws",
        )

    def remove_object(self, key: str) -> None:
        (self.store.objects / key).unlink(missing_ok=True)
        (self.store.meta / f"{key}.json").unlink(missing_ok=True)

    def set_certificate_tags(self, tags: dict[str, str]) -> None:
        meta_path = self.store.meta / f"{self.certificate_key}.json"
        meta = json.loads(meta_path.read_text())
        meta["tags"] = tags
        meta.pop("tagging_request_id", None)
        meta_path.write_bytes(canonical_json(meta))

    def rewrite_store_json(self, key: str, value: dict) -> bytes:
        encoded = canonical_json(value)
        object_path = self.store.objects / key
        meta_path = self.store.meta / f"{key}.json"
        object_path.write_bytes(encoded)
        meta = json.loads(meta_path.read_text())
        digest = sha256_bytes(encoded)
        meta.update(size=len(encoded), sha256=digest, etag=digest)
        meta_path.write_bytes(canonical_json(meta))
        return encoded

    def rewrite_receipt_and_rebind_ledger(
        self, receipt: dict, *, reseal: bool = True,
    ) -> tuple[bytes, bytes]:
        prefix = "sat49/campaign-20260825/h1-replay/"
        receipt_key = f"{prefix}receipts/{self.tag}.json"
        if reseal:
            seal_receipt_integrity(receipt)
        receipt_bytes = self.rewrite_store_json(receipt_key, receipt)
        ledger_key = f"{prefix}ledger/{self.tag}.accepted"
        ledger = json.loads((self.store.objects / ledger_key).read_text())
        ledger["receipt_sha256"] = sha256_bytes(receipt_bytes)
        ledger_bytes = self.rewrite_store_json(ledger_key, ledger)
        return receipt_bytes, ledger_bytes

    def test_success_resume_and_independent_validation(self) -> None:
        first = self.worker()
        self.assertEqual(first.returncode, 0, first.stderr)
        self.assertIn("ACCEPTED", first.stdout)
        certificate = self.store.head(self.certificate_key)
        self.assertEqual(certificate.tags.get("replay"), "consumed")
        receipt = self.receipt_path()
        self.assertTrue(receipt.is_file())
        check = subprocess.run([
            sys.executable, str(VALIDATOR), "--manifest", str(self.manifest),
            "--receipt", str(receipt), "--object-store-root", str(self.store_root),
        ], text=True, capture_output=True, check=False)
        self.assertEqual(check.returncode, 0, check.stderr)
        self.assertEqual(check.stdout.strip(), "VALID")
        receipt_sha = sha256_file(receipt)
        second = self.worker()
        self.assertEqual(second.returncode, 0, second.stderr)
        self.assertIn("ALREADY_ACCEPTED", second.stdout)
        self.assertEqual(sha256_file(receipt), receipt_sha)

    def test_validator_gets_live_receipt_ready_and_all_artifacts(self) -> None:
        self.assertEqual(self.worker().returncode, 0)
        downloads: list[str] = []
        base = self.store

        class RecordingStore:
            def download(self, key, destination):
                downloads.append(key)
                return base.download(key, destination)

            def head(self, key):
                return base.head(key)

        with patch.object(
            replay_receipt_validator, "LocalObjectStore",
            return_value=RecordingStore(),
        ):
            replay_receipt_validator.validate(self.validator_args())
        prefix = "sat49/campaign-20260825/h1-replay/"
        self.assertTrue({
            f"{prefix}receipts/{self.tag}.json",
            f"{prefix}replay-ready/{self.tag}.json",
            f"{prefix}sources/{self.tag}.lean.zst",
            f"{prefix}logs/{self.tag}.log.zst",
            f"{prefix}oleans/{self.tag}.olean.zst",
            f"{prefix}ledger/{self.tag}.accepted",
        } <= set(downloads))

    def test_validator_rehashes_artifact_bytes_despite_forged_head(self) -> None:
        self.assertEqual(self.worker().returncode, 0)
        prefix = "sat49/campaign-20260825/h1-replay/"
        target = f"{prefix}sources/{self.tag}.lean.zst"
        base = self.store

        class ForgedArtifactStore:
            def download(self, key, destination):
                if key == target:
                    info = base.head(key)
                    destination.write_bytes(b"forged bytes behind matching HEAD metadata")
                    return info
                return base.download(key, destination)

            def head(self, key):
                return base.head(key)

        with patch.object(
            replay_receipt_validator, "LocalObjectStore",
            return_value=ForgedArtifactStore(),
        ), self.assertRaisesRegex(ReplayError, "downloaded source bytes differ"):
            replay_receipt_validator.validate(self.validator_args())

    def test_validator_rejects_supplied_live_receipt_byte_divergence(self) -> None:
        self.assertEqual(self.worker().returncode, 0)
        supplied = self.root / "divergent-receipt.json"
        supplied.write_bytes(self.receipt_path().read_bytes() + b"\n")
        with self.assertRaisesRegex(ReplayError, "supplied receipt bytes differ"):
            replay_receipt_validator.validate(self.validator_args(supplied))

    def test_ledger_binds_downloaded_receipt_not_forged_head_sha(self) -> None:
        self.assertEqual(self.worker().returncode, 0)
        prefix = "sat49/campaign-20260825/h1-replay/"
        receipt_key = f"{prefix}receipts/{self.tag}.json"
        ledger_key = f"{prefix}ledger/{self.tag}.accepted"
        forged_sha = "f" * 64
        ledger_path = self.store.objects / ledger_key
        ledger = json.loads(ledger_path.read_text())
        ledger["receipt_sha256"] = forged_sha
        ledger_bytes = canonical_json(ledger)
        ledger_path.write_bytes(ledger_bytes)
        ledger_meta_path = self.store.meta / f"{ledger_key}.json"
        ledger_meta = json.loads(ledger_meta_path.read_text())
        ledger_digest = sha256_bytes(ledger_bytes)
        ledger_meta.update(size=len(ledger_bytes), sha256=ledger_digest, etag=ledger_digest)
        ledger_meta_path.write_bytes(canonical_json(ledger_meta))
        base = self.store

        class ForgedHeadStore:
            def download(self, key, destination):
                return base.download(key, destination)

            def head(self, key):
                info = base.head(key)
                return replace(info, sha256=forged_sha) if key == receipt_key else info

        with patch.object(
            replay_receipt_validator, "LocalObjectStore",
            return_value=ForgedHeadStore(),
        ), self.assertRaisesRegex(ReplayError, "terminal ledger"):
            replay_receipt_validator.validate(self.validator_args())

    def test_undisclosed_axiom_never_tags_or_accepts(self) -> None:
        work = self.state / "work" / self.tag
        work.mkdir(parents=True)
        (work / "emit-evil").write_text("1")
        result = self.worker()
        self.assertEqual(result.returncode, 2)
        self.assertIn("undisclosed axioms", result.stderr)
        self.assertNotIn("replay", self.store.head(self.certificate_key).tags)
        self.assertFalse(self.receipt_path().exists())

    def test_every_pre_tag_publication_boundary_leaves_certificate_unconsumed(self) -> None:
        manifest = load_manifest(self.manifest)
        manifest["manifest_sha256"] = sha256_file(self.manifest)
        job = validate_job(json.loads(self.job.read_text()), self.tag)
        job["job_sha256"] = sha256_file(self.job)
        worker_runtime = {
            "instance_id": "local-test", "availability_zone": "local-test",
            "region": "local-test", "instance_type": manifest["worker_instance_type"],
            "ami_id": manifest["worker_ami_id"],
            "container_image_digest": manifest["worker_image_digest"],
            "container_image_digest_source": "local-test-backend",
            "identity_source": "local-test-backend",
        }
        boundaries = ("/sources/", "/logs/", "/oleans/", "/replay-ready/")
        for boundary in boundaries:
            class FailingStore(LocalObjectStore):
                def put_immutable(self, key, source, metadata):
                    if boundary in f"/{key}":
                        raise ReplayError(f"injected boundary failure {boundary}")
                    return super().put_immutable(key, source, metadata)

                def put_bytes_immutable(self, key, value, metadata):
                    if boundary in f"/{key}":
                        raise ReplayError(f"injected boundary failure {boundary}")
                    return super().put_bytes_immutable(key, value, metadata)

            isolated_root = self.root / f"boundary-{boundary.strip('/')}"
            isolated = FailingStore(isolated_root)
            certificate = self.root / f"certificate-{boundary.strip('/')}"
            certificate.write_bytes((self.store.objects / self.certificate_key).read_bytes())
            isolated.put_immutable(
                self.certificate_key, certificate,
                {"cnf-sha256": "2" * 64, "tag": self.tag,
                 "simulate-head-without-sha256": "true"},
            )
            with self.subTest(boundary=boundary), self.assertRaisesRegex(
                ReplayError, "injected boundary failure"
            ):
                work = self.root / f"work-{boundary.strip('/')}"
                work.mkdir()
                replay_worker_module.compile_ready(
                    isolated, manifest, job, work, worker_runtime,
                )
            self.assertNotIn("replay", isolated.head(self.certificate_key).tags)

    def test_corrupt_certificate_is_rejected_before_generation(self) -> None:
        job = json.loads(self.job.read_text())
        job["certificate_gzip_sha256"] = "f" * 64
        self.job.write_bytes(canonical_json(job))
        result = self.worker()
        self.assertEqual(result.returncode, 2)
        self.assertIn("certificate gzip SHA-256 mismatch", result.stderr)
        self.assertFalse((self.state / "work" / self.tag / "module.lean").exists())
        self.assertNotIn("replay", self.store.head(self.certificate_key).tags)

    def test_dispatcher_enforces_manifest_and_runs_queue(self) -> None:
        result = subprocess.run([
            sys.executable, str(DISPATCHER), "--manifest", str(self.manifest),
            "--queue", str(self.queue), "--state-dir", str(self.state),
            "--parallelism", "1", "--execute", "YES",
            "--object-store-root", str(self.store_root),
        ], text=True, capture_output=True, check=False)
        self.assertEqual(result.returncode, 0, result.stderr)
        end = json.loads((self.state / "dispatch" / "END.json").read_text())
        self.assertEqual((end["accepted"], end["failed"]), (1, 0))
        self.assertTrue(self.receipt_path().is_file())

    def test_malformed_queue_row_is_rejected_before_start_or_freeze(self) -> None:
        malformed = json.loads(self.queue.read_text())
        del malformed["cnf_sha256"]
        self.queue.write_bytes(canonical_json(malformed))
        manifest = json.loads(self.manifest.read_text())
        manifest["queue_sha256"] = sha256_file(self.queue)
        self.manifest.write_bytes(canonical_json(manifest))

        dispatched = subprocess.run([
            sys.executable, str(DISPATCHER), "--manifest", str(self.manifest),
            "--queue", str(self.queue), "--state-dir", str(self.state),
            "--parallelism", "1", "--execute", "YES",
            "--object-store-root", str(self.store_root),
        ], text=True, capture_output=True, check=False)
        self.assertEqual(dispatched.returncode, 2)
        self.assertIn("missing=['cnf_sha256']", dispatched.stderr)
        self.assertFalse((self.state / "dispatch" / "START.json").exists())

        frozen = self.root / "must-not-freeze.json"
        freeze = subprocess.run([
            sys.executable, str(MANIFEST_BUILDER), "--draft", str(self.manifest),
            "--queue", str(self.queue), "--repo", str(HERE.parent),
            "--output", str(frozen),
            "--capacity-index", str(self.capacity_index),
            "--capacity-reindex-receipt", str(self.capacity_reindex_receipt),
            "--queue-build-receipt", str(self.queue_build_receipt),
            "--terminal-index", str(self.terminal_index),
            "--overlay-build-receipt", str(self.overlay_receipt),
            "--overlay-manifest", str(self.overlay_manifest),
            "--overlay-archive", str(self.overlay_archive),
            "--overlay-project-manifest", str(self.overlay_project_manifest),
        ], text=True, capture_output=True, check=False)
        self.assertEqual(freeze.returncode, 2, freeze.stderr)
        self.assertIn("missing=['cnf_sha256']", freeze.stderr)
        self.assertFalse(frozen.exists())

    def test_queue_rejects_boolean_indices_and_duplicate_slots(self) -> None:
        job = json.loads(self.job.read_text())
        for field in ("profile", "local_index"):
            malformed = dict(job)
            malformed[field] = True
            with self.subTest(field=field), self.assertRaises(ReplayError):
                validate_job(malformed, self.tag)

        second = dict(job)
        second["tag"] = "1123456789abcdef"
        second["certificate_key"] = (
            "sat49/campaign-20260825/h1/1123456789abcdef.compact.lrat.gz"
        )
        duplicate_slots = self.root / "duplicate-slots.jsonl"
        duplicate_slots.write_bytes(canonical_json(job) + canonical_json(second))
        with self.assertRaisesRegex(ReplayError, "duplicate profile/local-index slots"):
            load_queue(duplicate_slots)

    def test_queue_capacity_binding_rejects_family_local_index(self) -> None:
        jobs = load_queue(self.queue)
        capacity = load_capacity_index(self.capacity_index)
        validate_queue_capacity(jobs, capacity, require_complete=False)
        wrong = [dict(jobs[0], local_index=0)]
        with self.assertRaisesRegex(ReplayError, "expected capacity slot"):
            validate_queue_capacity(wrong, capacity, require_complete=False)

    def test_partial_capacity_index_rejects_out_of_range_ordinal(self) -> None:
        self.capacity_index.write_text(
            "orbit\tprofile\tlocalIndex\n"
            f"{self.tag}\tBBBB\t{CAPACITY_PROFILE_COUNTS[0]}\n"
        )
        with self.assertRaisesRegex(ReplayError, "outside profile range"):
            load_capacity_index(self.capacity_index)

    def test_complete_capacity_queue_requires_exact_13351_enumeration(self) -> None:
        capacity = {}
        jobs = []
        serial = 0
        for profile, count in enumerate(CAPACITY_PROFILE_COUNTS):
            for local_index in range(count):
                tag = f"{serial:016x}"
                capacity[tag] = (profile, local_index)
                jobs.append({
                    "tag": tag, "profile": profile, "local_index": local_index,
                })
                serial += 1
        validate_queue_capacity(jobs, capacity, require_complete=True)
        with self.assertRaisesRegex(ReplayError, "does not exactly cover"):
            validate_queue_capacity(jobs[:-1], capacity, require_complete=True)

    def test_queue_table_serialization_is_bound_to_tag(self) -> None:
        serialization = json.dumps([[[0, 2], 3], [[1, 3], 1]])
        tag = table_serialization_tag(serialization)
        validate_queue_tables([{"tag": tag, "table_serialization": serialization}])
        with self.assertRaisesRegex(ReplayError, "does not hash to tag"):
            validate_queue_tables([{
                "tag": "ffffffffffffffff", "table_serialization": serialization,
            }])

    def test_job_rejects_noncanonical_certificate_prefix(self) -> None:
        job = json.loads(self.job.read_text())
        self.assertIs(validate_job(job, self.tag), job)
        for prefix in (
            "attacker-copy/h1/",
            "../h1/",
            "/sat49/campaign-20260825/h1/",
            "sat49/campaign-20260825/extra/h1/",
        ):
            malformed = dict(job)
            malformed["certificate_key"] = f"{prefix}{self.tag}.compact.lrat.gz"
            with self.subTest(prefix=prefix), self.assertRaisesRegex(
                ReplayError, "certificate key must equal"
            ):
                validate_job(malformed, self.tag)

    def test_job_rejects_unknown_fields(self) -> None:
        job = json.loads(self.job.read_text())
        job["ignored_but_hashed"] = "not part of semantic job identity"
        with self.assertRaisesRegex(ReplayError, "unknown=.*ignored_but_hashed"):
            validate_job(job, self.tag)
        unknown = self.root / "unknown-field.jsonl"
        unknown.write_bytes(canonical_json(job))
        with self.assertRaisesRegex(ReplayError, "unknown=.*ignored_but_hashed"):
            load_queue(unknown)
        del job["cnf_sha256"]
        with self.assertRaisesRegex(
            ReplayError,
            r"missing=\['cnf_sha256'\], unknown=\['ignored_but_hashed'\]",
        ):
            validate_job(job, self.tag)

    def test_literal_axiom_report_parser(self) -> None:
        output = (
            "noise\naxioms Erdos85.h1V2P0I00003Checked : "
            "[propext, Classical.choice, Quot.sound, "
            "Erdos85.h1V2P0I00003Check._native.native_decide.ax_1]\n"
        )
        self.assertEqual(parse_axioms(output, "Erdos85.h1V2P0I00003Checked"), [
            "propext", "Classical.choice", "Quot.sound",
            "Erdos85.h1V2P0I00003Check._native.native_decide.ax_1",
        ])

    def test_resume_b_ready_without_consumed_tag_skips_compile(self) -> None:
        self.assertEqual(self.worker().returncode, 0)
        prefix = "sat49/campaign-20260825/h1-replay/"
        self.remove_object(f"{prefix}receipts/{self.tag}.json")
        self.remove_object(f"{prefix}ledger/{self.tag}.accepted")
        self.set_certificate_tags({})
        (self.state / "work" / self.tag / "emit-evil").write_text("1")
        resumed = self.worker()
        self.assertEqual(resumed.returncode, 0, resumed.stderr)
        self.assertIn("ACCEPTED", resumed.stdout)

    def test_resume_c_consumed_tag_without_receipt_does_not_retag(self) -> None:
        self.assertEqual(self.worker().returncode, 0)
        prefix = "sat49/campaign-20260825/h1-replay/"
        request_id = self.store.head(self.certificate_key).tagging_request_id
        self.remove_object(f"{prefix}receipts/{self.tag}.json")
        self.remove_object(f"{prefix}ledger/{self.tag}.accepted")
        resumed = self.worker()
        self.assertEqual(resumed.returncode, 0, resumed.stderr)
        receipt = json.loads(self.receipt_path().read_text())
        self.assertEqual(receipt["tagging_operation"], "already_present")
        self.assertEqual(receipt["tagging_request_id"], request_id)
        self.assertEqual(self.store.head(self.certificate_key).tagging_request_id, request_id)

    def test_resume_d_receipt_without_ledger_publishes_only_ledger(self) -> None:
        self.assertEqual(self.worker().returncode, 0)
        prefix = "sat49/campaign-20260825/h1-replay/"
        receipt_sha = sha256_file(self.receipt_path())
        self.remove_object(f"{prefix}ledger/{self.tag}.accepted")
        resumed = self.worker()
        self.assertEqual(resumed.returncode, 0, resumed.stderr)
        self.assertIn("RECOVERED_LEDGER", resumed.stdout)
        self.assertEqual(sha256_file(self.receipt_path()), receipt_sha)

    def test_resume_rejects_each_inconsistent_receipt_duplicate(self) -> None:
        self.assertEqual(self.worker().returncode, 0)
        prefix = "sat49/campaign-20260825/h1-replay/"
        receipt_key = f"{prefix}receipts/{self.tag}.json"
        ledger_key = f"{prefix}ledger/{self.tag}.accepted"
        paths = (
            self.store.objects / receipt_key, self.store.meta / f"{receipt_key}.json",
            self.store.objects / ledger_key, self.store.meta / f"{ledger_key}.json",
        )
        originals = [path.read_bytes() for path in paths]
        duplicate_fields = (
            "job_identity", "build_identity", "module", "compact_lrat",
            "source_raw", "olean_raw", "commands", "work_root",
            "worker_runtime", "artifacts", "axiom_audit", "certificate",
            "certificate_before_tagging",
        )
        for field in duplicate_fields:
            receipt = json.loads(originals[0])
            receipt[field] = "evil"
            receipt_bytes, ledger_bytes = self.rewrite_receipt_and_rebind_ledger(receipt)
            with self.subTest(field=field):
                result = self.worker()
                self.assertEqual(result.returncode, 2)
                self.assertIn(field, result.stderr)
                self.assertEqual(paths[0].read_bytes(), receipt_bytes)
                self.assertEqual(paths[2].read_bytes(), ledger_bytes)
                self.assertEqual(self.store.head(self.certificate_key).tags.get("replay"), "consumed")
            for path, original in zip(paths, originals):
                path.write_bytes(original)

    def test_resume_rejects_ready_tagging_and_receipt_integrity_inconsistency(self) -> None:
        self.assertEqual(self.worker().returncode, 0)
        prefix = "sat49/campaign-20260825/h1-replay/"
        receipt_key = f"{prefix}receipts/{self.tag}.json"
        ledger_key = f"{prefix}ledger/{self.tag}.accepted"
        paths = (
            self.store.objects / receipt_key, self.store.meta / f"{receipt_key}.json",
            self.store.objects / ledger_key, self.store.meta / f"{ledger_key}.json",
        )
        originals = [path.read_bytes() for path in paths]
        mutations = (
            ("replay-ready", True, lambda r: r["replay_ready"].__setitem__("etag", "evil")),
            ("tagging request", True, lambda r: r.__setitem__("tagging_request_id", "evil")),
            ("certificate-after-tagging", True, lambda r: r["certificate_after_tagging"]["metadata"].__setitem__("evil", "x")),
            ("certificate-after-tagging", True, lambda r: r["certificate_after_tagging"]["tags"].__setitem__("replay", "evil")),
            ("canonical SHA-256 integrity", False, lambda r: r["integrity"].__setitem__("receipt_sha256", "e" * 64)),
            ("integrity declaration", False, lambda r: r["integrity"].__setitem__("extra", True)),
        )
        for message, reseal, mutate in mutations:
            receipt = json.loads(originals[0])
            mutate(receipt)
            self.rewrite_receipt_and_rebind_ledger(receipt, reseal=reseal)
            with self.subTest(message=message):
                result = self.worker()
                self.assertEqual(result.returncode, 2)
                self.assertIn(message, result.stderr)
            for path, original in zip(paths, originals):
                path.write_bytes(original)

    def test_receipt_integrity_is_canonical_plain_sha256(self) -> None:
        self.assertEqual(self.worker().returncode, 0)
        receipt = json.loads(self.receipt_path().read_text())
        validate_receipt_integrity(receipt)
        self.assertEqual(receipt["integrity"]["scheme"], RECEIPT_INTEGRITY_SCHEME)
        self.assertRegex(receipt["integrity"]["receipt_sha256"], r"^[0-9a-f]{64}$")
        changed = json.loads(self.receipt_path().read_text())
        changed["accepted"] = False
        with self.assertRaisesRegex(ReplayError, "canonical SHA-256 integrity mismatch"):
            validate_receipt_integrity(changed)
        self.assertFalse(any("/claims/" in path.as_posix() for path in self.store.objects.rglob("*")))

    def test_resume_and_validator_reject_resealed_extra_receipt_field(self) -> None:
        self.assertEqual(self.worker().returncode, 0)
        receipt = json.loads(self.receipt_path().read_text())
        receipt["extra"] = "self-consistent-attacker-field"
        tbs = json.loads(json.dumps(receipt))
        del tbs["integrity"]["receipt_sha256"]
        receipt["integrity"]["receipt_sha256"] = sha256_bytes(canonical_json(tbs))
        self.rewrite_receipt_and_rebind_ledger(receipt, reseal=False)
        resumed = self.worker()
        self.assertEqual(resumed.returncode, 2)
        self.assertIn("receipt fields differ from exact schema", resumed.stderr)
        checked = self.validate_receipt()
        self.assertEqual(checked.returncode, 2)
        self.assertIn("receipt fields differ from exact schema", checked.stderr)

    def test_json_contract_rejects_duplicates_floats_and_v1_schema(self) -> None:
        duplicate = self.root / "duplicate.json"
        duplicate.write_text('{"schema":"x","schema":"y"}\n')
        with self.assertRaisesRegex(ReplayError, "duplicate JSON key"):
            load_manifest(duplicate)
        floating = self.root / "floating.json"
        floating.write_text('{"value":1.5}\n')
        with self.assertRaisesRegex(ReplayError, "floats are forbidden"):
            __import__("replay_common").load_json(floating)
        old = json.loads(self.manifest.read_text())
        old["schema"] = "erdos85-h1-replay-manifest-v1"
        old_path = self.root / "old-manifest.json"
        old_path.write_bytes(canonical_json(old))
        with self.assertRaisesRegex(ReplayError, "unsupported manifest schema"):
            load_manifest(old_path)

    def test_dispatcher_single_writer_lock_rejects_competitor(self) -> None:
        first_state = self.root / "dispatcher-a"
        second_state = self.root / "dispatcher-b"
        self.assertNotEqual(first_state.resolve(), second_state.resolve())
        lock_path = Path(json.loads(self.manifest.read_text())["single_writer_lock_path"])
        first = acquire_single_writer_lock(lock_path)
        try:
            with self.assertRaisesRegex(ReplayError, "single-writer lock"):
                acquire_single_writer_lock(lock_path)
            competitor = subprocess.run([
                sys.executable, str(DISPATCHER), "--manifest", str(self.manifest),
                "--queue", str(self.queue), "--state-dir", str(second_state),
                "--parallelism", "1", "--execute", "YES",
                "--object-store-root", str(self.store_root),
            ], text=True, capture_output=True, check=False)
            self.assertEqual(competitor.returncode, 2)
            self.assertIn("single-writer lock", competitor.stderr)
            self.assertFalse((second_state / "dispatch" / "START.json").exists())
        finally:
            first.close()
        second = acquire_single_writer_lock(lock_path)
        second.close()

    def test_s3_create_only_collision_gets_and_accepts_identical_winner(self) -> None:
        source = self.root / "immutable-source"
        source.write_bytes(b"winner")
        digest = sha256_file(source)
        metadata = {"tag": self.tag}
        winner = ObjectInfo(
            key="prefix/object", size=source.stat().st_size, sha256=digest,
            etag="etag", last_modified="now",
            metadata={"tag": self.tag, "sha256": digest}, tags={},
        )
        store = AwsCliObjectStore("example-bucket")
        failed_put = subprocess.CompletedProcess([], 1, "", "precondition failed")
        with patch.object(store, "_head_or_none", return_value=winner), patch.object(
            store, "download", return_value=winner
        ) as download, patch("replay_common.subprocess.run") as run:
            self.assertEqual(store.put_immutable("prefix/object", source, metadata), winner)
            download.assert_called_once()
            run.assert_not_called()

        with patch.object(store, "_head_or_none", side_effect=[None, winner]), patch(
            "replay_common.subprocess.run", return_value=failed_put
        ), patch.object(store, "download", return_value=winner) as download:
            self.assertEqual(store.put_immutable("prefix/object", source, metadata), winner)
            download.assert_called_once()

        divergent = replace(winner, sha256="f" * 64)
        with patch.object(store, "_head_or_none", side_effect=[None, divergent]), patch(
            "replay_common.subprocess.run", return_value=failed_put
        ), patch.object(store, "download", return_value=divergent), self.assertRaisesRegex(
            ReplayError, "immutable S3 collision"
        ):
            store.put_immutable("prefix/object", source, metadata)

        lying = replace(winner, metadata={"tag": self.tag, "sha256": "f" * 64})
        with patch.object(store, "_head_or_none", return_value=winner), patch.object(
            store, "download", return_value=lying
        ), self.assertRaisesRegex(ReplayError, "immutable S3 collision"):
            store.put_immutable("prefix/object", source, metadata)

    def test_resume_requires_exact_ledger_schema(self) -> None:
        self.assertEqual(self.worker().returncode, 0)
        ledger_key = f"sat49/campaign-20260825/h1-replay/ledger/{self.tag}.accepted"
        object_path = self.store.objects / ledger_key
        meta_path = self.store.meta / f"{ledger_key}.json"
        originals = (object_path.read_bytes(), meta_path.read_bytes())
        mutations = (
            lambda value: value.__setitem__("schema", "evil"),
            lambda value: value.pop("receipt_key"),
            lambda value: value.__setitem__("unknown", True),
        )
        for mutate in mutations:
            ledger = json.loads(originals[0])
            mutate(ledger)
            self.rewrite_store_json(ledger_key, ledger)
            result = self.worker()
            self.assertEqual(result.returncode, 2)
            self.assertIn("terminal ledger schema", result.stderr)
            object_path.write_bytes(originals[0])
            meta_path.write_bytes(originals[1])

    def test_e_changed_input_and_lost_tag_fail_closed(self) -> None:
        self.assertEqual(self.worker().returncode, 0)
        certificate_path = self.store.objects / self.certificate_key
        original = certificate_path.read_bytes()
        certificate_path.write_bytes(original + b"changed")
        changed = self.worker()
        self.assertEqual(changed.returncode, 2)
        self.assertIn("integrity mismatch", changed.stderr)
        certificate_path.write_bytes(original)
        self.set_certificate_tags({})
        lost = self.worker()
        self.assertEqual(lost.returncode, 2)
        self.assertIn("lost replay=consumed", lost.stderr)

    def test_receipt_contains_and_validator_enforces_section_four_fields(self) -> None:
        self.assertEqual(self.worker().returncode, 0)
        receipt = json.loads(self.receipt_path().read_text())
        for field in (
            "job_identity", "build_identity", "module", "certificate",
            "compact_lrat", "source_raw", "olean_raw", "commands",
            "worker_runtime", "replay_ready", "integrity",
        ):
            self.assertIn(field, receipt)
        self.assertEqual(
            sha256_bytes(receipt["job_identity"]["table_serialization"].encode()),
            receipt["job_identity"]["table_sha256"],
        )
        self.assertEqual(receipt["worker_runtime"]["identity_source"], "local-test-backend")
        self.assertGreater(receipt["commands"]["compile"]["peak_rss_kib"], 0)
        self.assertEqual(receipt["replay_ready"]["sha256"], receipt["replay_ready_sha256"])

    def test_manifest_rejects_retired_keyed_integrity_contract(self) -> None:
        manifest = json.loads(self.manifest.read_text())
        manifest["receipt_integrity_scheme"] = "TBD"
        self.manifest.write_bytes(canonical_json(manifest))
        result = subprocess.run([
            sys.executable, str(WORKER), "--manifest", str(self.manifest),
            "--job", str(self.job), "--tag", self.tag,
            "--state-dir", str(self.state), "--s3-bucket", "local-test",
        ], text=True, capture_output=True, check=False)
        self.assertEqual(result.returncode, 2, result.stderr)
        self.assertIn("receipt integrity contract must be canonical JSON SHA-256", result.stderr)

    def test_validator_rejects_backend_not_bound_to_frozen_manifest(self) -> None:
        manifest = json.loads(self.manifest.read_text())
        # Isolate the binding check from production-format and CLI checks: a
        # mismatched bucket must never reach either the CLI or object store.
        from unittest.mock import patch
        with patch("validate_replay_receipt.validate_production_manifest"), patch(
            "validate_replay_receipt.validate_aws_cli"
        ) as validate_cli:
            with self.assertRaisesRegex(ReplayError, "S3 bucket differs from frozen manifest"):
                validate_production_backend_binding(manifest, "attacker-copy", "aws")
            validate_cli.assert_not_called()

        with self.assertRaises(OSError):
            # The helper also proves the configured CLI identity before any
            # production object is accepted.
            with patch("validate_replay_receipt.validate_production_manifest"), patch(
                "validate_replay_receipt.validate_aws_cli", side_effect=OSError("missing CLI")
            ):
                validate_production_backend_binding(manifest, manifest["s3_bucket"], "missing")

    def test_command_receipt_rejects_repeated_placeholder_and_nonfinite_metrics(self) -> None:
        with self.assertRaises(ReplayError):
            canonical_json({"bad": float("nan")})
        self.assertFalse(__import__("replay_common")._argv_matches_template(
            ["tool", "evil-A", "evil-B"], ["tool", "{work}", "{work}"]
        ))
        manifest = json.loads(self.manifest.read_text())
        allowed_environment = ["ERDOS85_PRESENT_TEST", "ERDOS85_MISSING_TEST"]
        manifest["environment_allowlist"] = allowed_environment
        self.manifest.write_bytes(canonical_json(manifest))
        with patch.dict(__import__("os").environ, {"ERDOS85_PRESENT_TEST": "present"}):
            self.assertEqual(self.worker().returncode, 0)
        ready_path = self.store.objects / (
            f"sat49/campaign-20260825/h1-replay/replay-ready/{self.tag}.json"
        )
        commands = json.loads(ready_path.read_text())["commands"]
        self.assertEqual(commands["compile"]["environment"]["ERDOS85_PRESENT_TEST"], "present")
        self.assertIsNone(commands["compile"]["environment"]["ERDOS85_MISSING_TEST"])
        del commands["compile"]["environment"]["ERDOS85_MISSING_TEST"]
        with self.assertRaisesRegex(ReplayError, "exact allowlist"):
            validate_command_receipts(commands, allowed_environment)
        commands = json.loads(ready_path.read_text())["commands"]
        commands["compile"]["wall_ns"] = -1
        commands["compile"]["peak_rss_kib"] = True
        with self.assertRaises(ReplayError):
            validate_command_receipts(
                commands, allowed_environment,
                json.loads(self.manifest.read_text())["commands"],
            )

    def test_command_runs_with_exact_recorded_environment(self) -> None:
        observed = self.root / "observed-environment.json"
        names = (
            "ERDOS85_ALLOWED_TEST", "ERDOS85_MISSING_TEST", "PATH",
            "PYTHONPATH", "LEAN_PATH", "LD_PRELOAD",
        )
        program = (
            "import json,os,sys; names=json.loads(sys.argv[2]); "
            "json.dump({k:os.environ.get(k) for k in names}, open(sys.argv[1], 'w'))"
        )
        poison = {
            "ERDOS85_ALLOWED_TEST": "exact-value",
            "PATH": "poison-path",
            "PYTHONPATH": "poison-python",
            "LEAN_PATH": "poison-lean",
            "LD_PRELOAD": "poison-loader",
        }
        with patch.dict(__import__("os").environ, poison, clear=False):
            result = run_command(
                [sys.executable, "-c", program, str(observed), json.dumps(names)], self.root,
                self.root / "environment-command.log",
                ["ERDOS85_ALLOWED_TEST", "ERDOS85_MISSING_TEST"],
            )
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(result.environment, {
            "ERDOS85_ALLOWED_TEST": "exact-value",
            "ERDOS85_MISSING_TEST": None,
        })
        self.assertEqual(json.loads(observed.read_text()), {
            "ERDOS85_ALLOWED_TEST": "exact-value",
            "ERDOS85_MISSING_TEST": None,
            "PATH": None,
            "PYTHONPATH": None,
            "LEAN_PATH": None,
            "LD_PRELOAD": None,
        })

    def test_manifest_rejects_relative_tools_and_duplicate_environment(self) -> None:
        original = json.loads(self.manifest.read_text())
        duplicate = dict(original, environment_allowlist=["LEAN_PATH", "LEAN_PATH"])
        duplicate_path = self.root / "duplicate-environment.json"
        duplicate_path.write_bytes(canonical_json(duplicate))
        with self.assertRaisesRegex(ReplayError, "must not contain duplicates"):
            load_manifest(duplicate_path)

        for name in ("generate", "compile", "axiom_audit", "zstd"):
            manifest = json.loads(self.manifest.read_text())
            manifest["commands"][name][0] = "relative-tool"
            candidate = self.root / f"relative-{name}.json"
            candidate.write_bytes(canonical_json(manifest))
            with self.subTest(name=name), self.assertRaisesRegex(
                ReplayError, f"commands.{name} executable must be absolute"
            ):
                load_manifest(candidate)

    def test_validator_rejects_each_mutated_section_four_identity(self) -> None:
        self.assertEqual(self.worker().returncode, 0)
        receipt_path = self.receipt_path()
        meta_path = self.store.meta / (
            f"sat49/campaign-20260825/h1-replay/receipts/{self.tag}.json.json"
        )
        original_bytes = receipt_path.read_bytes()
        original_meta = meta_path.read_bytes()

        def reject(mutator) -> None:
            receipt = json.loads(original_bytes)
            mutator(receipt)
            value = (json.dumps(receipt, sort_keys=True, separators=(",", ":")) + "\n").encode()
            receipt_path.write_bytes(value)
            meta = json.loads(original_meta)
            digest = sha256_bytes(value)
            meta.update(size=len(value), sha256=digest, etag=digest)
            meta_path.write_bytes(canonical_json(meta))
            checked = self.validate_receipt()
            self.assertEqual(checked.returncode, 2, checked.stdout + checked.stderr)
            receipt_path.write_bytes(original_bytes)
            meta_path.write_bytes(original_meta)

        mutations = (
            lambda r: r["build_identity"].__setitem__("repository_commit", "evil"),
            lambda r: r["job_identity"].__setitem__("table_serialization", "evil"),
            lambda r: r["commands"]["compile"]["argv"].append("evil"),
            lambda r: r["commands"]["compile"].__setitem__("wall_ns", -1),
            lambda r: r["worker_runtime"].__setitem__("ami_id", "ami-evil"),
            lambda r: r["replay_ready"].__setitem__("sha256", "e" * 64),
            lambda r: r["integrity"].__setitem__("scheme", "evil"),
        )
        for mutation in mutations:
            reject(mutation)
        for field in (
            "overlay_builder_sha256", "overlay_project_manifest_sha256",
            "overlay_build_receipt_sha256", "overlay_manifest_sha256",
            "overlay_identity_sha256", "overlay_archive_sha256",
        ):
            reject(lambda receipt, field=field:
                   receipt["build_identity"].__setitem__(field, "e" * 64))

        certificate_meta = self.store.meta / f"{self.certificate_key}.json"
        original_certificate_meta = certificate_meta.read_bytes()
        changed = json.loads(original_certificate_meta)
        changed["version_id"] = "version-evil"
        certificate_meta.write_bytes(canonical_json(changed))
        self.assertEqual(self.validate_receipt().returncode, 2)
        certificate_meta.write_bytes(original_certificate_meta)

    def test_manifest_freezer_rejects_a_different_clean_repository(self) -> None:
        other = self.root / "other-repo"
        other.mkdir()
        subprocess.run(["git", "init", "-q"], cwd=other, check=True)
        subprocess.run(["git", "config", "user.email", "test@example.invalid"], cwd=other, check=True)
        subprocess.run(["git", "config", "user.name", "Test"], cwd=other, check=True)
        (other / "tracked").write_text("x")
        subprocess.run(["git", "add", "tracked"], cwd=other, check=True)
        subprocess.run(["git", "commit", "-qm", "initial"], cwd=other, check=True)
        result = subprocess.run([
            sys.executable, str(MANIFEST_BUILDER), "--draft", str(self.manifest),
            "--queue", str(self.queue), "--repo", str(other),
            "--output", str(self.root / "frozen.json"),
            "--capacity-index", str(self.capacity_index),
            "--capacity-reindex-receipt", str(self.capacity_reindex_receipt),
            "--queue-build-receipt", str(self.queue_build_receipt),
            "--terminal-index", str(self.terminal_index),
            "--overlay-build-receipt", str(self.overlay_receipt),
            "--overlay-manifest", str(self.overlay_manifest),
            "--overlay-archive", str(self.overlay_archive),
            "--overlay-project-manifest", str(self.overlay_project_manifest),
        ], text=True, capture_output=True, check=False)
        self.assertEqual(result.returncode, 2)
        self.assertIn("worktree containing replay scripts", result.stderr)

    def test_manifest_freezer_replaces_stale_generator_and_template_pins(self) -> None:
        manifest = json.loads(self.manifest.read_text())
        manifest["generator_sha256"] = "4a3e3488" + "0" * 56
        manifest["template_sha256"] = "4a3e3488" + "1" * 56
        manifest["commands"]["compile"] = PRODUCTION_COMPILE_COMMAND
        manifest["environment_allowlist"] = PRODUCTION_ENVIRONMENT_ALLOWLIST
        self.manifest.write_bytes(canonical_json(manifest))
        output = self.root / "frozen.json"
        real_git_value = manifest_builder.git_value

        def clean_git_value(repo, *arguments):
            if arguments == ("status", "--porcelain"):
                return ""
            return real_git_value(repo, *arguments)

        argv = [
            str(MANIFEST_BUILDER), "--draft", str(self.manifest),
            "--queue", str(self.queue), "--repo", str(HERE.parent),
            "--output", str(output), "--capacity-index", str(self.capacity_index),
            "--capacity-reindex-receipt", str(self.capacity_reindex_receipt),
            "--queue-build-receipt", str(self.queue_build_receipt),
            "--terminal-index", str(self.terminal_index),
            "--overlay-build-receipt", str(self.overlay_receipt),
            "--overlay-manifest", str(self.overlay_manifest),
            "--overlay-archive", str(self.overlay_archive),
            "--overlay-project-manifest", str(self.overlay_project_manifest),
        ]
        with patch.object(manifest_builder, "git_value", side_effect=clean_git_value), \
             patch.object(manifest_builder, "validate_queue_tables"), \
             patch.object(sys, "argv", argv):
            self.assertEqual(manifest_builder.main(), 0)
        frozen = json.loads(output.read_text())
        expected = sha256_file(HERE / "generate_replay_leaf.py")
        self.assertEqual(frozen["generator_sha256"], expected)
        self.assertEqual(frozen["template_sha256"], expected)
        self.assertNotIn("overlay_sha256", frozen)
        self.assertEqual(frozen["overlay_builder_sha256"],
                         sha256_file(HERE / "build_replay_overlay.py"))
        self.assertEqual(frozen["overlay_project_manifest_sha256"],
                         sha256_file(self.overlay_project_manifest))
        self.assertEqual(frozen["overlay_build_receipt_sha256"],
                         sha256_file(self.overlay_receipt))
        self.assertEqual(frozen["overlay_manifest_sha256"],
                         sha256_file(self.overlay_manifest))
        self.assertEqual(frozen["overlay_archive_sha256"],
                         sha256_file(self.overlay_archive))

    def test_overlay_freight_chain_rejects_each_wrong_crosslink(self) -> None:
        arguments = dict(
            receipt_path=self.overlay_receipt,
            manifest_path=self.overlay_manifest,
            archive_path=self.overlay_archive,
            project_manifest_path=self.overlay_project_manifest,
            builder_path=HERE / "build_replay_overlay.py",
            source_commit=json.loads(self.overlay_receipt.read_text())["source_commit"],
        )
        fields = manifest_builder.validate_overlay_freight(**arguments)
        self.assertEqual(set(fields), {
            "overlay_builder_sha256", "overlay_project_manifest_sha256",
            "overlay_build_receipt_sha256", "overlay_manifest_sha256",
            "overlay_identity_sha256", "overlay_archive_sha256",
        })
        original = self.overlay_receipt.read_bytes()
        for field in (
            "producer_sha256", "project_manifest_sha256", "manifest_sha256",
            "overlay_identity_sha256", "source_commit", "entry_count",
        ):
            receipt = json.loads(original)
            receipt[field] = 2 if field == "entry_count" else (
                "f" * 40 if field == "source_commit" else "f" * 64)
            self.overlay_receipt.write_bytes(canonical_json(receipt))
            with self.subTest(field=field), self.assertRaisesRegex(
                ReplayError, "crosslink mismatch"
            ):
                manifest_builder.validate_overlay_freight(**arguments)
        self.overlay_receipt.write_bytes(original)
        archive_before = fields["overlay_archive_sha256"]
        self.overlay_archive.write_bytes(b"different-archive-fixture")
        changed = manifest_builder.validate_overlay_freight(**arguments)
        self.assertNotEqual(changed["overlay_archive_sha256"], archive_before)

    def test_freezer_rejects_stale_lake_compile_contract(self) -> None:
        output = self.root / "stale-contract-must-not-freeze.json"
        real_git_value = manifest_builder.git_value

        def clean_git_value(repo, *arguments):
            if arguments == ("status", "--porcelain"):
                return ""
            return real_git_value(repo, *arguments)

        argv = [
            str(MANIFEST_BUILDER), "--draft", str(self.manifest),
            "--queue", str(self.queue), "--repo", str(HERE.parent),
            "--output", str(output), "--capacity-index", str(self.capacity_index),
            "--capacity-reindex-receipt", str(self.capacity_reindex_receipt),
            "--queue-build-receipt", str(self.queue_build_receipt),
            "--terminal-index", str(self.terminal_index),
            "--overlay-build-receipt", str(self.overlay_receipt),
            "--overlay-manifest", str(self.overlay_manifest),
            "--overlay-archive", str(self.overlay_archive),
            "--overlay-project-manifest", str(self.overlay_project_manifest),
        ]
        with patch.object(manifest_builder, "git_value", side_effect=clean_git_value), \
             patch.object(manifest_builder, "validate_queue_tables"), \
             patch.object(sys, "argv", argv):
            self.assertEqual(manifest_builder.main(), 2)
        self.assertFalse(output.exists())

    def test_manifest_rejects_ambiguous_legacy_overlay_identity(self) -> None:
        manifest = json.loads(self.manifest.read_text())
        manifest["overlay_sha256"] = "f" * 64
        candidate = self.root / "legacy-overlay.json"
        candidate.write_bytes(canonical_json(manifest))
        with self.assertRaisesRegex(ReplayError, "ambiguous legacy"):
            load_manifest(candidate)

    def test_invalid_manifest_is_rejected_before_publication(self) -> None:
        output = self.root / "must-not-exist.json"
        with self.assertRaises(ReplayError):
            publish_validated_manifest(output, canonical_json({"schema": SCHEMA}))
        self.assertFalse(output.exists())

    def test_manifest_publication_is_atomic_create_only(self) -> None:
        value = self.manifest.read_bytes()
        output = self.root / "create-only-manifest.json"
        sentinel = b"competing-manifest\n"
        output.write_bytes(sentinel)
        with self.assertRaises(FileExistsError):
            publish_validated_manifest(output, value)
        self.assertEqual(output.read_bytes(), sentinel)
        output.unlink()

        def fail_before_link():
            raise ReplayError("input drift")

        with self.assertRaisesRegex(ReplayError, "input drift"):
            publish_validated_manifest(output, value, fail_before_link)
        self.assertFalse(output.exists())

    def test_queue_build_receipt_is_exact_and_fully_bound(self) -> None:
        original = json.loads(self.queue_build_receipt.read_text())
        self.assertEqual(validate_queue_build_receipt(
            original, self.queue, self.capacity_index, self.terminal_index,
            ZERO_SHA, 1, False,
        ), sha256_file(self.terminal_index))
        mutations = (
            lambda r: r.__setitem__("extra", "x"),
            lambda r: r.__setitem__("schema", "old"),
            lambda r: r.__setitem__("output_sha256", "f" * 64),
            lambda r: r.__setitem__("certificate_index_sha256", "f" * 64),
            lambda r: r.__setitem__("inventory_sha256", "f" * 64),
            lambda r: r.__setitem__("emitted_jobs", 2),
            lambda r: r.__setitem__("require_complete", True),
        )
        for mutation in mutations:
            receipt = dict(original)
            mutation(receipt)
            with self.assertRaises(ReplayError):
                validate_queue_build_receipt(
                    receipt, self.queue, self.capacity_index, self.terminal_index,
                    ZERO_SHA, 1, False,
                )
        original_terminal = self.terminal_index.read_bytes()
        self.terminal_index.write_bytes(original_terminal + b"changed")
        with self.assertRaisesRegex(ReplayError, "terminal-index hash mismatch"):
            validate_queue_build_receipt(
                original, self.queue, self.capacity_index, self.terminal_index,
                ZERO_SHA, 1, False,
            )

    def test_manifest_execution_controls_are_exact_before_publication(self) -> None:
        original = json.loads(self.manifest.read_text())
        mutations = (
            ("queue_sha256", None, "missing string fields"),
            ("queue_sha256", "not-a-sha", "lowercase SHA-256"),
            ("expected_jobs", True, "positive integer"),
            ("expected_jobs", 0, "positive integer"),
            ("expected_jobs", -1, "positive integer"),
            ("expected_jobs", "1", "positive integer"),
            ("max_parallelism", True, "positive integer"),
            ("max_parallelism", 0, "positive integer"),
            ("max_parallelism", -1, "positive integer"),
            ("max_parallelism", "1", "positive integer"),
            ("single_dispatcher", False, "must be true"),
            ("single_dispatcher", "true", "must be true"),
            ("receipt_integrity_key_id", "obsolete", "obsolete lease or keyed-integrity"),
            ("claim_ttl_seconds", 60, "obsolete lease or keyed-integrity"),
        )
        for index, (field, value, message) in enumerate(mutations):
            manifest = dict(original)
            if value is None:
                del manifest[field]
            else:
                manifest[field] = value
            candidate = self.root / f"invalid-manifest-{index}.json"
            candidate.write_bytes(canonical_json(manifest))
            with self.subTest(field=field, value=value), self.assertRaisesRegex(
                ReplayError, message
            ):
                load_manifest(candidate)
            output = self.root / f"must-not-publish-{index}.json"
            with self.assertRaisesRegex(ReplayError, message):
                publish_validated_manifest(output, candidate.read_bytes())
            self.assertFalse(output.exists())

    def test_manifest_axiom_allowlist_is_exact_before_publication(self) -> None:
        original = json.loads(self.manifest.read_text())
        self.assertEqual(load_manifest(self.manifest).get("allowed_axiom_patterns", []), [])
        mutations = (
            ["propext", "Classical.choice", "Quot.sound", "evil.axiom"],
            ["propext", "Classical.choice"],
            ["propext", "Classical.choice", "Quot.sound", "Quot.sound"],
            ["Classical.choice", "propext", "Quot.sound"],
        )
        for index, allowed in enumerate(mutations):
            manifest = dict(original, allowed_axioms=allowed)
            candidate = self.root / f"bad-allowlist-{index}.json"
            candidate.write_bytes(canonical_json(manifest))
            output = self.root / f"must-not-publish-allowlist-{index}.json"
            with self.assertRaisesRegex(ReplayError, "canonical foundational list"):
                publish_validated_manifest(output, candidate.read_bytes())
            self.assertFalse(output.exists())

        for index, patterns in enumerate((
            ["evil\\..*"],
            [NATIVE_AXIOM_PATTERN, NATIVE_AXIOM_PATTERN],
            [NATIVE_AXIOM_PATTERN, "evil\\..*"],
        )):
            manifest = dict(original, allowed_axiom_patterns=patterns)
            candidate = self.root / f"bad-patterns-{index}.json"
            candidate.write_bytes(canonical_json(manifest))
            with self.assertRaisesRegex(ReplayError, "singleton reviewed"):
                load_manifest(candidate)

        # Local mechanics may omit native roots; production may not.
        with self.assertRaisesRegex(ReplayError, "allowed_axiom_patterns"):
            validate_production_manifest(original)
        production = dict(original, allowed_axiom_patterns=[NATIVE_AXIOM_PATTERN])
        loaded = self.root / "native-pattern.json"
        loaded.write_bytes(canonical_json(production))
        self.assertEqual(load_manifest(loaded)["allowed_axiom_patterns"], [NATIVE_AXIOM_PATTERN])


if __name__ == "__main__":
    unittest.main()
