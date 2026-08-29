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
from unittest.mock import patch
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))

from replay_common import (
    LocalObjectStore, NATIVE_AXIOM_PATTERN, ReplayError, SCHEMA, canonical_json, load_manifest,
    run_command, sha256_bytes, sha256_file, validate_command_receipts,
)
from audit_replay_leaf import parse_axioms
from build_replay_manifest import publish_validated_manifest
from replay_worker import validate_job, validate_production_manifest
from run_replay_queue import load_queue
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
        self.root = Path(self.temporary.name)
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
        self.manifest = self.root / "manifest.json"
        self.manifest.write_bytes(canonical_json({
            "schema": SCHEMA,
            "campaign_prefix": "sat49/campaign-20260825/h1-replay/",
            "repository_commit": "test-commit", "inventory_sha256": ZERO_SHA,
            "coverage_sha256": "1" * 64, "toolchain_identity": "lean-test",
            "overlay_sha256": "2" * 64, "generator_sha256": "3" * 64,
            "template_sha256": "4" * 64, "cnf_emitter_sha256": "d" * 64,
            "worker_sha256": sha256_file(WORKER),
            "validator_sha256": "6" * 64, "zstd_identity": "copy-test",
            "receipt_schema_sha256": "8" * 64,
            "aggregate_generator_sha256": "9" * 64,
            "axiom_auditor_sha256": "a" * 64, "common_sha256": "b" * 64,
            "dispatcher_sha256": "c" * 64,
            "aws_cli_identity": "local-backend-not-used",
            "worker_image_digest": "test-image@sha256:" + "7" * 64,
            "worker_ami_id": "local-test-ami",
            "worker_instance_type": "local-test", "ebs_shape": "local-test",
            "instance_role": "local-test", "s3_bucket": "local-test",
            "aws_region": "local-test",
            "receipt_integrity_scheme": "local-test-unkeyed",
            "receipt_integrity_key_id": "local-test",
            "queue_sha256": sha256_file(self.queue), "expected_jobs": 1,
            "max_parallelism": 1, "single_dispatcher": True,
            "allowed_axioms": ["propext", "Classical.choice", "Quot.sound"],
            "commands": {
                "generate": [sys.executable, str(self.helper), "generate", "{source}"],
                "compile": [sys.executable, str(self.helper), "compile", "{olean}"],
                "axiom_audit": [sys.executable, str(self.helper), "audit", "{audit_json}"],
                "zstd": [sys.executable, str(self.helper), "zstd", "{input}", "{output}"],
            },
        }))

    def tearDown(self) -> None:
        self.temporary.cleanup()

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

    def remove_object(self, key: str) -> None:
        (self.store.objects / key).unlink(missing_ok=True)
        (self.store.meta / f"{key}.json").unlink(missing_ok=True)

    def set_certificate_tags(self, tags: dict[str, str]) -> None:
        meta_path = self.store.meta / f"{self.certificate_key}.json"
        meta = json.loads(meta_path.read_text())
        meta["tags"] = tags
        meta.pop("tagging_request_id", None)
        meta_path.write_bytes(canonical_json(meta))

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

    def test_undisclosed_axiom_never_tags_or_accepts(self) -> None:
        work = self.state / "work" / self.tag
        work.mkdir(parents=True)
        (work / "emit-evil").write_text("1")
        result = self.worker()
        self.assertEqual(result.returncode, 2)
        self.assertIn("undisclosed axioms", result.stderr)
        self.assertNotIn("replay", self.store.head(self.certificate_key).tags)
        self.assertFalse(self.receipt_path().exists())

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
        ], text=True, capture_output=True, check=False)
        self.assertEqual(freeze.returncode, 2)
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

    def test_live_claim_rejected_and_stale_claim_recovered(self) -> None:
        key = f"sat49/campaign-20260825/h1-replay/claims/{self.tag}.json"
        token = self.store.acquire_claim(key, "first", time.time(), 60)
        with self.assertRaisesRegex(Exception, "live replay claim"):
            self.store.acquire_claim(key, "second", time.time(), 60)
        self.store.release_claim(key, "first", token, time.time() - 1)
        recovered = self.store.acquire_claim(key, "second", time.time(), 60)
        self.assertTrue(recovered)

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

    def test_production_launch_fails_while_integrity_selection_is_tbd(self) -> None:
        manifest = json.loads(self.manifest.read_text())
        manifest["receipt_integrity_scheme"] = "TBD"
        manifest["receipt_integrity_key_id"] = "TBD"
        self.manifest.write_bytes(canonical_json(manifest))
        result = subprocess.run([
            sys.executable, str(WORKER), "--manifest", str(self.manifest),
            "--job", str(self.job), "--tag", self.tag,
            "--state-dir", str(self.state), "--s3-bucket", "local-test",
        ], text=True, capture_output=True, check=False)
        self.assertEqual(result.returncode, 2)
        self.assertIn("production manifest contains unresolved or malformed identities", result.stderr)

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
        commands["compile"]["wall_seconds"] = float("nan")
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
            lambda r: r["commands"]["compile"].__setitem__("wall_seconds", float("nan")),
            lambda r: r["worker_runtime"].__setitem__("ami_id", "ami-evil"),
            lambda r: r["replay_ready"].__setitem__("sha256", "e" * 64),
            lambda r: r["integrity"].__setitem__("scheme", "evil"),
        )
        for mutation in mutations:
            reject(mutation)

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
        ], text=True, capture_output=True, check=False)
        self.assertEqual(result.returncode, 2)
        self.assertIn("worktree containing replay scripts", result.stderr)

    def test_invalid_manifest_is_rejected_before_publication(self) -> None:
        output = self.root / "must-not-exist.json"
        with self.assertRaises(ReplayError):
            publish_validated_manifest(output, canonical_json({"schema": SCHEMA}))
        self.assertFalse(output.exists())

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
            ("claim_ttl_seconds", True, "integer >= 60"),
            ("claim_ttl_seconds", -1, "integer >= 60"),
            ("claim_ttl_seconds", "60", "integer >= 60"),
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
