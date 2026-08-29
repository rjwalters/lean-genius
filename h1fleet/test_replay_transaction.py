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
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))

from replay_common import (
    LocalObjectStore, ReplayError, SCHEMA, canonical_json, sha256_bytes, sha256_file,
    validate_command_receipts,
)
from audit_replay_leaf import parse_axioms
from build_replay_manifest import publish_validated_manifest


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

    def test_command_receipt_rejects_repeated_placeholder_and_nonfinite_metrics(self) -> None:
        with self.assertRaises(ReplayError):
            canonical_json({"bad": float("nan")})
        self.assertFalse(__import__("replay_common")._argv_matches_template(
            ["tool", "evil-A", "evil-B"], ["tool", "{work}", "{work}"]
        ))
        self.assertEqual(self.worker().returncode, 0)
        ready_path = self.store.objects / (
            f"sat49/campaign-20260825/h1-replay/replay-ready/{self.tag}.json"
        )
        commands = json.loads(ready_path.read_text())["commands"]
        commands["compile"]["wall_seconds"] = float("nan")
        commands["compile"]["peak_rss_kib"] = True
        with self.assertRaises(ReplayError):
            validate_command_receipts(commands, [], json.loads(self.manifest.read_text())["commands"])

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


if __name__ == "__main__":
    unittest.main()
