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

from replay_common import LocalObjectStore, SCHEMA, canonical_json, sha256_bytes, sha256_file
from audit_replay_leaf import parse_axioms


WORKER = HERE / "replay_worker.py"
VALIDATOR = HERE / "validate_replay_receipt.py"
DISPATCHER = HERE / "run_replay_queue.py"
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
            {"cnf-sha256": "2" * 64, "tag": self.tag},
        )
        self.job = self.root / "job.json"
        self.job.write_bytes(canonical_json({
            "tag": self.tag, "profile": 0, "local_index": 3,
            "certificate_key": self.certificate_key,
            "certificate_gzip_sha256": sha256_bytes(compressed),
            "compact_lrat_sha256": sha256_bytes(compact),
            "cnf_sha256": "2" * 64, "table_sha256": "3" * 64,
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
            "template_sha256": "4" * 64, "worker_sha256": sha256_file(WORKER),
            "validator_sha256": "6" * 64, "zstd_identity": "copy-test",
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


if __name__ == "__main__":
    unittest.main()
