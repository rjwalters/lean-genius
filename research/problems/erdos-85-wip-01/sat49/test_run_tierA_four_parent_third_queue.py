#!/usr/bin/env python3

import hashlib
import tempfile
import unittest
from pathlib import Path

import run_tierA_four_parent_third_queue as module


class FourParentControllerTest(unittest.TestCase):
    def test_rejects_worker_receipt_drift(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            worker = root / "worker.py"
            generator = root / "generator.py"
            worker.write_text("worker")
            generator.write_text("generator")
            receipt = {
                "schema": "erdos85-tierA-four-parent-worker-receipt-v1",
                "source_worker_sha256": module.SOURCE_WORKER_SHA256,
                "third_generator_sha256": module.THIRD_GENERATOR_SHA256,
                "third_manifest_sha256": module.THIRD_MANIFEST_SHA256,
                "queue_receipt_sha256": module.BLESSED_QUEUE_RECEIPT_SHA256,
                "generator_sha256": hashlib.sha256(generator.read_bytes()).hexdigest(),
                "output_worker_sha256": hashlib.sha256(worker.read_bytes()).hexdigest(),
            }
            old = module.WORKER_GENERATOR_SHA256
            module.WORKER_GENERATOR_SHA256 = receipt["generator_sha256"]
            try:
                module.validate_worker_receipt(receipt, worker, generator)
                receipt["source_worker_sha256"] = "0" * 64
                with self.assertRaisesRegex(ValueError, "source_worker_sha256"):
                    module.validate_worker_receipt(receipt, worker, generator)
            finally:
                module.WORKER_GENERATOR_SHA256 = old

    def test_validate_jobs_accepts_only_exact_pinned_queue(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            queue = Path(directory) / "queue.txt"
            jobs = [
                f"h3_b1.cube-0-0.nested.cube-0-{parent}.third.cube-{i}-{j}"
                for parent in range(4) for i in range(8) for j in range(8)
            ] + [
                f"h3_b1.cube-0-0.nested.cube-0-{parent}.third.cover-{side}"
                for parent in range(4) for side in ("left", "right")
            ]
            queue.write_text("\n".join(jobs) + "\n")
            old = module.QUEUE_SHA256
            module.QUEUE_SHA256 = hashlib.sha256(queue.read_bytes()).hexdigest()
            try:
                self.assertEqual(module.validate_jobs(queue), jobs)
                queue.write_text(queue.read_text().replace("cube-0-0", "cube-8-0", 1))
                module.QUEUE_SHA256 = hashlib.sha256(queue.read_bytes()).hexdigest()
                with self.assertRaisesRegex(ValueError, "invalid or unexpected"):
                    module.validate_jobs(queue)
            finally:
                module.QUEUE_SHA256 = old


if __name__ == "__main__":
    unittest.main()
