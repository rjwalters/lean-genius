#!/usr/bin/env python3

import tempfile
import unittest
from pathlib import Path
from unittest import mock

import generate_h1_v3_retry_worker as worker_module
from generate_h1_v3_retry_worker import KNOWN_V2_SHA256, atomic_write, derive_worker


V2_TEMPLATE = """#!/bin/bash
#   h1-fleet-v2/claims/<tag>
#   h1-fleet-v2/ledger/<tag>.line
#   h1-fleet-v2/nodes/<instance>/heartbeat
META=h1-fleet-v2
  while IFS=$'\\t' read -r tag prof fam idx; do
    grep -qx \"$tag\" /opt/h1/ledger.$SLOT && continue
    grep -qx \"$tag\" /opt/h1/claims.$SLOT && continue
    aws s3 cp --only-show-errors $W/orbit.compact.lrat.gz s3://$B/$PFX/h1/$TAG.compact.lrat.gz > $W/upload.out 2>&1
"""


class V3RetryWorkerTest(unittest.TestCase):
    def derive_template(self, source: bytes) -> bytes:
        import generate_h1_v3_retry_worker as module

        prior = module.KNOWN_V2_SHA256
        module.KNOWN_V2_SHA256 = module.sha256_bytes(source)
        try:
            return module.derive_worker(source)
        finally:
            module.KNOWN_V2_SHA256 = prior

    def test_namespace_precheck_and_create_only_publication(self) -> None:
        output = self.derive_template(V2_TEMPLATE.encode()).decode()
        self.assertIn("META=h1-fleet-v3", output)
        self.assertIn("head-object --bucket \"$B\"", output)
        self.assertIn("(404|NotFound|NoSuchKey)", output)
        self.assertIn("CERT-PRECHECK-FAIL", output)
        self.assertIn("indeterminate object state, stopping slot", output)
        self.assertIn("--key \"$PFX/h1/$tag.compact.lrat.gz\"", output)
        self.assertIn("put-object --bucket \"$B\"", output)
        self.assertIn("--if-none-match '*'", output)
        self.assertNotIn("h1-fleet-v2", output)
        self.assertNotIn("s3 cp --only-show-errors $W/orbit.compact.lrat.gz", output)

    def test_output_publication_is_create_only(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            output = Path(directory) / "worker.sh"
            atomic_write(output, b"first\n", 0o755)
            with self.assertRaises(FileExistsError):
                atomic_write(output, b"replacement\n", 0o755)
            self.assertEqual(output.read_bytes(), b"first\n")

    def test_source_change_is_rejected(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            source = Path(directory) / "worker.sh"
            source.write_bytes(b"snapshot")
            first = source.stat()
            changed = mock.Mock(**{
                name: getattr(first, name)
                for name in ("st_dev", "st_ino", "st_size", "st_mtime_ns", "st_mode")
            })
            changed.st_size += 1
            with mock.patch.object(worker_module.os, "fstat", side_effect=[first, changed]):
                with self.assertRaisesRegex(ValueError, "changed while being read"):
                    worker_module.stable_read(source)

    def test_wrong_source_hash_fails_closed(self) -> None:
        self.assertEqual(len(KNOWN_V2_SHA256), 64)
        with self.assertRaisesRegex(ValueError, "does not match"):
            derive_worker(b"not the audited worker")

    def test_source_shape_drift_fails_closed(self) -> None:
        malformed = V2_TEMPLATE.replace("META=h1-fleet-v2", "META=changed").encode()
        with self.assertRaisesRegex(ValueError, "namespace assignment"):
            self.derive_template(malformed)


if __name__ == "__main__":
    unittest.main()
