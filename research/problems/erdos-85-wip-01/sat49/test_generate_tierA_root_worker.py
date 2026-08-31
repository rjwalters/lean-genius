#!/usr/bin/env python3

import hashlib
import tempfile
import unittest
from pathlib import Path

import generate_tierA_root_worker as module


TEMPLATE = f'''#!/usr/bin/env python3
import json
import subprocess
from pathlib import Path
C = Path("/campaign")
CONFIG = {{
    "root": {{
        "generator": {module.OLD_GENERATOR_PATH},
        "generator_sha": "{module.OLD_GENERATOR_SHA256}",
        "manifest": {module.OLD_MANIFEST_PATH},
        "manifest_sha": "{module.OLD_MANIFEST_SHA256}",
    }},
}}
def sha(path): return ""
def publish(a, b): pass
def fail(*args): return 1
def run(work, job, cfg, emitted):
{module.OLD_HEADER_BLOCK}    return solved
'''


class RootWorkerTest(unittest.TestCase):
    def derive(self, text: str = TEMPLATE) -> str:
        source = text.encode()
        old = module.SOURCE_WORKER_SHA256
        module.SOURCE_WORKER_SHA256 = hashlib.sha256(source).hexdigest()
        try:
            return module.derive_worker(
                source, Path("/campaign/generator.py"), "1" * 64,
                Path("/campaign/manifest.json"), "2" * 64).decode()
        finally:
            module.SOURCE_WORKER_SHA256 = old

    def test_rebinds_root_and_removes_header_rewrite(self) -> None:
        output = self.derive()
        self.assertIn('Path("/campaign/generator.py")', output)
        self.assertIn('Path("/campaign/manifest.json")', output)
        self.assertIn('"generator_sha": "' + "1" * 64 + '"', output)
        self.assertIn('"manifest_sha": "' + "2" * 64 + '"', output)
        self.assertIn('publish(emitted, solved)', output)
        self.assertIn('root_record["variables"]', output)
        self.assertNotIn("/usr/bin/sed", output)
        self.assertNotIn("header-rewrite", output)

    def test_wrong_source_and_shape_drift_fail_closed(self) -> None:
        with self.assertRaisesRegex(ValueError, "audited worker"):
            module.derive_worker(
                b"wrong", Path("/g"), "1" * 64, Path("/m"), "2" * 64)
        with self.assertRaisesRegex(ValueError, "header rewrite block"):
            self.derive(TEMPLATE.replace("sed = subprocess.run", "other = subprocess.run"))

    def test_manifest_requires_exact_406_unique_jobs_and_pins(self) -> None:
        with tempfile.TemporaryDirectory() as raw:
            root = Path(raw)
            path = root / "manifest.json"
            cells = {}
            index = 0
            for cell in range(7):
                count = 58
                cells[str(cell)] = {
                    "jobs": [{"id": f"j{index + offset}"} for offset in range(count)]}
                index += count
            manifest = {
                "schema": "erdos85-small-high-cube-jobs-v1",
                "freight_receipt_sha256": module.APPROVED_FREIGHT_RECEIPT_SHA256,
                "positive_cube_jobs": 392, "negative_cover_jobs": 14,
                "cells": cells,
            }
            path.write_text(__import__("json").dumps(manifest))
            digest = module.sha256_file(path)
            module.validate_manifest(path, digest, module.APPROVED_FREIGHT_RECEIPT_SHA256)
            manifest["cells"]["6"]["jobs"][-1]["id"] = "j0"
            path.write_text(__import__("json").dumps(manifest))
            with self.assertRaisesRegex(ValueError, "406 unique"):
                module.validate_manifest(
                    path, module.sha256_file(path), module.APPROVED_FREIGHT_RECEIPT_SHA256)

    def test_approved_pins_are_hard_constants(self) -> None:
        pins = [module.APPROVED_ROOT_GENERATOR_SHA256,
                module.APPROVED_ROOT_MANIFEST_SHA256,
                module.APPROVED_FREIGHT_RECEIPT_SHA256]
        module.validate_approved_pins(*pins)
        for index, label in enumerate(("root generator", "root manifest", "freight receipt")):
            wrong = pins.copy()
            wrong[index] = "1" * 64
            with self.assertRaisesRegex(ValueError, label):
                module.validate_approved_pins(*wrong)

    def test_create_only_preserves_existing_output(self) -> None:
        with tempfile.TemporaryDirectory() as raw:
            path = Path(raw) / "worker.py"
            path.write_bytes(b"existing")
            with self.assertRaisesRegex(ValueError, "already exists"):
                module.create_only_write(path, b"new", 0o755)
            self.assertEqual(path.read_bytes(), b"existing")
            self.assertEqual(list(path.parent.glob(".*.tmp")), [])

    def test_cleanup_does_not_unlink_replacement(self) -> None:
        with tempfile.TemporaryDirectory() as raw:
            path = Path(raw) / "worker.py"
            identity = module.create_only_write(path, b"ours", 0o755)
            path.unlink()
            path.write_bytes(b"replacement")
            module.unlink_if_same_file(path, identity)
            self.assertEqual(path.read_bytes(), b"replacement")


if __name__ == "__main__":
    unittest.main()
