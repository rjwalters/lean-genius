#!/usr/bin/env python3

import hashlib
import os
import sys
import tempfile
import unittest
from pathlib import Path
from unittest import mock

import generate_tierA_root_worker as module


TEMPLATE = f'''#!/usr/bin/env python3
import json
import os
import re
import subprocess
import sys
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
    mode = "quick"
{module.OLD_KIND_LINE}    cfg = CONFIG[kind]
{module.OLD_PREFLIGHT_BLOCK}
{module.OLD_WORK_ROOT}{module.OLD_HEADER_BLOCK}    return solved
'''


class RootWorkerTest(unittest.TestCase):
    def derive(self, text: str = TEMPLATE, work_root: Path = Path("/campaign/tierA-root-fresh")) -> str:
        source = text.encode()
        old = module.SOURCE_WORKER_SHA256
        module.SOURCE_WORKER_SHA256 = hashlib.sha256(source).hexdigest()
        try:
            return module.derive_worker(
                source, Path("/campaign/generator.py"), "1" * 64,
                Path("/campaign/manifest.json"), "2" * 64,
                work_root).decode()
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
        self.assertIn('work = Path("/campaign/tierA-root-fresh") / job', output)
        self.assertIn('lineage["queue_receipt_sha256"] == "' + module.APPROVED_QUEUE_RECEIPT_SHA256, output)
        self.assertIn('queue_sha256"] == "' + module.APPROVED_QUEUE_SHA256, output)
        self.assertIn('root campaign lineage marker missing or invalid', output)
        self.assertIn('if kind != "root":', output)
        self.assertLess(output.index('if kind != "root":'), output.index('work = Path('))
        namespace = {"__name__": "derived_test", "__file__": "/dev/null"}
        exec(output, namespace)
        self.assertEqual(namespace["run"](None, "h3_b1.nested.0", None, None), 64)
        self.assertFalse(Path("/campaign/tierA-root-fresh").exists())
        self.assertEqual(namespace["run"](None, "h3_b1.cube.0", None, None), 66)
        self.assertFalse(Path("/campaign/tierA-root-fresh/h3_b1.cube.0").exists())
        with mock.patch.dict(os.environ, {"TIERA_PREFLIGHT_ONLY": "1"}):
            self.assertEqual(namespace["run"](None, "h3_b1.cube.0", None, None), 0)
        self.assertNotIn("/usr/bin/sed", output)
        self.assertNotIn("header-rewrite", output)

    def test_wrong_source_and_shape_drift_fail_closed(self) -> None:
        with self.assertRaisesRegex(ValueError, "audited worker"):
            module.derive_worker(
                b"wrong", Path("/g"), "1" * 64, Path("/m"), "2" * 64, Path("/w"))
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

    def test_existing_work_namespace_fails_closed(self) -> None:
        with tempfile.TemporaryDirectory() as raw:
            path = Path(raw) / "occupied"
            path.mkdir()
            (path / "old-evidence").write_bytes(b"preserve")
            with self.assertRaisesRegex(ValueError, "already exists"):
                module.require_absent_work_root(path)
            self.assertEqual((path / "old-evidence").read_bytes(), b"preserve")

    def test_dangling_symlink_namespace_fails_closed(self) -> None:
        with tempfile.TemporaryDirectory() as raw:
            path = Path(raw) / "dangling"
            path.symlink_to(Path(raw) / "missing-target", target_is_directory=True)
            self.assertFalse(path.exists())
            with self.assertRaisesRegex(ValueError, "already exists"):
                module.require_absent_work_root(path)
            self.assertTrue(path.is_symlink())

    def test_malformed_noncanonical_and_wrong_marker_fail_before_job_path(self) -> None:
        with tempfile.TemporaryDirectory() as raw:
            work_root = Path(raw) / "work"
            work_root.mkdir()
            output = self.derive(work_root=work_root)
            namespace = {"__name__": "derived_test", "__file__": "/dev/null"}
            exec(output, namespace)
            marker = {
                "schema": module.LINEAGE_SCHEMA, "work_root": str(work_root),
                "worker_sha256": "", "worker_receipt_sha256": "1" * 64,
                "queue_receipt_sha256": module.APPROVED_QUEUE_RECEIPT_SHA256,
                "queue_sha256": module.APPROVED_QUEUE_SHA256,
                "root_manifest_sha256": module.APPROVED_ROOT_MANIFEST_SHA256,
                "freight_receipt_sha256": module.APPROVED_FREIGHT_RECEIPT_SHA256,
                "controller_git_commit": "2" * 40,
                "controller_source": module.CONTROLLER_SOURCE, "controller_sha256": "3" * 64,
            }
            encodings = [b"{", __import__("json").dumps(marker, indent=2).encode()]
            for field, value in (
                ("queue_sha256", "4" * 64), ("work_root", "/wrong"),
                ("controller_source", "research/wrong.py"),
                ("controller_git_commit", "not-a-commit"),
            ):
                wrong = marker.copy()
                wrong[field] = value
                encodings.append(module.canonical_json(wrong))
            extra = marker.copy()
            extra["extra"] = "forbidden"
            encodings.append(module.canonical_json(extra))
            for data in encodings:
                (work_root / "lineage.json").write_bytes(data)
                self.assertEqual(namespace["run"](None, "h3_b1.cube.0", None, None), 66)
                self.assertFalse((work_root / "h3_b1.cube.0").exists())
            (work_root / "lineage.json").write_bytes(module.canonical_json(marker))
            with self.assertRaises(FileNotFoundError):
                namespace["run"](None, "h3_b1.cube.0", None, None)

    def test_relative_cli_generator_is_embedded_and_receipted_absolute(self) -> None:
        with tempfile.TemporaryDirectory() as raw:
            root = Path(raw)
            source = root / "source.py"
            generator = root / "generator.py"
            manifest = root / "manifest.json"
            source.write_text(TEMPLATE)
            generator.write_bytes(b"generator")
            cells = {str(cell): {"jobs": [
                {"id": f"j{cell * 58 + offset}"} for offset in range(58)]}
                for cell in range(7)}
            manifest_data = {
                "schema": "erdos85-small-high-cube-jobs-v1",
                "freight_receipt_sha256": module.APPROVED_FREIGHT_RECEIPT_SHA256,
                "positive_cube_jobs": 392, "negative_cover_jobs": 14, "cells": cells,
            }
            manifest.write_text(__import__("json").dumps(manifest_data))
            output, receipt = root / "worker.py", root / "receipt.json"
            argv = ["generate", "--source-worker", "source.py",
                    "--root-generator", "generator.py",
                    "--expected-root-generator-sha256", module.sha256_file(generator),
                    "--root-manifest", "manifest.json",
                    "--expected-root-manifest-sha256", module.sha256_file(manifest),
                    "--expected-freight-receipt-sha256", module.APPROVED_FREIGHT_RECEIPT_SHA256,
                    "--output", "worker.py", "--receipt-output", "receipt.json",
                    "--work-root", "fresh-work"]
            old_cwd = Path.cwd()
            try:
                os.chdir(root)
                with mock.patch.object(sys, "argv", argv), \
                     mock.patch.object(module, "SOURCE_WORKER_SHA256", module.sha256_file(source)), \
                     mock.patch.object(module, "APPROVED_ROOT_GENERATOR_SHA256", module.sha256_file(generator)), \
                     mock.patch.object(module, "APPROVED_ROOT_MANIFEST_SHA256", module.sha256_file(manifest)), \
                     mock.patch.object(module, "git_identity", side_effect=[(root, "generator.py", "a" * 40),
                                                                            (root, "worker-generator.py", "a" * 40)]):
                    self.assertEqual(module.main(), 0)
            finally:
                os.chdir(old_cwd)
            receipt_data = __import__("json").loads(receipt.read_text())
            self.assertEqual(receipt_data["root_generator_path"], str(generator.resolve()))
            self.assertIn(f'Path("{generator.resolve()}")', output.read_text())
            self.assertIn(f'Path("{manifest.resolve()}")', output.read_text())
            self.assertEqual(receipt_data["work_root"], str((root / "fresh-work").resolve()))
            self.assertIn(
                f'work = Path("{(root / "fresh-work").resolve()}") / job', output.read_text())


if __name__ == "__main__":
    unittest.main()
