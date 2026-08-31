import importlib.util
import json
import hashlib
import tempfile
import unittest
from unittest import mock
from pathlib import Path


HERE = Path(__file__).resolve().parent
SPEC = importlib.util.spec_from_file_location(
    "cube_lean", HERE / "generate_small_high_cube_lean_module.py")
MOD = importlib.util.module_from_spec(SPEC)
assert SPEC.loader is not None
SPEC.loader.exec_module(MOD)


class GenerateCubeLeanModuleTest(unittest.TestCase):
    def production_fixture(self, root):
        cells, payloads = {}, []
        for cell in MOD.CELL_LEAN:
            jobs = [{"id": f"{cell}.cover-left", "kind": "cover-left"},
                    {"id": f"{cell}.cover-right", "kind": "cover-right"}]
            jobs += [{"id": f"{cell}.cube-{li}-{ri}", "kind": "cube",
                      "left_index": li, "right_index": ri}
                     for li in range(7) for ri in range(8)]
            cells[cell] = {"jobs": jobs}
            for job in jobs:
                path = root / f"{job['id']}.lrat"; path.write_text("0\n")
                payloads.append({"job_id": job["id"], "path": str(path),
                                 "sha256": MOD.sha256(path)})
        manifest = root / "manifest.json"
        manifest.write_bytes(MOD.canonical({"schema": "erdos85-small-high-cube-jobs-v1",
            "cells": cells, "lean_commit": MOD.APPROVED_ROOT_COMMIT,
            "freight_receipt_sha256": MOD.APPROVED_FREIGHT_RECEIPT_SHA256}))
        MOD.APPROVED_ROOT_MANIFEST_SHA256 = MOD.sha256(manifest)  # synthetic fixture only
        payload_manifest = root / "payloads.json"
        payload_manifest.write_bytes(MOD.canonical({"schema": MOD.PAYLOAD_SCHEMA,
            "root_manifest_sha256": MOD.sha256(manifest), "payloads": payloads}))
        return manifest, payload_manifest
    def test_complete_manifest_renders_all_checks_and_grids(self):
        with tempfile.TemporaryDirectory() as raw:
            root = Path(raw)
            cells = {}
            for cell in MOD.CELL_LEAN:
                jobs = [
                    {"id": f"{cell}.cover-left", "kind": "cover-left"},
                    {"id": f"{cell}.cover-right", "kind": "cover-right"},
                ]
                jobs += [{"id": f"{cell}.cube-{li}-{ri}", "kind": "cube",
                          "left_index": li, "right_index": ri}
                         for li in range(7) for ri in range(8)]
                cells[cell] = {"jobs": jobs}
                for job in jobs:
                    (root / f"{job['id']}.lrat").write_text("0\n")
            path = root / "manifest.json"
            path.write_text(json.dumps({
                "schema": "erdos85-small-high-cube-jobs-v1", "cells": cells}))
            manifest = MOD.load_and_validate(path, root)
            rendered = MOD.render(
                manifest, root, root, root / "Generated.lean")
            # Two theorems per job, then one grid and one base theorem per cell.
            self.assertEqual(rendered.count("theorem smallHighH"), 826)
            self.assertEqual(rendered.count("native_decide"), 406)
            self.assertEqual(rendered.count("CheckedCubeGrid"), 7)
            self.assertIn("smallHighH3B1Cube00_unsat", rendered)
            self.assertIn("smallHighH5T2Base_unsat", rendered)
            self.assertIn(
                "orderFortyNineStratumExcluded_three_of_cubeCertificates",
                rendered)
            self.assertIn(
                "orderFortyNineStratumExcluded_five_of_cubeCertificates",
                rendered)
            self.assertIn(
                "orderFortyNineGeneratedVariableHighSatCnf (5 : Fin 50) "
                "orderFortyNineFiveHighT0Masks",
                rendered)
            self.assertNotIn("orderFortyNineGeneratedH5SatCnf", rendered)
            self.assertNotIn(str(root), rendered)
            self.assertIn('(include_str "h3_b1.cover-left.lrat")', rendered)

    def test_missing_payload_is_rejected(self):
        with tempfile.TemporaryDirectory() as raw:
            root = Path(raw)
            path = root / "manifest.json"
            path.write_text(json.dumps({
                "schema": "erdos85-small-high-cube-jobs-v1", "cells": {}}))
            with self.assertRaisesRegex(ValueError, "seven checked cells"):
                MOD.load_and_validate(path, root)

    def test_worker_job_layout_is_accepted(self):
        with tempfile.TemporaryDirectory() as raw:
            root = Path(raw)
            job = root / "h3_b1.cube-0-0"
            job.mkdir()
            payload = job / "job.lrat"
            payload.write_text("0\n")
            self.assertEqual(
                MOD.payload_path(root, "h3_b1.cube-0-0"), payload.resolve())

    def test_production_inputs_and_create_only_module_receipt(self):
        with tempfile.TemporaryDirectory() as raw:
            root = Path(raw); manifest, payloads = self.production_fixture(root)
            value, rows = MOD.validate_production_inputs(
                manifest, MOD.sha256(manifest), root, root,
                payloads, MOD.sha256(payloads))
            output = root / "Generated.lean"
            source = MOD.render(value, root, root, output).encode()
            MOD.atomic_create(output, source)
            with self.assertRaises(FileExistsError): MOD.atomic_create(output, b"drift")
            self.assertEqual(len(rows), 406)
            self.assertEqual(output.read_bytes(), source)

    def test_main_publishes_module_then_canonical_receipt_and_refuses_existing(self):
        with tempfile.TemporaryDirectory() as raw:
            root = Path(raw); manifest, payloads = self.production_fixture(root)
            output = root / "Generated.lean"
            argv = ["generator", "--manifest", str(manifest),
                "--manifest-sha256", MOD.sha256(manifest),
                "--certificate-dir", str(root), "--payload-manifest", str(payloads),
                "--payload-manifest-sha256", MOD.sha256(payloads),
                "--include-root", str(root), "--output", str(output)]
            with mock.patch("sys.argv", argv): self.assertEqual(MOD.main(), 0)
            receipt_path = Path(str(output) + ".receipt.json")
            receipt = json.loads(receipt_path.read_text())
            self.assertEqual(receipt_path.read_bytes(), MOD.canonical(receipt))
            self.assertEqual(receipt["module_sha256"], MOD.sha256(output))
            with mock.patch("sys.argv", argv), self.assertRaises(SystemExit): MOD.main()

    def test_main_detects_render_time_payload_mutation_before_publication(self):
        with tempfile.TemporaryDirectory() as raw:
            root = Path(raw); manifest, payloads = self.production_fixture(root)
            output = root / "Generated.lean"
            argv = ["generator", "--manifest", str(manifest),
                "--manifest-sha256", MOD.sha256(manifest),
                "--certificate-dir", str(root), "--payload-manifest", str(payloads),
                "--payload-manifest-sha256", MOD.sha256(payloads),
                "--include-root", str(root), "--output", str(output)]
            real_render = MOD.render
            def mutate(*args):
                rendered = real_render(*args)
                (root / "h3_b1.cover-left.lrat").write_text("changed")
                return rendered
            with mock.patch("sys.argv", argv), mock.patch.object(MOD, "render", mutate), self.assertRaises(ValueError):
                MOD.main()
            self.assertFalse(output.exists())
            self.assertFalse(Path(str(output) + ".receipt.json").exists())

    def test_receipt_last_rechecks_mutation_during_module_publication(self):
        with tempfile.TemporaryDirectory() as raw:
            root = Path(raw); manifest, payloads = self.production_fixture(root)
            output = root / "Generated.lean"
            argv = ["generator", "--manifest", str(manifest),
                "--manifest-sha256", MOD.sha256(manifest),
                "--certificate-dir", str(root), "--payload-manifest", str(payloads),
                "--payload-manifest-sha256", MOD.sha256(payloads),
                "--include-root", str(root), "--output", str(output)]
            real_atomic = MOD.atomic_create
            calls = 0
            def mutate(path, value):
                nonlocal calls
                calls += 1; real_atomic(path, value)
                if calls == 1: (root / "h3_b1.cover-left.lrat").write_text("changed")
            with mock.patch("sys.argv", argv), mock.patch.object(MOD, "atomic_create", mutate), self.assertRaises(ValueError):
                MOD.main()
            self.assertTrue(output.exists())
            self.assertFalse(Path(str(output) + ".receipt.json").exists())

    def test_production_rejects_payload_mutation_symlink_and_manifest_drift(self):
        with tempfile.TemporaryDirectory() as raw:
            root = Path(raw); manifest, payloads = self.production_fixture(root)
            document = json.loads(payloads.read_text())
            Path(document["payloads"][0]["path"]).write_text("mutated")
            with self.assertRaisesRegex(ValueError, "payload SHA mismatch"):
                MOD.validate_production_inputs(manifest, MOD.sha256(manifest), root,
                                               root, payloads, MOD.sha256(payloads))
        with tempfile.TemporaryDirectory() as raw:
            root = Path(raw); manifest, payloads = self.production_fixture(root)
            target = root / "h3_b1.cover-left.lrat"
            real = root / "real.lrat"; target.rename(real); target.symlink_to(real)
            with self.assertRaisesRegex(ValueError, "non-symlink"):
                MOD.validate_production_inputs(manifest, MOD.sha256(manifest), root,
                                               root, payloads, MOD.sha256(payloads))
        with tempfile.TemporaryDirectory() as raw:
            root = Path(raw); manifest, payloads = self.production_fixture(root)
            with self.assertRaisesRegex(ValueError, "approved SHA"):
                MOD.validate_production_inputs(manifest, "9" * 64, root, root,
                                               payloads, MOD.sha256(payloads))


if __name__ == "__main__":
    unittest.main()
