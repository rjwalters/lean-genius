import importlib.util
import json
import tempfile
import unittest
from pathlib import Path


HERE = Path(__file__).resolve().parent
SPEC = importlib.util.spec_from_file_location(
    "cube_lean", HERE / "generate_small_high_cube_lean_module.py")
MOD = importlib.util.module_from_spec(SPEC)
assert SPEC.loader is not None
SPEC.loader.exec_module(MOD)


class GenerateCubeLeanModuleTest(unittest.TestCase):
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


if __name__ == "__main__":
    unittest.main()
