import importlib.util
import json
import sys
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch


HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
SPEC = importlib.util.spec_from_file_location(
    "nested_cube_lean", HERE / "generate_small_high_nested_cube_lean_module.py")
MOD = importlib.util.module_from_spec(SPEC)
assert SPEC.loader is not None
SPEC.loader.exec_module(MOD)


class GenerateNestedCubeLeanModuleTest(unittest.TestCase):
    def fixtures(self):
        cells = {}
        for cell in MOD.CELL_LEAN:
            jobs = [
                {"id": f"{cell}.cover-left", "kind": "cover-left"},
                {"id": f"{cell}.cover-right", "kind": "cover-right"},
            ]
            jobs += [
                {"id": f"{cell}.cube-{li}-{ri}", "kind": "cube",
                 "left_index": li, "right_index": ri, "units": [li, ri]}
                for li in range(7) for ri in range(8)
            ]
            cells[cell] = {"jobs": jobs}
        parent = {"cells": cells}
        hard_id = "h3_b1.cube-0-0"
        left, right = MOD.SELECTORS["h3_b1"]
        nested_jobs = [
            {"id": f"{hard_id}.nested.cover-left", "kind": "cover-left"},
            {"id": f"{hard_id}.nested.cover-right", "kind": "cover-right"},
        ]
        nested_jobs += [
            {"id": f"{hard_id}.nested.cube-{li}-{ri}", "kind": "cube",
             "left_index": li, "right_index": ri, "units": [li, ri]}
            for li in range(len(left)) for ri in range(len(right))
        ]
        nested = {"leaves": {hard_id: {
            "cell": "h3_b1", "left": list(left), "right": list(right),
            "jobs": nested_jobs,
        }}}
        return parent, nested, hard_id

    def test_render_exposes_three_and_five_high_strata(self):
        parent, nested, _ = self.fixtures()
        with tempfile.TemporaryDirectory() as raw:
            root = Path(raw)
            with patch.object(MOD, "payload_path",
                              side_effect=lambda _, job_id: root / f"{job_id}.lrat"):
                rendered = MOD.render(parent, nested, root, root,
                                      root / "Generated.lean")
        self.assertIn(
            "theorem orderFortyNineStratumExcluded_three_of_mixedCubeCertificates",
            rendered)
        self.assertIn(
            "smallHighH3C2Base_unsat smallHighH3Dist2Base_unsat", rendered)
        self.assertIn(
            "theorem orderFortyNineStratumExcluded_five_of_mixedCubeCertificates",
            rendered)
        self.assertIn(
            "smallHighH5T0Base_unsat smallHighH5T1Base_unsat", rendered)

    def test_render_replaces_selected_nested_payload_with_third_grid(self):
        parent, nested, hard_id = self.fixtures()
        nested_id = f"{hard_id}.nested.cube-0-0"
        third_jobs = [
            {"id": f"{nested_id}.third.cover-left", "kind": "cover-left"},
            {"id": f"{nested_id}.third.cover-right", "kind": "cover-right"},
        ]
        third_jobs += [
            {"id": f"{nested_id}.third.cube-{li}-{ri}", "kind": "cube",
             "left_index": li, "right_index": ri}
            for li in range(8) for ri in range(8)
        ]
        third = {"leaves": {nested_id: {"jobs": third_jobs}}}
        with tempfile.TemporaryDirectory() as raw:
            root = Path(raw)
            with patch.object(MOD, "payload_path",
                              side_effect=lambda _, job_id: root / f"{job_id}.lrat"):
                rendered = MOD.render(parent, nested, root, root,
                                      root / "Generated.lean", third)
        stem = MOD.lean_stem(nested_id)
        self.assertIn(
            f"theorem {MOD.lean_stem(nested_id + '.third-grid')} :", rendered)
        self.assertIn(f"theorem {stem}_unsat :", rendered)
        self.assertIn(
            f"exact {MOD.lean_stem(nested_id + '.third.cube-7-7')}_unsat",
            rendered)
        self.assertNotIn(f"def {stem}Proof", rendered)

    def test_load_validates_bound_third_manifest(self):
        parent, nested, hard_id = self.fixtures()
        parent["schema"] = "erdos85-small-high-cube-jobs-v1"
        for cell in parent["cells"].values():
            for job in cell["jobs"]:
                job.setdefault("units", [])
        nested["schema"] = "erdos85-small-high-nested-cube-jobs-v1"
        nested_leaf = nested["leaves"][hard_id]
        nested_leaf["parent_units"] = [11, 12]
        nested_id = f"{hard_id}.nested.cube-0-0"
        with tempfile.TemporaryDirectory() as raw:
            root = Path(raw)
            parent_path = root / "parent.json"
            nested_path = root / "nested.json"
            third_path = root / "third.json"
            parent_path.write_text(json.dumps(parent))
            nested["parent_manifest_sha256"] = MOD.sha256(parent_path)
            nested_path.write_text(json.dumps(nested))
            nested_job = next(
                job for job in nested_leaf["jobs"] if job["id"] == nested_id)
            third = {
                "schema": "erdos85-small-high-third-cube-jobs-v1",
                "parent_manifest_sha256": MOD.sha256(nested_path),
                "leaves": {nested_id: {
                    "cell": "h3_b1",
                    "parent_units": [*nested_leaf["parent_units"],
                                     *nested_job["units"]],
                    "left": list(MOD.THIRD_LEFT),
                    "right": list(MOD.THIRD_RIGHT),
                    "jobs": MOD.third_jobs(nested_id),
                }},
            }
            third_path.write_text(json.dumps(third))
            with patch.object(MOD, "payload_path",
                              side_effect=lambda _, job_id: root / f"{job_id}.lrat"):
                loaded = MOD.load_and_validate(
                    parent_path, nested_path, root, third_path)
            self.assertEqual(loaded[2], third)
            third["leaves"][nested_id]["jobs"][-1]["id"] += ".wrong"
            third_path.write_text(json.dumps(third))
            with patch.object(MOD, "payload_path",
                              side_effect=lambda _, job_id: root / f"{job_id}.lrat"):
                with self.assertRaisesRegex(ValueError, "malformed or incomplete"):
                    MOD.load_and_validate(parent_path, nested_path, root, third_path)


if __name__ == "__main__":
    unittest.main()
