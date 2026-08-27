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
            cells[cell] = {
                "base": f"/fixture/{cell}.cnf",
                "base_sha256": cell * 8,
                "variables": 500,
                "base_clauses": 2,
                "jobs": MOD.jobs_for(cell),
            }
        parent = {"cells": cells}
        hard_id = "h3_b1.cube-0-0"
        left, right = MOD.SELECTORS["h3_b1"]
        parent_job = next(
            job for job in cells["h3_b1"]["jobs"] if job["id"] == hard_id)
        nested = {"leaves": {hard_id: {
            "cell": "h3_b1", "left": list(left), "right": list(right),
            "base": cells["h3_b1"]["base"],
            "base_sha256": cells["h3_b1"]["base_sha256"],
            "variables": cells["h3_b1"]["variables"],
            "base_clauses": cells["h3_b1"]["base_clauses"],
            "parent_units": parent_job["units"],
            "jobs": MOD.nested_jobs(hard_id, left, right),
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
        nested["schema"] = "erdos85-small-high-nested-cube-jobs-v1"
        nested_leaf = nested["leaves"][hard_id]
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

    def test_load_rejects_tampered_parent_and_nested_records(self):
        parent, nested, hard_id = self.fixtures()
        parent["schema"] = "erdos85-small-high-cube-jobs-v1"
        nested["schema"] = "erdos85-small-high-nested-cube-jobs-v1"
        with tempfile.TemporaryDirectory() as raw:
            root = Path(raw)
            parent_path = root / "parent.json"
            nested_path = root / "nested.json"
            parent_path.write_text(json.dumps(parent))
            nested["parent_manifest_sha256"] = MOD.sha256(parent_path)

            nested["leaves"][hard_id]["parent_units"] = [999]
            nested_path.write_text(json.dumps(nested))
            with patch.object(MOD, "payload_path",
                              side_effect=lambda _, job_id: root / f"{job_id}.lrat"):
                with self.assertRaisesRegex(ValueError, "leaf metadata mismatch"):
                    MOD.load_and_validate(parent_path, nested_path, root)

            parent, nested, hard_id = self.fixtures()
            parent["schema"] = "erdos85-small-high-cube-jobs-v1"
            nested["schema"] = "erdos85-small-high-nested-cube-jobs-v1"
            parent_path.write_text(json.dumps(parent))
            nested["parent_manifest_sha256"] = MOD.sha256(parent_path)
            nested["leaves"][hard_id]["jobs"][-1]["units"] = [999, 1000]
            nested_path.write_text(json.dumps(nested))
            with patch.object(MOD, "payload_path",
                              side_effect=lambda _, job_id: root / f"{job_id}.lrat"):
                with self.assertRaisesRegex(ValueError, "malformed or incomplete nested"):
                    MOD.load_and_validate(parent_path, nested_path, root)

            parent, nested, hard_id = self.fixtures()
            parent["schema"] = "erdos85-small-high-cube-jobs-v1"
            nested["schema"] = "erdos85-small-high-nested-cube-jobs-v1"
            parent["cells"]["h3_c1"]["jobs"][-1]["units"] = [999, 1000]
            parent_path.write_text(json.dumps(parent))
            nested["parent_manifest_sha256"] = MOD.sha256(parent_path)
            nested_path.write_text(json.dumps(nested))
            with patch.object(MOD, "payload_path",
                              side_effect=lambda _, job_id: root / f"{job_id}.lrat"):
                with self.assertRaisesRegex(ValueError, "malformed or incomplete parent"):
                    MOD.load_and_validate(parent_path, nested_path, root)


if __name__ == "__main__":
    unittest.main()
