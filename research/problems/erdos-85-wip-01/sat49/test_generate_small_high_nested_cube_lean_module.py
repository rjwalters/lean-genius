import importlib.util
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
    def test_render_exposes_three_and_five_high_strata(self):
        cells = {}
        for cell in MOD.CELL_LEAN:
            jobs = [
                {"id": f"{cell}.cover-left", "kind": "cover-left"},
                {"id": f"{cell}.cover-right", "kind": "cover-right"},
            ]
            jobs += [
                {"id": f"{cell}.cube-{li}-{ri}", "kind": "cube",
                 "left_index": li, "right_index": ri}
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
             "left_index": li, "right_index": ri}
            for li in range(len(left)) for ri in range(len(right))
        ]
        nested = {"leaves": {hard_id: {
            "cell": "h3_b1", "left": list(left), "right": list(right),
            "jobs": nested_jobs,
        }}}
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


if __name__ == "__main__":
    unittest.main()
