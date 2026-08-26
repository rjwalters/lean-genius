import importlib.util
import sys
import unittest
from pathlib import Path


HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
SPEC = importlib.util.spec_from_file_location(
    "h7_hybrid", HERE / "generate_h7_t0_cube_one_binary_hybrid_lean.py")
MOD = importlib.util.module_from_spec(SPEC)
assert SPEC.loader is not None
SPEC.loader.exec_module(MOD)


class GenerateH7BinaryHybridLeanTest(unittest.TestCase):
    def test_render_uses_override_in_exact_grid_slot(self):
        jobs = [
            {"id": "h7_t0_cube1.cover-left", "kind": "cover-left"},
            {"id": "h7_t0_cube1.cover-right", "kind": "cover-right"},
        ]
        jobs += [
            {"id": f"h7_t0_cube1.cube-{li}-{ri}", "kind": "cube",
             "left_index": li, "right_index": ri}
            for li in range(8) for ri in range(8)
        ]
        override_id = "h7_t0_cube1.cube-0-0"
        overrides = {override_id: {
            "module": "Proofs.Generated.H7Cube00",
            "theorem": "h7CubeOneH7T0Cube1Cube00BinaryUnsat",
        }}
        direct = {job["id"]: f"certs/{job['id']}.lrat" for job in jobs
                  if job["id"] != override_id}
        rendered = MOD.render({"jobs": jobs}, overrides, direct)
        self.assertEqual(rendered.count("native_decide"), 65)
        self.assertEqual(rendered.count("import Proofs.Generated.H7Cube00\n"), 1)
        self.assertIn("· exact h7CubeOneH7T0Cube1Cube00BinaryUnsat", rendered)
        self.assertIn(
            "orderFortyNineStratumExcluded_seven_of_binaryHybridCertificates",
            rendered)


if __name__ == "__main__":
    unittest.main()
