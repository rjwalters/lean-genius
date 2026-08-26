#!/usr/bin/env python3

import importlib.util
import unittest
from pathlib import Path


HERE = Path(__file__).resolve().parent
SPEC = importlib.util.spec_from_file_location(
    "h1_refinement_pin", HERE / "generate_h1_refinement_pin_lean.py")
MOD = importlib.util.module_from_spec(SPEC)
assert SPEC.loader is not None
SPEC.loader.exec_module(MOD)


class GenerateH1RefinementPinLeanTest(unittest.TestCase):
    def test_complete_bank_has_unbounded_resource_envelope(self):
        records = [
            (0, {"profile": 1}, Path("unused"), []),
            (1, {"profile": 3}, Path("unused"), []),
        ]
        source = MOD.bank_text(records)
        marker = "theorem h1OddProfileRefinementPinBank :"
        self.assertIn(
            "set_option maxHeartbeats 0 in\n"
            "set_option maxRecDepth 1000000 in\n" + marker,
            source,
        )
        self.assertEqual(source.count("set_option maxHeartbeats 0 in"), 1)
        self.assertEqual(source.count("set_option maxRecDepth 1000000 in"), 1)
        self.assertEqual(
            source.count(
                "simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem"
            ),
            2,
        )


if __name__ == "__main__":
    unittest.main()
