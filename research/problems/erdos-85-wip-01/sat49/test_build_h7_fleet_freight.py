#!/usr/bin/env python3

import importlib.util
import tempfile
import unittest
from pathlib import Path


HERE = Path(__file__).resolve().parent
SPEC = importlib.util.spec_from_file_location("freight", HERE / "build_h7_fleet_freight.py")
assert SPEC and SPEC.loader
MOD = importlib.util.module_from_spec(SPEC); SPEC.loader.exec_module(MOD)


class FreightTests(unittest.TestCase):
    def test_rejects_wrong_cardinality(self) -> None:
        with tempfile.TemporaryDirectory() as raw:
            with self.assertRaisesRegex(ValueError, "232 source jobs"):
                MOD.relative_rows({"jobs": []}, Path(raw))

    def test_rejects_path_escape_before_hashing(self) -> None:
        with tempfile.TemporaryDirectory() as raw:
            root = Path(raw)
            row = {"manifest": str(root / "outside.json"),
                   "spec": str(root / "specs/x.json")}
            with self.assertRaisesRegex(ValueError, "manifest escapes"):
                MOD.relative_rows({"jobs": [row] * 232}, root)


if __name__ == "__main__":
    unittest.main()
