#!/usr/bin/env python3

import importlib.util
import sys
import unittest
from pathlib import Path, PurePosixPath


HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
SPEC = importlib.util.spec_from_file_location(
    "freight_validator", HERE / "validate_h7_fleet_freight.py")
assert SPEC and SPEC.loader
MOD = importlib.util.module_from_spec(SPEC); SPEC.loader.exec_module(MOD)


class FreightValidatorTests(unittest.TestCase):
    def test_safe_relative_accepts_scoped_path(self) -> None:
        self.assertEqual(MOD.safe_relative("manifests/x.json", "manifests"),
                         PurePosixPath("manifests/x.json"))

    def test_safe_relative_rejects_escape_and_wrong_scope(self) -> None:
        for value, prefix in (("/tmp/x", None), ("../x", None),
                              ("specs/x", "manifests"), ("manifests/a/x", "manifests")):
            with self.assertRaises(ValueError):
                MOD.safe_relative(value, prefix)


if __name__ == "__main__":
    unittest.main()
