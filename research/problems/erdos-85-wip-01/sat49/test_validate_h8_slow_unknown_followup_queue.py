#!/usr/bin/env python3

import importlib.util
import sys
import unittest
from pathlib import Path


HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
SPEC = importlib.util.spec_from_file_location(
    "h8validator", HERE / "validate_h8_slow_unknown_followup_queue.py")
assert SPEC and SPEC.loader
MOD = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MOD)


class ValidatorTests(unittest.TestCase):
    def test_source_row_requires_exactly_one_match(self) -> None:
        row = {"id": "job", "manifest": "m"}
        self.assertEqual(MOD.source_row({"jobs": [row]}, "job"), row)
        for jobs in ([], [row, row]):
            with self.assertRaisesRegex(ValueError, "not unique"):
                MOD.source_row({"jobs": jobs}, "job")


if __name__ == "__main__":
    unittest.main()
