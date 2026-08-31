#!/usr/bin/env python3

import importlib.util
import subprocess
import unittest
from pathlib import Path
from unittest.mock import patch


HERE = Path(__file__).resolve().parent
SPEC = importlib.util.spec_from_file_location(
    "selector_contract", HERE / "validate_small_high_selector_contract.py")
MOD = importlib.util.module_from_spec(SPEC)
assert SPEC.loader is not None
SPEC.loader.exec_module(MOD)


class ValidateSmallHighSelectorContractTest(unittest.TestCase):
    def lean_output(self, values):
        return (f"noise\n{MOD.BEGIN}\n#[" + ", ".join(map(str, values)) +
                f"]\n{MOD.END}\n")

    def test_validate_accepts_exact_live_contract(self):
        expected = MOD.expected_values(MOD.load_python_selectors())
        completed = subprocess.CompletedProcess(
            args=[], returncode=0, stdout=self.lean_output(expected), stderr="")
        with patch.object(MOD, "run_lean", return_value=completed):
            receipt = MOD.validate()
        self.assertEqual(receipt["status"], "PASS")
        self.assertEqual(receipt["cells"], 7)
        self.assertEqual(receipt["selector_literals"], len(expected))

    def test_validate_rejects_value_mismatch(self):
        expected = MOD.expected_values(MOD.load_python_selectors())
        expected[17] += 1
        completed = subprocess.CompletedProcess(
            args=[], returncode=0, stdout=self.lean_output(expected), stderr="")
        with patch.object(MOD, "run_lean", return_value=completed):
            with self.assertRaisesRegex(ValueError, "selector mismatch"):
                MOD.validate()

    def test_parser_rejects_ambiguous_output(self):
        with self.assertRaisesRegex(ValueError, "delimiters"):
            MOD.parse_lean_values(f"{MOD.BEGIN}\n{MOD.BEGIN}\n{MOD.END}\n")

    def test_validate_reports_lean_failure(self):
        completed = subprocess.CompletedProcess(
            args=[], returncode=1, stdout="", stderr="type error")
        with patch.object(MOD, "run_lean", return_value=completed):
            with self.assertRaisesRegex(ValueError, "type error"):
                MOD.validate()


if __name__ == "__main__":
    unittest.main()
