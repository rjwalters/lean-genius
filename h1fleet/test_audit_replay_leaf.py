import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))

from audit_replay_leaf import parse_axioms
from replay_common import ReplayError


class AxiomReportTests(unittest.TestCase):
    theorem = "Erdos85.oneHighFamilyV2CheckedUnsat_of_extension_lrat"
    # Captured from lean4-arm64:v4.31.0 with the frozen import-data overlay.
    observed = (
        "'Erdos85.oneHighFamilyV2CheckedUnsat_of_extension_lrat' "
        "depends on axioms: [propext, Classical.choice, Quot.sound]\n"
    )

    def test_pinned_image_report(self):
        self.assertEqual(parse_axioms(self.observed, self.theorem),
                         ["propext", "Classical.choice", "Quot.sound"])

    def test_multiline_native_report(self):
        name = "Erdos85.h1V2P2I00000Checked"
        native = "Erdos85.h1V2P2I00000Check._native.native_decide.ax_1"
        self.assertEqual(parse_axioms(
            f"'{name}' depends on axioms: [propext,\n {native}]\n", name),
            ["propext", native])

    def test_rejects_duplicate_reports_in_either_format(self):
        legacy = f"axioms {self.theorem} : [propext]\n"
        for extra in (self.observed, legacy):
            with self.subTest(extra=extra), self.assertRaisesRegex(
                    ReplayError, "found 2"):
                parse_axioms(self.observed + extra, self.theorem)

    def test_rejects_wrong_name_or_embedded_text(self):
        for output in (self.observed.replace(self.theorem, self.theorem + "Other"),
                       "error: " + self.observed,
                       self.observed.rstrip() + " extra\n"):
            with self.subTest(output=output), self.assertRaisesRegex(
                    ReplayError, "found 0"):
                parse_axioms(output, self.theorem)

    def test_rejects_duplicate_or_invalid_axioms(self):
        for body in ("propext, propext", "propext, invalid axiom"):
            with self.subTest(body=body), self.assertRaises(ReplayError):
                parse_axioms(f"'{self.theorem}' depends on axioms: [{body}]",
                             self.theorem)

    def test_cli_reads_observed_report_from_worker_json_log(self):
        with tempfile.TemporaryDirectory() as raw:
            root = Path(raw)
            source, log, output = (root / name for name in
                                   ("module.lean", "worker.log", "audit.json"))
            source.write_text(f"#print axioms {self.theorem}\n")
            log.write_text(json.dumps({"argv": ["lean", str(source)],
                                       "returncode": 0, "stdout": self.observed,
                                       "stderr": ""}) + "\n")
            result = subprocess.run([
                sys.executable, str(HERE / "audit_replay_leaf.py"),
                "--source", str(source), "--log", str(log),
                "--theorem", self.theorem, "--output", str(output),
            ], text=True, capture_output=True)
            self.assertEqual(result.returncode, 0, result.stderr)
            receipt = json.loads(output.read_text())
            self.assertEqual(receipt["axioms"],
                             ["propext", "Classical.choice", "Quot.sound"])
            self.assertIs(receipt["sorry_ax"], False)


if __name__ == "__main__":
    unittest.main()
