"""Control tests use temporary text files and Python children, never Lean."""
import json
import os
import sys
import tempfile
import threading
import time
import unittest
from unittest.mock import patch
from pathlib import Path

import audit
import prepare
import run


class Controls(unittest.TestCase):
    def test_nested_comments_and_strings(self):
        text = '/- import Proofs.Bad /- nested -/ -/\nimport Proofs.Good -- import Proofs.Bad\ndef s := "-- /-"\n'
        clean = prepare.uncomment(text)
        self.assertNotIn("Proofs.Bad", clean)
        self.assertIn("import Proofs.Good", clean)
        self.assertIn('"-- /-"', clean)

    def test_unterminated_comment_rejected(self):
        with self.assertRaises(ValueError):
            prepare.uncomment("/- unclosed")

    def test_complete_project_closure(self):
        actual = prepare.closure(prepare.ROOT)
        baseline = json.loads((prepare.ROOT / "research/problems/erdos-85-wip-01/release_assembly_20261011/source-manifest.json").read_text())["sources"]
        self.assertEqual(set(actual), set(baseline))
        self.assertEqual(len(actual), 893)
        for row in actual.values():
            self.assertTrue(set(row["dependencies"]) <= actual.keys())

    def test_cyclic_graph_rejected(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            src = root / "proofs/Proofs"
            src.mkdir(parents=True)
            (src / (prepare.ENDPOINT + ".lean")).write_text("import Proofs.Foo\n")
            (src / "Foo.lean").write_text("import Proofs." + prepare.ENDPOINT + "\n")
            with self.assertRaisesRegex(ValueError, "Cyclic"):
                prepare.closure(root)

    def test_axiom_admission_and_duplicate_rejected(self):
        for text in ["'x' depends on axioms: [sorryAx]", "'x' depends on axioms: [propext, propext]"]:
            with self.assertRaises(ValueError):
                run.exports(text)
        self.assertEqual(run.exports("'x' depends on axioms: [Quot.sound, propext]"),
                         [{"theorem": "x", "axioms": ["Quot.sound", "propext"]}])

    def test_timeout_records_failure(self):
        with tempfile.TemporaryDirectory() as tmp:
            log = Path(tmp) / "slow.log"
            with self.assertRaises(RuntimeError):
                run.command_run([sys.executable, "-c", "import time;time.sleep(30)"], log,
                                dict(os.environ), time.monotonic() + 0.1, threading.Event())
            self.assertEqual(json.loads(log.with_suffix(".json").read_text())["stop_reason"], "TIMEOUT")

    def test_nonzero_exit_records_failure(self):
        with tempfile.TemporaryDirectory() as tmp:
            log = Path(tmp) / "bad.log"
            with self.assertRaises(RuntimeError):
                run.command_run([sys.executable, "-c", "raise SystemExit(7)"], log,
                                dict(os.environ), time.monotonic() + 5, threading.Event())
            self.assertEqual(json.loads(log.with_suffix(".json").read_text())["returncode"], 7)

    def test_stop_records_failure(self):
        with tempfile.TemporaryDirectory() as tmp:
            stop = threading.Event()
            stop.set()
            log = Path(tmp) / "stop.log"
            with self.assertRaises(RuntimeError):
                run.command_run([sys.executable, "-c", "import time;time.sleep(30)"], log,
                                dict(os.environ), time.monotonic() + 10, stop)
            self.assertEqual(json.loads(log.with_suffix(".json").read_text())["stop_reason"], "STOP")

    def test_existing_output_refused(self):
        with tempfile.TemporaryDirectory() as tmp:
            with self.assertRaises(FileExistsError):
                run.build({}, Path(tmp))

    def test_large_certificates_cannot_overlap(self):
        self.assertGreater(2 * run.weight("Erdos85OrderFortyNineSevenHighT1Rep0Certificate"), 96)

    def test_failed_bundle_never_passes_audit(self):
        with tempfile.TemporaryDirectory() as tmp:
            out = Path(tmp)
            (out / "RUN.json").write_text('{"status":"FAILED"}')
            with self.assertRaisesRegex(ValueError, "not complete"):
                audit.audit({}, out)

    def test_package_revision_drift_rejected(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            (root / "proofs").mkdir()
            (root / "proofs/lake-manifest.json").write_text(json.dumps({
                "packagesDir": ".lake/packages", "packages": [{"name": "mathlib", "rev": "expected"}]}))
            with patch.object(run.subprocess, "check_output", return_value="different\n"):
                with self.assertRaisesRegex(ValueError, "revision mismatch"):
                    run.package_revisions(root)

    def test_runner_drift_rejected(self):
        plan = {"sources": {}, "config_sha256": {}, "runner_sha256": {"run.py": "0" * 64}}
        with patch.object(run, "closure", return_value={}):
            with self.assertRaisesRegex(ValueError, "Runner drift"):
                run.validate_inputs(plan, prepare.ROOT)

    def test_source_drift_rejected(self):
        with patch.object(run, "closure", return_value={"changed": {}}):
            with self.assertRaisesRegex(ValueError, "Source/dependency drift"):
                run.validate_inputs({"sources": {}}, prepare.ROOT)

    def test_real_accepted_endpoint_axiom_format(self):
        root = prepare.ROOT / "research/problems/erdos-85-wip-01"
        expected = json.loads((root / "order49_h3_closed_capstone_20261008/PLAN.json").read_text())["exports"]
        raw = (root / "release_assembly_20261011/evidence1/Erdos85FiniteDropCapstone.log").read_text()
        actual = run.exports(raw)
        self.assertEqual(actual, expected)
        self.assertEqual([len(row["axioms"]) for row in actual], [601, 607, 604])


if __name__ == "__main__":
    unittest.main()
