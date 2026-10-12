"""Exercise target selection and failure propagation without running Lean."""
import os
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest


class SafeSubsetTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        root = Path(self.tmp.name)
        proofs = root / "proofs"
        (proofs / "scripts").mkdir(parents=True)
        (proofs / "Proofs").mkdir()
        self.script = proofs / "scripts/build-safe-subset.sh"
        shutil.copyfile(Path(__file__).with_name("build-safe-subset.sh"), self.script)
        for name in ("KeepOne", "KeepTwo", "Erdos30WIP01", "BirthdayProblemOQ03OQ01OQ01",
                     "AngleTrisectionOQ02OQ01OQ02Incomplete01Aristotle"):
            (proofs / "Proofs" / (name + ".lean")).touch()
        bindir = root / "bin"
        bindir.mkdir()
        lake = bindir / "lake"
        lake.write_text('#!/bin/sh\nprintf "%s\\n" "$@" >> "$TEST_LAKE_ARGS"\nexit 23\n')
        lake.chmod(0o755)
        self.args = root / "lake.args"
        self.env = dict(os.environ, PATH=str(bindir) + os.pathsep + os.environ["PATH"],
                        TEST_LAKE_ARGS=str(self.args))

    def test_one_build_propagates_failure_and_omits_quarantined_targets(self):
        result = subprocess.run(["bash", str(self.script)], env=self.env, capture_output=True)
        self.assertEqual(result.returncode, 23)
        self.assertEqual(self.args.read_text().splitlines(),
                         ["build", "Proofs.KeepOne", "Proofs.KeepTwo"])

    def test_list_has_same_scope_without_invoking_lake(self):
        result = subprocess.run(["bash", str(self.script), "--list"],
                                env=self.env, text=True, capture_output=True, check=True)
        self.assertEqual(result.stdout.splitlines(), ["Proofs.KeepOne", "Proofs.KeepTwo"])
        self.assertFalse(self.args.exists())


if __name__ == "__main__":
    unittest.main()
