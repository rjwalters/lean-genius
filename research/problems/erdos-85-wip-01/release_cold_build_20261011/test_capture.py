"""Offline evidence-collector tests; no cloud calls or Lean builds."""
import io
import subprocess
import tarfile
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

import capture


class CaptureTests(unittest.TestCase):
    def archive(self, root, name, symbolic=False):
        path = root / "test.tar.gz"
        with tarfile.open(path, "w:gz") as tar:
            item = tarfile.TarInfo(name)
            if symbolic:
                item.type = tarfile.SYMTYPE
                item.linkname = "/tmp/escape"
                tar.addfile(item)
            else:
                item.size = 3
                tar.addfile(item, io.BytesIO(b"abc"))
        return path

    def test_regular_bundle_extracts(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            capture.safe_extract(self.archive(root, "run-output/test.log"), root / "out")
            self.assertEqual((root / "out/run-output/test.log").read_bytes(), b"abc")

    def test_traversal_rejected(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            with self.assertRaises(ValueError):
                capture.safe_extract(self.archive(root, "run-output/../../escape"), root / "out")

    def test_link_rejected(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            with self.assertRaises(ValueError):
                capture.safe_extract(self.archive(root, "run-output/link", True), root / "out")

    def test_missing_exit_is_not_restarted_or_collected(self):
        with tempfile.TemporaryDirectory() as tmp, patch.object(capture, "remote") as remote:
            remote.side_effect = subprocess.CalledProcessError(1, ["cat", "exit"])
            with self.assertRaisesRegex(RuntimeError, "do not restart"):
                capture.collect("20261011T215126-commit-8d4f59c82e40-9322", "a" * 40, Path(tmp) / "out")
            self.assertEqual(remote.call_count, 1)
            self.assertFalse((Path(tmp) / "out").exists())

    def test_host_commit_mismatch_refused(self):
        with tempfile.TemporaryDirectory() as tmp, patch.object(capture, "remote") as remote:
            remote.side_effect = [subprocess.CompletedProcess([], 0, stdout=b"0\n"),
                                  subprocess.CompletedProcess([], 0, stdout=b"b" * 40 + b"\n")]
            with self.assertRaisesRegex(ValueError, "commit differs"):
                capture.collect("20261011T215126-commit-8d4f59c82e40-9322", "a" * 40, Path(tmp) / "out")
            self.assertEqual(remote.call_count, 2)


if __name__ == "__main__":
    unittest.main()
