import importlib.util
import gzip
import hashlib
import sys
import tempfile
import unittest
from pathlib import Path


HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
SPEC = importlib.util.spec_from_file_location(
    "run_h7_cadical_lrat", HERE / "run_h7_cadical_lrat.py")
MOD = importlib.util.module_from_spec(SPEC)
assert SPEC.loader is not None
SPEC.loader.exec_module(MOD)


class RunH7CadicalLratTest(unittest.TestCase):
    def test_canonical_receipt_accepts_all_campaign_id_forms(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            cnf, proof = root / "job.cnf", root / "proof.lrat.gz"
            cnf.write_bytes(b"p cnf 1 2\n1 0\n-1 0\n")
            with proof.open("wb") as raw:
                with gzip.GzipFile(filename="", mode="wb", fileobj=raw,
                                   mtime=0) as stream:
                    stream.write(b"3 0 1 2 0\n")
            for job_id in ("cube_F6_t2", "cube_F6_t2.split-0",
                           "cube_F6_t2.adaptive.leaf-010"):
                receipt = MOD.canonical_receipt(job_id, cnf, proof)
                self.assertTrue(receipt.startswith(job_id + " "))
                self.assertIn(hashlib.sha256(cnf.read_bytes()).hexdigest(), receipt)
            with self.assertRaisesRegex(ValueError, "invalid H7 job id"):
                MOD.canonical_receipt("cube_F6_t2.bad", cnf, proof)


if __name__ == "__main__":
    unittest.main()
