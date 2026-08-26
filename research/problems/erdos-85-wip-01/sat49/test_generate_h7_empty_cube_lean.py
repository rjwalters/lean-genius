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
    "h7_empty_lean", HERE / "generate_h7_empty_cube_lean.py")
MOD = importlib.util.module_from_spec(SPEC)
assert SPEC.loader is not None
SPEC.loader.exec_module(MOD)


class GenerateH7EmptyCubeLeanTest(unittest.TestCase):
    def test_receipts_are_strict_and_preserve_polarity(self):
        sha0 = "0" * 64
        sha1 = "1" * 64
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "receipts.tsv"
            path.write_text(
                f"cube_F6_t2.split-0 {sha0} {sha1} 123\n"
                f"cube_F6_t2.split-1 {sha1} {sha0} 456\n")
            rows = MOD.read_split_receipts(path)
            self.assertEqual(rows["cube_F6_t2.split-0"]["value"], 0)
            self.assertEqual(rows["cube_F6_t2.split-1"]["value"], 1)
            path.write_text(f"cube_F6_t2.split-x {sha0} {sha1} 123\n")
            with self.assertRaisesRegex(ValueError, "malformed split receipt"):
                MOD.read_split_receipts(path)

    def test_render_mixes_direct_and_zero_based_split_evidence(self):
        evidence = []
        includes = {}
        for edge_count, count in MOD.COUNTS.items():
            for index in range(count):
                job_id = f"cube_F{edge_count}_t{index}"
                job = {"id": job_id, "edge_count": edge_count,
                       "type_index": index, "kind": "direct"}
                if (edge_count, index) == (6, 2):
                    job.update(kind="binarySplit", split_variable=41)
                    for bit in (0, 1):
                        includes[f"{job_id}.split-{bit}"] = f"proofs/{bit}.lrat"
                else:
                    includes[job_id] = f"proofs/{job_id}.lrat"
                evidence.append(job)
        rendered = MOD.render(evidence, includes)
        self.assertIn("EmptyCubeSplitSatCnf 6 2 40 false", rendered)
        self.assertIn("EmptyCubeSplitSatCnf 6 2 40 true", rendered)
        self.assertIn(".binarySplit 40", rendered)
        self.assertEqual(rendered.count("native_decide"), 44)
        self.assertIn("of_evidenceVectors", rendered)
        self.assertIn("Fin 19", rendered)
        self.assertIn("Fin 2", rendered)

    def test_compressed_payload_gate_and_unpack(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            payload = root / "cube_F6_t0.lrat.gz"
            with gzip.open(payload, "wb") as stream:
                stream.write(b"1 0 0\n")
            metadata = {
                "lrat_gz_bytes": payload.stat().st_size,
                "lrat_gz_sha256": hashlib.sha256(payload.read_bytes()).hexdigest(),
            }
            accepted = MOD._gzip_payload(root, "cube_F6_t0", metadata)
            unpacked = root / "proofs" / "cube_F6_t0.lrat"
            MOD._unpack(accepted, unpacked)
            self.assertEqual(unpacked.read_bytes(), b"1 0 0\n")
            metadata["lrat_gz_sha256"] = "f" * 64
            with self.assertRaisesRegex(ValueError, "identity mismatch"):
                MOD._gzip_payload(root, "cube_F6_t0", metadata)

    def test_split_index_rejects_duplicates_values_and_variable_range(self):
        def record(parent="cube_F6_t2", variable=41, false=False, true=True):
            return {"parent_id": parent, "split_variable": variable, "leaves": [
                {"id": f"{parent}.split-0", "value": false},
                {"id": f"{parent}.split-1", "value": true},
            ]}
        missing = {"cube_F6_t2"}
        self.assertIn("cube_F6_t2", MOD.index_split_records(
            [record()], missing, 17633))
        with self.assertRaisesRegex(ValueError, "exactly the missing"):
            MOD.index_split_records([record(), record()], missing, 17633)
        with self.assertRaisesRegex(ValueError, "value/suffix"):
            MOD.index_split_records([record(false=0)], missing, 17633)
        with self.assertRaisesRegex(ValueError, "split variable"):
            MOD.index_split_records([record(variable=17634)], missing, 17633)


if __name__ == "__main__":
    unittest.main()
