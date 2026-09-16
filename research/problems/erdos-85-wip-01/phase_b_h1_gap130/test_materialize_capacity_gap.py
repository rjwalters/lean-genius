import hashlib
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

import materialize_capacity_gap as target


class CapacityGapMaterializerTests(unittest.TestCase):
    @staticmethod
    def first_outside_id():
        rows = json.loads(target.MANIFEST.read_text())["rows"]
        return next(row["id"] for row in rows if row["class"] == "outside_frozen_phase_b")

    @staticmethod
    def fake_native(manifest, manifest_sha, case_id, output_dir, *, corrupt=False):
        row = target.select(case_id)
        output_dir.mkdir()
        cnf = output_dir / "input.cnf"
        cnf.write_bytes(b"p cnf 1 1\n1 0\n")
        result = {
            "id": case_id, "tag": row["tag"], "profile": row["profile"],
            "manifest_sha256": manifest_sha, "status": "materialized",
            "solver_launched": False, "container_absent": True,
            "cnf_path": str(cnf), "cnf_sha256": target.sha(cnf.read_bytes()),
            "cnf_bytes": cnf.stat().st_size,
        }
        (output_dir / "receipt.json").write_text(json.dumps(result))
        if corrupt:
            cnf.write_bytes(cnf.read_bytes() + b"c changed after native return\n")
        return result

    def test_all_34_adapters_match_reviewed_native_selector(self):
        rows = json.loads(target.MANIFEST.read_text())["rows"]
        outside = [row for row in rows if row["class"] == "outside_frozen_phase_b"]
        self.assertEqual(len(outside), 34)
        with tempfile.TemporaryDirectory() as temp:
            path = Path(temp) / "one.json"
            for row in outside:
                selected = target.select(row["id"])
                raw = target.one_row_manifest(selected)
                path.write_bytes(raw)
                native_row, _, prior_hash = target.native.select_input(
                    path, hashlib.sha256(raw).hexdigest(), row["id"])
                self.assertEqual(native_row["table_values"], row["table_values"])
                self.assertEqual(native_row["tag"], row["tag"])
                self.assertIsNone(prior_hash)

    def test_historical_and_unknown_ids_are_rejected(self):
        rows = json.loads(target.MANIFEST.read_text())["rows"]
        historical = next(row for row in rows if row["class"].startswith("historical"))
        with self.assertRaisesRegex(ValueError, "absent from the 34"):
            target.select(historical["id"])
        with self.assertRaisesRegex(ValueError, "absent from the 34"):
            target.select("h1_0000000000000000")

    def test_manifest_byte_drift_is_rejected_before_native_work(self):
        rows = json.loads(target.MANIFEST.read_text())["rows"]
        case_id = next(row["id"] for row in rows if row["class"] == "outside_frozen_phase_b")
        with tempfile.TemporaryDirectory() as temp:
            changed = Path(temp) / "gap130.json"
            changed.write_bytes(target.MANIFEST.read_bytes() + b" ")
            with patch.object(target, "MANIFEST", changed):
                with self.assertRaisesRegex(ValueError, "manifest bytes changed"):
                    target.select(case_id)

    def test_native_cnf_bytes_are_read_back_before_success(self):
        with tempfile.TemporaryDirectory() as temp:
            output = Path(temp) / "case"
            with patch.object(target.native, "materialize", side_effect=self.fake_native):
                result = target.materialize(self.first_outside_id(), output)
            self.assertEqual(result["status"], "materialized")
            self.assertEqual(result["cnf_sha256"], target.sha((output / "native/input.cnf").read_bytes()))
            self.assertEqual(result["cnf_bytes"], (output / "native/input.cnf").stat().st_size)
            self.assertEqual(len(result["adapter_source_sha256"]), 64)
            self.assertEqual(len(result["freeze_source_sha256"]), 64)

    def test_mutated_native_cnf_is_an_error(self):
        with tempfile.TemporaryDirectory() as temp:
            output = Path(temp) / "case"
            with patch.object(target.native, "materialize",
                              side_effect=lambda *args: self.fake_native(*args, corrupt=True)):
                with self.assertRaisesRegex(ValueError, "Native CNF bytes differ"):
                    target.materialize(self.first_outside_id(), output)
            binding = json.loads((output / "binding.json").read_text())
            self.assertEqual(binding["status"], "ERROR")
            self.assertFalse(binding["solver_launched"])
            self.assertNotIn("cnf_sha256", binding)

    def test_native_receipt_drift_is_an_error(self):
        def tamper(*args):
            result = self.fake_native(*args)
            receipt = Path(args[3]) / "receipt.json"
            value = json.loads(receipt.read_text())
            value["container_absent"] = False
            receipt.write_text(json.dumps(value))
            return result

        with tempfile.TemporaryDirectory() as temp:
            output = Path(temp) / "case"
            with patch.object(target.native, "materialize", side_effect=tamper):
                with self.assertRaisesRegex(ValueError, "Native receipt differs"):
                    target.materialize(self.first_outside_id(), output)
            self.assertEqual(json.loads((output / "binding.json").read_text())["status"], "ERROR")


if __name__ == "__main__":
    unittest.main()
