import hashlib
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

import materialize_capacity_gap as target


class CapacityGapMaterializerTests(unittest.TestCase):
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


if __name__ == "__main__":
    unittest.main()
