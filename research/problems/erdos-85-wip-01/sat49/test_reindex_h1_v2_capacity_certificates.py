#!/usr/bin/env python3

import unittest
from dataclasses import replace
from pathlib import Path
from tempfile import TemporaryDirectory

from generate_h1_v2_lean_stubs import IndexRow
from reindex_h1_v2_capacity_certificates import (
    reindex_loaded_rows, reindex_rows, render_index, require_unchanged,
    require_distinct_paths, require_fresh_outputs, row_fields, sha256,
)


ROW = IndexRow(
    "0123456789abcdef", 2, 99, "1" * 64, "2" * 64, "3" * 64,
    None, 7, 8, True, "4" * 64, 9, "5" * 64, 10, "6" * 64, 11,
)


class CapacityReindexTest(unittest.TestCase):
    def test_render_round_trips_all_evidence_fields(self) -> None:
        text = render_index([replace(ROW, local_index=17)])
        self.assertIn("0123456789abcdef\tAABB\t17\t", text)
        self.assertIn("\t\t7\t8\t1\t", text)

    def test_row_fields_replaces_only_operational_index(self) -> None:
        fields = row_fields(replace(ROW, local_index=17))
        self.assertEqual(fields[0:3], [ROW.orbit, "AABB", "17"])
        self.assertEqual(fields[-1], "11")

    def test_family_local_collisions_are_rekeyed_by_tag(self) -> None:
        second = replace(ROW, orbit="fedcba9876543210")
        with TemporaryDirectory() as directory:
            first_path = Path(directory) / "first.tsv"
            second_path = Path(directory) / "second.tsv"
            first_path.write_text(render_index([ROW]))
            second_path.write_text(render_index([second]))
            rows = reindex_rows(
                [first_path, second_path],
                {ROW.orbit: (2, 17), second.orbit: (2, 23)},
                require_complete=True,
            )
        self.assertEqual(
            [(row.orbit, row.local_index) for row in rows],
            [(ROW.orbit, 17), (second.orbit, 23)],
        )

    def test_outside_capacity_fails_closed(self) -> None:
        with TemporaryDirectory() as directory:
            path = Path(directory) / "index.tsv"
            path.write_text(render_index([ROW]))
            with self.assertRaisesRegex(ValueError, "outside the capacity inventory"):
                reindex_rows([path], {})
            self.assertEqual(reindex_rows([path], {}, drop_outside_capacity=True), [])

    def test_complete_mode_rejects_missing_capacity_tag(self) -> None:
        with TemporaryDirectory() as directory:
            path = Path(directory) / "index.tsv"
            path.write_text(render_index([ROW]))
            with self.assertRaisesRegex(ValueError, "1 missing row"):
                reindex_rows(
                    [path],
                    {ROW.orbit: (2, 17), "fedcba9876543210": (2, 23)},
                    require_complete=True,
                )

    def test_duplicate_outside_capacity_tag_is_rejected(self) -> None:
        with TemporaryDirectory() as directory:
            first_path = Path(directory) / "first.tsv"
            second_path = Path(directory) / "second.tsv"
            first_path.write_text(render_index([ROW]))
            second_path.write_text(render_index([ROW]))
            with self.assertRaisesRegex(ValueError, "duplicate certificate orbit"):
                reindex_rows(
                    [first_path, second_path], {}, drop_outside_capacity=True
                )

    def test_loaded_rows_are_reused_without_rereading_inputs(self) -> None:
        rows = reindex_loaded_rows(
            [[ROW]], {ROW.orbit: (2, 17)}, require_complete=True,
        )
        self.assertEqual(rows, [replace(ROW, local_index=17)])

    def test_input_drift_is_rejected(self) -> None:
        with TemporaryDirectory() as directory:
            path = Path(directory) / "index.tsv"
            path.write_text(render_index([ROW]))
            expected = sha256(path)
            require_unchanged([path], [expected])
            path.write_text(render_index([replace(ROW, compact_bytes=9)]))
            with self.assertRaisesRegex(ValueError, "input changed"):
                require_unchanged([path], [expected])

    def test_input_output_and_receipt_aliases_are_rejected(self) -> None:
        with TemporaryDirectory() as directory:
            root = Path(directory)
            inventory = root / "inventory"
            index = root / "index"
            output = root / "output"
            receipt = root / "receipt"
            require_distinct_paths([inventory, index], output, receipt)
            cases = (
                ([inventory, inventory], output, receipt),
                ([inventory, index], inventory, receipt),
                ([inventory, index], output, index),
                ([inventory, index], output, output),
            )
            for inputs, candidate_output, candidate_receipt in cases:
                with self.subTest(
                    output=candidate_output, receipt=candidate_receipt,
                ), self.assertRaisesRegex(ValueError, "paths alias"):
                    require_distinct_paths(
                        inputs, candidate_output, candidate_receipt,
                    )

    def test_outputs_must_be_fresh(self) -> None:
        with TemporaryDirectory() as directory:
            root = Path(directory)
            output = root / "output"
            receipt = root / "receipt"
            require_fresh_outputs(output, receipt)
            for existing, other in ((output, receipt), (receipt, output)):
                existing.write_text("stale")
                with self.subTest(existing=existing), self.assertRaisesRegex(
                    ValueError, "must not already exist",
                ):
                    require_fresh_outputs(output, receipt)
                existing.unlink()


if __name__ == "__main__":
    unittest.main()
