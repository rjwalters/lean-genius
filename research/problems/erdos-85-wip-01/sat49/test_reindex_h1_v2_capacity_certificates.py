#!/usr/bin/env python3

import unittest
from dataclasses import replace
from pathlib import Path
from tempfile import TemporaryDirectory

from generate_h1_v2_lean_stubs import IndexRow
from reindex_h1_v2_capacity_certificates import reindex_rows, render_index, row_fields


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


if __name__ == "__main__":
    unittest.main()
