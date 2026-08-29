#!/usr/bin/env python3

import tempfile
import unittest
from contextlib import redirect_stdout
from io import StringIO
from pathlib import Path
from unittest.mock import patch

from generate_h1_v2_lean_stubs import (
    CAPACITY_PROFILE_COUNTS,
    RAW_PROFILE_COUNTS,
    EXPECTED_COLUMNS,
    IndexRow,
    lean_source,
    main,
    read_inventory,
    worker_tag,
)


ROW = IndexRow(
    "0123456789abcdef", 2, 17, *("0" * 64,) * 3, 1, 2, 3, True,
    "0" * 64, 4, "0" * 64, 5, "0" * 64, 6,
)


class StubCapacityContractTest(unittest.TestCase):
    @staticmethod
    def write_inventory(path: Path, counts: tuple[int, ...]) -> None:
        path.write_text("".join(
            f"{profile} " + " ".join(["0"] * 24) + "\n"
            for profile, count in enumerate(counts)
            for _ in range(count)
        ))

    def test_capacity_table_is_default(self) -> None:
        source = lean_source(ROW, Path("proof.lrat.lz4p7"))
        self.assertIn("(oneHighCapacityInventoryTables (2 : Fin 5)).get", source)
        self.assertNotIn("(oneHighInventoryTables (2 : Fin 5)).get", source)

    def test_raw_table_requires_explicit_legacy_mode(self) -> None:
        source = lean_source(
            ROW, Path("proof.lrat.lz4p7"), legacy_raw_inventory=True
        )
        self.assertIn("(oneHighInventoryTables (2 : Fin 5)).get", source)
        self.assertNotIn("oneHighCapacityInventoryTables", source)

    def test_inventory_count_contract_is_selected_explicitly(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            inventory = Path(directory) / "inventory.compact"
            for expected in (CAPACITY_PROFILE_COUNTS, RAW_PROFILE_COUNTS):
                with self.subTest(expected=expected):
                    self.write_inventory(inventory, expected)
                    self.assertEqual(
                        tuple(map(len, read_inventory(inventory, expected))), expected
                    )
                    wrong = (
                        RAW_PROFILE_COUNTS
                        if expected == CAPACITY_PROFILE_COUNTS
                        else CAPACITY_PROFILE_COUNTS
                    )
                    with self.assertRaisesRegex(
                        ValueError, "unexpected inventory profile counts"
                    ):
                        read_inventory(inventory, wrong)

    def test_cli_emits_capacity_stub_and_binds_inventory_receipt(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            inventory = root / "capacity.compact"
            self.write_inventory(inventory, CAPACITY_PROFILE_COUNTS)
            tag = worker_tag((0,) * 24)
            packed_sha = "0" * 64
            payload = root / "cert-root" / "packed" / "00" / (
                packed_sha + ".lrat.lz4p7"
            )
            payload.parent.mkdir(parents=True)
            payload.write_bytes(b"packed")
            values = {
                "orbit": tag,
                "profile": "BBBB",
                "localIndex": "0",
                "compact_lrat_sha256": "1" * 64,
                "raw_lrat_sha256": "2" * 64,
                "cnf_sha256": "3" * 64,
                "lrat_actions": "1",
                "source_cnf_clauses": "2",
                "compact_bytes": "3",
                "stub_ready": "1",
                "binary_lrat_sha256": "4" * 64,
                "binary_bytes": "4",
                "lz4_frame_sha256": "5" * 64,
                "lz4_frame_bytes": "5",
                "packed_lz4_sha256": packed_sha,
                "packed_lz4_bytes": "6",
            }
            index = root / "index.tsv"
            index.write_text(
                "\t".join(EXPECTED_COLUMNS) + "\n" +
                "\t".join(values[column] for column in EXPECTED_COLUMNS) + "\n"
            )
            output = root / "lean"
            receipt = root / "receipt.json"
            argv = [
                "generate_h1_v2_lean_stubs.py", "--index", str(index),
                "--cert-root", str(root / "cert-root"), "--inventory", str(inventory),
                "--output-dir", str(output), "--orbit", tag,
                "--skip-payload-hash", "--manifest-output", str(receipt),
            ]
            with patch("sys.argv", argv), redirect_stdout(StringIO()):
                self.assertEqual(main(), 0)
            source = (output / "Erdos85H1V2CertP0I00000.lean").read_text()
            self.assertIn("(oneHighCapacityInventoryTables (0 : Fin 5)).get", source)
            manifest = receipt.read_text()
            self.assertIn('"inventory_kind": "capacity"', manifest)
            self.assertIn('"inventory_sha256":', manifest)


if __name__ == "__main__":
    unittest.main()
