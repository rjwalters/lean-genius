#!/usr/bin/env python3

import hashlib
import tempfile
import unittest
from pathlib import Path

import generate_h7_empty_cube_manifest as manifest


class H7EmptyCubeManifestTest(unittest.TestCase):
    def test_receipts_accept_valid_and_ignore_failures(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            ledger = Path(directory) / "events"
            ledger.write_text(
                "compactcube F=6 type=0 UNSAT_CERT_FAILED drat_trim=0\n"
                "compactcube F=6 type=0 UNSAT_CERT solve_s=9 "
                f"cnf_sha={'1' * 64} lrat_gz_sha={'2' * 64} "
                "lrat_gz_bytes=123\n")
            self.assertEqual(manifest.accepted_receipts(ledger), {
                (6, 0): {
                    "cnf_sha256": "1" * 64,
                    "lrat_gz_sha256": "2" * 64,
                    "lrat_gz_bytes": 123,
                }
            })

    def test_conflicting_receipts_rejected(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            ledger = Path(directory) / "events"
            row = ("compactcube F=6 type=0 UNSAT_CERT solve_s=9 "
                   f"cnf_sha={'1' * 64} lrat_gz_sha={{}} lrat_gz_bytes=123\n")
            ledger.write_text(row.format("2" * 64) + row.format("3" * 64))
            with self.assertRaisesRegex(ValueError, "conflicting"):
                manifest.accepted_receipts(ledger)

    def test_canonical_tsv_receipt_is_consumable(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            receipts = Path(directory) / "receipts.tsv"
            receipts.write_text(
                "# id cnf_sha256 lrat_gz_sha256 lrat_gz_bytes\n"
                f"cube_F7_t1 {'1' * 64} {'2' * 64} 456\n")
            self.assertEqual(manifest.accepted_receipts(receipts), {
                (7, 1): {
                    "cnf_sha256": "1" * 64,
                    "lrat_gz_sha256": "2" * 64,
                    "lrat_gz_bytes": 456,
                }
            })

    def test_malformed_canonical_tsv_receipt_is_rejected(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            receipts = Path(directory) / "receipts.tsv"
            receipts.write_text("cube_F7_t1 truncated\n")
            with self.assertRaisesRegex(ValueError, "malformed"):
                manifest.accepted_receipts(receipts)

    def test_cube_identity_is_header_plus_units(self) -> None:
        base = b"p cnf 4 2\n1 0\n"
        prefix = hashlib.sha256(base)
        digest, size = manifest.cube_identity(prefix, len(base), [2, -3])
        expected = b"p cnf 4 2\n1 0\n2 0\n-3 0\n"
        self.assertEqual(digest, hashlib.sha256(expected).hexdigest())
        self.assertEqual(size, len(expected))


if __name__ == "__main__":
    unittest.main()
