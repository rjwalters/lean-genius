import csv
import importlib.util
import json
import tempfile
import unittest
from pathlib import Path


HERE = Path(__file__).resolve().parent
SPEC = importlib.util.spec_from_file_location(
    "socket_table", HERE / "validate_socket_table.py")
MOD = importlib.util.module_from_spec(SPEC)
assert SPEC.loader is not None
SPEC.loader.exec_module(MOD)


class ValidateSocketTableTest(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.root = Path(self.temporary.name)
        self.expected = self.root / "expected.txt"
        self.table = self.root / "sockets.tsv"
        self.expected.write_text(json.dumps({
            "version": 1,
            "sockets": [
                {"hypothesis": "Erdos85.h1Leaf0",
                 "campaign_manifest_rows": ["queue:h1:0"]},
                {"hypothesis": "Erdos85.h1Leaf1",
                 "campaign_manifest_rows": ["queue:h1:1"]},
            ],
        }))
        self.rows = [self.row("Erdos85.h1Leaf0", "queue:h1:0", "b", "d"),
                     self.row("Erdos85.h1Leaf1", "queue:h1:1", "e", "f")]

    def tearDown(self):
        self.temporary.cleanup()

    @staticmethod
    def row(hypothesis, manifest_row, cnf="b", receipt="d"):
        return {
            "hypothesis": hypothesis,
            "theorem": f"{hypothesis}Checked",
            "source_module": "Proofs.Generated.Socket",
            "commit": "a" * 40,
            "campaign_manifest_rows": f'["{manifest_row}"]',
            "cnf_sha256": cnf * 64,
            "compact_lrat_sha256": "c" * 64,
            "replay_receipt": receipt * 64,
            "review_id": "#1155",
        }

    def write(self, rows=None, fields=MOD.FIELDS):
        with self.table.open("w", newline="") as stream:
            writer = csv.DictWriter(
                stream, fieldnames=fields, delimiter="\t", extrasaction="ignore")
            writer.writeheader()
            writer.writerows(self.rows if rows is None else rows)

    def test_accepts_exact_bijection(self):
        self.write()
        self.assertEqual(MOD.validate(self.table, self.expected), 2)
        receipt = MOD.evidence_receipt(self.table, self.expected, 2)
        self.assertRegex(
            receipt,
            r"^PASS schema=erdos85-sat49-socket-table-v1 sockets=2 "
            r"table_sha256=[0-9a-f]{64} expected_manifest_sha256=[0-9a-f]{64} "
            r"identity_sha256=[0-9a-f]{64}$",
        )

    def test_receipt_hashes_exact_input_bytes(self):
        self.write()
        before = MOD.evidence_receipt(self.table, self.expected, 2)
        self.table.write_bytes(self.table.read_bytes() + b"\n")
        after_table = MOD.evidence_receipt(self.table, self.expected, 2)
        self.assertNotEqual(before, after_table)
        self.table.write_bytes(self.table.read_bytes()[:-1])
        self.expected.write_bytes(self.expected.read_bytes() + b" ")
        after_expected = MOD.evidence_receipt(self.table, self.expected, 2)
        self.assertNotEqual(before, after_expected)

    def test_rejects_missing_unknown_and_duplicate_hypotheses(self):
        for rows in ([self.rows[0]],
                     [self.rows[0], self.row("Erdos85.unknown", "queue:x")],
                     [self.rows[0], self.row("Erdos85.h1Leaf0", "queue:x")]):
            with self.subTest(rows=rows):
                self.write(rows)
                with self.assertRaises(MOD.SocketTableError):
                    MOD.validate(self.table, self.expected)

    def test_rejects_reused_manifest_row(self):
        self.rows[1]["campaign_manifest_rows"] = '["queue:h1:0"]'
        self.write()
        with self.assertRaises(MOD.SocketTableError):
            MOD.validate(self.table, self.expected)

    def test_rejects_manifest_row_not_bound_by_frozen_expectation(self):
        self.rows[0]["campaign_manifest_rows"] = '["queue:invented"]'
        self.write()
        with self.assertRaisesRegex(MOD.SocketTableError, "frozen expectation"):
            MOD.validate(self.table, self.expected)

    def test_rejects_reused_leaf_receipt(self):
        self.rows[1]["replay_receipt"] = self.rows[0]["replay_receipt"]
        self.write()
        with self.assertRaisesRegex(MOD.SocketTableError, "replay receipts"):
            MOD.validate(self.table, self.expected)

    def test_rejects_placeholder_and_malformed_identities(self):
        mutations = (
            ("commit", "abc"),
            ("cnf_sha256", "0" * 63),
            ("replay_receipt", "TBD"),
            ("review_id", "0"),
            ("campaign_manifest_rows", "[]"),
        )
        for field, value in mutations:
            with self.subTest(field=field):
                rows = [dict(row) for row in self.rows]
                rows[0][field] = value
                self.write(rows)
                with self.assertRaises(MOD.SocketTableError):
                    MOD.validate(self.table, self.expected)

    def test_rejects_header_drift(self):
        self.write(fields=MOD.FIELDS[:-1])
        with self.assertRaisesRegex(MOD.SocketTableError, "header"):
            MOD.validate(self.table, self.expected)


if __name__ == "__main__":
    unittest.main()
