import csv
import hashlib
import importlib.util
import json
import tempfile
import unittest
from pathlib import Path


HERE = Path(__file__).resolve().parent
SPEC = importlib.util.spec_from_file_location(
    "cell_receipts", HERE / "build_small_high_cell_aggregate_receipts.py")
MOD = importlib.util.module_from_spec(SPEC)
assert SPEC.loader is not None
SPEC.loader.exec_module(MOD)


class SmallHighCellAggregateReceiptsTest(unittest.TestCase):
    def fixture(self, root: Path):
        module_name = "Proofs.Generated.Erdos85OrderFortyNineSmallHighCertificates"
        module = root / "Erdos85OrderFortyNineSmallHighCertificates.lean"
        manifest = {"schema": "erdos85-small-high-cube-jobs-v1", "cells": {}}
        expected = {"version": 1, "sockets": []}
        rows = []
        theorem_lines = []
        for _, cell, base_theorem in MOD.CELLS:
            jobs = MOD.expected_job_ids(cell)
            manifest["cells"][cell] = {"jobs": [{"id": job} for job in jobs]}
            for number, job in enumerate(jobs):
                stem = "leaf_" + job.replace(".", "_").replace("-", "_")
                hypothesis = f"Erdos85.{stem}_unsat"
                theorem = f"Erdos85.{stem}_check"
                expected["sockets"].append({
                    "hypothesis": hypothesis, "campaign_manifest_rows": [job]})
                rows.append({
                    "hypothesis": hypothesis,
                    "theorem": theorem,
                    "source_module": module_name,
                    "commit": f"{len(rows) + 1:040x}",
                    "campaign_manifest_rows": json.dumps([job]),
                    "cnf_sha256": f"{len(rows) + 1:064x}",
                    "compact_lrat_sha256": f"{len(rows) + 501:064x}",
                    "replay_receipt": f"{len(rows) + 1001:064x}",
                    "review_id": f"#{number + 1}",
                })
                theorem_lines.append(f"theorem {theorem.split('.')[-1]} : True := by trivial")
            theorem_lines.append(
                f"theorem {base_theorem.split('.')[-1]} : True := by trivial")
        module.write_text("\n".join(theorem_lines) + "\n")
        manifest_path = root / "manifest.json"
        manifest_path.write_text(json.dumps(manifest))
        expected_path = root / "expected.json"
        expected_path.write_text(json.dumps(expected))
        table = root / "sockets.tsv"
        with table.open("w", newline="") as stream:
            writer = csv.DictWriter(stream, fieldnames=MOD.SOCKETS.FIELDS,
                                    delimiter="\t")
            writer.writeheader(); writer.writerows(rows)
        validation = root / "socket-validation.receipt"
        validation.write_text(MOD.SOCKETS.evidence_receipt(table, expected_path, 406) + "\n")
        return {
            "root_manifest": manifest_path.resolve(),
            "root_manifest_sha256": MOD.sha256(manifest_path),
            "table": table.resolve(), "expected": expected_path.resolve(),
            "validation": validation.resolve(), "module": module.resolve(),
            "source_module": module_name, "module_sha256": MOD.sha256(module),
            "rows": rows,
        }

    def build(self, fixture):
        return MOD.build_receipts(
            fixture["root_manifest"], fixture["root_manifest_sha256"],
            fixture["table"], fixture["expected"], fixture["validation"],
            fixture["module"], fixture["source_module"], fixture["module_sha256"])

    def test_exact_406_to_seven_receipts_and_create_only_index_last(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            fixture = self.fixture(root)
            receipts, index = self.build(fixture)
            self.assertEqual([cell for cell, _ in receipts],
                             [cell for _, cell, _ in MOD.CELLS])
            self.assertTrue(all(receipt["leaf_count"] == 58
                                for _, receipt in receipts))
            self.assertEqual(sum(len(receipt["leaf_job_ids"])
                                 for _, receipt in receipts), 406)
            output = root / "published"
            MOD.publish(output, receipts, index)
            self.assertEqual(
                {path.name for path in output.iterdir()},
                {"index.receipt.json", *(
                    f"{cell}.receipt.json" for _, cell, _ in MOD.CELLS)})
            published_index = json.loads((output / "index.receipt.json").read_text())
            for row in published_index["cells"]:
                self.assertEqual(
                    MOD.sha256(output / row["receipt"]), row["receipt_sha256"])
            with self.assertRaises(FileExistsError):
                MOD.publish(output, receipts, index)

    def test_rejects_manifest_socket_receipt_and_source_drift(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            for kind in ("manifest-order", "socket-order", "receipt-whitespace",
                         "source-bytes", "source-module", "source-symlink",
                         "receipt-symlink"):
                fixture = self.fixture(root)
                if kind == "manifest-order":
                    document = json.loads(fixture["root_manifest"].read_text())
                    document["cells"]["h3_b1"]["jobs"][2:4] = reversed(
                        document["cells"]["h3_b1"]["jobs"][2:4])
                    fixture["root_manifest"].write_text(json.dumps(document))
                    fixture["root_manifest_sha256"] = MOD.sha256(fixture["root_manifest"])
                elif kind == "socket-order":
                    lines = fixture["table"].read_text().splitlines()
                    lines[1], lines[2] = lines[2], lines[1]
                    fixture["table"].write_text("\n".join(lines) + "\n")
                    fixture["validation"].write_text(
                        MOD.SOCKETS.evidence_receipt(
                            fixture["table"], fixture["expected"], 406) + "\n")
                elif kind == "receipt-whitespace":
                    fixture["validation"].write_text(
                        fixture["validation"].read_text().rstrip() + "  \n")
                elif kind == "source-bytes":
                    fixture["module"].write_text(fixture["module"].read_text() + "-- drift\n")
                elif kind == "source-module":
                    fixture["source_module"] = "Proofs.Generated.Wrong"
                elif kind == "source-symlink":
                    target = fixture["module"]
                    link_dir = root / "linked-module"
                    link_dir.mkdir(exist_ok=True)
                    link = link_dir / target.name
                    link.symlink_to(target)
                    fixture["module"] = link
                else:
                    target = fixture["validation"]
                    link = root / "receipt-link.txt"
                    link.symlink_to(target)
                    fixture["validation"] = link
                with self.subTest(kind=kind), self.assertRaises((ValueError, MOD.SOCKETS.SocketTableError)):
                    self.build(fixture)

    def test_leaf_identity_binds_every_full_socket_row(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            fixture = self.fixture(root)
            before, _ = self.build(fixture)
            rows = MOD.read_socket_rows(fixture["table"])
            rows[0]["review_id"] = "#9999"
            with fixture["table"].open("w", newline="") as stream:
                writer = csv.DictWriter(stream, fieldnames=MOD.SOCKETS.FIELDS,
                                        delimiter="\t")
                writer.writeheader(); writer.writerows(rows)
            fixture["expected"].write_text(fixture["expected"].read_text())
            fixture["validation"].write_text(MOD.SOCKETS.evidence_receipt(
                fixture["table"], fixture["expected"], 406) + "\n")
            after, _ = self.build(fixture)
            self.assertNotEqual(before[0][1]["leaf_evidence_identity_sha256"],
                                after[0][1]["leaf_evidence_identity_sha256"])
            self.assertEqual(before[1][1]["leaf_evidence_identity_sha256"],
                             after[1][1]["leaf_evidence_identity_sha256"])


if __name__ == "__main__":
    unittest.main()
