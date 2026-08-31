import hashlib
import json
import tempfile
import unittest
from pathlib import Path

import build_replay_queue as target
from replay_common import ReplayError
from run_replay_queue import load_queue
from capacity_queue import validate_queue_tables


class BuildReplayQueueTests(unittest.TestCase):
    def inputs(self):
        rows = []
        cert = ["orbit\tprofile\tlocalIndex\tcompact_lrat_sha256\tcnf_sha256"]
        terminal = ["\t".join(target.TERMINAL_COLUMNS)]
        counts = [0] * 5
        for profile, count in enumerate(target.CAPACITY_PROFILE_COUNTS):
            for index in range(count):
                values = [0] * len(target.TABLE_PAIRS)
                values[0] = profile + 1
                values[1] = index + 1
                serialization = json.dumps(sorted({pair: value for pair, value in
                    zip(target.TABLE_PAIRS, values, strict=True) if value}.items()))
                tag = target.table_serialization_tag(serialization)
                rows.append(f"{profile} " + " ".join(map(str, values)))
                compact = hashlib.sha256((tag + "c").encode()).hexdigest()
                cnf = hashlib.sha256((tag + "n").encode()).hexdigest()
                gzip = hashlib.sha256((tag + "g").encode()).hexdigest()
                cert.append(f"{tag}\t{target.PROFILE_NAMES[profile]}\t{index}\t{compact}\t{cnf}")
                key = f"sat49/campaign-20260825/h1/{tag}.compact.lrat.gz"
                terminal.append(f"{tag}\t{key}\t{gzip}\t{gzip}")
                counts[profile] += 1
        return ("\n".join(rows) + "\n").encode(), ("\n".join(cert) + "\n").encode(), ("\n".join(terminal) + "\n").encode()

    def test_builds_exact_complete_queue_and_receipts_inputs(self):
        inputs = self.inputs()
        output, receipt = target.build(*inputs)
        lines = output.splitlines()
        self.assertEqual(len(lines), sum(target.CAPACITY_PROFILE_COUNTS))
        first = json.loads(lines[0])
        self.assertEqual(set(first), {"tag", "profile", "local_index", "certificate_key",
            "certificate_gzip_sha256", "compact_lrat_sha256", "cnf_sha256",
            "table_serialization", "table_sha256"})
        self.assertEqual(receipt["output_sha256"], hashlib.sha256(output).hexdigest())
        self.assertEqual(receipt["inventory_sha256"], hashlib.sha256(inputs[0]).hexdigest())
        with tempfile.TemporaryDirectory() as raw:
            queue = Path(raw) / "queue.jsonl"
            queue.write_bytes(output)
            loaded = load_queue(queue)
            self.assertEqual([job["tag"] for job in loaded], sorted(job["tag"] for job in loaded))
            validate_queue_tables(loaded)

    def test_rejects_missing_duplicate_and_readback_mismatch(self):
        inventory, cert, terminal = self.inputs()
        for kind in ("missing", "duplicate", "readback"):
            with self.subTest(kind=kind):
                lines = terminal.decode().splitlines()
                if kind == "missing": lines.pop()
                elif kind == "duplicate": lines.append(lines[1])
                else:
                    fields = lines[1].split("\t"); fields[-1] = "f" * 64; lines[1] = "\t".join(fields)
                with self.assertRaises(ReplayError):
                    target.build(inventory, cert, ("\n".join(lines) + "\n").encode())

    def test_input_byte_mutation_changes_receipt_identity(self):
        values = self.inputs()
        _, before = target.build(*values)
        mutated = values[1] + b"\n"
        _, after = target.build(values[0], mutated, values[2])
        self.assertNotEqual(before["certificate_index_sha256"], after["certificate_index_sha256"])
        self.assertEqual(before["output_sha256"], after["output_sha256"])

    def test_rejects_aliases_and_preexisting_outputs(self):
        with tempfile.TemporaryDirectory() as raw:
            root = Path(raw)
            inputs = [root / name for name in ("inventory", "cert", "terminal")]
            output, receipt = root / "queue", root / "receipt"
            target.require_fresh_distinct_paths(inputs, [output, receipt])
            with self.assertRaisesRegex(ReplayError, "distinct"):
                target.require_fresh_distinct_paths(inputs, [inputs[0], receipt])
            output.write_text("stale")
            with self.assertRaisesRegex(ReplayError, "fresh"):
                target.require_fresh_distinct_paths(inputs, [output, receipt])
            output.unlink()
            output.symlink_to(root / "missing")
            with self.assertRaisesRegex(ReplayError, "fresh"):
                target.require_fresh_distinct_paths(inputs, [output, receipt])

    def test_partial_mode_rejects_mismatched_or_empty_indexes(self):
        inventory, cert, terminal = self.inputs()
        terminal_lines = terminal.decode().splitlines()
        with self.assertRaisesRegex(ReplayError, "different orbits"):
            target.build(inventory, cert, ("\n".join(terminal_lines[:-1]) + "\n").encode(),
                         require_complete=False)
        cert_header = cert.splitlines()[0] + b"\n"
        terminal_header = terminal.splitlines()[0] + b"\n"
        with self.assertRaisesRegex(ReplayError, "empty"):
            target.build(inventory, cert_header, terminal_header, require_complete=False)


if __name__ == "__main__":
    unittest.main()
