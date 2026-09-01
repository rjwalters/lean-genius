#!/usr/bin/env python3

import json
import contextlib
import io
import sys
import tempfile
import unittest
from pathlib import Path
from unittest import mock

import generate_h1_conflict_readback_queue as mod


HEADER = "\t".join(mod.COVERAGE_COLUMNS) + "\n"


def capacity_fixture(count: int = 8) -> tuple[bytes, list[dict]]:
    lines, entries = [], []
    locals_ = [0] * 5
    for index in range(count):
        profile = index % 5
        quotient = index
        values = []
        for _ in mod.capacity.TABLE_PAIRS:
            values.append(quotient % 5)
            quotient //= 5
        tag = mod.capacity.worker_tag(tuple(values))
        entries.append({"tag": tag, "profile": profile,
                        "local_index": locals_[profile], "values": values})
        locals_[profile] += 1
        lines.append(" ".join(map(str, (profile, *values))) + "\n")
    return "".join(lines).encode(), entries


def coverage_rows(count: int = 8) -> bytes:
    rows = []
    _, entries = capacity_fixture(count)
    for index, entry in enumerate(entries):
        profile = entry["profile"]
        values = {
            "tag": entry["tag"], "profile": str(profile),
            "family": mod.PROFILE_NAMES[profile], "local_index": str(900 + index),
            "inventory_source": "all_even_capacity", "status": "certificate-key-conflict",
            "certificate_key_present": "1", "certificate_ledger_valid": "0",
            "certificate_key_conflict": "1", "certified_s3": "0",
            "host_unsat": "0", "fleet_claim": "0", "cnf_sha_divergent": "0",
            "fleet_v2_claim": "0", "fleet_v3_claim": "0",
        }
        rows.append("\t".join(values.get(name, "") for name in mod.COVERAGE_COLUMNS) + "\n")
    return (HEADER + "".join(rows)).encode()


def audit_receipt(coverage: bytes, count: int = 8) -> bytes:
    tags = sorted(row["tag"] for row in
                  __import__("csv").DictReader(io.StringIO(coverage.decode()), delimiter="\t")
                  if row["status"] == "certificate-key-conflict")
    empty_identity = {"bytes": 0, "sha256": mod.sha256_bytes(b"")}
    return mod.canonical({
        "aws": {"bucket": "bucket", "profile": "read-only", "s3_prefix": "prefix"},
        "host_ledger_snapshot": {"count": 0, "identity_sha256": "0" * 64},
        "inputs": {}, "live_campaign": "/campaign",
        "live_named_output_paths": {}, "live_named_outputs_mutated": False,
        "live_outputs_after": {}, "live_outputs_before": {},
        "outputs": {
            "counts.json": empty_identity,
            "coverage.tsv": {"bytes": len(coverage), "sha256": mod.sha256_bytes(coverage)},
            "inventory_universe_diff.tsv": empty_identity,
        },
        "schema": mod.AUDIT_SCHEMA,
        "summary": {
            "anomalies": ({"certificate-key-present-without-valid-upload-ledger": count}
                          if count else {}),
            "certificate_key_conflict_count": count,
            "certificate_key_conflict_tags": tags,
            "certificate_key_present": count, "certificate_ledger_valid": 0,
            "certified": 0, "cnf_sha_comparable_count": 0,
            "cnf_sha_divergent_count": 0, "fleet_claim_tags": 0,
            "fleet_in_flight": 0, "fleet_ledger_rows": 0,
            "fleet_unknown_without_cert": 0, "host_ledger_rows": 0,
            "pending": 0, "status_total": count,
            "unknown_tags": {"certified_s3": [], "fleet_v2_claim": [],
                "fleet_v2_ledger": [], "fleet_v3_claim": [],
                "fleet_v3_ledger": [], "host_ledger": []},
        },
        "timestamp_utc": "2026-08-31T00:00:00Z",
    })


class ConflictReadbackQueueTest(unittest.TestCase):
    def test_main_writes_canonical_create_only_queue_and_receipt(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            coverage = coverage_rows()
            coverage_path = root / "coverage.tsv"; coverage_path.write_bytes(coverage)
            audit_path = root / "audit.json"; audit_path.write_bytes(audit_receipt(coverage))
            inventory_data, entries = capacity_fixture()
            inventory = root / "capacity.compact"; inventory.write_bytes(inventory_data)
            output, receipt = root / "queue.jsonl", root / "queue-receipt.json"
            argv = ["generator", "--audit-receipt", str(audit_path),
                    "--audit-receipt-sha256", mod.sha256_bytes(audit_path.read_bytes()),
                    "--coverage", str(coverage_path),
                    "--capacity-inventory", str(inventory),
                    "--capacity-inventory-sha256", mod.sha256_bytes(inventory_data),
                    "--output", str(output),
                    "--receipt-output", str(receipt)]
            counts = tuple(sum(entry["profile"] == profile for entry in entries)
                           for profile in range(5))
            with (mock.patch.object(sys, "argv", argv),
                  mock.patch.object(mod, "EXPECTED_COUNTS", counts),
                  mock.patch.object(mod, "EXPECTED_TOTAL", len(entries)),
                  contextlib.redirect_stdout(io.StringIO())):
                self.assertEqual(mod.main(), 0)
            jobs = [json.loads(line) for line in output.read_text().splitlines()]
            record = json.loads(receipt.read_text())
            self.assertEqual(len(jobs), 8)
            self.assertEqual(record["schema"], mod.QUEUE_SCHEMA)
            self.assertEqual(record["rows"], 8)
            self.assertEqual(record["capacity_inventory_sha256"],
                             mod.sha256_bytes(inventory_data))
            self.assertEqual(record["output_sha256"], mod.sha256_bytes(output.read_bytes()))
            self.assertEqual(receipt.read_bytes(), mod.canonical(record))
            with mock.patch.object(sys, "argv", argv), self.assertRaises(FileExistsError):
                mod.main()

    def test_eight_conflicts_emit_canonical_sorted_jsonl(self) -> None:
        coverage = coverage_rows()
        audit = audit_receipt(coverage)
        tags, summary = mod.parse_audit_receipt(
            Path("receipt.json"), audit, mod.sha256_bytes(audit), coverage)
        jobs = mod.parse_coverage(Path("coverage.tsv"), coverage, tags, summary)
        inventory, entries = capacity_fixture()
        counts = tuple(sum(entry["profile"] == profile for entry in entries)
                       for profile in range(5))
        with mock.patch.object(mod, "EXPECTED_COUNTS", counts), \
                mock.patch.object(mod, "EXPECTED_TOTAL", len(entries)):
            jobs = mod.reconcile_capacity(Path("capacity.compact"), inventory, jobs)
        self.assertEqual(len(jobs), 8)
        self.assertEqual([job["tag"] for job in jobs], tags)
        expected = {entry["tag"]: entry for entry in entries}
        self.assertEqual([job["profile"] for job in jobs],
                         [expected[tag]["profile"] for tag in tags])
        self.assertEqual([job["local_index"] for job in jobs],
                         [expected[tag]["local_index"] for tag in tags])
        for job in jobs:
            mod.validate_certificate_key(job["tag"], job["certificate_key"])
            self.assertEqual(json.loads(mod.canonical(job)), job)

    def test_nested_arbitrary_cross_tag_and_malformed_keys_fail(self) -> None:
        tag = "0000000000000001"
        for key in (
            f"{mod.CERTIFICATE_PREFIX}nested/{tag}{mod.CERTIFICATE_SUFFIX}",
            f"arbitrary/{tag}{mod.CERTIFICATE_SUFFIX}",
            f"{mod.CERTIFICATE_PREFIX}0000000000000002{mod.CERTIFICATE_SUFFIX}",
            f"{mod.CERTIFICATE_PREFIX}{tag}.other",
        ):
            with self.subTest(key=key), self.assertRaisesRegex(ValueError, "not exact"):
                mod.validate_certificate_key(tag, key)

    def test_receipt_hash_schema_count_and_tag_drift_fail(self) -> None:
        coverage = coverage_rows()
        base = json.loads(audit_receipt(coverage))
        cases = []
        for mutate in (
            lambda value: value.update(schema="wrong"),
            lambda value: value["outputs"]["coverage.tsv"].update(sha256="0" * 64),
            lambda value: value["outputs"]["coverage.tsv"].update(bytes=1),
            lambda value: value["summary"].update(certificate_key_conflict_count=7),
            lambda value: value["summary"].update(certificate_key_conflict_tags=["bad"]),
            lambda value: value["summary"].update(status_total=7),
        ):
            value = json.loads(json.dumps(base)); mutate(value); cases.append(mod.canonical(value))
        for data in cases:
            with self.subTest(data=data), self.assertRaises(ValueError):
                mod.parse_audit_receipt(
                    Path("receipt.json"), data, mod.sha256_bytes(data), coverage)

    def test_receipt_pin_minimal_noncanonical_and_summary_mismatch_fail(self) -> None:
        coverage = coverage_rows()
        data = audit_receipt(coverage)
        with self.assertRaisesRegex(ValueError, "SHA-256 mismatch"):
            mod.parse_audit_receipt(Path("receipt.json"), data, "0" * 64, coverage)
        minimal = mod.canonical({"schema": mod.AUDIT_SCHEMA})
        with self.assertRaises(ValueError):
            mod.parse_audit_receipt(
                Path("receipt.json"), minimal, mod.sha256_bytes(minimal), coverage)
        noncanonical = json.dumps(json.loads(data), indent=2).encode()
        with self.assertRaises(ValueError):
            mod.parse_audit_receipt(
                Path("receipt.json"), noncanonical, mod.sha256_bytes(noncanonical), coverage)
        value = json.loads(data); value["summary"]["certified"] = 1
        changed = mod.canonical(value)
        tags, summary = mod.parse_audit_receipt(
            Path("receipt.json"), changed, mod.sha256_bytes(changed), coverage)
        with self.assertRaisesRegex(ValueError, "counts differ"):
            mod.parse_coverage(Path("coverage.tsv"), coverage, tags, summary)

    def test_duplicate_extra_and_missing_coverage_headers_fail(self) -> None:
        coverage = coverage_rows()
        audit = audit_receipt(coverage)
        tags, summary = mod.parse_audit_receipt(
            Path("receipt.json"), audit, mod.sha256_bytes(audit), coverage)
        lines = coverage.decode().splitlines()
        headers = lines[0].split("\t")
        variants = []
        duplicate = headers.copy(); duplicate[-1] = duplicate[-2]
        variants.append(duplicate)
        variants.append(headers + ["extra"])
        variants.append(headers[:-1])
        for header in variants:
            changed = ("\t".join(header) + "\n" + "\n".join(lines[1:]) + "\n").encode()
            with self.subTest(header=header), self.assertRaisesRegex(ValueError, "header"):
                mod.parse_coverage(Path("coverage.tsv"), changed, tags, summary)

    def test_coverage_status_flags_profile_duplicates_and_empty_fail(self) -> None:
        coverage = coverage_rows()
        audit = audit_receipt(coverage)
        tags, summary = mod.parse_audit_receipt(
            Path("receipt.json"), audit, mod.sha256_bytes(audit), coverage)
        parsed = list(__import__("csv").DictReader(
            io.StringIO(coverage.decode()), delimiter="\t"))
        replacements = (
            ("certificate-key-conflict\t1\t0\t1\t0", "pending\t1\t0\t1\t0"),
            ("\t1\t0\t1\t0\t", "\t1\t1\t1\t0\t"),
            (f"\t{parsed[0]['profile']}\t{parsed[0]['family']}\t{parsed[0]['local_index']}\t",
             f"\t{parsed[0]['profile']}\tABBB\t{parsed[0]['local_index']}\t"),
            (parsed[1]["tag"], parsed[0]["tag"]),
        )
        for old, new in replacements:
            changed = coverage.decode().replace(old, new, 1).encode()
            with self.subTest(new=new), self.assertRaises(ValueError):
                mod.parse_coverage(Path("coverage.tsv"), changed, tags, summary)
        values = {"tag": "0000000000000001", "profile": "0", "family": "BBBB",
                  "local_index": "0", "inventory_source": "all_even_capacity",
                  "status": "pending", "certificate_key_present": "0",
                  "certificate_ledger_valid": "0", "certificate_key_conflict": "0",
                  "certified_s3": "0", "host_unsat": "0", "fleet_claim": "0",
                  "cnf_sha_divergent": "0", "fleet_v2_claim": "0", "fleet_v3_claim": "0"}
        empty = (HEADER + "\t".join(values.get(name, "") for name in mod.COVERAGE_COLUMNS) + "\n").encode()
        empty_value = json.loads(audit_receipt(empty, 0))
        empty_value["summary"]["status_total"] = 1
        empty_value["summary"]["pending"] = 1
        empty_audit = mod.canonical(empty_value)
        empty_tags, empty_summary = mod.parse_audit_receipt(
            Path("receipt.json"), empty_audit, mod.sha256_bytes(empty_audit), empty)
        with self.assertRaisesRegex(ValueError, "no certificate-key conflicts"):
            mod.parse_coverage(Path("coverage.tsv"), empty, empty_tags, empty_summary)

    def test_create_only_output_and_input_replacement(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            output = root / "queue.jsonl"
            mod.create_only(output, b"first\n")
            with self.assertRaises(FileExistsError):
                mod.create_only(output, b"replacement\n")
            self.assertEqual(output.read_bytes(), b"first\n")
            source = root / "source"; source.write_bytes(b"snapshot")
            first = source.stat()
            changed = mock.Mock(**{
                name: getattr(first, name)
                for name in ("st_dev", "st_ino", "st_size", "st_mtime_ns", "st_mode")
            })
            changed.st_mtime_ns += 1
            with mock.patch.object(mod.os, "fstat", side_effect=[first, changed]):
                with self.assertRaisesRegex(ValueError, "changed while being read"):
                    mod.stable_read(source)

    def test_both_before_link_input_revalidation_gates(self) -> None:
        for phase in ("queue", "receipt"):
            with self.subTest(phase=phase), tempfile.TemporaryDirectory() as directory:
                root = Path(directory)
                coverage = coverage_rows()
                coverage_path = root / "coverage.tsv"; coverage_path.write_bytes(coverage)
                audit_path = root / "audit.json"; audit_path.write_bytes(audit_receipt(coverage))
                inventory_data, entries = capacity_fixture()
                inventory = root / "capacity.compact"; inventory.write_bytes(inventory_data)
                output, receipt = root / "queue.jsonl", root / "queue-receipt.json"
                argv = ["generator", "--audit-receipt", str(audit_path),
                        "--audit-receipt-sha256", mod.sha256_bytes(audit_path.read_bytes()),
                        "--coverage", str(coverage_path),
                        "--capacity-inventory", str(inventory),
                        "--capacity-inventory-sha256", mod.sha256_bytes(inventory_data),
                        "--output", str(output),
                        "--receipt-output", str(receipt)]
                if phase == "queue":
                    original = mod.parse_coverage
                    def mutate_after_parse(*args, **kwargs):
                        result = original(*args, **kwargs)
                        coverage_path.write_bytes(coverage + b"\n")
                        return result
                    patches = mock.patch.object(mod, "parse_coverage", side_effect=mutate_after_parse)
                else:
                    original_create = mod.create_only
                    calls = 0
                    def mutate_after_queue(path, data):
                        nonlocal calls
                        original_create(path, data); calls += 1
                        if calls == 1:
                            audit_path.write_bytes(audit_path.read_bytes() + b"\n")
                    patches = mock.patch.object(mod, "create_only", side_effect=mutate_after_queue)
                counts = tuple(sum(entry["profile"] == profile for entry in entries)
                               for profile in range(5))
                with (mock.patch.object(sys, "argv", argv), patches,
                      mock.patch.object(mod, "EXPECTED_COUNTS", counts),
                      mock.patch.object(mod, "EXPECTED_TOTAL", len(entries)),
                      self.assertRaisesRegex(ValueError, "changed before output publication")):
                    mod.main()
                self.assertFalse(receipt.exists())
                self.assertEqual(output.exists(), phase == "receipt")


if __name__ == "__main__":
    unittest.main()
