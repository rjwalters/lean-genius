#!/usr/bin/env python3

import importlib.util
import sys
import tempfile
import unittest
from pathlib import Path


HERE = Path(__file__).resolve().parent
SPEC = importlib.util.spec_from_file_location("reconcile_h1_coverage", HERE / "reconcile_h1_coverage.py")
MOD = importlib.util.module_from_spec(SPEC)
assert SPEC.loader
sys.modules[SPEC.name] = MOD
SPEC.loader.exec_module(MOD)


def ledger(tag: str, *, verdict: str = "UNSAT", trim: str = "VERIFIED",
           raw_bytes: int = 12, compact_bytes: int = 9, upload: str = "uploaded"):
    sha = "a" * 64
    raw = (
        f"2026-08-31T00:00:00Z {tag} p=0 i=0 {verdict} rc="
        f"{'20' if verdict == 'UNSAT' else '0'} cnf_sha256={'b' * 64} "
        f"trim={trim} raw_lrat_sha256={sha} raw_lrat_bytes={raw_bytes} "
        f"compact=ok compact_lrat_sha256={sha} compact_bytes={compact_bytes} "
        f"compact_gz_sha256={'c' * 64} upload={upload}"
    )
    return MOD.parse_ledger(raw, tag)


class FakePaginator:
    def __init__(self, objects):
        self.objects = objects

    def paginate(self, **_kwargs):
        yield {"Contents": self.objects}


class FakeS3:
    def __init__(self, objects):
        self.objects = objects

    def get_paginator(self, _name):
        return FakePaginator(self.objects)

    def download_file(self, *_args):
        raise AssertionError("malformed key must be rejected before download")


class ReconcileCoverageTests(unittest.TestCase):
    def setUp(self):
        self.tags = [f"{index:016x}" for index in range(1, 6)]
        self.inventory = [MOD.InventoryRow(tag, 0, "BBBB", index, "all_even_capacity")
                          for index, tag in enumerate(self.tags)]

    def reconcile(self, *, host=None, v2=None, v3=None, keys=(), v2_claims=(), v3_claims=()):
        rows, summary, divergent = MOD.reconcile(
            self.inventory, host or {}, v2 or {}, v3 or {}, set(keys),
            set(v2_claims), set(v3_claims))
        return {row[0]: dict(zip(MOD.COVERAGE_COLUMNS, map(str, row))) for row in rows}, summary, divergent

    def test_key_presence_requires_verified_nonempty_upload_ledger(self):
        good, empty, failed = self.tags[:3]
        rows, summary, _ = self.reconcile(
            host={good: ledger(good), empty: ledger(empty, raw_bytes=0, compact_bytes=0),
                  failed: ledger(failed, trim="TRIM-FAIL")},
            keys=(good, empty, failed))
        self.assertEqual(rows[good]["status"], "certified-in-S3")
        self.assertEqual(rows[good]["certificate_key_present"], "1")
        self.assertEqual(rows[good]["certificate_ledger_valid"], "1")
        self.assertEqual(rows[good]["certified_s3"], "1")
        for tag in (empty, failed):
            self.assertEqual(rows[tag]["status"], "certificate-key-conflict")
            self.assertEqual(rows[tag]["certificate_key_present"], "1")
            self.assertEqual(rows[tag]["certificate_ledger_valid"], "0")
            self.assertEqual(rows[tag]["certificate_key_conflict"], "1")
            self.assertEqual(rows[tag]["certified_s3"], "0")
        self.assertEqual(summary["certificate_key_present_tags"], 3)
        self.assertEqual(summary["certified_s3_tags"], 1)
        self.assertEqual(summary["certificate_key_conflict_count"], 2)
        self.assertEqual(summary["certificate_key_conflict_tags"], [empty, failed])

    def test_valid_fleet_ledger_supersedes_bad_host_evidence(self):
        tag = self.tags[0]
        rows, summary, _ = self.reconcile(
            host={tag: ledger(tag, trim="TRIM-FAIL")}, v2={tag: ledger(tag)}, keys=(tag,))
        self.assertEqual(rows[tag]["status"], "certified-in-S3")
        self.assertEqual(rows[tag]["certificate_ledger_valid"], "1")
        self.assertEqual(summary["certificate_key_conflict_count"], 0)

    def test_conflict_precedes_claim_and_unknown_retry_states(self):
        tag = self.tags[0]
        rows, _, _ = self.reconcile(
            v2={tag: ledger(tag, verdict="UNKNOWN")}, keys=(tag,), v2_claims=(tag,))
        self.assertEqual(rows[tag]["status"], "certificate-key-conflict")
        self.assertEqual(rows[tag]["certified_s3"], "0")

    def test_absent_key_claim_partition_is_unchanged(self):
        in_flight, unknown = self.tags[:2]
        rows, summary, _ = self.reconcile(
            v2={unknown: ledger(unknown, verdict="UNKNOWN")},
            v2_claims=(in_flight, unknown))
        self.assertEqual(rows[in_flight]["status"], "fleet-in-flight")
        self.assertEqual(rows[unknown]["status"], "pending")
        self.assertEqual(summary["fleet_unknown_without_cert"], 1)

    def test_duplicate_ledger_attribute_is_rejected(self):
        tag = self.tags[0]
        with self.assertRaisesRegex(RuntimeError, "duplicate ledger attribute"):
            MOD.parse_ledger(
                f"2026-08-31T00:00:00Z {tag} UNSAT rc=20 rc=20", "duplicate")

    def test_nested_and_duplicate_object_keys_are_rejected(self):
        prefix = "campaign/h1/"
        tag = self.tags[0]
        with self.assertRaisesRegex(RuntimeError, "nested object key"):
            MOD.list_s3_tags(
                FakeS3([{"Key": f"{prefix}nested/{tag}.compact.lrat.gz"}]),
                "bucket", prefix, ".compact.lrat.gz")
        with self.assertRaisesRegex(RuntimeError, "duplicate object key"):
            MOD.list_s3_tags(
                FakeS3([{"Key": f"{prefix}{tag}.compact.lrat.gz"}] * 2),
                "bucket", prefix, ".compact.lrat.gz")

    def test_nested_ledger_key_is_rejected_before_cache_collapse(self):
        prefix = "campaign"
        tag = self.tags[0]
        key = f"{prefix}/h1-fleet-v2/ledger/nested/{tag}.line"
        with tempfile.TemporaryDirectory() as directory:
            with self.assertRaisesRegex(RuntimeError, "nested ledger key"):
                MOD.sync_fleet_ledgers(
                    FakeS3([{"Key": key, "Size": 1}]), "bucket", prefix,
                    "h1-fleet-v2", Path(directory))
        canonical = f"{prefix}/h1-fleet-v2/ledger/{tag}.line"
        with tempfile.TemporaryDirectory() as directory:
            (Path(directory) / f"{tag}.line").write_bytes(b"x")
            with self.assertRaisesRegex(RuntimeError, "duplicate ledger key"):
                MOD.sync_fleet_ledgers(
                    FakeS3([{"Key": canonical, "Size": 1}] * 2), "bucket", prefix,
                    "h1-fleet-v2", Path(directory))


if __name__ == "__main__":
    unittest.main()
