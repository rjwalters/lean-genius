import hashlib
import importlib.util
import json
import tempfile
import unittest
from pathlib import Path


HERE = Path(__file__).resolve().parent
SPEC = importlib.util.spec_from_file_location(
    "h1_audit", HERE / "publish_h1_coverage_audit_snapshot.py")
MOD = importlib.util.module_from_spec(SPEC)
assert SPEC.loader is not None
SPEC.loader.exec_module(MOD)


FAKE_RECONCILER = r'''#!/usr/bin/env python3
import argparse, json
from pathlib import Path
p = argparse.ArgumentParser()
p.add_argument("--campaign", type=Path, required=True)
p.add_argument("--aws-profile"); p.add_argument("--bucket"); p.add_argument("--s3-prefix")
p.add_argument("--compact-inventory")
a = p.parse_args()
out = a.campaign / "h1fleet/coverage"; out.mkdir(parents=True)
counts = {
 "anomalies": {}, "capacity_inventory_total": 13351, "capacity_only_error": 0,
 "certificate_key_conflict_count": 0, "certificate_key_conflict_tags": [],
 "certificate_key_present_tags": 9804, "certificate_ledger_valid_tags": 9804,
 "certified_s3_tags": 9804, "cnf_sha_comparable_count": 30,
 "cnf_sha_divergent_count": 0, "cnf_sha_divergent_tags": [],
 "compact_inventory_total": 13541, "compact_only_pre_capacity": 190,
 "fleet_claim_tags": 11006, "fleet_ledger_rows": 10830,
 "fleet_unknown_without_cert": 1391, "host_ledger_rows": 409,
 "status_counts": {"certificate-key-conflict": 0, "certified-in-S3": 9804,
                   "fleet-in-flight": 176, "host-ledgered-UNSAT-not-uploaded": 0,
                   "pending": 3371},
 "status_total": 13351,
 "unknown_tags": {"certified_s3": [], "fleet_v2_claim": [], "fleet_v2_ledger": [],
                  "fleet_v3_claim": [], "fleet_v3_ledger": [], "host_ledger": []}}
(out / "counts.json").write_text(json.dumps(counts, sort_keys=True) + "\n")
(out / "coverage.tsv").write_text("tag\tstatus\nabc\tpending\n")
(out / "inventory_universe_diff.tsv").write_text("tag\trelation\nabc\tboth\n")
# MUTATE_ORIGINAL
'''


class H1CoverageAuditSnapshotTest(unittest.TestCase):
    def fixture(self, root: Path):
        campaign = root / "campaign"; coverage = campaign / "h1fleet/coverage"
        grind = campaign / "h1grind"; coverage.mkdir(parents=True); grind.mkdir()
        all_even = grind / "all_even_manifest.tsv"; all_even.write_text("all-even\n")
        complement = grind / "complement_manifest.tsv"; complement.write_text("complement\n")
        ledger = grind / "orbits/tag/ledger.line"; ledger.parent.mkdir(parents=True)
        ledger.write_text("time tag UNSAT rc=20\n")
        compact = root / "compact.txt"; compact.write_text("compact\n")
        reconciler = root / "reconcile.py"; reconciler.write_text(FAKE_RECONCILER)
        (coverage / "counts.json").write_text("live-counts\n")
        (coverage / "coverage.tsv").write_text("live-coverage\n")
        (coverage / "inventory_universe_diff.tsv").write_text("live-universe\n")
        return {"campaign": campaign.resolve(), "reconciler": reconciler.resolve(),
            "reconciler_sha256": MOD.sha256(reconciler),
            "all_even_manifest": all_even.resolve(),
            "complement_manifest": complement.resolve(),
            "compact_inventory": compact.resolve(), "aws_profile": "read-only",
            "bucket": "bucket", "s3_prefix": "prefix",
            "output": (root / "audits/snapshot").resolve()}

    def test_publishes_canonical_create_only_snapshot_without_live_changes(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory); (root / "audits").mkdir()
            values = self.fixture(root)
            before = MOD.snapshot_files(values["campaign"] / MOD.LIVE_RELATIVE)
            receipt = MOD.publish_snapshot(**values, timestamp="2026-08-31T02:47:00Z")
            output = values["output"]
            self.assertEqual(MOD.snapshot_files(values["campaign"] / MOD.LIVE_RELATIVE), before)
            self.assertFalse(any(path.name.startswith(".h1-audit-stage.")
                                 for path in output.parent.iterdir()))
            self.assertEqual(set(path.name for path in output.iterdir()),
                             {*MOD.OUTPUTS, "receipt.json"})
            self.assertEqual((output / "receipt.json").read_bytes(), MOD.canonical(receipt))
            self.assertFalse(receipt["live_named_outputs_mutated"])
            self.assertEqual(receipt["host_ledger_snapshot"]["count"], 1)
            self.assertEqual(receipt["summary"]["certified"], 9804)
            for name, identity in receipt["outputs"].items():
                self.assertEqual(MOD.sha256(output / name), identity["sha256"])
            with self.assertRaises(ValueError):
                MOD.publish_snapshot(**values, timestamp="2026-08-31T02:48:00Z")

    def test_rejects_pin_symlink_inside_campaign_and_integrity_failure(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory); (root / "audits").mkdir()
            for kind in ("pin", "symlink", "inside", "bad-summary",
                         "unexpected-status", "unknown-shape", "input-toctou"):
                case = root / kind; case.mkdir(); (case / "audits").mkdir()
                values = self.fixture(case)
                values["output"] = (case / "audits" / "snapshot").resolve()
                if kind == "pin": values["reconciler_sha256"] = "0" * 64
                elif kind == "symlink":
                    link = case / "reconciler-link.py"; link.symlink_to(values["reconciler"])
                    values["reconciler"] = link.absolute()
                elif kind == "inside":
                    values["output"] = values["campaign"] / "audit"
                elif kind == "bad-summary":
                    values["reconciler"].write_text(
                        FAKE_RECONCILER.replace('"anomalies": {}', '"anomalies": {"bad": 1}'))
                    values["reconciler_sha256"] = MOD.sha256(values["reconciler"])
                elif kind == "unexpected-status":
                    values["reconciler"].write_text(FAKE_RECONCILER.replace(
                        '"pending": 3371}', '"pending": 3370, "invented": 1}'))
                    values["reconciler_sha256"] = MOD.sha256(values["reconciler"])
                elif kind == "unknown-shape":
                    values["reconciler"].write_text(FAKE_RECONCILER.replace(
                        '"host_ledger": []}', '"host_ledger": [], "invented": []}'))
                    values["reconciler_sha256"] = MOD.sha256(values["reconciler"])
                else:
                    mutation = ("from pathlib import Path\nPath(" +
                        repr(str(values["compact_inventory"])) +
                        ").write_text('mutated-original\\n')")
                    values["reconciler"].write_text(
                        FAKE_RECONCILER.replace("# MUTATE_ORIGINAL", mutation))
                    values["reconciler_sha256"] = MOD.sha256(values["reconciler"])
                with self.subTest(kind=kind), self.assertRaises(ValueError):
                    MOD.publish_snapshot(**values, timestamp="2026-08-31T02:47:00Z")
                self.assertFalse(values["output"].exists())

    def test_publishes_recognized_key_conflict_as_nonterminal_audit(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory); (root / "audits").mkdir()
            values = self.fixture(root)
            conflict = FAKE_RECONCILER.replace(
                '"anomalies": {}',
                '"anomalies": {"certificate-key-present-without-valid-upload-ledger": 1}')
            conflict = conflict.replace(
                '"certificate_key_conflict_count": 0, "certificate_key_conflict_tags": [],',
                '"certificate_key_conflict_count": 1, "certificate_key_conflict_tags": ["e6f717d2e69cc8e0"],')
            conflict = conflict.replace('"certificate_ledger_valid_tags": 9804',
                                        '"certificate_ledger_valid_tags": 9803')
            conflict = conflict.replace('"certified_s3_tags": 9804',
                                        '"certified_s3_tags": 9803')
            conflict = conflict.replace('"certificate-key-conflict": 0, "certified-in-S3": 9804',
                                        '"certificate-key-conflict": 1, "certified-in-S3": 9803')
            values["reconciler"].write_text(conflict)
            values["reconciler_sha256"] = MOD.sha256(values["reconciler"])
            receipt = MOD.publish_snapshot(**values, timestamp="2026-08-31T02:47:00Z")
            self.assertEqual(receipt["summary"]["certificate_key_conflict_count"], 1)
            self.assertEqual(receipt["summary"]["certified"], 9803)
            counts = json.loads((values["output"] / "counts.json").read_text())
            counts["certificate_key_conflict_tags"] = ["NOT-A-CANONICAL-TAG"]
            with self.assertRaisesRegex(ValueError, "integrity gate"):
                MOD.validate_summary(counts)
            counts["certificate_key_conflict_tags"] = ["ffffffffffffffff", "0000000000000000"]
            counts["certificate_key_conflict_count"] = 2
            counts["certificate_key_present_tags"] = 9805
            counts["status_counts"]["certificate-key-conflict"] = 2
            counts["status_counts"]["pending"] = 3370
            counts["anomalies"]["certificate-key-present-without-valid-upload-ledger"] = 2
            with self.assertRaisesRegex(ValueError, "integrity gate"):
                MOD.validate_summary(counts)


if __name__ == "__main__":
    unittest.main()
