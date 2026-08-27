#!/usr/bin/env python3

import json
import tempfile
import unittest
from pathlib import Path

from validate_sat49_terminal_ledger import ReceiptError, manifest_identity, parse


SHA = "a" * 64


def receipt(verdict: str = "UNSAT", **changes: str) -> str:
    common = {
        "schema": "erdos85-sat49-terminal-v1", "provenance": "fresh",
        "mode": "slow", "rc": "20",
        "solve_s": "900", "solve_peak_rss_kb": "1000", "cap_s": "900",
        "generator_kind": "third", "generator_sha256": SHA,
        "manifest_sha256": SHA, "emitted_cnf_sha256": SHA,
        "solved_cnf_sha256": SHA, "cnf_bytes": "100", "maxvar": "29500",
        "kissat_sha256": SHA,
    }
    if verdict == "UNSAT":
        common.update({
            "raw_lrat_sha256": SHA, "raw_lrat_bytes": "90", "trim": "VERIFIED",
            "trim_s": "1", "trim_peak_rss_kb": "100", "drat_trim_sha256": SHA,
            "compact_lrat_sha256": SHA, "compact_lrat_bytes": "80",
            "compact_s": "1", "compact_peak_rss_kb": "100",
            "compactor_sha256": SHA, "lrat_kind": "compact-v1",
            "native_lratcheck": "VERIFIED", "native_lratcheck_s": "1",
            "native_lratcheck_peak_rss_kb": "100", "lrat_check_sha256": SHA,
            "lean_lratreplay": "VERIFIED", "lean_lratreplay_s": "1",
            "lean_lratreplay_peak_rss_kb": "100", "lratreplay_sha256": SHA,
            "lean_image_digest": "sha256:" + SHA,
            "compact_lrat_gz_sha256": SHA, "compact_lrat_gz_bytes": "70",
            "upload": "uploaded", "remote_sha256": SHA,
        })
    else:
        common.update({"rc": "10", "reproduce_rc": "10", "model": "VERIFIED",
                       "model_verifier_sha256": SHA})
    common.update(changes)
    metadata = " ".join(f"{key}={value}" for key, value in common.items())
    return ("2026-08-27T17:00:00Z "
            "h3_b1.cube-0-0.nested.cube-0-0.third.cube-7-7 "
            f"{verdict} {metadata}")


class TerminalLedgerTests(unittest.TestCase):
    def test_accepts_complete_unsat_and_sat_receipts(self):
        self.assertEqual(parse(receipt())["verdict"], "UNSAT")
        self.assertEqual(parse(receipt("SAT"))["verdict"], "SAT")

    def test_rejects_nonterminal_and_partial_rows(self):
        with self.assertRaisesRegex(ReceiptError, "nonterminal verdict"):
            parse(receipt().replace(" UNSAT ", " UNKNOWN "))
        fields = receipt().split()
        fields = [field for field in fields if not field.startswith("lean_lratreplay=")]
        with self.assertRaisesRegex(ReceiptError, "missing terminal metadata"):
            parse(" ".join(fields))

    def test_rejects_duplicate_keys_and_bad_job_membership(self):
        with self.assertRaisesRegex(ReceiptError, "duplicate metadata key"):
            parse(receipt() + " rc=20")
        with self.assertRaisesRegex(ReceiptError, "absent from the selected manifest"):
            parse(receipt(), {"h3_b1.cube-0-0"})
        with self.assertRaisesRegex(ReceiptError, "malformed job id"):
            parse(receipt().replace("h3_b1.cube-0-0", "../escape", 1))

    def test_rejects_unverified_unsat_stages_and_remote_mismatch(self):
        for key, value in (("trim", "FAIL"), ("lrat_kind", "raw"),
                           ("native_lratcheck", "FAIL"),
                           ("lean_lratreplay", "FAIL"), ("upload", "FAIL")):
            with self.subTest(key=key), self.assertRaises(ReceiptError):
                parse(receipt(**{key: value}))
        with self.assertRaisesRegex(ReceiptError, "remote SHA"):
            parse(receipt(remote_sha256="b" * 64))

    def test_rejects_unverified_or_unreproduced_sat(self):
        with self.assertRaisesRegex(ReceiptError, "reproduction rc=10"):
            parse(receipt("SAT", reproduce_rc="20"))
        with self.assertRaisesRegex(ReceiptError, "model=VERIFIED"):
            parse(receipt("SAT", model="FAIL"))
        with self.assertRaisesRegex(ReceiptError, "cannot use legacy-migration"):
            parse(receipt("SAT", provenance="legacy-migration",
                          solve_peak_rss_kb="0"))

    def test_migration_provenance_is_explicit_and_unsat_only(self):
        migrated = parse(receipt(provenance="legacy-migration",
                                 solve_peak_rss_kb="0"))
        self.assertEqual(migrated["provenance"], "legacy-migration")
        with self.assertRaisesRegex(ReceiptError, "positive solve_peak_rss_kb"):
            parse(receipt(solve_peak_rss_kb="0"))
        with self.assertRaisesRegex(ReceiptError, "unavailable solve peak RSS"):
            parse(receipt(provenance="legacy-migration", solve_peak_rss_kb="1"))

    def test_rejects_bad_hash_integer_mode_and_timestamp(self):
        with self.assertRaisesRegex(ReceiptError, "invalid SHA256"):
            parse(receipt(manifest_sha256="xyz"))
        with self.assertRaisesRegex(ReceiptError, "non-integer"):
            parse(receipt(cnf_bytes="many"))
        with self.assertRaisesRegex(ReceiptError, "invalid mode"):
            parse(receipt(mode="slwo"))
        with self.assertRaisesRegex(ReceiptError, "requires generator_kind=third"):
            parse(receipt(generator_kind="nested"))
        with self.assertRaisesRegex(ReceiptError, "Lean image digest"):
            parse(receipt(lean_image_digest="latest"))
        with self.assertRaisesRegex(ReceiptError, "UTC"):
            parse(receipt().replace("2026-08-27T17:00:00Z", "2026-08-27T17:00:00"))

    def test_loads_each_manifest_layer_and_binds_its_hash(self):
        job = "h3_b1.cube-0-0.nested.cube-0-0.third.cube-7-7"
        schemas = (
            ("erdos85-small-high-cube-jobs-v1", "cells"),
            ("erdos85-small-high-nested-cube-jobs-v1", "leaves"),
            ("erdos85-small-high-third-cube-jobs-v1", "leaves"),
        )
        with tempfile.TemporaryDirectory() as directory:
            for index, (schema, group_key) in enumerate(schemas):
                path = Path(directory) / f"manifest-{index}.json"
                path.write_text(json.dumps({
                    "schema": schema,
                    group_key: {"group": {"jobs": [{"id": job}]}},
                }))
                jobs, digest = manifest_identity(path)
                self.assertEqual(jobs, {job})
                self.assertEqual(
                    parse(receipt(manifest_sha256=digest), jobs, digest)["job"], job
                )
                with self.assertRaisesRegex(ReceiptError, "does not bind"):
                    parse(receipt(), jobs, digest)

    def test_rejects_malformed_or_duplicate_manifest_jobs(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "manifest.json"
            path.write_text(json.dumps({"schema": "wrong", "cells": {}}))
            with self.assertRaisesRegex(ReceiptError, "unsupported job manifest"):
                manifest_identity(path)
            path.write_text(json.dumps({
                "schema": "erdos85-small-high-cube-jobs-v1",
                "cells": {
                    "a": {"jobs": [{"id": "same"}]},
                    "b": {"jobs": [{"id": "same"}]},
                },
            }))
            with self.assertRaisesRegex(ReceiptError, "duplicate job ids"):
                manifest_identity(path)


if __name__ == "__main__":
    unittest.main()
