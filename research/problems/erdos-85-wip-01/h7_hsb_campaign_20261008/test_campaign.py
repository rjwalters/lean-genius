#!/usr/bin/env python3
"""Metadata-only acceptance tests for the campaign tooling (no solver, no Lean, no AWS).

    python3 test_campaign.py            # stdlib unittest; runs anywhere

Collector cases 1-8 are codex's fixtures from its review of commit 1cab73ef2a2
(branch erdos85/h7-lrat-adapter-20261008, h7_campaign_controller_review_20261008/check_patch.py,
room messages 52742-52751), run against the in-tree collector instead of a patched temporary copy.
The cert_batch cases cover the third finding of that review: the checker heap is never escalated
inside a batch, and STOP is honoured between items.
"""
from __future__ import annotations

import contextlib
import io
import json
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import cert_batch  # noqa: E402
import cert_item  # noqa: E402
import collect_receipts as collector  # noqa: E402
import h7_common as hc  # noqa: E402

CAKE = "4d47ffdd19fc6a80e24025f8c5d27d89c4309c9931bdad6d389d87e35be5464b"


class FakeCube:
    def __init__(self, *args, **kwargs):
        self.name = args[1] if len(args) > 1 else "cube_a"
        self.meta = {"cover_cnf_sha256": "a" * 64}
        self.n_leaves = 1

    def leaf_sha256(self, leaf):
        assert leaf == 0
        return "b" * 64


class Collector(unittest.TestCase):
    def run_collector(self, cake, selectors=(), inventory=("cube_a", "cube_b"), cadical=None):
        with tempfile.TemporaryDirectory(prefix="e85-h7-collector-") as tmp:
            root = Path(tmp)
            inputs, receipts = root / "inputs", root / "results"
            inputs.mkdir()
            receipts.mkdir()
            (inputs / "inputs.json").write_text("{}\n")
            (receipts / "fixture.jsonl.zst").write_bytes(b"fixture")
            rows = []
            for name in inventory:
                for kind, leaf, sha in [("cover", None, "a" * 64), ("leaf", 0, "b" * 64)]:
                    bins = {"cadical": cadical or collector.CADICAL}
                    if cake is not None:
                        bins["cake_lpr"] = cake
                    rows.append({"cube": name, "kind": kind, "leaf": leaf, "status": "CERTIFIED", "cnf_sha256": sha,
                                 "binaries": bins, "checker": {"verified_line": True, "cpu_seconds": 1},
                                 "solver": {"returncode": 20, "cpu_seconds": 1}, "host": "h",
                                 "proof": {"checker_closed_early": False, "bytes": 1, "sha256": "c" * 64}})
            decoded = "".join(json.dumps(row) + "\n" for row in rows).encode()
            argv = ["collect_receipts.py", "--inputs", str(inputs), "--results", str(receipts)]
            with patch.object(collector.hc, "CUBES", list(inventory)), \
                    patch.object(collector.hc, "Cube", FakeCube), \
                    patch.object(collector.subprocess, "run",
                                 return_value=subprocess.CompletedProcess([], 0, stdout=decoded)), \
                    patch.object(sys, "argv", argv + list(selectors)), \
                    contextlib.redirect_stdout(io.StringIO()) as out, \
                    contextlib.redirect_stderr(io.StringIO()) as err:
                try:
                    rc = collector.main()
                except SystemExit as exc:
                    rc = exc.code
            return {"exit_code": rc, "summary": json.loads(out.getvalue()) if out.getvalue() else None,
                    "argument_error": bool(err.getvalue())}

    def test_pins_are_the_reviewed_hashes(self):
        self.assertEqual(collector.CAKE_LPR, CAKE)
        self.assertEqual(hc.PINNED_BINARIES, {"cadical": collector.CADICAL, "cake_lpr": CAKE})

    def test_approved_checker(self):
        r = self.run_collector(CAKE)
        self.assertEqual(r["exit_code"], 0)
        self.assertTrue(r["summary"]["full_campaign_complete"])

    def test_wrong_or_missing_checker_hash_counts_for_nothing(self):
        for cake in ("0" * 64, None):
            r = self.run_collector(cake)
            self.assertEqual(r["exit_code"], 1)
            self.assertFalse(r["summary"]["all_complete"])
            self.assertFalse(r["summary"]["full_campaign_complete"])
            self.assertEqual(r["summary"]["totals"]["certified_leaves"], 0)

    def test_wrong_solver_hash_counts_for_nothing(self):
        r = self.run_collector(CAKE, cadical="0" * 64)
        self.assertEqual(r["exit_code"], 1)
        self.assertEqual(r["summary"]["totals"]["certified_leaves"], 0)

    def test_unknown_mixed_and_empty_selectors_are_rejected(self):
        for selectors, inventory in [(["--cubes", "cube_TYPO"], ("cube_a", "cube_b")),
                                     (["--cubes", "cube_a,cube_TYPO"], ("cube_a", "cube_b")),
                                     (["--cubes", ","], ("cube_a", "cube_b")),
                                     ([], ())]:
            r = self.run_collector(CAKE, selectors, inventory)
            self.assertEqual(r["exit_code"], 2, selectors)
            self.assertTrue(r["argument_error"])
            self.assertIsNone(r["summary"])

    def test_known_subset_is_not_the_full_campaign(self):
        r = self.run_collector(CAKE, ["--cubes", "cube_a"])
        self.assertEqual(r["exit_code"], 0)
        self.assertTrue(r["summary"]["all_complete"])
        self.assertFalse(r["summary"]["full_campaign_complete"])
        self.assertEqual(r["summary"]["selected_cubes"], ["cube_a"])


class Batch(unittest.TestCase):
    def run_batch(self, statuses, stop_after=None, extra=()):
        """Run cert_batch.main on a 3-leaf row with cert_item.certify replaced by a stub."""
        calls = []
        with tempfile.TemporaryDirectory(prefix="e85-h7-batch-") as tmp:
            root = Path(tmp)
            out, stop = root / "receipts.jsonl", root / "STOP"

            def fake_certify(cube, kind, leaf, work, bins, cap, heap_mb, keep_logs=False):
                calls.append((leaf, heap_mb))
                if stop_after is not None and len(calls) == stop_after:
                    stop.write_text("stop\n")
                return {"cube": "cube_a", "kind": kind, "leaf": leaf, "status": statuses[len(calls) - 1]}

            class Cube(FakeCube):
                n_leaves = 3

            row = {"id": "cube_a-b0000", "cube": "cube_a", "kind": "leaves", "start": 0, "end": 3}
            argv = ["cert_batch.py", "--inputs", str(root), "--batch", json.dumps(row), "--out", str(out),
                    "--work", str(root / "work"), "--heap-mb", "2000", "--stop-file", str(stop), *extra]
            bins = {k: {"path": k, "sha256": v} for k, v in hc.PINNED_BINARIES.items()}
            with patch.object(cert_batch.hc, "Cube", Cube), patch.object(cert_batch.cert_item, "certify", fake_certify), \
                    patch.object(cert_batch.cert_item, "tools", return_value=bins), patch.object(sys, "argv", argv):
                rc = cert_batch.main()
            recs = [json.loads(l) for l in out.read_text().splitlines()] if out.exists() else []
        return rc, calls, recs

    def test_heap_exhaustion_is_recorded_not_escalated(self):
        rc, calls, recs = self.run_batch(["CERTIFIED", "CHECK_HEAP_EXHAUSTED", "CERTIFIED"])
        self.assertEqual(rc, 1)
        self.assertEqual(calls, [(0, 2000), (1, 2000), (2, 2000)])  # one attempt per leaf, heap never grows
        self.assertEqual([r["status"] for r in recs], ["CERTIFIED", "CHECK_HEAP_EXHAUSTED", "CERTIFIED"])

    def test_stop_between_items(self):
        rc, calls, recs = self.run_batch(["CERTIFIED", "CERTIFIED", "CERTIFIED"], stop_after=1)
        self.assertEqual(rc, 4)
        self.assertEqual(len(calls), 1)
        self.assertEqual(len(recs), 1)

    def test_alarm_stops_the_batch(self):
        rc, calls, _ = self.run_batch(["CERTIFIED", "CHECK_FAILED", "CERTIFIED"])
        self.assertEqual(rc, 3)
        self.assertEqual(len(calls), 2)

    def test_no_heap_retry_symbol_left(self):
        self.assertFalse(hasattr(cert_batch, "MAX_HEAP_MB"))


class Pins(unittest.TestCase):
    def test_unapproved_binary_is_refused(self):
        with tempfile.TemporaryDirectory() as tmp:
            fake = Path(tmp) / "cake_lpr"
            fake.write_text("#!/bin/sh\nexit 0\n")
            with self.assertRaises(SystemExit):
                cert_item.tools(str(fake), str(fake))
            self.assertEqual(set(cert_item.tools(str(fake), str(fake), allow_unpinned=True)), {"cadical", "cake_lpr"})


if __name__ == "__main__":
    unittest.main(verbosity=2)
