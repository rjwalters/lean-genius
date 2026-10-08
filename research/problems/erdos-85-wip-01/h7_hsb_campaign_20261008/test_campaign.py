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
MANIFEST_V2_SHA256 = "0deb438f9bd7f5cfb840fd799330e6b80e70a043b21f96fcf0737c826515290c"  # 12,605 rows


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


def exercise_slot_loop(mode="race", max_batches=1):
    """codex's reservation fixture (h7_canary_limit_review_20261008/test_reservation.py, room 52850):
    the in-tree slot_loop AST with a delayed fake store and fake batches, two slots."""
    import ast
    import threading
    import time
    from types import SimpleNamespace
    path = HERE / "cert_worker.py"
    function, = [n for n in ast.parse(path.read_text()).body if isinstance(n, ast.FunctionDef) and n.name == "slot_loop"]
    state = {"errors": 0, "done": 0, "items": 0, "stop": False, "active": {}, "statuses": {}}
    node_lock, store_lock, second_listing = threading.Lock(), threading.Lock(), threading.Event()
    claims, batch_ids, logs, failures = set(), [], [], []

    class Store:
        listings = 0

        def exists(self, key):
            return mode == "stop"

        def listing(self, prefix):
            if mode == "store_error":
                raise RuntimeError("injected store error")
            with store_lock:
                self.listings += 1
                if self.listings >= 2:
                    second_listing.set()
            if mode == "race":
                second_listing.wait(timeout=0.25)
            with store_lock:
                return set(claims)

        def put_new(self, key, marker):
            row_id = key[len("claims/"):]
            with store_lock:
                if row_id in claims:
                    return False
                claims.add(row_id)
                return True

    def batch(args, store, slot, row):
        if mode == "batch_error":
            raise RuntimeError("injected batch error")
        with store_lock:
            batch_ids.append(row["id"])
        return {"id": row["id"], "status": "CERTIFIED", "ran": 1, "items": 1, "certified": 1}

    namespace = {"node": state, "lock": node_lock, "STARTED": time.time(), "MAX_NODE_ERRORS": 6,
                 "time": SimpleNamespace(time=time.time, sleep=lambda seconds: None), "run_batch": batch, "log": logs.append,
                 "put_with_retry": lambda *a: True}
    exec(compile(ast.Module(body=[function], type_ignores=[]), str(path), "exec"), namespace)
    args = SimpleNamespace(local_store=True, max_batches=max_batches, out=Path("/mock-only"),
                           lifetime=-1 if mode == "expired" else 60, min_left=0)
    rows = [] if mode == "empty" else [{"id": "batch-a"}, {"id": "batch-b"}]
    store = Store()

    def target(slot):
        try:
            namespace["slot_loop"](args, store, slot, rows)
        except BaseException as error:  # noqa: BLE001
            failures.append(repr(error))

    threads = [threading.Thread(target=target, args=(slot,), daemon=True) for slot in range(2)]
    for t in threads:
        t.start()
    for t in threads:
        t.join(timeout=3)
    assert not any(t.is_alive() for t in threads) and not failures, failures
    return {"claimed": sorted(claims), "completed": sorted(batch_ids), "state": state}


class Reservation(unittest.TestCase):
    def test_one_batch_limit_holds_with_a_slow_store(self):
        r = exercise_slot_loop()
        self.assertEqual(len(r["claimed"]), 1)
        self.assertEqual(r["state"]["done"], 1)
        self.assertEqual(r["state"]["active"], {})

    def test_stop_expiry_empty_and_store_errors_release_capacity(self):
        for mode in ("stop", "expired", "empty", "store_error"):
            with self.subTest(mode=mode):
                r = exercise_slot_loop(mode=mode)
                self.assertEqual(r["claimed"], [])
                self.assertEqual(r["state"]["done"], 0)
                self.assertEqual(r["state"]["active"], {})

    def test_batch_exception_releases_capacity(self):
        r = exercise_slot_loop(mode="batch_error")
        self.assertEqual(r["state"]["active"], {})
        self.assertGreater(r["state"]["errors"], 0)

    def test_unlimited_mode_still_runs_available_batches(self):
        r = exercise_slot_loop(mode="normal", max_batches=0)
        self.assertEqual(r["state"]["done"], 2)
        self.assertEqual(r["state"]["active"], {})


class Canary(unittest.TestCase):
    def test_canary_is_a_pinned_mix_of_main_manifest_rows(self):
        meta = json.loads((HERE / "receipts" / "inputs.json").read_text())
        rows = hc.canary_rows(meta)
        main = {r["id"]: r for r in hc.batches(meta)}
        self.assertEqual([r["id"] for r in rows], hc.CANARY_IDS)
        self.assertTrue(all(main[r["id"]] == r for r in rows))
        self.assertEqual(sum(r["kind"] == "cover" for r in rows), 2)
        self.assertEqual(sum(hc.row_items(r) for r in rows), 394)
        self.assertTrue(all(r["kind"] == "cover" for r in hc.batches(meta)[:28]))


class ManifestV2(unittest.TestCase):
    def setUp(self):
        self.meta = json.loads((HERE / "receipts" / "inputs.json").read_text())
        self.rows = hc.batches(self.meta)

    def test_every_leaf_exactly_once_and_covers(self):
        seen = {}
        for r in self.rows:
            if r["kind"] == "leaves":
                for leaf in range(r["start"], r["end"]):
                    self.assertNotIn((r["cube"], leaf), seen)
                    seen[(r["cube"], leaf)] = r["id"]
        self.assertEqual(len(seen), 377776)
        for c in hc.CUBES:
            self.assertEqual(sum(1 for k in seen if k[0] == c), self.meta["cubes"][c]["leaves"])
        self.assertEqual(sum(r["kind"] == "cover" for r in self.rows), 28)
        self.assertEqual(len({r["id"] for r in self.rows}), len(self.rows))
        self.assertFalse(any("." in r["id"] for r in self.rows))

    def test_head_first_in_batches_of_four(self):
        leaves = [r for r in self.rows if r["kind"] == "leaves"]
        first_tail = next(i for i, r in enumerate(leaves) if "-b" in r["id"])
        head, tail = leaves[:first_tail], leaves[first_tail:]
        self.assertTrue(all("-h" in r["id"] and r["end"] <= 1024 and r["end"] - r["start"] <= 4 for r in head))
        self.assertTrue(all("-b" in r["id"] and r["start"] >= 1024 and r["end"] - r["start"] <= 64 for r in tail))
        self.assertEqual([r["start"] for r in head[:28]], [0] * 28)  # leaf 0..3 of all 28 cubes come first
        self.assertEqual({r["cube"] for r in head[:28]}, set(hc.CUBES))

    def test_manifest_sha_is_pinned(self):
        self.assertEqual(hc.sha_bytes(hc.manifest_bytes(self.meta)), MANIFEST_V2_SHA256)


class ControllerStop(unittest.TestCase):
    """The detached controller must return (so its host powers off) when anyone has written STOP."""

    def run_pass(self, control):
        import cert_controller as cc
        calls = []
        base = {"utc": "t", "control": control, "estimated_spend_usd": 1.0}
        with patch.object(cc, "_reviewed_one_pass", lambda state, act: dict(base)), patch.object(cc, "ledgers", lambda: []), \
                patch.object(cc, "put_json", lambda key, obj: calls.append(key)), \
                patch.object(cc.vc, "aws", lambda *a, **k: ""), patch.object(cc.vc, "stop", lambda a: calls.append("stop")), \
                patch.object(cc, "MANIFEST", [{"id": "x"}]), tempfile.TemporaryDirectory() as tmp, \
                patch.object(cc.vc, "STRIPE", Path(tmp)):
            return cc.one_pass({}, True), calls

    def test_exits_on_foreign_stop_without_touching_the_cause(self):
        report, calls = self.run_pass(["STOP", "STOP-CAUSE"])
        self.assertEqual(report["action"], "STOP marker present; controller exits")
        self.assertNotIn("control/STOP-CAUSE", calls)
        self.assertNotIn("stop", calls)

    def test_keeps_watching_without_stop(self):
        report, _ = self.run_pass([])
        self.assertNotIn("action", report)


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
