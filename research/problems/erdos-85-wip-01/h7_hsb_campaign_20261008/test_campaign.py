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
            if prefix.startswith("ledger"):
                with store_lock:
                    return {f"{i}.i-x.1.json" for i in batch_ids}
            if mode == "orphan":  # batch-a is held by a dead node until the 3rd listing of claims
                with store_lock:
                    return set(claims) | ({"batch-a"} if self.listings <= 4 else set())
            with store_lock:
                return set(claims)

        def put_new(self, key, marker):
            row_id = key[len("claims/"):]
            with store_lock:
                if row_id in claims or (mode == "orphan" and row_id == "batch-a" and self.listings <= 4):
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
                 "put_with_retry": lambda *a: True, "random": SimpleNamespace(random=lambda: 0.0)}
    exec(compile(ast.Module(body=[function], type_ignores=[]), str(path), "exec"), namespace)
    args = SimpleNamespace(local_store=True, max_batches=max_batches, out=Path("/mock-only"),
                           lifetime=-1 if mode == "expired" else 60, min_left=0, claim_wait=0)
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

    def test_slot_waits_for_orphaned_claims_instead_of_exiting(self):
        # batch-a is claimed by a dead node and has no ledger; the controller releases it later.
        r = exercise_slot_loop(mode="orphan", max_batches=0)
        self.assertEqual(r["completed"], ["batch-a", "batch-b"])
        self.assertEqual(r["state"]["done"], 2)
        self.assertEqual(r["state"]["active"], {})

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
                patch.object(cc.vc, "aws", lambda *a, **k: calls.append(("aws",) + a) or ""), \
                patch.object(cc.vc, "stop", lambda a: calls.append("stop")), \
                patch.object(cc.vc, "aws_json", lambda *a: {"Fleets": [{"FleetId": "fleet-1", "Tags": [{"Key": "project", "Value": cc.vc.TAG}]}]}), \
                patch.object(cc.vc, "instances", lambda: [{"id": "i-1", "state": "running"}]), \
                patch.object(cc.vc, "row_filter", lambda rows, states: [r for r in rows if r["state"] in states]), \
                patch.object(cc, "MANIFEST", [{"id": "x"}]), tempfile.TemporaryDirectory() as tmp, \
                patch.object(cc.vc, "STRIPE", Path(tmp)):
            return cc.one_pass({}, True), calls

    def test_exits_on_foreign_stop_without_touching_the_cause(self):
        report, calls = self.run_pass(["STOP", "STOP-CAUSE"])
        self.assertEqual(report["action"], "STOP marker present; controller exits")
        self.assertNotIn("control/STOP-CAUSE", calls)
        self.assertNotIn("stop", calls)  # the marker is not rewritten
        # but the fleet is ended (codex 53145): a maintain fleet must not outlive the controller
        self.assertIn(("aws", "ec2", "delete-fleets", "--fleet-ids", "fleet-1", "--terminate-instances"), calls)
        self.assertIn(("aws", "ec2", "terminate-instances", "--instance-ids", "i-1"), calls)
        self.assertEqual(report["stop_enforced"], {"deleted_fleets": ["fleet-1"], "terminated": ["i-1"]})

    def test_orphan_release_total_is_cumulative(self):
        import cert_controller as cc
        state = {}
        seq = iter([2, 0])
        with patch.object(cc, "_reviewed_one_pass", lambda s, act: {"utc": "t", "control": [], "orphans_released": next(seq)}), \
                patch.object(cc, "ledgers", lambda: []), patch.object(cc, "put_json", lambda *a: None), \
                patch.object(cc.vc, "aws", lambda *a, **k: ""), patch.object(cc, "MANIFEST", [{"id": "x"}]), \
                tempfile.TemporaryDirectory() as tmp, patch.object(cc.vc, "STRIPE", Path(tmp)):
            cc.one_pass(state, True)
            report = cc.one_pass(state, True)
        self.assertEqual(report["orphans_released_this_pass"], 0)
        self.assertEqual(report["orphans_released_total"], 2)
        self.assertEqual(report["orphan_release_passes"], [{"utc": "t", "released": 2}])

    def test_drained_main_pass_stops_the_fleet(self):
        import cert_controller as cc
        calls = []
        ledgers = [{"id": "x", "status": "CERTIFIED"}, {"id": "y", "status": "INCOMPLETE"}]
        with patch.object(cc, "_reviewed_one_pass", lambda s, act: {"utc": "t", "control": []}), \
                patch.object(cc, "ledgers", lambda: ledgers), patch.object(cc, "put_json", lambda key, obj: calls.append((key, obj))), \
                patch.object(cc.vc, "aws", lambda *a, **k: ""), patch.object(cc.vc, "stop", lambda a: calls.append("stop")), \
                patch.object(cc, "MANIFEST", [{"id": "x"}, {"id": "y"}]), tempfile.TemporaryDirectory() as tmp, \
                patch.object(cc.vc, "STRIPE", Path(tmp)):
            report = cc.one_pass({}, True)
        self.assertEqual(report["action"], cc.DRAINED)
        self.assertIn("stop", calls)
        self.assertEqual(report["incomplete_batches"], 1)

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


# ---- split leaves (README section 9) ---------------------------------------------------------------

import hashlib  # noqa: E402
import random  # noqa: E402

import split_leaf  # noqa: E402

REAL_INPUTS = Path("/Volumes/Stripe/lean-genius/artifacts/erdos85-sat49/h7-hsb-campaign-20261008/inputs")


def independent_cnf(files: dict, leaf: int, appended: list[str]) -> bytes:
    """Build a split CNF from the raw input files without h7_common: header with the counted clause
    lines, canonical body, cube units, hsb, the leaf's positive units (cover line negated, in order),
    then the appended lines."""
    cover_line = files["cover"].splitlines()[leaf].split()
    assert cover_line[-1] == b"0"
    leaf_units = [f"{-int(t)} 0\n".encode() for t in cover_line[:-1]]
    lines = (files["body"] + files["units"] + files["hsb"]).splitlines(keepends=True) + leaf_units + \
        [x.encode() for x in appended]
    return f"p cnf 17633 {len(lines)}\n".encode() + b"".join(lines)


def make_inputs(root: Path, name: str = "cube_syn", nvars: int = 14, seed: int = 7) -> dict:
    """A tiny synthetic cube in the inputs layout. Variables nvars+1..861 are fixed by cube units, so the
    split can only branch on 1..nvars."""
    rng = random.Random(seed)
    body = "".join(" ".join(str(rng.choice((-1, 1)) * v) for v in rng.sample(range(1, nvars + 1), 3)) + " 0\n"
                   for _ in range(2 * nvars)).encode()
    units = "".join(f"{v} 0\n" for v in range(nvars + 1, 862)).encode()
    hsb = b"-1 -2 3 0\n4 5 0\n"
    cover = b"-6 -7 0\n-8 -9 0\n-6 -9 0\n"
    files = {"body": body, "units": units, "hsb": hsb, "cover": cover}
    root.mkdir(parents=True, exist_ok=True)
    (root / "canonical.body").write_bytes(body)
    for ext in ("units", "hsb", "cover"):
        (root / f"{name}.{ext}").write_bytes(files[ext])
    (root / "inputs.json").write_text(json.dumps({"cubes": {name: {"mask": 0}}}))
    return files


class SyntheticCube:
    """Context manager: hc.Cube / CUBES / CUBE_CLAUSES patched for a synthetic inputs directory."""

    def __init__(self, root: Path, files: dict, name: str = "cube_syn"):
        n_body = files["body"].count(b"\n") + files["units"].count(b"\n")
        real = hc.Cube
        self.patches = [patch.object(hc, "CUBE_CLAUSES", n_body), patch.object(hc, "CUBES", [name]),
                        patch.object(hc, "Cube", lambda inputs, nm, verify=True: real(inputs, nm, verify=False))]

    def __enter__(self):
        for p in self.patches:
            p.start()

    def __exit__(self, *exc):
        for p in reversed(self.patches):
            p.stop()


class SplitBytes(unittest.TestCase):
    """Sub-leaf / sub-cover CNF bytes = an independent construction of the Lean terms
    leafSatCnf ++ cnfClauseNegUnits c  and  leafSatCnf ++ cnfOfClauseList blocking."""

    def test_synthetic_subleaf_and_subcover_bytes(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            files = make_inputs(root)
            with SyntheticCube(root, files):
                cube = hc.Cube(root, "cube_syn")
                for leaf in range(3):
                    clause = [-5, 7, -12]  # Lean literals (4,false),(6,true),(11,false)
                    # cnfClauseNegUnits flips each literal: units 5, -7, 12 in clause order
                    want = independent_cnf(files, leaf, ["5 0\n", "-7 0\n", "12 0\n"])
                    out = root / "s.cnf"
                    cube.write_subleaf(leaf, clause, out)
                    self.assertEqual(out.read_bytes(), want)
                    self.assertEqual(cube.subleaf_sha256(leaf, clause), hashlib.sha256(want).hexdigest())
                    blocking = [[-5, 7], [5, -7, 3], [11]]
                    want = independent_cnf(files, leaf, ["-5 7 0\n", "5 -7 3 0\n", "11 0\n"])
                    cube.write_subcover(leaf, blocking, out)
                    self.assertEqual(out.read_bytes(), want)
                    self.assertEqual(cube.subcover_sha256(leaf, blocking), hashlib.sha256(want).hexdigest())

    def test_bad_clauses_are_refused(self):
        for bad in ([], [0], [17634], [3, -3], [2, 2], "1 2", [1.0]):
            with self.assertRaises(ValueError, msg=repr(bad)):
                hc.check_clause(bad)

    @unittest.skipUnless((REAL_INPUTS / "inputs.json").is_file(), "pinned inputs not on this host")
    def test_real_inputs_subleaf_and_subcover_bytes(self):
        cube = hc.Cube(REAL_INPUTS, "cube_F9_t0")  # verifies every pinned hash of the cube
        files = {"body": (REAL_INPUTS / "canonical.body").read_bytes(), "units": (REAL_INPUTS / "cube_F9_t0.units").read_bytes(),
                 "hsb": (REAL_INPUTS / "cube_F9_t0.hsb").read_bytes(), "cover": (REAL_INPUTS / "cube_F9_t0.cover").read_bytes()}
        leaf_cnf = independent_cnf(files, 1, [])
        self.assertEqual(hashlib.sha256(leaf_cnf).hexdigest(), cube.leaf_sha256(1))
        clause = [-158, -153, 266, -860]
        want = independent_cnf(files, 1, ["158 0\n", "153 0\n", "-266 0\n", "860 0\n"])
        self.assertEqual(cube.subleaf_sha256(1, clause), hashlib.sha256(want).hexdigest())
        blocking = [[-158], [158, -153], [158, 153]]
        want = independent_cnf(files, 1, ["-158 0\n", "158 -153 0\n", "158 153 0\n"])
        self.assertEqual(cube.subcover_sha256(1, blocking), hashlib.sha256(want).hexdigest())
        with tempfile.TemporaryDirectory() as tmp:
            out = Path(tmp) / "c.cnf"
            cube.write_subcover(1, blocking, out)
            self.assertEqual(hc.sha_file(out), hashlib.sha256(want).hexdigest())


class SplitGenerator(unittest.TestCase):
    def run_generate(self, leaves, depth=3):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            files = make_inputs(root)
            with SyntheticCube(root, files):
                specs, rows = split_leaf.generate(root, leaves, depth, jobs=1)
                raw = split_leaf.manifest_bytes(rows)
        return specs, rows, raw, files

    def test_manifest_is_deterministic_and_order_independent(self):
        a = self.run_generate([("cube_syn", 0), ("cube_syn", 2), ("cube_syn", 1)])
        b = self.run_generate([("cube_syn", 1), ("cube_syn", 0), ("cube_syn", 2)])
        self.assertEqual(a[2], b[2])
        specs, rows = a[0], a[1]
        self.assertEqual([s["leaf"] for s in specs], [0, 1, 2])
        self.assertEqual(len({r["id"] for r in rows}), len(rows))
        self.assertFalse(any("." in r["id"] for r in rows))
        for s in specs:
            mine = [r for r in rows if r["leaf"] == s["leaf"]]
            self.assertEqual(mine[0]["kind"], "subcover")
            self.assertEqual(mine[0]["clauses"], s["clauses"])
            self.assertEqual([r["clause"] for r in mine[1:]], s["clauses"])
            self.assertEqual([r["index"] for r in mine[1:]], list(range(len(s["clauses"]))))
            self.assertTrue(all(r["split_sha256"] == s["split_sha256"] for r in mine))
            self.assertTrue(1 <= len(s["clauses"]) <= 8)

    def test_cubes_cover_every_model_of_the_leaf(self):
        """Brute force: every model of the leaf CNF falsifies some blocking clause (sub-cover UNSAT)."""
        specs, _, _, files = self.run_generate([("cube_syn", 0), ("cube_syn", 1), ("cube_syn", 2)], depth=4)
        base = [[int(t) for t in l.split()[:-1]] for l in (files["body"] + files["hsb"]).splitlines()]
        base = [c for c in base if all(abs(x) <= 14 for x in c)]
        for s in specs:
            units = [-int(t) for t in files["cover"].splitlines()[s["leaf"]].split()[:-1]]
            models = 0
            for bits in range(1 << 14):
                val = lambda x: ((bits >> (abs(x) - 1)) & 1) == (1 if x > 0 else 0)  # noqa: E731
                if not all(val(u) for u in units) or not all(any(val(x) for x in c) for c in base):
                    continue
                models += 1
                self.assertTrue(any(not any(val(x) for x in c) for c in s["clauses"]), (s["leaf"], bits))
            self.assertGreater(models, 0)


class SplitFakeCube:
    def __init__(self, *args, **kwargs):
        self.name = args[1] if len(args) > 1 else "cube_a"
        self.meta = {"cover_cnf_sha256": "a" * 64}
        self.n_leaves = 2

    def leaf_sha256(self, leaf):
        return {0: "b" * 64, 1: "d" * 64}[leaf]

    def subleaf_sha256(self, leaf, clause):
        hc.check_clause(clause)
        return hashlib.sha256(json.dumps(["sub", leaf, clause]).encode()).hexdigest()

    def subcover_sha256(self, leaf, clauses):
        return hashlib.sha256(json.dumps(["cov", leaf, clauses]).encode()).hexdigest()


class SplitCollector(unittest.TestCase):
    """Leaf 1 of cube_a is certified only through a complete split; leaf 0 and the cover directly."""
    B = [[-3, -4], [-3, 4], [3]]

    def receipts(self, mutate=None):
        cube = SplitFakeCube(None, "cube_a")
        sha = hc.split_sha256("cube_a", 1, cube.leaf_sha256(1), self.B)
        ok = {"status": "CERTIFIED", "binaries": {"cadical": collector.CADICAL, "cake_lpr": CAKE},
              "checker": {"verified_line": True, "cpu_seconds": 1}, "solver": {"returncode": 20, "cpu_seconds": 2, "conflicts": 5},
              "host": "h", "proof": {"checker_closed_early": False, "bytes": 10, "sha256": "c" * 64}}
        rows = [dict(ok, cube="cube_a", kind="cover", leaf=None, cnf_sha256="a" * 64),
                dict(ok, cube="cube_a", kind="leaf", leaf=0, cnf_sha256="b" * 64),
                dict(ok, cube="cube_a", kind="subcover", leaf=1, split_sha256=sha, clauses=self.B,
                     cnf_sha256=cube.subcover_sha256(1, self.B))]
        rows += [dict(ok, cube="cube_a", kind="subleaf", leaf=1, split_sha256=sha, index=i, clause=c,
                      cnf_sha256=cube.subleaf_sha256(1, c)) for i, c in enumerate(self.B)]
        if mutate:
            mutate(rows)
        return rows

    def collect(self, rows):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            (root / "in").mkdir()
            (root / "res").mkdir()
            (root / "in" / "inputs.json").write_text("{}\n")
            (root / "res" / "f.jsonl.zst").write_bytes(b"x")
            decoded = "".join(json.dumps(r) + "\n" for r in rows).encode()
            argv = ["collect_receipts.py", "--inputs", str(root / "in"), "--results", str(root / "res"), "--out", str(root / "out")]
            real_run = subprocess.run

            def fake_run(cmd, *a, **k):
                if cmd[0] == "zstd" and "-dc" in cmd:
                    return subprocess.CompletedProcess([], 0, stdout=decoded)
                return real_run(cmd, *a, **k)
            with patch.object(collector.hc, "CUBES", ["cube_a"]), patch.object(collector.hc, "Cube", SplitFakeCube), \
                    patch.object(collector.subprocess, "run", fake_run), patch.object(sys, "argv", argv), \
                    contextlib.redirect_stdout(io.StringIO()) as out:
                rc = collector.main()
            summary = json.loads(out.getvalue())
            split_tsv = (root / "out" / "cube_a.split-receipts.tsv.zst").is_file()
        return rc, summary["cubes"]["cube_a"], split_tsv

    def test_complete_split_certifies_the_leaf(self):
        rc, c, split_tsv = self.collect(self.receipts())
        self.assertEqual(rc, 0)
        self.assertTrue(c["complete"])
        self.assertEqual((c["certified_leaves"], c["split_leaves"], c["split_items"]), (2, 1, 4))
        self.assertTrue(split_tsv)

    def test_incomplete_or_mismatched_splits_do_not(self):
        def drop_subleaf(rows):
            rows.pop()

        def other_split_sha(rows):
            rows[-1]["split_sha256"] = "e" * 64

        def cover_list_not_the_split(rows):
            rows[2]["clauses"] = self.B[:2]  # cnf sha recomputed would differ, and the split sha no longer matches

        def cover_list_tampered_consistently(rows):  # sha256 of the CNF fits the new list, but split sha does not
            rows[2]["clauses"] = self.B[:2]
            rows[2]["cnf_sha256"] = SplitFakeCube(None, "cube_a").subcover_sha256(1, self.B[:2])

        def subleaf_wrong_clause(rows):
            rows[-1]["clause"] = [-3, 5]
            rows[-1]["cnf_sha256"] = SplitFakeCube(None, "cube_a").subleaf_sha256(1, [-3, 5])

        def subleaf_cnf_sha_wrong(rows):
            rows[-1]["cnf_sha256"] = "0" * 64

        def subcover_unapproved_checker(rows):
            rows[2]["binaries"] = dict(rows[2]["binaries"], cake_lpr="0" * 64)

        def subleaf_not_verified(rows):
            rows[3]["checker"] = {"verified_line": False, "cpu_seconds": 1}

        def no_subcover(rows):
            del rows[2]

        for m in (drop_subleaf, other_split_sha, cover_list_not_the_split, cover_list_tampered_consistently,
                  subleaf_wrong_clause, subleaf_cnf_sha_wrong, subcover_unapproved_checker, subleaf_not_verified, no_subcover):
            with self.subTest(m.__name__):
                rc, c, _ = self.collect(self.receipts(m))
                self.assertEqual(rc, 1)
                self.assertFalse(c["complete"])
                self.assertEqual((c["certified_leaves"], c["split_leaves"], c["missing_leaves"]), (1, 0, 1))

    def test_sat_subleaf_is_an_alarm(self):
        def sat(rows):
            rows.append(dict(rows[-1], status="SOLVER_SAT"))
        rc, c, _ = self.collect(self.receipts(sat))
        self.assertEqual(c["alarm_receipts"], 1)
        self.assertFalse(c["complete"])


class SplitBatch(unittest.TestCase):
    """cert_batch passes the manifest row to cert_item for split kinds, and requires retention for sub-covers."""

    def test_subleaf_and_subcover_rows(self):
        calls = []
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)

            def fake_certify(cube, kind, leaf, work, bins, cap, heap_mb, keep_logs=False, split=None):
                calls.append((kind, leaf, split["id"]))
                return {"cube": "cube_a", "kind": kind, "leaf": leaf, "status": "CERTIFIED"}

            def fake_retained(cube, retain, bins, cap, heap_mb, split=None):
                calls.append(("retained", split["leaf"], split["id"]))
                return {"cube": "cube_a", "kind": "subcover", "leaf": split["leaf"], "status": "CERTIFIED"}

            class Cube(SplitFakeCube):
                pass
            bins = {k: {"path": k, "sha256": v} for k, v in hc.PINNED_BINARIES.items()}
            sub = {"id": "cube_a-s00001-abcdef01-002", "cube": "cube_a", "kind": "subleaf", "leaf": 1, "index": 2,
                   "clause": [3], "split_sha256": "f" * 64, "subleaves": 3}
            cov = {"id": "cube_a-s00001-abcdef01-cover", "cube": "cube_a", "kind": "subcover", "leaf": 1,
                   "clauses": [[-3], [3]], "split_sha256": "f" * 64, "subleaves": 2}
            for row, extra in ((sub, []), (cov, ["--retain-covers", str(root / "ret")])):
                argv = ["cert_batch.py", "--inputs", str(root), "--batch", json.dumps(row), "--out", str(root / f"{row['kind']}.jsonl"),
                        "--work", str(root / "w"), *extra]
                with patch.object(cert_batch.hc, "Cube", Cube), patch.object(cert_batch.cert_item, "certify", fake_certify), \
                        patch.object(cert_batch.cert_item, "certify_cover_retained", fake_retained), \
                        patch.object(cert_batch.cert_item, "tools", return_value=bins), patch.object(sys, "argv", argv):
                    self.assertEqual(cert_batch.main(), 0)
            self.assertEqual(calls, [("subleaf", 1, sub["id"]), ("retained", 1, cov["id"])])
            self.assertEqual(hc.row_items(sub), 1)
            self.assertEqual(hc.row_items(cov), 1)


class SplitPass(unittest.TestCase):
    def test_split_pass_has_its_own_prefix_tag_and_stop(self):
        import cert_controller as cc
        saved = (cc.vc.PREFIX, cc.vc.BASE_PREFIX, cc.vc.TAG, cc.vc.LT_NAME, cc.vc.STRIPE, cc.vc.BASE_STRIPE,
                 cc.vc.HARD_STOP_USD, dict(cc.vc.PASS), cc.PASS_NAME)
        try:
            cc.select_pass("split")
            self.assertEqual(cc.vc.PREFIX, "sat49/h7hsb-20261008-split")
            self.assertEqual(cc.vc.TAG, "e85-h7hsb-20261008-split")
            self.assertEqual(cc.vc.LT_NAME, cc.vc.TAG)
            self.assertEqual(cc.vc.HARD_STOP_USD, 60.0)
            self.assertTrue(str(cc.vc.STRIPE).endswith("run-split"))
            self.assertNotIn(cc.vc.PREFIX, (cc.MAIN_PREFIX, cc.RESIDUAL_PREFIX, cc.CANARY_PREFIX))
            self.assertIn(cc.SPLIT_PREFIX, cc.ALL_PREFIXES)
            self.assertIn(cc.SPLIT_TAG, cc.ALL_TAGS)
        finally:
            (cc.vc.PREFIX, cc.vc.BASE_PREFIX, cc.vc.TAG, cc.vc.LT_NAME, cc.vc.STRIPE, cc.vc.BASE_STRIPE,
             cc.vc.HARD_STOP_USD, pass_, cc.PASS_NAME) = saved
            cc.vc.PASS.clear()
            cc.vc.PASS.update(pass_)

    def test_uncertified_leaves_from_main_and_residual_ledgers(self):
        import cert_controller as cc
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            for d, ledgers in (("run", [{"id": "cube_F7_t0-h0000", "cube": "cube_F7_t0", "kind": "leaves", "status": "INCOMPLETE",
                                         "not_certified": [{"leaf": 1, "status": "SOLVER_TIMEOUT"}, {"leaf": 2, "status": "SOLVER_TIMEOUT"},
                                                           {"leaf": 3, "status": "CHECK_HEAP_EXHAUSTED"}]},
                                        {"id": "cube_F9_t0-h0000", "cube": "cube_F9_t0", "kind": "leaves", "status": "CERTIFIED",
                                         "not_certified": []}]),
                               ("run-residual", [{"id": "cube_F7_t0-r00001", "cube": "cube_F7_t0", "kind": "leaves", "status": "CERTIFIED"},
                                                 {"id": "cube_F7_t0-r00002", "cube": "cube_F7_t0", "kind": "leaves", "status": "INCOMPLETE"}])):
                (root / d / "ledger").mkdir(parents=True)
                for k, l in enumerate(ledgers):
                    (root / d / "ledger" / f"{l['id']}.i-x.{k}.json").write_text(json.dumps(l))
            with patch.object(cc, "STRIPE", root):
                leaves, info = cc.uncertified_leaves("uncertified")
                failed, _ = cc.uncertified_leaves("residual-failed")
        self.assertEqual(leaves, [("cube_F7_t0", 2), ("cube_F7_t0", 3)])
        self.assertEqual(failed, [("cube_F7_t0", 2)])
        self.assertEqual(info["residual_certified"], 1)


if __name__ == "__main__":
    unittest.main(verbosity=2)
