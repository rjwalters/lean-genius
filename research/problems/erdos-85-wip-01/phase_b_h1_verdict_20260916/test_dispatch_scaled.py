import concurrent.futures
import contextlib
import io
import json
from pathlib import Path
import tempfile
import time
import unittest
from unittest.mock import patch

import dispatch_scaled as target


class ScaledDispatchTests(unittest.TestCase):
    def test_dry_run_selects_exact_residual_without_solving(self):
        with patch.object(target.base.runner, "run_case", side_effect=AssertionError("solver")), \
             patch.object(target.sys, "argv", ["scaled", "--workers", "24",
                                               "--materializers", "4"]), \
             contextlib.redirect_stdout(io.StringIO()) as output:
            self.assertEqual(target.main(), 0)
        report = json.loads(output.getvalue())
        self.assertEqual((report["selected_cases"], report["inventory_cases"]), (1137, 1161))
        self.assertEqual((report["workers"], report["materializers"]), (24, 4))
        self.assertFalse(report["proof_logging"])

    def test_scaled_route_does_not_accept_a_pilot_override(self):
        with patch.object(target.sys, "argv", ["scaled", "--pilot", "/tmp/alternate.json"]), \
             contextlib.redirect_stderr(io.StringIO()):
            with self.assertRaises(SystemExit):
                target.main()

    def test_frozen_pilot_manifest_bytes_are_required(self):
        with tempfile.TemporaryDirectory() as temp:
            changed = Path(temp) / "pilot-24.json"
            changed.write_bytes(target.PILOT.read_bytes() + b" ")
            with patch.object(target, "PILOT", changed), \
                 patch.object(target.sys, "argv", ["scaled"]):
                with self.assertRaisesRegex(ValueError, "Frozen 24-case pilot manifest changed"):
                    target.main()

    def test_preparation_semaphore_limits_concurrency(self):
        def prepare(*_):
            time.sleep(0.02)
            return {"status": "materialized"}
        gated = target.PreparationGate(prepare, 2)
        with concurrent.futures.ThreadPoolExecutor(max_workers=10) as pool:
            values = list(pool.map(lambda _: gated(None, None, None), range(10)))
        self.assertEqual(len(values), 10)
        self.assertEqual(gated.active, 0)
        self.assertEqual(gated.peak, 2)

    def test_scaling_gate_requires_completed_exact_pilot_and_monitor(self):
        with tempfile.TemporaryDirectory() as temp:
            base = Path(temp)
            ids = {f"h1_{i:016x}" for i in range(24)}
            config = b"pinned-config"
            pilot = {"schema": "erdos85-dispatch-results-v1",
                     "status": "complete", "config_sha256": target.sha(config),
                     "workers": 4, "proof_logging": False,
                     "selected_cases": sorted(ids),
                     "results": [{"id": case_id, "status": "UNKNOWN"} for case_id in sorted(ids)]}
            pilot_path = base / "pilot-results.json"
            pilot_path.write_text(json.dumps(pilot))
            monitor_path = base / "monitor.csv"
            monitor_path.write_bytes(
                b"utc,kissat_processes,cadical_processes,solver_rss_mib\n" +
                b"sample,4,0,500\n" * 24)
            gate = {"schema": "erdos85-h1-host-scaling-gate-v1",
                    "config_sha256": target.sha(config),
                    "pilot_results_sha256": target.sha(pilot_path.read_bytes()),
                    "resource_monitor_sha256": target.sha(monitor_path.read_bytes()),
                    "max_workers": 24, "max_materializers": 4,
                    "decision": "reviewed_host_scaling"}
            gate_path = base / "gate.json"
            gate_path.write_text(json.dumps(gate))
            with patch.object(target.base.runner, "require_banked_inventory"):
                with self.assertRaisesRegex(ValueError, "has not been approved"):
                    target.read_gate(gate_path, "a" * 40, {"raw": config},
                                     pilot_path, monitor_path, 24, 4, ids)
            with patch.object(target.base.runner, "require_banked_inventory"), \
                 patch.object(target, "APPROVED_GATE_SHA256", target.sha(gate_path.read_bytes())):
                loaded, _, saved_pilot, saved_monitor = target.read_gate(
                    gate_path, "a" * 40, {"raw": config},
                    pilot_path, monitor_path, 24, 4, ids)
                self.assertEqual(loaded, gate)
                self.assertEqual(saved_pilot, pilot_path.read_bytes())
                self.assertEqual(saved_monitor, monitor_path.read_bytes())
                pilot["selected_cases"][0] = "h1_wrong"
                pilot_path.write_text(json.dumps(pilot))
                with self.assertRaisesRegex(ValueError, "Banked scaling gate"):
                    target.read_gate(gate_path, "a" * 40, {"raw": config},
                                     pilot_path, monitor_path, 24, 4, ids)

    def test_gated_execution_keeps_base_receipt_schema_and_strict_status(self):
        plan, fresh = target.residual.select(target.CONFIG)
        pilot_ids = set(target.residual.pilot_ids(target.PILOT, target.CONFIG, fresh))
        selected = next(row["id"] for row in fresh if row["id"] not in pilot_ids)
        pilot = {"schema": "erdos85-dispatch-results-v1", "status": "complete",
                 "config_sha256": target.sha(plan["raw"]), "workers": 4,
                 "proof_logging": False, "selected_cases": sorted(pilot_ids),
                 "results": [{"id": case_id, "status": "UNKNOWN"}
                             for case_id in sorted(pilot_ids)]}
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            pilot_path = root / "pilot-results.json"
            pilot_path.write_text(json.dumps(pilot))
            monitor_path = root / "monitor.csv"
            monitor_path.write_bytes(
                b"utc,kissat_processes,cadical_processes,solver_rss_mib\n" +
                b"sample,4,0,500\n" * 24)
            gate = {"schema": "erdos85-h1-host-scaling-gate-v1",
                    "config_sha256": target.sha(plan["raw"]),
                    "pilot_results_sha256": target.sha(pilot_path.read_bytes()),
                    "resource_monitor_sha256": target.sha(monitor_path.read_bytes()),
                    "max_workers": 8, "max_materializers": 2,
                    "decision": "reviewed_host_scaling"}
            gate_path = root / "gate.json"
            gate_path.write_text(json.dumps(gate))
            output = root / "output"
            def fake_dispatch(cases, worker, workers, output_dir, state):
                self.assertEqual([case["id"] for case in cases], [selected])
                self.assertIsInstance(target.base.prepare, target.PreparationGate)
                state["results"] = [worker(cases[0])]
                state["not_started"] = []
                state["status"] = "complete"
                target.base.runner.write_json(output_dir / "results.json", state)
            with patch.object(target.base.runner, "require_banked_inventory"), \
                 patch.object(target, "APPROVED_GATE_SHA256", target.sha(gate_path.read_bytes())), \
                 patch.object(target.base.runner, "solver_identity",
                              side_effect=lambda p: {"path": str(p), "sha256": "a" * 64}), \
                 patch.object(target.base, "run_prepared_case",
                              return_value={"id": selected, "sector": "H1",
                                            "status": "UNSAT_CROSSCHECKED"}), \
                 patch.object(target.base, "dispatch", side_effect=fake_dispatch), \
                 patch.object(target.base, "RESERVE", 0), \
                 patch.object(target.sys, "argv",
                              ["scaled", "--execute", "--config-commit", "a" * 40,
                               "--wrapper-commit", "b" * 40,
                               "--scaling-gate", str(gate_path),
                               "--scaling-gate-commit", "c" * 40,
                               "--pilot-results", str(pilot_path),
                               "--resource-monitor", str(monitor_path),
                               "--case-id", selected, "--workers", "8",
                               "--materializers", "2", "--output-dir", str(output)]), \
                 contextlib.redirect_stdout(io.StringIO()):
                self.assertEqual(target.main(), 0)
            state = json.loads((output / "results.json").read_text())
            self.assertEqual(state["schema"], "erdos85-dispatch-results-v1")
            self.assertEqual((state["inventory_cases"], state["selected_cases"]), (1416, [selected]))
            self.assertTrue(state["selected_all_unsat"])
            self.assertFalse(state["inventory_all_unsat"])
            self.assertEqual(state["scaling_gate_sha256"], target.sha(gate_path.read_bytes()))
            self.assertEqual(state["pilot_results_sha256"], target.sha(pilot_path.read_bytes()))
            self.assertEqual(state["resource_monitor_sha256"], target.sha(monitor_path.read_bytes()))
            self.assertEqual(state["frozen_pilot_manifest_sha256"], target.PILOT_SHA256)
            self.assertEqual((output / "snapshots/pilot-24.json").read_bytes(), target.PILOT.read_bytes())


if __name__ == "__main__":
    unittest.main()
