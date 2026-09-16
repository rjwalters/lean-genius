#!/usr/bin/env python3
"""Host-only H1 residual verdict dispatch with bounded input preparation.

Dry run by default. A full queue needs a banked gate tied to the finished
24-case pilot and resource profile. No proof logging is requested.
"""
from __future__ import annotations

import argparse
import datetime as dt
import hashlib
import json
import os
from pathlib import Path
import shutil
import sys
import threading

HERE = Path(__file__).resolve().parent
SAT49 = HERE.parent / "sat49"
sys.path.insert(0, str(SAT49))

import dispatch_verdict_only as base  # noqa: E402
import dispatch_h1_residual_verdict_only as residual  # noqa: E402

CONFIG = HERE / "config.draft.json"
POLICY = {"crosscheck": True, "primary_cap_seconds": 14400,
          "crosscheck_cap_seconds": 14400}
MAX_WORKERS = 24
MAX_MATERIALIZERS = 4
PILOT = HERE / "pilot-24.json"
# A post-pilot reviewed revision must set this to the exact gate bytes.
# Until then, no scaled execution is possible.
APPROVED_GATE_SHA256 = None


def sha(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


class PreparationGate:
    """Bound simultaneous Docker materializations within the worker pool."""

    def __init__(self, prepare, slots: int):
        self.prepare = prepare
        self.semaphore = threading.Semaphore(slots)
        self.lock = threading.Lock()
        self.active = 0
        self.peak = 0

    def __call__(self, case, plan, directory):
        with self.semaphore:
            with self.lock:
                self.active += 1
                self.peak = max(self.peak, self.active)
            try:
                return self.prepare(case, plan, directory)
            finally:
                with self.lock:
                    self.active -= 1


def read_gate(path: Path, commit: str, plan: dict, pilot_results: Path,
              resource_monitor: Path, workers: int, materializers: int,
              expected_pilot_ids: set[str]) -> tuple[dict, bytes, bytes, bytes]:
    raw = path.read_bytes()
    base.runner.require_banked_inventory(path, commit, expected_bytes=raw)
    if APPROVED_GATE_SHA256 is None or sha(raw) != APPROVED_GATE_SHA256:
        raise ValueError("Scaling gate has not been approved in this source revision")
    gate = json.loads(raw)
    pilot_raw = pilot_results.read_bytes()
    monitor_raw = resource_monitor.read_bytes()
    pilot = json.loads(pilot_raw)
    if (gate.get("schema") != "erdos85-h1-host-scaling-gate-v1" or
            gate.get("config_sha256") != sha(plan["raw"]) or
            gate.get("pilot_results_sha256") != sha(pilot_raw) or
            gate.get("resource_monitor_sha256") != sha(monitor_raw) or
            type(gate.get("max_workers")) is not int or
            not 1 <= gate["max_workers"] <= MAX_WORKERS or
            type(gate.get("max_materializers")) is not int or
            not 1 <= gate["max_materializers"] <= MAX_MATERIALIZERS or
            gate.get("decision") != "reviewed_host_scaling" or
            pilot.get("schema") != "erdos85-dispatch-results-v1" or
            pilot.get("status") != "complete" or
            pilot.get("config_sha256") != sha(plan["raw"]) or
            pilot.get("workers") != 4 or pilot.get("proof_logging") is not False or
            len(pilot.get("selected_cases", [])) != 24 or
            set(pilot["selected_cases"]) != expected_pilot_ids or
            len(pilot.get("results", [])) != 24 or
            {r["id"] for r in pilot["results"]} != expected_pilot_ids or
            not monitor_raw.startswith(b"utc,kissat_processes,cadical_processes,") or
            len(monitor_raw.splitlines()) < 25 or
            workers > gate["max_workers"] or materializers > gate["max_materializers"]):
        raise ValueError("Banked scaling gate does not match completed pilot and resource profile")
    return gate, raw, pilot_raw, monitor_raw


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__, allow_abbrev=False)
    parser.add_argument("--execute", action="store_true")
    parser.add_argument("--config-commit")
    parser.add_argument("--wrapper-commit")
    parser.add_argument("--output-dir", type=Path)
    parser.add_argument("--workers", type=int, choices=range(1, MAX_WORKERS + 1), default=4)
    parser.add_argument("--materializers", type=int, choices=range(1, MAX_MATERIALIZERS + 1), default=2)
    parser.add_argument("--case-id", action="append")
    parser.add_argument("--scaling-gate", type=Path)
    parser.add_argument("--scaling-gate-commit")
    parser.add_argument("--pilot-results", type=Path)
    parser.add_argument("--resource-monitor", type=Path)
    parser.add_argument("--kissat", type=Path, default=Path("/opt/homebrew/bin/kissat"))
    parser.add_argument("--cadical", type=Path, default=Path("/opt/homebrew/bin/cadical"))
    args = parser.parse_args()
    if args.materializers > args.workers:
        parser.error("Materializer slots cannot exceed worker slots")
    plan, fresh = residual.select(CONFIG)
    if plan["config"]["policies"]["H1"] != POLICY:
        raise ValueError("H1 two-solver policy changed")
    allowed = {row["id"] for row in fresh}
    frozen_pilot_ids = set(residual.pilot_ids(PILOT, CONFIG, fresh))
    if args.case_id:
        selected = set(args.case_id)
        if (len(selected) != len(args.case_id) or not selected <= allowed or
                selected & frozen_pilot_ids):
            parser.error("Case IDs must be distinct H1 residual roots outside the frozen pilot")
        ids = [row["id"] for row in fresh if row["id"] in selected]
    else:
        ids = [row["id"] for row in fresh if row["id"] not in frozen_pilot_ids]
    cases = [row for row in fresh if row["id"] in set(ids)]
    if not args.execute:
        print(json.dumps({"mode": "dry_run", "selected_cases": len(cases),
                          "inventory_cases": 1161, "workers": args.workers,
                          "materializers": args.materializers, "proof_logging": False,
                          "solver_launched": False}))
        return 0
    if not args.config_commit or not args.wrapper_commit or not args.output_dir:
        parser.error("Execution requires banked config/wrapper commits and a new output directory")
    for path, raw in plan["captured"]:
        base.runner.require_banked_inventory(path, args.config_commit, expected_bytes=raw)
    wrapper = Path(__file__).resolve()
    wrapper_raw = wrapper.read_bytes()
    base.runner.require_banked_inventory(wrapper, args.wrapper_commit, expected_bytes=wrapper_raw)
    residual_path = Path(residual.__file__).resolve()
    base.runner.require_banked_inventory(residual_path, args.config_commit,
                                         expected_bytes=residual_path.read_bytes())
    if not all((args.scaling_gate, args.scaling_gate_commit,
                args.pilot_results, args.resource_monitor)):
        parser.error("Execution requires a banked scaling gate and pilot receipts")
    gate_path = args.scaling_gate.resolve()
    gate, raw, pilot_raw, monitor_raw = read_gate(
        gate_path, args.scaling_gate_commit, plan,
        args.pilot_results.resolve(), args.resource_monitor.resolve(),
        args.workers, args.materializers, frozen_pilot_ids)
    snapshots = [(gate_path.name, raw),
                 ("pilot-results.json", pilot_raw),
                 ("resource-monitor.csv", monitor_raw)]
    start = dt.datetime.fromisoformat(plan["config"]["not_before"].replace("Z", "+00:00"))
    if dt.datetime.now(dt.timezone.utc) < start:
        parser.error("Execution window has not started")
    output = args.output_dir.resolve()
    output.parent.mkdir(parents=True, exist_ok=True)
    if shutil.disk_usage(output.parent).free < base.RESERVE:
        parser.error("Fewer than 8 GiB free on output volume")
    output.mkdir()
    retained = output / "snapshots"
    retained.mkdir()
    for number, (path, raw) in enumerate(plan["captured"]):
        (retained / f"{number:02d}-{path.name}").write_bytes(raw)
    (retained / wrapper.name).write_bytes(wrapper_raw)
    (retained / residual_path.name).write_bytes(residual_path.read_bytes())
    for name, raw in snapshots:
        (retained / name).write_bytes(raw)
    kissat, cadical = args.kissat.resolve(), args.cadical.resolve()
    identities = {name: base.runner.solver_identity(binary) for name, binary in
                  (("kissat", kissat), ("cadical", cadical))}
    state = {"schema": "erdos85-dispatch-results-v1", "status": "running",
             "pid": os.getpid(), "config_sha256": sha(plan["raw"]),
             "config_commit": args.config_commit, "wrapper_commit": args.wrapper_commit,
             "index_sha256": plan["config"]["index"]["sha256"],
             "inventory_cases": 1416, "residual_inventory_cases": 1161,
             "frozen_pilot_cases": len(frozen_pilot_ids),
             "selected_cases": ids,
             "workers": args.workers, "materializers": args.materializers,
             "proof_logging": False, "solvers": identities,
             "results": [], "historical_evidence": plan["historical"],
             "historical_skipped": sorted(r["id"] for r in plan["historical"])}
    base.runner.write_json(output / "results.json", state)
    original_prepare = base.prepare
    bounded_prepare = PreparationGate(original_prepare, args.materializers)

    def worker(case):
        result = base.run_prepared_case(case, plan, output, kissat, cadical)
        if result["status"] == "UNSAT_PRIMARY":
            result["status"] = "ERROR"
            result["error"] = "Primary-only UNSAT is insufficient for H1"
            base.runner.write_json(output / case["id"] / "result.json", result)
        return result

    try:
        base.prepare = bounded_prepare
        with base.runner.cancellation_handlers():
            base.dispatch(cases, worker, args.workers, output, state)
    finally:
        base.prepare = original_prepare
    state["max_concurrent_preparations"] = bounded_prepare.peak
    if wrapper.read_bytes() != wrapper_raw or residual_path.read_bytes() != (
            retained / residual_path.name).read_bytes():
        state["status"] = "stopped"
        state["source_drift"] = True
    state["selected_all_unsat"] = (not state["not_started"] and
                                   not state.get("source_drift", False) and
                                   all(r["status"] == "UNSAT_CROSSCHECKED" for r in state["results"]))
    state["inventory_all_unsat"] = False
    state["scaled_remainder_all_unsat"] = len(cases) == 1137 and state["selected_all_unsat"]
    base.runner.write_json(output / "results.json", state)
    print(json.dumps({k: v for k, v in state.items() if k not in ("results", "solvers")}))
    return 0 if state["selected_all_unsat"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
