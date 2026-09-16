#!/usr/bin/env python3
"""Read-only receipt and resource audit for the frozen H1 24-root pilot.

The report supplies evidence for a later human-reviewed scaling gate. It does
not approve scaling, launch solvers, or turn UNSAT verdicts into proofs.
"""
from __future__ import annotations

import argparse
from collections import Counter
import csv
import datetime as dt
import hashlib
import json
import math
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
SAT49 = HERE.parent / "sat49"
sys.path.insert(0, str(SAT49))

import dispatch_h1_residual_verdict_only as residual  # noqa: E402
import summarize_phase_b_verdicts as verdicts  # noqa: E402

CONFIG = HERE / "config.draft.json"
PILOT = HERE / "pilot-24.json"
CONFIG_SHA256 = "f7cf7a15894a114d30f4069abc1198af1397d6f8f3b85b0f0eae3b4e294d66a3"
PILOT_SHA256 = "f94b9c0d77061db7c65575bd50ad68690ba9442a8898830bd4a38ec53c340063"
PRIMARY_FIELDS = {"utc", "kissat_processes", "cadical_processes",
                  "solver_rss_mib", "largest_solver_rss_mib",
                  "memory_free_percent", "output_disk_kib"}
SUPPLEMENT_FIELDS = {"utc", "host_process_rss_mib", "docker_host_rss_mib",
                     "swap_used_mib", "docker_container_stats_json",
                     "docker_stats_error"}


def require(condition, message):
    if not condition:
        raise ValueError(message)


def sha(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def read_monitor(path: Path, required: set[str]):
    raw = path.read_bytes()
    text = raw.decode("utf-8")
    reader = csv.DictReader(text.splitlines())
    require(reader.fieldnames is not None and required <= set(reader.fieldnames) and
            len(set(reader.fieldnames)) == len(reader.fieldnames),
            f"Monitor header mismatch: {path}")
    rows = list(reader)
    require(rows and all(None not in row and all(value is not None for value in row.values())
                         for row in rows), f"Empty or malformed monitor: {path}")
    times = [dt.datetime.fromisoformat(row["utc"]) for row in rows]
    require(all(t.tzinfo is not None and t.utcoffset() == dt.timedelta(0) for t in times)
            and all(a < b for a, b in zip(times, times[1:])),
            f"Monitor timestamps are not increasing UTC: {path}")
    gaps = [(b - a).total_seconds() for a, b in zip(times, times[1:])]
    common = {"path": str(path), "sha256": sha(raw), "bytes": len(raw),
              "samples": len(rows), "first_utc": times[0].isoformat(),
              "last_utc": times[-1].isoformat(),
              "span_seconds": (times[-1] - times[0]).total_seconds(),
              "maximum_sample_gap_seconds": max(gaps, default=0)}
    return rows, times, common


def nonnegative(row: dict, key: str) -> float:
    value = float(row[key])
    require(math.isfinite(value) and value >= 0, f"Invalid monitor value: {key}")
    return value


def count(row: dict, key: str) -> int:
    value = int(row[key])
    require(str(value) == row[key] and value >= 0, f"Invalid monitor process count: {key}")
    return value


def primary_monitor(path: Path, workers: int) -> dict:
    rows, _, report = read_monitor(path, PRIMARY_FIELDS)
    process_counts = [(count(r, "kissat_processes"), count(r, "cadical_processes"))
                      for r in rows]
    require(all(k + c <= workers for k, c in process_counts),
            "Primary monitor exceeds frozen worker count")
    rss = [nonnegative(r, "solver_rss_mib") for r in rows]
    largest = [nonnegative(r, "largest_solver_rss_mib") for r in rows]
    free = [nonnegative(r, "memory_free_percent") for r in rows]
    disk = [nonnegative(r, "output_disk_kib") for r in rows]
    require(all(a <= b for a, b in zip(largest, rss)) and all(x <= 100 for x in free),
            "Primary monitor memory fields are inconsistent")
    return dict(report, maximum_solver_processes=max(k + c for k, c in process_counts),
                maximum_kissat_processes=max(k for k, _ in process_counts),
                maximum_cadical_processes=max(c for _, c in process_counts),
                maximum_solver_rss_mib=max(rss),
                maximum_largest_solver_rss_mib=max(largest),
                minimum_memory_free_percent=min(free),
                maximum_output_disk_kib=max(disk))


def supplement_monitor(path: Path) -> dict:
    rows, _, report = read_monitor(path, SUPPLEMENT_FIELDS)
    host = [nonnegative(r, "host_process_rss_mib") for r in rows]
    docker = [nonnegative(r, "docker_host_rss_mib") for r in rows]
    swap = [nonnegative(r, "swap_used_mib") for r in rows]
    own_counts = []
    names = set()
    for row in rows:
        stats = json.loads(row["docker_container_stats_json"] or "[]")
        require(isinstance(stats, list) and all(isinstance(entry, dict) and
                isinstance(entry.get("Name"), str) for entry in stats),
                "Malformed Docker container stats")
        sample_names = [entry["Name"] for entry in stats]
        names.update(sample_names)
        own_counts.append(sum(name.startswith("erdos85-h1-input-")
                              for name in sample_names))
    return dict(report, maximum_host_process_rss_mib=max(host),
                maximum_docker_host_rss_mib=max(docker),
                maximum_swap_used_mib=max(swap),
                maximum_h1_input_containers=max(own_counts),
                docker_stats_error_samples=sum(bool(r["docker_stats_error"]) for r in rows),
                observed_container_names=sorted(names))


def audit(run_dir: Path, primary_path: Path, supplement_path: Path) -> dict:
    run_dir = run_dir.resolve()
    primary_path = primary_path.resolve()
    supplement_path = supplement_path.resolve()
    plan, fresh = residual.select(CONFIG)
    require(sha(plan["raw"]) == CONFIG_SHA256 and sha(PILOT.read_bytes()) == PILOT_SHA256,
            "Frozen pilot configuration or selection bytes changed")
    pilot_ids = residual.pilot_ids(PILOT, CONFIG, fresh)
    state_raw = (run_dir / "results.json").read_bytes()
    state = json.loads(state_raw)
    require(state["schema"] == "erdos85-dispatch-results-v1" and
            state["config_sha256"] == sha(plan["raw"]) and
            state["index_sha256"] == plan["config"]["index"]["sha256"] and
            state["workers"] == 4 and state["proof_logging"] is False and
            len(state["selected_cases"]) == 24 and
            set(state["selected_cases"]) == set(pilot_ids),
            "Pilot state differs from frozen 24-ID configuration")
    index_path = (CONFIG.parent / plan["config"]["index"]["path"]).resolve()
    checked = verdicts.summarize(index_path, plan["config"]["index"]["sha256"], [run_dir])
    rows = {row["id"]: row for row in checked["rows"] if row["id"] in pilot_ids}
    require(len(rows) == 24, "Receipt summarizer lost a pilot root")
    statuses = {case_id: rows[case_id]["status"] for case_id in pilot_ids}
    primary = primary_monitor(primary_path, 4)
    supplement = supplement_monitor(supplement_path)
    snapshots_mtime = (run_dir / "snapshots").stat().st_mtime
    results_mtime = (run_dir / "results.json").stat().st_mtime
    require(sha((run_dir / "results.json").read_bytes()) == sha(state_raw) and
            sha(primary_path.read_bytes()) == primary["sha256"] and
            sha(supplement_path.read_bytes()) == supplement["sha256"],
            "Pilot receipts or monitor bytes changed during readback; retry")
    first = dt.datetime.fromisoformat(primary["first_utc"])
    last = dt.datetime.fromisoformat(primary["last_utc"])
    supplement_first = dt.datetime.fromisoformat(supplement["first_utc"])
    supplement_last = dt.datetime.fromisoformat(supplement["last_utc"])
    return {"schema": "erdos85-h1-pilot-gate-input-audit-v1",
            "scope": "Read-only receipts/logs and monitor arithmetic; monitor provenance/full time coverage need human review; no scaling approval or proof",
            "run_dir": str(run_dir), "pilot_results_sha256": sha(state_raw),
            "config_sha256": CONFIG_SHA256,
            "pilot_manifest_sha256": PILOT_SHA256,
            "recorded_config_commit": state["config_commit"],
            "pilot_pid": state["pid"],
            "input_snapshots_mtime_utc": dt.datetime.fromtimestamp(
                snapshots_mtime, dt.timezone.utc).isoformat(),
            "pilot_results_mtime_utc": dt.datetime.fromtimestamp(
                results_mtime, dt.timezone.utc).isoformat(),
            "pilot_selected_cases": 24,
            "pilot_status": state["status"],
            "completed_results": len(state["results"]),
            "verdict_status_counts": dict(Counter(statuses.values())),
            "all_24_terminal_rows_published": (state["status"] == "complete" and
                                               len(state["results"]) == 24 and
                                               all(s not in {"INCOMPLETE", "NOT_RUN"}
                                                   for s in statuses.values())),
            "crosschecked_unsat_rows": sum(s == "UNSAT_CROSSCHECKED"
                                            for s in statuses.values()),
            "primary_monitor": primary,
            "supplement_monitor": supplement,
            "primary_maximum_gap_at_most_60s": primary["maximum_sample_gap_seconds"] <= 60,
            "supplement_maximum_gap_at_most_60s": supplement["maximum_sample_gap_seconds"] <= 60,
            "supplement_covers_primary_interval": supplement_first <= first and supplement_last >= last,
            "gate_approved": False,
            "rows": [{"id": case_id, "status": statuses[case_id]}
                     for case_id in sorted(pilot_ids)]}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--pilot-run", required=True, type=Path)
    parser.add_argument("--resource-monitor", type=Path)
    parser.add_argument("--supplement-monitor", type=Path)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    run = args.pilot_run.resolve()
    report = audit(run, args.resource_monitor or run / "resource-monitor.csv",
                   args.supplement_monitor or run / "resource-supplement.csv")
    if args.output:
        with args.output.open("x") as out:
            json.dump(report, out, indent=2)
            out.write("\n")
    print(json.dumps({k: v for k, v in report.items() if k != "rows"}))


if __name__ == "__main__":
    main()
