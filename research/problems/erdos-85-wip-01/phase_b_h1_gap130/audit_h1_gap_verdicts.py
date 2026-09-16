#!/usr/bin/env python3
"""Reconcile fresh dual-solver receipts against all 1,288 dated H1 gaps.

This is a read-only computational census. It does not launch solvers, replay
proof certificates, or turn a solver verdict into a Lean theorem.
"""
from __future__ import annotations

import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
BASE = HERE.parent
SAT49 = BASE / "sat49"
sys.path.insert(0, str(SAT49))

import dispatch_h1_residual_verdict_only as residual  # noqa: E402
import summarize_phase_b_verdicts as summary  # noqa: E402
import dispatch_capacity34 as outside  # noqa: E402
import materialize_capacity_gap as adapter  # noqa: E402

VALID = {"UNSAT_CROSSCHECKED", "UNKNOWN", "ERROR", "SAT_CANDIDATE",
         "DISAGREEMENT", "INCOMPLETE", "NOT_RUN"}
CONFIG_SHA256 = "f7cf7a15894a114d30f4069abc1198af1397d6f8f3b85b0f0eae3b4e294d66a3"
WRAPPER_SHA256 = "87239aea874456fc0c4ad88cbe0cfc61a7700278d0d3c570e8963d6335a70be1"
ADAPTER_SHA256 = "b223db0913341b69d8be23c89c28e3ea8f966a1ed8099b8d9fe00363125cf2fa"
FREEZE_SHA256 = "5beca242a3f0cd4b86fe8aa361be5b306b4ab46f300e4b86e3b7ffac6761dece"
NATIVE_SHA256 = "00201aa9e23c2c55bce8cab3532d5eaf34df9fdb24d0134df01a974e0ff74dbd"
GAP130_SHA256 = "e65684212b851d3fa3cb0e7598b6ead5662da7b3abcc97c64835945cccd7baf0"


def require(condition, message):
    if not condition:
        raise ValueError(message)


def one_row_bytes(row):
    candidate = {"id": row["id"], "tag": row["tag"],
                 "profile": str(row["profile"]), "table_values": row["table_values"],
                 "host_cnf_sha256": "", "fleet_cnf_sha256": "",
                 "fleet_v2_cnf_sha256": "", "fleet_v3_cnf_sha256": ""}
    return (json.dumps({"schema": "erdos85-phase-b-h1-candidates-v1",
                        "rows": [candidate]}, indent=2) + "\n").encode()


def table_bytes(row):
    pairs = [(a, b) for a in range(8) for b in range(a + 1, 8) if b != (a ^ 1)]
    require(len(row["table_values"]) == len(pairs), "Outside-34 table length mismatch")
    table = sorted((pair, value) for pair, value in zip(pairs, row["table_values"]) if value)
    require(hashlib.sha1(json.dumps(table).encode()).hexdigest()[:16] == row["tag"],
            "Outside-34 table/tag mismatch")
    return (json.dumps(table) + "\n").encode()


def dated_gap_ids(plan, rows):
    """Rebuild the 1,288 set from the dated object and rescue snapshots."""
    joined = json.loads((BASE / "closure-inventory-evidence/h1-exact-set-join.json").read_text())["rows"]
    rescue = json.loads((BASE / "closure-inventory-evidence/followup-20260910/h1-rescue-set-join.json").read_text())
    listed = {r["tag"] for r in joined if r["object_listed"]}
    gap_tags = {r["tag"] for r in joined} - listed - set(rescue["rescue_tags"])
    gaps = {"h1_" + tag for tag in gap_tags}
    frozen = {case["id"] for case in plan["cases"] if case["sector"] == "H1"}
    residual_ids = frozen - {r["id"] for r in plan["historical"]}
    historical = {r["id"] for r in rows if r["class"] == "historical_overlay_without_listed_object"}
    extra = {r["id"] for r in rows if r["class"] == "outside_frozen_phase_b"}
    require(len(gaps) == 1288 and len(residual_ids & gaps) == 1158 and
            len(residual_ids - gaps) == 3 and len(historical) == 96 and
            len(extra) == 34 and gaps == (residual_ids & gaps) | historical | extra,
            "Dated 1,288-gap decomposition changed")
    return gaps, residual_ids & gaps, historical, extra


def audit_outside_case(run: Path, state: dict, record: dict, row: dict) -> dict:
    case_id = row["id"]
    directory = run / case_id
    saved, saved_raw = summary.read_json(directory / "result.json")
    require(saved == record and record["id"] == case_id and
            record["sector"] == "H1" and record["profile"] == row["profile"] and
            record["capacity_local_index"] == row["capacity_local_index"] and
            record["gap130_sha256"] == GAP130_SHA256,
            "Outside-34 case receipt/row mismatch")
    attempt = {"run": str(run), "status": record["status"],
               "case_receipt_sha256": summary.digest(saved_raw)}
    attempt["sat_alarm"] = summary.retained_partial(run, case_id)["sat_alarm"]
    if record["status"] == "ERROR":
        return attempt
    require(record["status"] in VALID, "Invalid outside-34 status")
    binding, _ = summary.read_json(directory / "materialization/binding.json")
    prepared, _ = summary.read_json(directory / "preparation.json")
    require(binding == prepared == record["binding"], "Outside-34 binding receipt mismatch")
    require(binding["status"] == "materialized" and binding["id"] == case_id and
            binding["tag"] == row["tag"] and binding["profile"] == row["profile"] and
            binding["capacity_local_index"] == row["capacity_local_index"] and
            binding["gap130_sha256"] == GAP130_SHA256 and
            binding["one_row_source_sha256"] == summary.digest(one_row_bytes(row)) and
            binding["native_materializer_sha256"] == NATIVE_SHA256 and
            binding["adapter_source_sha256"] == ADAPTER_SHA256 and
            binding["freeze_source_sha256"] == FREEZE_SHA256 and
            binding["solver_launched"] is False,
            "Outside-34 native binding identity mismatch")
    native_path = directory / "materialization/native/receipt.json"
    native, native_raw = summary.read_json(native_path)
    adapter_path = directory / "materialization/one-row-source.json"
    require(adapter_path.read_bytes() == one_row_bytes(row),
            "Outside-34 one-row source differs from capacity table")
    table_path = directory / "materialization/native/table.json"
    require(table_path.read_bytes() == table_bytes(row) and
            summary.digest(table_path.read_bytes()) == native["table_sha256"],
            "Outside-34 native table differs from selected source")
    check_log = summary.read_bytes(directory / "materialization/native/check.log", 4096).decode("ascii").strip()
    require(summary.digest(native_raw) == binding["native_receipt_sha256"] and
            native["status"] == "materialized" and native["container_absent"] is True and
            native["id"] == case_id and native["cnf_sha256"] == binding["cnf_sha256"] and
            native["cnf_bytes"] == binding["cnf_bytes"] and
            native["manifest_sha256"] == binding["one_row_source_sha256"] and
            native["tag"] == row["tag"] and native["profile"] == row["profile"] and
            native["emitter_sha256"] == adapter.native.EMITTER_SHA256 and
            native["image_id"] == adapter.native.IMAGE_ID and
            native["runner_sha256"] == NATIVE_SHA256 and
            native["validator_sha256"] == state["config"]["tool_sha256"]["materialize_verdict_input.py"] and
            native["emit"]["returncode"] == 0 and
            native["solver_launched"] is False and
            native["check"]["returncode"] == 0 and
            check_log == f"MATCH ({native['clauses']} clauses, top {native['variables']})",
            "Outside-34 native emission/check mismatch")
    cnf = directory / "materialization/native/input.cnf"
    require(not cnf.is_symlink() and cnf.is_file() and
            outside.runner.sha256(cnf) == binding["cnf_sha256"] and
            cnf.stat().st_size == binding["cnf_bytes"],
            "Outside-34 retained CNF identity mismatch")
    solved, _ = summary.read_json(directory / "solve" / case_id / "result.json")
    require(solved == record["solve"] and solved["id"] == case_id and
            solved["sector"] == "H1" and
            solved["cnf_sha256"] == record["cnf_sha256"] == binding["cnf_sha256"] and
            solved["generator_commit"] == state["h1_generator_commit"],
            "Outside-34 solver receipt mismatch")
    solver_dir = directory / "solve" / case_id
    prepared_input = {"cnf_path": str(cnf)}
    primary = summary.check_solver(solved["primary"], solver_dir / "kissat.log",
                                   "kissat", prepared_input, state["solvers"]["kissat"], 14400)
    if primary == "UNSAT":
        secondary = summary.check_solver(solved["crosscheck"], solver_dir / "cadical.log",
                                         "cadical", prepared_input, state["solvers"]["cadical"], 14400)
        expected = {"UNSAT": "UNSAT_CROSSCHECKED", "UNKNOWN": "UNKNOWN",
                    "SAT_CANDIDATE": "DISAGREEMENT", "ERROR": "ERROR"}[secondary]
    else:
        require("crosscheck" not in solved, "Unexpected outside-34 crosscheck")
        expected = primary
    require(solved["status"] == record["status"] == expected and
            record["status"] != "UNSAT_PRIMARY", "Outside-34 verdict disagrees with logs")
    return dict(attempt, cnf_sha256=binding["cnf_sha256"])


def summarize_outside(run_dirs, rows):
    by_id = {r["id"]: r for r in rows if r["class"] == "outside_frozen_phase_b"}
    attempts = {case_id: [] for case_id in by_id}
    incomplete = set()
    runs = []
    for run_dir in run_dirs:
        run = Path(run_dir).resolve()
        state, state_raw = summary.read_json(run / "results.json")
        require(state["schema"] == "erdos85-h1-capacity34-verdict-results-v1" and
                state["inventory_cases"] == 34 and
                state["gap130_sha256"] == GAP130_SHA256 and
                state["proof_logging"] is False,
                "Outside-34 run scope mismatch")
        selected = state["selected_cases"]
        require(len(set(selected)) == len(selected) and set(selected) <= set(by_id),
                "Outside-34 run selection mismatch")
        require(state["config_sha256"] == CONFIG_SHA256,
                "Outside-34 config identity mismatch")
        snapshots = {summary.digest(path.read_bytes()): path.read_bytes()
                     for path in (run / "snapshots").iterdir() if path.is_file()}
        required = {CONFIG_SHA256, GAP130_SHA256, WRAPPER_SHA256,
                    ADAPTER_SHA256, FREEZE_SHA256}
        require(required <= set(snapshots), "Missing outside-34 source snapshots")
        config = json.loads(snapshots[state["config_sha256"]])
        require(config["policies"]["H1"] == outside.POLICY,
                "Outside-34 policy changed")
        state["h1_generator_commit"] = config["h1_generator_commit"]
        state["config"] = config
        done = set()
        for record in state["results"]:
            case_id = record["id"]
            require(case_id in selected and case_id not in done,
                    "Unexpected or duplicate outside-34 result")
            done.add(case_id)
            attempts[case_id].append(audit_outside_case(run, state, record, by_id[case_id]))
        missing = set(selected) - done
        if "not_started" in state:
            require(set(state["not_started"]) == missing, "Outside-34 not_started mismatch")
        else:
            incomplete.update(missing)
        for case_id in missing:
            if (run / case_id).exists():
                attempts[case_id].append(summary.retained_partial(run, case_id))
                incomplete.add(case_id)
        require(state["status"] != "complete" or not missing,
                "Incomplete outside-34 run declared complete")
        if state["status"] in {"complete", "stopped", "aborted"}:
            expected_complete = (not missing and all(r["status"] == "UNSAT_CROSSCHECKED"
                                                     for r in state["results"]))
            require(state["selected_all_unsat"] == expected_complete,
                    "Outside-34 final coverage flag disagrees with receipts")
        runs.append({"path": str(run), "results_sha256": summary.digest(state_raw),
                     "selected": len(selected), "completed": len(done)})
    results = {case_id: summary.combine(attempts[case_id], case_id in incomplete)
               for case_id in by_id}
    return results, runs


def audit(phase_b_runs, outside_runs):
    plan, selected_outside = outside.select()
    rows = adapter.freeze()["rows"]
    require({r["id"] for r in selected_outside} ==
            {r["id"] for r in rows if r["class"] == "outside_frozen_phase_b"},
            "Outside-34 source selection changed")
    gap_ids, residual_gaps, historical_gaps, outside_gaps = dated_gap_ids(plan, rows)
    config = plan["config"]
    index_path = (outside.CONFIG.parent / config["index"]["path"]).resolve()
    phase_b = summary.summarize(index_path, config["index"]["sha256"], phase_b_runs)
    base_rows = {r["id"]: r for r in phase_b["rows"]}
    outside_status, outside_evidence = summarize_outside(outside_runs, rows)
    statuses = {case_id: base_rows[case_id]["status"] for case_id in residual_gaps | historical_gaps}
    statuses.update(outside_status)
    require(set(statuses) == gap_ids, "Audited status set is not the dated 1,288 gaps")
    counts = dict(Counter(statuses.values()))
    return {"schema": "erdos85-h1-dated-gap-verdict-census-v1",
            "scope": "Fresh receipt/log-consistent dual-solver verdicts only; no proof certificate or Lean theorem",
            "snapshot_gap_count": 1288,
            "decomposition": {"residual_phase_b_gaps": len(residual_gaps),
                              "historical_overlay_gaps": len(historical_gaps),
                              "outside_frozen_gaps": len(outside_gaps)},
            "counts": counts,
            "crosschecked_unsat": counts.get("UNSAT_CROSSCHECKED", 0),
            "open": 1288 - counts.get("UNSAT_CROSSCHECKED", 0),
            "computational_gap_census_complete": all(s == "UNSAT_CROSSCHECKED" for s in statuses.values()),
            "phase_b_runs": phase_b["runs"], "outside_runs": outside_evidence,
            "rows": [{"id": case_id, "status": statuses[case_id]} for case_id in sorted(gap_ids)]}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--phase-b-run", action="append", type=Path, default=[])
    parser.add_argument("--outside-run", action="append", type=Path, default=[])
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    report = audit(args.phase_b_run, args.outside_run)
    if args.output:
        with args.output.open("x") as destination:
            json.dump(report, destination, indent=2)
            destination.write("\n")
    print(json.dumps({k: v for k, v in report.items()
                      if k not in ("rows", "phase_b_runs", "outside_runs")}))


if __name__ == "__main__":
    main()
