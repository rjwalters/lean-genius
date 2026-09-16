#!/usr/bin/env python3
"""Prepare the 34 outside-frozen H1 gaps and request dual verdicts.

Dry run by default. Execution uses the reviewed native adapter and unchanged
verdict runner, with no proof logging. No case here is in the Phase B index.
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

HERE = Path(__file__).resolve().parent
SAT49 = HERE.parent / "sat49"
sys.path.insert(0, str(SAT49))

import dispatch_verdict_only as dispatch  # noqa: E402
import run_verdict_only as runner  # noqa: E402
import materialize_capacity_gap as adapter  # noqa: E402

CONFIG = HERE.parent / "phase_b_h1_verdict_20260916/config.draft.json"
SELECTED_IDS_SHA256 = "8cbdc9b262febf775770e3f3136cd2ef3caea8aeb1836fa0f7b5690ce6b163c4"
POLICY = {"crosscheck": True, "primary_cap_seconds": 14400,
          "crosscheck_cap_seconds": 14400}


def id_digest(ids) -> str:
    return hashlib.sha256("".join(name + "\n" for name in sorted(ids)).encode()).hexdigest()


def select():
    plan = dispatch.load_plan(CONFIG)
    if plan["config"]["policies"]["H1"] != POLICY:
        raise ValueError("Reviewed H1 dual-solver policy changed")
    raw = adapter.MANIFEST.read_bytes()
    if (hashlib.sha256(raw).hexdigest() != adapter.MANIFEST_SHA256 or
            json.loads(raw) != adapter.freeze()):
        raise ValueError("Gap130 manifest or source join changed")
    rows = [r for r in json.loads(raw)["rows"]
            if r["class"] == "outside_frozen_phase_b"]
    ids = [r["id"] for r in rows]
    indexed = {case["id"] for case in plan["cases"]}
    if (len(rows) != 34 or len(set(ids)) != 34 or
            id_digest(ids) != SELECTED_IDS_SHA256 or
            any(r["id"] != "h1_" + r["tag"] or not r["in_v3_queue"] or
                r["historical_cnf_sha256"] is not None for r in rows) or
            set(ids) & indexed):
        raise ValueError("Outside-frozen 34 identity or Phase B separation changed")
    return plan, rows


def run_one(row, plan, output, kissat, cadical):
    case_id = row["id"]
    directory = output / case_id
    result = {"id": case_id, "sector": "H1", "status": "ERROR",
              "gap130_sha256": adapter.MANIFEST_SHA256,
              "capacity_local_index": row["capacity_local_index"],
              "profile": row["profile"]}
    created = False
    try:
        directory.mkdir()
        created = True
        dispatch.check_sources(plan)
        if runner.ABORT.is_set() or shutil.disk_usage(output).free < dispatch.RESERVE:
            raise RuntimeError("Cancelled or insufficient free space before preparation")
        binding = adapter.materialize(case_id, directory / "materialization")
        result["binding"] = binding
        runner.write_json(directory / "preparation.json", binding)
        dispatch.check_sources(plan)
        if runner.ABORT.is_set() or shutil.disk_usage(output).free < dispatch.RESERVE:
            raise RuntimeError("Cancelled or insufficient free space after preparation")
        cnf = directory / "materialization/native/input.cnf"
        if (binding.get("status") != "materialized" or
                binding.get("id") != case_id or binding.get("tag") != row["tag"] or
                binding.get("profile") != row["profile"] or
                binding.get("capacity_local_index") != row["capacity_local_index"] or
                binding.get("gap130_sha256") != adapter.MANIFEST_SHA256 or
                binding.get("one_row_source_sha256") !=
                    adapter.sha(adapter.one_row_manifest(row)) or
                binding.get("native_materializer_sha256") != adapter.NATIVE_SHA256 or
                binding.get("solver_launched") is not False or
                binding.get("adapter_source_sha256") != runner.sha256(Path(adapter.__file__)) or
                binding.get("freeze_source_sha256") != runner.sha256(HERE / "freeze.py") or
                not runner.HEX.fullmatch(binding.get("native_receipt_sha256", "")) or
                runner.sha256(cnf) != binding["cnf_sha256"] or
                cnf.stat().st_size != binding["cnf_bytes"]):
            raise ValueError("Capacity-gap binding or CNF changed before solver dispatch")
        solve = directory / "solve"
        solve.mkdir()
        solve_case = dict(POLICY, id=case_id, sector="H1",
                          resolved_cnf=str(cnf), cnf_sha256=binding["cnf_sha256"],
                          generator_commit=plan["config"]["h1_generator_commit"])
        solved = runner.run_case(solve_case, solve, kissat, cadical)
        result["solve"] = solved
        if solved["status"] == "UNSAT_PRIMARY":
            raise ValueError("Primary-only UNSAT is insufficient for a gap verdict")
        result.update(status=solved["status"], cnf_sha256=binding["cnf_sha256"])
        dispatch.check_sources(plan)
    except Exception as error:
        result.update(status="ERROR", error=f"{type(error).__name__}: {error}")
    if created:
        runner.write_json(directory / "result.json", result)
    return result


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--execute", action="store_true")
    parser.add_argument("--config-commit")
    parser.add_argument("--wrapper-commit")
    parser.add_argument("--output-dir", type=Path)
    parser.add_argument("--workers", type=int, choices=range(1, 5), default=1)
    parser.add_argument("--case-id", action="append")
    parser.add_argument("--kissat", type=Path, default=Path("/opt/homebrew/bin/kissat"))
    parser.add_argument("--cadical", type=Path, default=Path("/opt/homebrew/bin/cadical"))
    args = parser.parse_args()
    plan, rows = select()
    if args.case_id:
        selected = set(args.case_id)
        if len(selected) != len(args.case_id) or not selected <= {r["id"] for r in rows}:
            parser.error("Only distinct outside-frozen gap IDs are allowed")
        rows = [r for r in rows if r["id"] in selected]
    if not args.execute:
        print(json.dumps({"mode": "dry_run", "selected_cases": len(rows),
                          "selected_ids_sha256": id_digest(r["id"] for r in rows),
                          "inventory_cases": 34, "workers": args.workers,
                          "proof_logging": False, "solver_launched": False}))
        return 0
    if not args.config_commit or not args.wrapper_commit or not args.output_dir:
        parser.error("Execution requires both banked commits and a new output directory")
    for path, raw in plan["captured"]:
        runner.require_banked_inventory(path, args.config_commit, expected_bytes=raw)
    for path in (Path(__file__), Path(adapter.__file__), HERE / "freeze.py", adapter.MANIFEST):
        runner.require_banked_inventory(path.resolve(), args.wrapper_commit,
                                        expected_bytes=path.read_bytes())
    start = dt.datetime.fromisoformat(plan["config"]["not_before"].replace("Z", "+00:00"))
    if dt.datetime.now(dt.timezone.utc) < start:
        parser.error("Execution window has not started")
    output = args.output_dir.resolve()
    output.parent.mkdir(parents=True, exist_ok=True)
    if shutil.disk_usage(output.parent).free < dispatch.RESERVE:
        parser.error("Fewer than 8 GiB free")
    output.mkdir()
    snapshots = output / "snapshots"
    snapshots.mkdir()
    for number, (path, raw) in enumerate(plan["captured"]):
        (snapshots / f"{number:02d}-{path.name}").write_bytes(raw)
    for path in (Path(__file__), Path(adapter.__file__), HERE / "freeze.py", adapter.MANIFEST):
        (snapshots / path.name).write_bytes(path.read_bytes())
    kissat, cadical = args.kissat.resolve(), args.cadical.resolve()
    identities = {name: runner.solver_identity(binary) for name, binary in
                  (("kissat", kissat), ("cadical", cadical))}
    state = {"schema": "erdos85-h1-capacity34-verdict-results-v1", "status": "running",
             "pid": os.getpid(), "config_sha256": hashlib.sha256(plan["raw"]).hexdigest(),
             "config_commit": args.config_commit, "wrapper_commit": args.wrapper_commit,
             "gap130_sha256": adapter.MANIFEST_SHA256,
             "inventory_cases": 34, "selected_cases": [r["id"] for r in rows],
             "workers": args.workers, "solvers": identities,
             "proof_logging": False, "results": []}
    runner.write_json(output / "results.json", state)
    with runner.cancellation_handlers():
        dispatch.dispatch(rows,
            lambda row: run_one(row, plan, output, kissat, cadical),
            args.workers, output, state)
    state["selected_all_unsat"] = (not state["not_started"] and
                                   all(r["status"] == "UNSAT_CROSSCHECKED"
                                       for r in state["results"]))
    runner.write_json(output / "results.json", state)
    print(json.dumps({k: v for k, v in state.items() if k not in ("results", "solvers")}))
    return 0 if state["selected_all_unsat"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
