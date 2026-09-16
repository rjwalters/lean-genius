#!/usr/bin/env python3
"""Dispatch only the 96 historical-overlay H1 gaps for two-solver verdicts.

Dry run by default. This reuses the unchanged Phase B dispatcher and its
reviewed H1 native materializer; it never requests proof logging.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
BASE = HERE.parent
SAT49 = BASE / "sat49"
sys.path.insert(0, str(SAT49))

import dispatch_verdict_only as dispatch  # noqa: E402
import dispatch_h1_residual_verdict_only as residual  # noqa: E402

GAP130 = HERE / "gap130.json"
GAP130_SHA256 = "e65684212b851d3fa3cb0e7598b6ead5662da7b3abcc97c64835945cccd7baf0"
CONFIG = BASE / "phase_b_h1_verdict_20260916/config.draft.json"
HISTORICAL_IDS_SHA256 = "04097bb4dec4c381ed614d17937a2d011127ffa6debb1db79f2de85a4cad64f3"


def id_digest(ids) -> str:
    return hashlib.sha256(("".join(name + "\n" for name in sorted(ids))).encode()).hexdigest()


def select():
    plan, fresh = residual.select(CONFIG)
    raw = GAP130.read_bytes()
    if hashlib.sha256(raw).hexdigest() != GAP130_SHA256:
        raise ValueError("Reviewed gap130 manifest changed")
    gap = json.loads(raw)
    historical = {row["id"] for row in gap["rows"]
                  if row["class"] == "historical_overlay_without_listed_object"}
    if (len(historical) != 96 or id_digest(historical) != HISTORICAL_IDS_SHA256
            or historical != {row["id"] for row in plan["historical"]}):
        raise ValueError("Historical-overlay gap set differs from reviewed 96")
    selected = [case for case in plan["cases"] if case["id"] in historical]
    fresh_ids = {case["id"] for case in fresh}
    if (len(selected) != 96 or any(case["sector"] != "H1" or case["id"] in
            fresh_ids or case["policy"] !=
            {"crosscheck": True, "primary_cap_seconds": 14400,
             "crosscheck_cap_seconds": 14400} for case in selected)):
        raise ValueError("Historical dispatch scope or two-solver policy changed")
    return plan, selected


def prepare_with_overlay_hash(case, plan, directory, original, expected_by_id):
    """Guard the reviewed historical CNF identity before solver dispatch."""
    expected = expected_by_id.get(case["id"])
    if expected is None:
        raise ValueError("Case lacks a reviewed historical-overlay CNF hash")
    if ({row["id"]: row["cnf_sha256"] for row in plan["historical"]} != expected_by_id
            or plan["config"]["policies"]["H1"] !=
            {"crosscheck": True, "primary_cap_seconds": 14400,
             "crosscheck_cap_seconds": 14400}):
        raise ValueError("Loaded historical overlay or two-solver policy drifted")
    prepared = original(case, plan, directory)
    if prepared["cnf_sha256"] != expected:
        raise ValueError("Native CNF differs from reviewed historical overlay")
    prepared["historical_overlay_expected_cnf_sha256"] = expected
    prepared["historical_overlay_verified"] = True
    return prepared


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--execute", action="store_true")
    parser.add_argument("--config-commit")
    parser.add_argument("--wrapper-commit")
    parser.add_argument("--output-dir", type=Path)
    parser.add_argument("--workers", type=int, choices=range(1, 5), default=1)
    parser.add_argument("--case-id", action="append")
    parser.add_argument("--kissat", type=Path)
    parser.add_argument("--cadical", type=Path)
    args = parser.parse_args()
    plan, historical = select()
    allowed = {case["id"] for case in historical}
    if args.case_id:
        picked = set(args.case_id)
        if len(picked) != len(args.case_id) or not picked <= allowed:
            parser.error("Only distinct historical-overlay gap IDs are allowed")
        ids = [case["id"] for case in historical if case["id"] in picked]
    else:
        ids = [case["id"] for case in historical]
    if args.execute:
        if not args.config_commit or not args.wrapper_commit or not args.output_dir:
            parser.error("Execution requires both banked commits and a new output directory")
        for path in (Path(__file__).resolve(), GAP130):
            dispatch.runner.require_banked_inventory(path, args.wrapper_commit,
                expected_bytes=path.read_bytes())
    forwarded = ["dispatch_verdict_only.py", "--config", str(CONFIG),
                 "--workers", str(args.workers)]
    if args.execute:
        forwarded += ["--execute", "--config-commit", args.config_commit,
                      "--output-dir", str(args.output_dir)]
    if args.kissat is not None:
        forwarded += ["--kissat", str(args.kissat)]
    if args.cadical is not None:
        forwarded += ["--cadical", str(args.cadical)]
    for case_id in ids:
        forwarded += ["--case-id", case_id]
    expected_by_id = {row["id"]: row["cnf_sha256"] for row in plan["historical"]}
    if len(expected_by_id) != 96 or any(not dispatch.runner.HEX.fullmatch(value)
                                         for value in expected_by_id.values()):
        raise ValueError("Historical overlay has an invalid CNF digest")
    previous = sys.argv
    original_prepare = dispatch.prepare
    try:
        sys.argv = forwarded
        dispatch.prepare = lambda case, loaded_plan, directory: prepare_with_overlay_hash(
            case, loaded_plan, directory, original_prepare, expected_by_id)
        return dispatch.main()
    finally:
        sys.argv = previous
        dispatch.prepare = original_prepare


if __name__ == "__main__":
    raise SystemExit(main())
