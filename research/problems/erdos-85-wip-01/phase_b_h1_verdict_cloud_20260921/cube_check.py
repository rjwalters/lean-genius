#!/usr/bin/env python3
"""Independent checker for a cube_verdict.py run directory (board goal #47). SINGLE-SEAT.

Re-derives, from `base.cnf` and each recorded assignment alone: (1) that the 2^k assignments are
exactly all 0/1 vectors over the recorded k distinct variables of the base CNF; (2) each cube's
bytes (base + k unit clauses, header count raised by k) and its recorded sha256; (3) each solver
verdict from the solver log bytes, exit code and stop reason using the reviewed classifier;
(4) the combined status. Never launches a solver. Prints the recomputed summary; exits 0 only if
every cube is UNSAT_CROSSCHECKED and the base CNF matches the pinned sha256.
"""
from __future__ import annotations

import argparse
import itertools
import json
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent / "sat49"))
import run_verdict_only as runner  # noqa: E402
import cube_verdict as cube  # noqa: E402


def require(condition: bool, message: str) -> None:
    if not condition:
        raise SystemExit(f"CHECK FAILED: {message}")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("run_dir", type=Path)
    parser.add_argument("--base-sha256", required=True)
    args = parser.parse_args()
    run = args.run_dir.resolve()
    state = json.loads((run / "results.json").read_text())
    require(state.get("schema") == "erdos85-cube-verdict-v1", "schema")
    require(state["proof_logging"] is False, "proof logging must be off")
    base_path = run / "base.cnf"
    require(runner.sha256(base_path) == args.base_sha256 == state["base_sha256"], "base CNF identity")
    raw, header_index, variables, clauses = cube.read_cnf(base_path)
    require((variables, clauses) == (state["base_variables"], state["base_clauses"]), "base dimensions")
    split = state["split_variables"]
    k = state["k"]
    require(len(split) == k == len(set(split)) and all(1 <= v <= variables for v in split), "split variables")
    expected = {tuple(bits) for bits in itertools.product((0, 1), repeat=k)}
    seen = set()
    statuses = []
    for record in state["results"]:
        assignment = {int(v): a for v, a in record["assignment"].items()}
        require(set(assignment) == set(split), f"cube {record['cube']} assigns the wrong variables")
        bits = tuple(assignment[v] for v in split)
        require(bits not in seen, f"duplicate cube {bits}")
        seen.add(bits)
        directory = run / f"cube-{record['cube']:03d}"
        saved = json.loads((directory / "result.json").read_text())
        require(saved == record, f"cube {record['cube']} receipt differs from run state")
        expected_bytes = cube.cube_bytes(raw, header_index, variables, clauses, assignment)
        require(runner.sha256_bytes(expected_bytes) == record["cube_sha256"] if hasattr(runner, "sha256_bytes")
                else __import__("hashlib").sha256(expected_bytes).hexdigest() == record["cube_sha256"],
                f"cube {record['cube']} bytes do not re-derive from base + assignment")
        cnf_path = directory / "cube.cnf"
        if cnf_path.exists():
            require(cnf_path.read_bytes() == expected_bytes, f"cube {record['cube']} file differs from derivation")
        verdicts = {}
        for name, kind, log_name in (("primary", "kissat", "kissat.log"), ("crosscheck", "cadical", "cadical.log")):
            if name not in record:
                continue
            receipt = record[name]
            log = (directory / log_name).read_bytes()
            require(__import__("hashlib").sha256(log).hexdigest() == receipt["log_sha256"] and len(log) == receipt["log_bytes"],
                    f"cube {record['cube']} {kind} log identity")
            require(receipt["proof_requested"] is False, "proof requested")
            require(receipt["solver_sha256"] == state["solvers"][kind]["sha256"], f"{kind} binary identity")
            option = f"--time={state['cap_seconds']}" if kind == "kissat" else str(state["cap_seconds"])
            require(option in receipt["command"], f"cube {record['cube']} {kind} cap not in command")
            verdicts[name] = runner.classify(receipt["returncode"], log, receipt["stop_reason"])
            require(verdicts[name] == receipt["verdict"], f"cube {record['cube']} {kind} verdict disagrees with log evidence")
        if verdicts.get("primary") == "UNSAT" and "crosscheck" in verdicts:
            status = {"UNSAT": "UNSAT_CROSSCHECKED", "UNKNOWN": "UNKNOWN", "SAT_CANDIDATE": "DISAGREEMENT", "ERROR": "ERROR"}[verdicts["crosscheck"]]
        elif "primary" in verdicts:
            status = "UNSAT_PRIMARY" if verdicts["primary"] == "UNSAT" else verdicts["primary"]
        else:
            status = "ERROR"
        require(status == record["status"], f"cube {record['cube']} combined status mismatch")
        statuses.append(status)
    require(seen == expected, f"cubes do not partition the space: {len(seen)} of {len(expected)} assignments present")
    summary = {"case_id": state["case_id"], "base_sha256": args.base_sha256, "k": k, "cubes": len(expected),
               "checked": len(statuses), "counts": {s: statuses.count(s) for s in sorted(set(statuses))},
               "all_cubes_unsat_crosschecked": len(statuses) == len(expected) and all(s == "UNSAT_CROSSCHECKED" for s in statuses),
               "sat_alarm": any(s in ("SAT_CANDIDATE", "DISAGREEMENT") for s in statuses)}
    print(json.dumps(summary))
    return 0 if summary["all_cubes_unsat_crosschecked"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
