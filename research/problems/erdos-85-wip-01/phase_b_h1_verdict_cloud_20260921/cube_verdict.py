#!/usr/bin/env python3
"""Pass 4: cube-and-conquer, two-solver, verdict-only, for a single H1 instance (board goal #47).

Soundness. Let F be the base CNF and x_1..x_k distinct variables of F. For every assignment
a in {0,1}^k the cube CNF F_a is F plus the k unit clauses forcing x_i = a_i. Every model of F
satisfies exactly one F_a, so F is UNSAT iff every F_a is UNSAT. This tool writes the 2^k cube
files as byte-exact copies of the base CNF plus the unit clauses (header clause count raised by
k), runs each through the REVIEWED `run_verdict_only.run_solver` (Kissat, then CaDiCaL after a
Kissat UNSAT) under the given caps, and reports UNSAT_CUBE_CROSSCHECKED only when all 2^k cubes
are UNSAT_CROSSCHECKED. Any SAT cube is a SAT candidate for F. A cap hit on any cube leaves the
instance open. No proof logging. SINGLE-SEAT (claude, 2026-09-26), Sol re-audit pending.

Variable choice is a heuristic only (highest occurrence count); it cannot affect soundness.
`--check <run dir>` re-derives every cube file from the base CNF and the recorded assignment,
compares bytes, and recomputes the verdict from the solver logs via the reviewed classifier.
"""
from __future__ import annotations

import argparse
import collections
import concurrent.futures as futures
import datetime as dt
import hashlib
import itertools
import json
import os
from pathlib import Path
import sys
import threading

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent / "sat49"))
import run_verdict_only as runner  # noqa: E402  (reviewed: run_solver, classify, sha256, solver_identity)

lock = threading.Lock()


def read_cnf(path: Path):
    raw = path.read_bytes()
    lines = raw.split(b"\n")
    header = None
    for index, line in enumerate(lines):
        if line.startswith(b"c"):
            continue
        if line.startswith(b"p cnf "):
            header = (index, line)
            break
        raise ValueError("Unexpected line before DIMACS header")
    if header is None:
        raise ValueError("No DIMACS header")
    _, hdr = header
    parts = hdr.split()
    variables, clauses = int(parts[2]), int(parts[3])
    return raw, header[0], variables, clauses


def occurrence_top(raw: bytes, header_index: int, variables: int, k: int) -> list[int]:
    counts = collections.Counter()
    for line in raw.split(b"\n")[header_index + 1:]:
        if not line or line.startswith(b"c"):
            continue
        for token in line.split():
            literal = int(token)
            if literal:
                counts[abs(literal)] += 1
    if any(v > variables for v in counts):
        raise ValueError("Literal exceeds declared variable count")
    return [v for v, _ in sorted(counts.items(), key=lambda kv: (-kv[1], kv[0]))[:k]]


def cube_bytes(raw: bytes, header_index: int, variables: int, clauses: int, assignment: dict[int, int]) -> bytes:
    lines = raw.split(b"\n")
    lines[header_index] = f"p cnf {variables} {clauses + len(assignment)}".encode()
    units = "".join(f"{(v if a else -v)} 0\n" for v, a in sorted(assignment.items())).encode()
    # Insert the unit clauses right after the header so the rest of the file is byte-identical.
    return b"\n".join(lines[:header_index + 1]) + b"\n" + units + b"\n".join(lines[header_index + 1:])


def run_cube(args, run: Path, base, identities, index: int, assignment: dict[int, int]) -> dict:
    raw, header_index, variables, clauses = base
    directory = run / f"cube-{index:03d}"
    directory.mkdir()
    cnf = directory / "cube.cnf"
    cnf.write_bytes(cube_bytes(raw, header_index, variables, clauses, assignment))
    record = {"cube": index, "assignment": {str(v): a for v, a in sorted(assignment.items())},
              "cube_sha256": runner.sha256(cnf), "cube_bytes": cnf.stat().st_size, "status": "ERROR",
              "started_utc": dt.datetime.now(dt.timezone.utc).isoformat()}
    try:
        primary = runner.run_solver(Path(args.kissat), cnf, args.cap, directory / "kissat.log", kind="kissat")
        record["primary"] = primary
        if primary["verdict"] == "UNSAT":
            secondary = runner.run_solver(Path(args.cadical), cnf, args.cap, directory / "cadical.log", kind="cadical")
            record["crosscheck"] = secondary
            record["status"] = {"UNSAT": "UNSAT_CROSSCHECKED", "UNKNOWN": "UNKNOWN",
                                "SAT_CANDIDATE": "DISAGREEMENT", "ERROR": "ERROR"}[secondary["verdict"]]
        else:
            record["status"] = primary["verdict"]
        if runner.sha256(cnf) != record["cube_sha256"]:
            raise ValueError("Cube changed during solving")
    except Exception as error:  # noqa: BLE001
        record.update(status="ERROR", error=f"{type(error).__name__}: {error}")
    record["finished_utc"] = dt.datetime.now(dt.timezone.utc).isoformat()
    if record["status"] == "UNSAT_CROSSCHECKED":
        cnf.unlink()  # regenerable byte-exactly from base + assignment; cube_check.py does so
        record["cube_removed"] = True
    runner.write_json(directory / "result.json", record)
    return record


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--base-cnf", type=Path, required=True)
    parser.add_argument("--base-sha256", required=True, help="pinned identity of the base CNF (reviewed materializer receipt)")
    parser.add_argument("--case-id", required=True)
    parser.add_argument("-k", type=int, default=5, help="split variables; 2^k cubes")
    parser.add_argument("--cap", type=int, default=86400, help="seconds per solver per cube")
    parser.add_argument("--workers", type=int, default=16)
    parser.add_argument("--output-dir", type=Path, required=True)
    parser.add_argument("--kissat", default="/opt/homebrew/bin/kissat")
    parser.add_argument("--cadical", default="/opt/homebrew/bin/cadical")
    args = parser.parse_args()
    if not 1 <= args.k <= 8 or not 1 <= args.cap <= 86400:
        parser.error("k in 1..8, cap in 1..86400")
    base_path = args.base_cnf.resolve()
    if runner.sha256(base_path) != args.base_sha256:
        raise SystemExit("base CNF identity mismatch")
    base = read_cnf(base_path)
    raw, header_index, variables, clauses = base
    split = occurrence_top(raw, header_index, variables, args.k)
    run = args.output_dir.resolve()
    run.mkdir(parents=True)
    (run / "base.cnf").write_bytes(raw)
    identities = {"kissat": runner.solver_identity(Path(args.kissat)), "cadical": runner.solver_identity(Path(args.cadical))}
    assignments = [dict(zip(split, bits)) for bits in itertools.product((0, 1), repeat=args.k)]
    state = {"schema": "erdos85-cube-verdict-v1", "case_id": args.case_id, "base_sha256": args.base_sha256,
             "base_variables": variables, "base_clauses": clauses, "k": args.k, "split_variables": split,
             "cubes": len(assignments), "cap_seconds": args.cap, "workers": args.workers, "proof_logging": False,
             "solvers": identities, "tool_sha256": runner.sha256(Path(__file__)), "runner_sha256": runner.sha256(Path(runner.__file__)),
             "status": "running", "pid": os.getpid(), "results": []}
    runner.write_json(run / "results.json", state)
    with runner.cancellation_handlers(), futures.ThreadPoolExecutor(max_workers=args.workers) as pool:
        pending = {pool.submit(run_cube, args, run, base, identities, i, a): i for i, a in enumerate(assignments)}
        for future in futures.as_completed(pending):
            record = future.result()
            with lock:
                state["results"].append(record)
                runner.write_json(run / "results.json", state)
    statuses = collections.Counter(r["status"] for r in state["results"])
    state["counts"] = dict(statuses)
    state["status"] = ("UNSAT_CUBE_CROSSCHECKED" if len(state["results"]) == len(assignments)
                       and all(r["status"] == "UNSAT_CROSSCHECKED" for r in state["results"])
                       else "SAT_CANDIDATE" if "SAT_CANDIDATE" in statuses or "DISAGREEMENT" in statuses
                       else "OPEN")
    runner.write_json(run / "results.json", state)
    print(json.dumps({k: v for k, v in state.items() if k not in ("results", "solvers")}))
    return 0 if state["status"] == "UNSAT_CUBE_CROSSCHECKED" else 1


if __name__ == "__main__":
    raise SystemExit(main())
