#!/usr/bin/env python3
"""Pass 4: ADAPTIVE cube-and-conquer, two-solver, verdict-only, for one H1 instance (board goal #47).

Tree partition. The root cube is the base CNF F. A cube is F plus the unit clauses of a partial
assignment. Each cube is probed with Kissat under a short cap; if Kissat proves it UNSAT, CaDiCaL
must confirm under the full cap and the cube becomes a LEAF. If the probe times out and the depth
allows, the cube is SPLIT on one variable chosen by unit-propagation lookahead inside the cube
(both children replace the parent). At the maximum depth the probe cap is the full cap. Since a
split replaces a cube by two cubes that partition it exactly, the leaves always partition F, so
F is UNSAT iff every leaf is UNSAT. Any SAT leaf is a SAT candidate for F and stops the run.
No proof logging. Solver runs and verdict classification come from the REVIEWED
run_verdict_only.run_solver. The independent checker cube_tree_check.py re-derives the tree,
every leaf's bytes and every verdict from the logs.

This layout also records, per instance, how much of the search space is trivial: leaves that
Kissat refutes within seconds versus leaves that need hours. SINGLE-SEAT (claude, 2026-09-26).
"""
from __future__ import annotations

import argparse
import collections
import datetime as dt
import json
import os
from pathlib import Path
import queue
import sys
import threading
import time

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent / "sat49"))
import run_verdict_only as runner  # noqa: E402
import cube_split  # noqa: E402
import cube_verdict  # noqa: E402  (read_cnf, cube_bytes)

lock = threading.Lock()


def choose_split(prop: cube_split.Propagator, candidates: list[int], literals: tuple[int, ...]) -> int | None:
    """Variable maximizing min(forced literals) over both branches, given the cube's literals."""
    assigned = {abs(l) for l in literals}
    base_forced, base_value = prop.probe(list(literals))
    best, best_score = None, (-1, -1)
    for v in candidates:
        if v in assigned or v in base_value:
            continue
        up, _ = prop.probe(list(literals) + [v])
        down, _ = prop.probe(list(literals) + [-v])
        score = (min(up, down), up + down if up != float("inf") and down != float("inf") else float("inf"))
        if score > best_score:
            best, best_score = v, score
    return best


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--base-cnf", type=Path, required=True)
    parser.add_argument("--base-sha256", required=True)
    parser.add_argument("--case-id", required=True)
    parser.add_argument("--probe-cap", type=int, default=3600, help="Kissat seconds before a cube is split")
    parser.add_argument("--full-cap", type=int, default=86400, help="seconds per solver at max depth and for every CaDiCaL confirmation")
    parser.add_argument("--max-depth", type=int, default=24)
    parser.add_argument("--workers", type=int, default=24)
    parser.add_argument("--candidates", type=int, default=80, help="lookahead candidates per split (most balanced occurrence, unassigned)")
    parser.add_argument("--initial-depth", type=int, default=0, help="pre-split the root to this depth by lookahead before any solving, so every worker starts busy")
    parser.add_argument("--output-dir", type=Path, required=True)
    parser.add_argument("--kissat", default="/opt/homebrew/bin/kissat")
    parser.add_argument("--cadical", default="/opt/homebrew/bin/cadical")
    args = parser.parse_args()
    if not (1 <= args.probe_cap <= args.full_cap <= 86400):
        parser.error("need 1 <= probe cap <= full cap <= 86400")
    base_path = args.base_cnf.resolve()
    if runner.sha256(base_path) != args.base_sha256:
        raise SystemExit("base CNF identity mismatch")
    raw, header_index, variables, clauses = cube_verdict.read_cnf(base_path)
    parsed = cube_split.parse(base_path)
    prop = cube_split.Propagator(parsed)
    occ_pos, occ_neg = collections.Counter(), collections.Counter()
    for clause in parsed:
        for lit in clause:
            (occ_pos if lit > 0 else occ_neg)[abs(lit)] += 1
    candidates = sorted(set(occ_pos) | set(occ_neg), key=lambda v: -min(occ_pos[v], occ_neg[v]))[:args.candidates]
    run = args.output_dir.resolve()
    run.mkdir(parents=True)
    (run / "base.cnf").write_bytes(raw)
    identities = {"kissat": runner.solver_identity(Path(args.kissat)), "cadical": runner.solver_identity(Path(args.cadical))}
    state = {"schema": "erdos85-cube-tree-verdict-v1", "case_id": args.case_id, "base_sha256": args.base_sha256,
             "base_variables": variables, "base_clauses": clauses, "probe_cap_seconds": args.probe_cap,
             "full_cap_seconds": args.full_cap, "max_depth": args.max_depth, "workers": args.workers,
             "split_method": "unit-propagation lookahead inside the cube, greedy max-min forced literals",
             "proof_logging": False, "solvers": identities, "tool_sha256": runner.sha256(Path(__file__)),
             "runner_sha256": runner.sha256(Path(runner.__file__)), "status": "running", "pid": os.getpid(),
             "nodes": {}}
    work: queue.Queue = queue.Queue()
    counter = {"next": 1, "active": 0, "stop": False}
    state["nodes"]["0"] = {"id": 0, "parent": None, "literals": [], "depth": 0, "kind": "pending"}
    # Optional initial split (no solving): a split node without a probe is marked SPLIT_INITIAL.
    frontier = [0]
    for _ in range(args.initial_depth):
        next_frontier = []
        for nid in frontier:
            node = state["nodes"][str(nid)]
            var = choose_split(prop, candidates, tuple(node["literals"]))
            if var is None:
                next_frontier.append(nid)
                continue
            a, b = counter["next"], counter["next"] + 1
            counter["next"] += 2
            for cid, lit in ((a, var), (b, -var)):
                state["nodes"][str(cid)] = {"id": cid, "parent": nid, "literals": list(node["literals"]) + [lit],
                                            "depth": node["depth"] + 1, "kind": "pending"}
            node.update(kind="split", status="SPLIT_INITIAL", children=[a, b], split_variable=var)
            directory = run / f"node-{nid:05d}"
            directory.mkdir()
            runner.write_json(directory / "result.json", node)
            next_frontier += [a, b]
        frontier = next_frontier
    for nid in frontier:
        work.put(nid)

    def save():
        runner.write_json(run / "results.json", state)

    def process(node_id: int) -> None:
        node = state["nodes"][str(node_id)]
        literals = tuple(node["literals"])
        depth = node["depth"]
        directory = run / f"node-{node_id:05d}"
        directory.mkdir()
        assignment = {abs(l): int(l > 0) for l in literals}
        cnf = directory / "cube.cnf"
        cnf.write_bytes(cube_verdict.cube_bytes(raw, header_index, variables, clauses, assignment))
        record = {"cube_sha256": runner.sha256(cnf), "cube_bytes": cnf.stat().st_size,
                  "started_utc": dt.datetime.now(dt.timezone.utc).isoformat()}
        cap = args.full_cap if depth >= args.max_depth else args.probe_cap
        record["probe_cap_seconds"] = cap
        primary = runner.run_solver(Path(args.kissat), cnf, cap, directory / "kissat.log", kind="kissat")
        record["primary"] = primary
        kind, status, children = "leaf", "ERROR", None
        if primary["verdict"] == "UNSAT":
            secondary = runner.run_solver(Path(args.cadical), cnf, args.full_cap, directory / "cadical.log", kind="cadical")
            record["crosscheck"] = secondary
            status = {"UNSAT": "UNSAT_CROSSCHECKED", "UNKNOWN": "UNKNOWN", "SAT_CANDIDATE": "DISAGREEMENT", "ERROR": "ERROR"}[secondary["verdict"]]
        elif primary["verdict"] == "UNKNOWN" and depth < args.max_depth and not counter["stop"]:
            var = choose_split(prop, candidates, literals)
            if var is None:
                status = "UNKNOWN"
            else:
                kind, status = "split", "SPLIT"
                with lock:
                    a, b = counter["next"], counter["next"] + 1
                    counter["next"] += 2
                    for cid, lit in ((a, var), (b, -var)):
                        state["nodes"][str(cid)] = {"id": cid, "parent": node_id, "literals": list(literals) + [lit],
                                                    "depth": depth + 1, "kind": "pending"}
                children = [a, b]
                record["split_variable"] = var
        else:
            status = primary["verdict"]
        if runner.sha256(cnf) != record["cube_sha256"]:
            status, kind = "ERROR", "leaf"
            record["error"] = "cube changed during solving"
        record["finished_utc"] = dt.datetime.now(dt.timezone.utc).isoformat()
        if status in ("UNSAT_CROSSCHECKED", "SPLIT"):
            cnf.unlink()
            record["cube_removed"] = True
        with lock:
            node.update(kind=kind, status=status, children=children, **record)
            runner.write_json(directory / "result.json", node)
            if status in ("SAT_CANDIDATE", "DISAGREEMENT"):
                counter["stop"] = True
            save()
        if children:
            for cid in children:
                work.put(cid)

    def worker() -> None:
        while True:
            try:
                node_id = work.get(timeout=5)
            except queue.Empty:
                with lock:
                    if counter["active"] == 0 and work.empty():
                        return
                continue
            with lock:
                counter["active"] += 1
            try:
                process(node_id)
            except Exception as error:  # noqa: BLE001
                with lock:
                    state["nodes"][str(node_id)].update(kind="leaf", status="ERROR", error=f"{type(error).__name__}: {error}")
                    save()
            finally:
                with lock:
                    counter["active"] -= 1
                work.task_done()

    with runner.cancellation_handlers():
        threads = [threading.Thread(target=worker, daemon=True) for _ in range(args.workers)]
        for t in threads:
            t.start()
        while any(t.is_alive() for t in threads):
            time.sleep(30)
            if runner.ABORT.is_set():
                counter["stop"] = True
    leaves = [n for n in state["nodes"].values() if n.get("kind") == "leaf"]
    state["leaf_counts"] = dict(collections.Counter(n.get("status") for n in leaves))
    state["splits"] = sum(1 for n in state["nodes"].values() if n.get("kind") == "split")
    pending = [n for n in state["nodes"].values() if n.get("kind") == "pending"]
    if any(n.get("status") in ("SAT_CANDIDATE", "DISAGREEMENT") for n in leaves):
        state["status"] = "SAT_CANDIDATE"
    elif not pending and leaves and all(n.get("status") == "UNSAT_CROSSCHECKED" for n in leaves):
        state["status"] = "UNSAT_CUBE_CROSSCHECKED"
    else:
        state["status"] = "OPEN"
    # trivial-fraction summary for the cost-to-verify discussion
    quick = [n for n in leaves if n.get("status") == "UNSAT_CROSSCHECKED" and n["primary"]["elapsed_seconds"] < 10]
    state["trivial_leaves_under_10s"] = len(quick)
    save()
    print(json.dumps({k: v for k, v in state.items() if k not in ("nodes", "solvers")}))
    return 0 if state["status"] == "UNSAT_CUBE_CROSSCHECKED" else 1


if __name__ == "__main__":
    raise SystemExit(main())
