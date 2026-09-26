#!/usr/bin/env python3
"""Independent checker for a cube_adaptive.py run directory (board goal #47). SINGLE-SEAT.

From base.cnf and results.json alone it verifies: (1) the tree — the root has no literals, every
split node has exactly two children whose literal lists are the parent's plus v and plus -v for
one variable v not already assigned in the parent, and every non-split node is a leaf; hence the
leaves partition the base formula's search space; (2) every leaf and split node's cube bytes
re-derive from base + its literals and match the recorded sha256; (3) every solver verdict from
its log bytes, exit code and stop reason via the reviewed classifier, and the binary identities
and caps recorded in the commands; (4) the combined status. Never launches a solver. Exit 0 only
if every leaf is UNSAT_CROSSCHECKED and the base CNF matches the pinned sha256.
"""
from __future__ import annotations

import argparse
import hashlib
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
    require(state.get("schema") == "erdos85-cube-tree-verdict-v1", "schema")
    require(state["proof_logging"] is False, "proof logging must be off")
    base_path = run / "base.cnf"
    require(runner.sha256(base_path) == args.base_sha256 == state["base_sha256"], "base CNF identity")
    raw, header_index, variables, clauses = cube.read_cnf(base_path)
    require((variables, clauses) == (state["base_variables"], state["base_clauses"]), "base dimensions")
    nodes = {int(k): v for k, v in state["nodes"].items()}
    require(0 in nodes and nodes[0]["literals"] == [] and nodes[0]["parent"] is None, "root")
    leaves, splits = [], 0
    for nid, node in nodes.items():
        kind = node.get("kind")
        require(kind in ("leaf", "split"), f"node {nid} unresolved ({kind})")
        if nid != 0:
            parent = nodes[node["parent"]]
            require(parent.get("kind") == "split" and nid in parent["children"], f"node {nid} parent link")
            require(node["literals"][:-1] == parent["literals"] and node["depth"] == parent["depth"] + 1, f"node {nid} literal prefix")
        directory = run / f"node-{nid:05d}"
        saved = json.loads((directory / "result.json").read_text())
        require(saved == node, f"node {nid} receipt differs from run state")
        assignment = {abs(l): int(l > 0) for l in node["literals"]}
        require(len(assignment) == len(node["literals"]), f"node {nid} assigns a variable twice")
        if kind == "split" and node.get("status") == "SPLIT_INITIAL":
            # Pre-split without solving: only the tree structure matters for soundness.
            a, b = node["children"]
            v = node["split_variable"]
            require(v not in assignment and 1 <= v <= variables, f"initial split node {nid} variable")
            require(sorted([nodes[a]["literals"][-1], nodes[b]["literals"][-1]]) == sorted([v, -v]), f"initial split node {nid} children literals")
            require(nodes[a]["literals"][:-1] == node["literals"] and nodes[b]["literals"][:-1] == node["literals"], f"initial split node {nid} children prefix")
            splits += 1
            continue
        expected = cube.cube_bytes(raw, header_index, variables, clauses, assignment)
        require(hashlib.sha256(expected).hexdigest() == node["cube_sha256"], f"node {nid} cube bytes do not re-derive")
        if (directory / "cube.cnf").exists():
            require((directory / "cube.cnf").read_bytes() == expected, f"node {nid} cube file differs")
        verdicts = {}
        for name, solver, log_name, cap in (("primary", "kissat", "kissat.log", node["probe_cap_seconds"]),
                                            ("crosscheck", "cadical", "cadical.log", state["full_cap_seconds"])):
            if name not in node:
                continue
            receipt = node[name]
            log = (directory / log_name).read_bytes()
            require(hashlib.sha256(log).hexdigest() == receipt["log_sha256"] and len(log) == receipt["log_bytes"], f"node {nid} {solver} log identity")
            require(receipt["proof_requested"] is False, "proof requested")
            require(receipt["solver_sha256"] == state["solvers"][solver]["sha256"], f"{solver} binary identity")
            option = f"--time={cap}" if solver == "kissat" else str(cap)
            require(option in receipt["command"], f"node {nid} {solver} cap not in command")
            verdicts[name] = runner.classify(receipt["returncode"], log, receipt["stop_reason"])
            require(verdicts[name] == receipt["verdict"], f"node {nid} {solver} verdict disagrees with log evidence")
        if kind == "split":
            require(verdicts.get("primary") == "UNKNOWN" and node["status"] == "SPLIT", f"split node {nid} was not an UNKNOWN probe")
            a, b = node["children"]
            v = node["split_variable"]
            require(v not in assignment and 1 <= v <= variables, f"split node {nid} variable")
            require(sorted([nodes[a]["literals"][-1], nodes[b]["literals"][-1]]) == sorted([v, -v]), f"split node {nid} children literals")
            require(nodes[a]["literals"][:-1] == node["literals"] and nodes[b]["literals"][:-1] == node["literals"], f"split node {nid} children prefix")
            splits += 1
        else:
            if verdicts.get("primary") == "UNSAT" and "crosscheck" in verdicts:
                status = {"UNSAT": "UNSAT_CROSSCHECKED", "UNKNOWN": "UNKNOWN", "SAT_CANDIDATE": "DISAGREEMENT", "ERROR": "ERROR"}[verdicts["crosscheck"]]
            elif "primary" in verdicts:
                status = "UNSAT_PRIMARY" if verdicts["primary"] == "UNSAT" else verdicts["primary"]
            else:
                status = "ERROR"
            require(status == node["status"], f"leaf {nid} combined status mismatch")
            leaves.append(status)
    summary = {"case_id": state["case_id"], "base_sha256": args.base_sha256, "nodes": len(nodes), "splits": splits, "leaves": len(leaves),
               "max_depth": max(n["depth"] for n in nodes.values()),
               "leaf_counts": {s: leaves.count(s) for s in sorted(set(leaves))},
               "all_leaves_unsat_crosschecked": bool(leaves) and all(s == "UNSAT_CROSSCHECKED" for s in leaves),
               "sat_alarm": any(s in ("SAT_CANDIDATE", "DISAGREEMENT") for s in leaves)}
    print(json.dumps(summary))
    return 0 if summary["all_leaves_unsat_crosschecked"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
