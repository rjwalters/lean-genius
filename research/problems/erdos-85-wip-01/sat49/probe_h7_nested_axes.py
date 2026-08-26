#!/usr/bin/env python3
"""Boundedly score exact positive-clause axes for a hard H7 parent cube.

Every candidate is an eight-literal positive clause already present in the
authoritative base CNF.  Consequently its all-negative cover is immediately
inconsistent with the base.  The probe measures a deterministic sample of
positive two-axis children; it does not emit campaign jobs or certificates.
"""

from __future__ import annotations

import argparse
import itertools
import json
import random
import subprocess
import tempfile
import time
from pathlib import Path


SAMPLE_POINTS = ((0, 0), (0, 7), (7, 0), (7, 7),
                 (2, 3), (3, 5), (5, 2), (6, 6))


def read_dimacs(path: Path) -> tuple[int, list[tuple[int, ...]]]:
    variables = 0
    clauses: list[tuple[int, ...]] = []
    with path.open() as source:
        for line_number, line in enumerate(source, 1):
            stripped = line.strip()
            if not stripped or stripped.startswith(("c", "%")):
                continue
            if stripped.startswith("p cnf "):
                fields = stripped.split()
                if len(fields) != 4 or variables:
                    raise ValueError(f"{path}:{line_number}: malformed/duplicate header")
                variables = int(fields[2])
                continue
            fields = tuple(map(int, stripped.split()))
            if not fields or fields[-1] != 0:
                raise ValueError(f"{path}:{line_number}: malformed clause")
            clauses.append(fields[:-1])
    if variables == 0:
        raise ValueError(f"missing DIMACS header: {path}")
    return variables, clauses


def solve(variables: int, clauses: list[tuple[int, ...]], units: tuple[int, ...],
          seconds: int, kissat: str) -> tuple[str, float]:
    started = time.monotonic()
    with tempfile.NamedTemporaryFile(mode="w", suffix=".cnf") as output:
        output.write(f"p cnf {variables} {len(clauses) + len(units)}\n")
        for clause in clauses:
            output.write(" ".join(map(str, clause)) + " 0\n")
        for unit in units:
            output.write(f"{unit} 0\n")
        output.flush()
        try:
            result = subprocess.run(
                [kissat, "-q", "--no-factor", "--no-preprocessfactor",
                 f"--time={seconds}", output.name],
                stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL,
                timeout=seconds + 10, check=False)
            outcome = {10: "SAT", 20: "UNSAT"}.get(
                result.returncode, "UNKNOWN")
        except subprocess.TimeoutExpired:
            outcome = "UNKNOWN"
    return outcome, round(time.monotonic() - started, 3)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("base", type=Path)
    parser.add_argument("--parent-units", type=int, nargs=2, required=True)
    parser.add_argument("--exclude", type=int, nargs="*", default=[])
    parser.add_argument("--seconds", type=int, default=5)
    parser.add_argument("--sample-pairs", type=int, default=16)
    parser.add_argument("--binary", action="store_true",
                        help="score individual variables with false/true branches")
    parser.add_argument("--sample-variables", type=int, default=32)
    parser.add_argument("--seed", type=int, default=85)
    parser.add_argument("--kissat", default="kissat")
    args = parser.parse_args()
    if args.seconds <= 0 or args.sample_pairs <= 0 or args.sample_variables <= 0:
        parser.error("seconds and sample counts must be positive")

    variables, clauses = read_dimacs(args.base)
    base_units = {clause[0] for clause in clauses if len(clause) == 1}
    forbidden = {abs(value) for value in (*args.parent_units, *args.exclude)}
    candidates = sorted({
        clause for clause in clauses
        if len(clause) == 8 and all(literal > 0 for literal in clause)
        and all(literal not in forbidden
                and literal not in base_units and -literal not in base_units
                for literal in clause)
    })
    pairs = [(left, right) for left, right in itertools.combinations(candidates, 2)
             if set(left).isdisjoint(right)]
    rng = random.Random(args.seed)
    if args.binary:
        variables_to_probe = sorted({literal for clause in candidates for literal in clause})
        chosen_variables = rng.sample(
            variables_to_probe, min(args.sample_variables, len(variables_to_probe)))
        print(json.dumps({"event": "binary-inventory",
                          "candidate_clauses": len(candidates),
                          "candidate_variables": len(variables_to_probe),
                          "sampled": len(chosen_variables),
                          "seconds": args.seconds, "seed": args.seed}), flush=True)
        results = []
        for sample_index, variable in enumerate(chosen_variables):
            outcomes = []
            elapsed = 0.0
            for literal in (-variable, variable):
                outcome, duration = solve(
                    variables, clauses, (*args.parent_units, literal),
                    args.seconds, args.kissat)
                outcomes.append(outcome)
                elapsed += duration
            record = {"event": "binary", "sample_index": sample_index,
                      "variable": variable, "unsat": outcomes.count("UNSAT"),
                      "sat": outcomes.count("SAT"),
                      "unknown": outcomes.count("UNKNOWN"),
                      "outcomes_false_true": outcomes,
                      "elapsed_s": round(elapsed, 3)}
            results.append(record)
            print(json.dumps(record), flush=True)
        ranking = sorted(results, key=lambda row: (
            -row["unsat"], row["unknown"], row["elapsed_s"], row["sample_index"]))
        print(json.dumps({"event": "binary-ranking", "variables": ranking}),
              flush=True)
        return
    chosen = rng.sample(pairs, min(args.sample_pairs, len(pairs)))
    print(json.dumps({"event": "inventory", "candidates": len(candidates),
                      "disjoint_pairs": len(pairs), "sampled": len(chosen),
                      "seconds": args.seconds, "seed": args.seed}), flush=True)
    results = []
    for pair_index, (left, right) in enumerate(chosen):
        outcomes = []
        elapsed = 0.0
        for li, ri in SAMPLE_POINTS:
            outcome, duration = solve(
                variables, clauses,
                (*args.parent_units, left[li], right[ri]),
                args.seconds, args.kissat)
            outcomes.append(outcome)
            elapsed += duration
        record = {
            "event": "pair", "sample_index": pair_index,
            "left": left, "right": right,
            "unsat": outcomes.count("UNSAT"), "sat": outcomes.count("SAT"),
            "unknown": outcomes.count("UNKNOWN"), "outcomes": outcomes,
            "elapsed_s": round(elapsed, 3),
        }
        results.append(record)
        print(json.dumps(record), flush=True)
    ranking = sorted(results, key=lambda row: (
        -row["unsat"], row["unknown"], row["elapsed_s"], row["sample_index"]))
    print(json.dumps({"event": "ranking", "pairs": ranking}), flush=True)


if __name__ == "__main__":
    main()
