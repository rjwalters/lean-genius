#!/usr/bin/env python3
"""Rank exact-clause third-level splits of a hard small-high cube."""

from __future__ import annotations

import argparse
import itertools
import subprocess
import tempfile
from pathlib import Path


def read_dimacs(path: Path) -> tuple[int, list[tuple[int, ...]]]:
    variables = 0
    clauses: list[tuple[int, ...]] = []
    for line in path.read_text().splitlines():
        if line.startswith("p cnf "):
            variables = int(line.split()[2])
        elif line and line[0] not in "c%0":
            clause = tuple(map(int, line.split()))
            if not clause or clause[-1] != 0:
                raise ValueError(f"malformed DIMACS line: {line}")
            clauses.append(clause[:-1])
    if variables == 0:
        raise ValueError("missing DIMACS header")
    return variables, clauses


def solve(variables: int, clauses: list[tuple[int, ...]], units: tuple[int, ...],
          seconds: int, kissat: str) -> str:
    with tempfile.NamedTemporaryFile(mode="w", suffix=".cnf") as out:
        out.write(f"p cnf {variables} {len(clauses) + len(units)}\n")
        for clause in clauses:
            out.write(" ".join(map(str, clause)) + " 0\n")
        for unit in units:
            out.write(f"{unit} 0\n")
        out.flush()
        result = subprocess.run(
            [kissat, "-q", f"--time={seconds}", out.name],
            stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL, check=False)
    return {10: "SAT", 20: "UNSAT"}.get(result.returncode, "UNKNOWN")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("base", type=Path)
    parser.add_argument("--units", type=int, nargs="+", required=True)
    parser.add_argument("--exclude", type=int, nargs="*", default=[])
    parser.add_argument("--seconds", type=int, default=20)
    parser.add_argument("--offset", type=int, default=0)
    parser.add_argument("--limit", type=int, default=12)
    parser.add_argument("--kissat", default="kissat")
    args = parser.parse_args()

    variables, clauses = read_dimacs(args.base)
    base_units = {c[0] for c in clauses if len(c) == 1}
    forbidden = {abs(x) for x in (*args.units, *args.exclude)}
    candidates = [c for c in clauses
                  if len(c) == 8 and all(x > 0 for x in c)
                  and not any(x in forbidden or x in base_units or -x in base_units
                              for x in c)]
    pairs = [(left, right) for left, right in itertools.combinations(candidates, 2)
             if set(left).isdisjoint(right)]
    print(f"candidates={len(candidates)} disjoint_pairs={len(pairs)}")
    for left, right in pairs[args.offset:args.offset + args.limit]:
        outcomes = []
        for li, ri in ((0, 0), (3, 3), (7, 7), (0, 7)):
            outcomes.append(solve(variables, clauses,
                                  tuple(args.units) + (left[li], right[ri]),
                                  args.seconds, args.kissat))
        print(left, right, outcomes, flush=True)


if __name__ == "__main__":
    main()
