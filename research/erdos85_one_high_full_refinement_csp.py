#!/usr/bin/env python3
"""Test exact 40-leaf realizability of one-high pairing refinements.

Input is JSON, either one refinement or a list of refinements.  A refinement
is eight rows; each row contains one or two canonical miss-label pairs, e.g.

  [[[2, 4], [3, 5]], [[0, 6]], ...]

Canonical lex order fixes the low/high labels on the two endpoints.  Each
non-mate branch cut is required to be a bijection between precisely the
vertices which do not miss the opposite branch.  Standard-mate cuts are
empty.  Finally every pair of the 40 vertices has at most one common
neighbor, exactly the C4-free condition.  Thus SAT returns a concrete graph
realizing all pairing-refinement data; UNSAT says that refinement is already
excluded without the remaining V2 constraints.
"""

from __future__ import annotations

import argparse
from concurrent.futures import ProcessPoolExecutor
from itertools import combinations
import json
from pathlib import Path
import subprocess
import tempfile

BRANCHES = 8
WIDTH = 5


class Cnf:
    def __init__(self) -> None:
        self.variables = 0
        self.clauses: list[list[int]] = []

    def variable(self) -> int:
        self.variables += 1
        return self.variables

    def add(self, literals) -> None:
        clause: list[int] = []
        seen: set[int] = set()
        for literal in literals:
            if literal is True:
                return
            if literal is False:
                continue
            if -literal in seen:
                return
            if literal not in seen:
                clause.append(literal)
                seen.add(literal)
        self.clauses.append(clause)


def negate(literal):
    return not literal if isinstance(literal, bool) else -literal


def conjunction(cnf: Cnf, literals):
    literals = [x for x in literals if x is not True]
    if any(x is False for x in literals):
        return False
    if not literals:
        return True
    if len(literals) == 1:
        return literals[0]
    out = cnf.variable()
    for literal in literals:
        cnf.add([-out, literal])
    cnf.add([out] + [negate(x) for x in literals])
    return out


def disjunction(cnf: Cnf, literals):
    literals = [x for x in literals if x is not False]
    if any(x is True for x in literals):
        return True
    if not literals:
        return False
    if len(literals) == 1:
        return literals[0]
    out = cnf.variable()
    for literal in literals:
        cnf.add([negate(literal), out])
    cnf.add([-out] + literals)
    return out


def exact_cardinality(cnf: Cnf, literals: list, target: int) -> None:
    """Small direct encoding, efficient here because target is 22 or 24/25."""
    fixed_true = sum(x is True for x in literals)
    variables = [x for x in literals if not isinstance(x, bool)]
    target -= fixed_true
    if target < 0 or target > len(variables):
        cnf.add([])
        return
    # At most target true; at most n-target false.
    for chosen in combinations(variables, target + 1):
        cnf.add([-x for x in chosen])
    for chosen in combinations(variables, len(variables) - target + 1):
        cnf.add(chosen)


def vertex(branch: int, slot: int) -> int:
    return WIDTH * branch + slot


def standard_mate(branch: int) -> int:
    return branch ^ 1


def validate(refinement: list[list[list[int]]]) -> None:
    if len(refinement) != BRANCHES:
        raise ValueError("a refinement must have eight rows")
    profile = sum(len(refinement[i]) == 1 for i in range(0, BRANCHES, 2))
    for i, row in enumerate(refinement):
        expected = 1 if i % 2 == 0 and i // 2 < profile else 2
        if len(row) != expected:
            raise ValueError(f"row {i} has {len(row)} pairs, expected {expected}")
        for pair in row:
            if len(pair) != 2 or not all(0 <= x < BRANCHES for x in pair):
                raise ValueError(f"invalid label pair in row {i}: {pair}")
            if pair[0] > pair[1]:
                raise ValueError(f"noncanonical label pair in row {i}: {pair}")
        codes = [8 * pair[0] + pair[1] for pair in row]
        if codes != sorted(codes):
            raise ValueError(f"row {i} pairing edges are not lex sorted")


def solve_refinement(refinement: list[list[list[int]]], timeout_ms: int,
                     include_f2: bool = True):
    validate(refinement)
    cnf = Cnf()

    def active(i: int, slot: int, other: int):
        edge = slot // 2
        if edge >= len(refinement[i]):
            return True  # the unmatched branch vertex has no miss label
        lo, hi = refinement[i][edge]
        label = lo if slot % 2 == 0 else hi
        return label != other

    cross = {}
    for i in range(BRANCHES):
        for j in range(i + 1, BRANCHES):
            if j == standard_mate(i):
                continue
            for a in range(WIDTH):
                for b in range(WIDTH):
                    cross[(i, a, j, b)] = cnf.variable()

    def adj(u: int, v: int):
        if u == v:
            return False
        if u > v:
            u, v = v, u
        i, a = divmod(u, WIDTH)
        j, b = divmod(v, WIDTH)
        if i == j:
            return a // 2 == b // 2 and a < 2 * len(refinement[i])
        if j == standard_mate(i):
            return False
        return cross[(i, a, j, b)]

    # Each far cut is a bijection on its active sets.  This simultaneously
    # enforces exact far degrees and at-most-one neighbor in every branch.
    for i in range(BRANCHES):
        for j in range(i + 1, BRANCHES):
            if j == standard_mate(i):
                continue
            for a in range(WIDTH):
                variables = [cross[(i, a, j, b)] for b in range(WIDTH)]
                if active(i, a, j):
                    cnf.add(variables)
                    for left, right in combinations(variables, 2):
                        cnf.add([-left, -right])
                else:
                    for variable in variables:
                        cnf.add([-variable])
            for b in range(WIDTH):
                variables = [cross[(i, a, j, b)] for a in range(WIDTH)]
                if active(j, b, i):
                    cnf.add(variables)
                    for left, right in combinations(variables, 2):
                        cnf.add([-left, -right])
                else:
                    for variable in variables:
                        cnf.add([-variable])

    # Direct four-edge clauses encode common-neighbor count <= 1 without the
    # hundreds of thousands of symbolic conjunction nodes Z3 created here.
    n = BRANCHES * WIDTH
    for u in range(n):
        for v in range(u + 1, n):
            candidates = [w for w in range(n) if w != u and w != v]
            for w, x in combinations(candidates, 2):
                cnf.add([negate(adj(u, w)), negate(adj(v, w)),
                         negate(adj(u, x)), negate(adj(v, x))])

    # Same-branch vertices already share their root in the ambient graph, so
    # they may have no common leaf neighbor at all.
    for i in range(BRANCHES):
        for a in range(WIDTH):
            for b in range(a + 1, WIDTH):
                u, v = vertex(i, a), vertex(i, b)
                for w in range(n):
                    if w == u or w == v:
                        continue
                    auw, avw = adj(u, w), adj(v, w)
                    cnf.add([negate(auw), negate(avw)])

    # F2 paired-common ledger.  The preceding C4 constraints make each
    # Boolean below equivalent to "this ordered mate-block pair has exactly
    # one common leaf neighbor".
    if include_f2:
        # The equations for i and mate(i) count the same unordered pairs.
        for i in range(0, BRANCHES, 2):
            j = standard_mate(i)
            indicators = []
            for a in range(WIDTH):
                for b in range(WIDTH):
                    u, v = vertex(i, a), vertex(j, b)
                    witnesses = []
                    for w in range(n):
                        auw, avw = adj(u, w), adj(v, w)
                        witnesses.append(conjunction(cnf, [auw, avw]))
                    indicators.append(disjunction(cnf, witnesses))
            target = 30 - 2 * len(refinement[i]) - 2 * len(refinement[j])
            exact_cardinality(cnf, indicators, target)

    with tempfile.TemporaryDirectory(prefix="erdos85-h1-csp-") as directory:
        dimacs = Path(directory) / "instance.cnf"
        with dimacs.open("w") as output:
            output.write(f"p cnf {cnf.variables} {len(cnf.clauses)}\n")
            for clause in cnf.clauses:
                output.write(" ".join(map(str, clause)) + " 0\n")
        try:
            run = subprocess.run(
                ["kissat", "--quiet", str(dimacs)], capture_output=True,
                text=True, timeout=None if not timeout_ms else timeout_ms / 1000)
        except subprocess.TimeoutExpired:
            return "unknown", None
    if run.returncode == 20:
        return "unsat", None
    if run.returncode != 10:
        raise RuntimeError(f"kissat failed ({run.returncode}): {run.stderr}")
    assignment = set()
    for line in run.stdout.splitlines():
        if line.startswith("v "):
            assignment.update(int(x) for x in line[2:].split() if int(x) > 0)
    cuts = []
    for (i, a, j, b), variable in cross.items():
        if variable in assignment:
            cuts.append([i, a, j, b])
    return "sat", {"cross_edges": cuts}


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("input", type=Path)
    parser.add_argument("--timeout-ms", type=int, default=0)
    parser.add_argument("--models", action="store_true")
    parser.add_argument("--jobs", type=int, default=1)
    parser.add_argument("--indices", help="comma-separated original indices")
    parser.add_argument("--no-f2", action="store_true",
                        help="omit paired-common equalities (lex-prefix test)")
    args = parser.parse_args()
    data = json.loads(args.input.read_text())
    refinements = data if (data and isinstance(data[0][0][0], list)) else [data]
    selected = list(enumerate(refinements))
    if args.indices:
        wanted = {int(text) for text in args.indices.split(",")}
        if any(index < 0 or index >= len(refinements) for index in wanted):
            parser.error("--indices contains an out-of-range index")
        selected = [(index, refinement) for index, refinement in selected
                    if index in wanted]
    summary = {"sat": 0, "unsat": 0, "unknown": 0}
    if args.jobs < 1:
        parser.error("--jobs must be positive")
    if args.jobs == 1:
        results = map(lambda refinement:
                      solve_refinement(refinement, args.timeout_ms,
                                       not args.no_f2),
                      [refinement for _, refinement in selected])
    else:
        executor = ProcessPoolExecutor(max_workers=args.jobs)
        results = executor.map(solve_refinement,
                               [refinement for _, refinement in selected],
                               [args.timeout_ms] * len(selected),
                               [not args.no_f2] * len(selected))
    for (index, _), (status, model) in zip(selected, results):
        summary[status] += 1
        record = {"index": index, "status": status}
        if args.models and model is not None:
            record["model"] = model
        print(json.dumps(record, separators=(",", ":")), flush=True)
    print(json.dumps({"summary": summary}, separators=(",", ":")), flush=True)


if __name__ == "__main__":
    main()
