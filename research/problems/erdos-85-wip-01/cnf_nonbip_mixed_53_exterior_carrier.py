#!/usr/bin/env python3
"""Deterministic CNF/Kissat form of the q=8 [5,3] triangle-carrier probe.

The semantic interface matches ``probe_nonbip_mixed_53_exterior_carrier.py``.
It is only the displayed-defect-triangle relaxation; defect connectivity and
triangle-free nonbipartite (C5+) cases are deliberately absent.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from itertools import combinations
from pathlib import Path


Q = 8
LARGE = 40
ORDER = 64
Clause = list[int]


class CNF:
    def __init__(self) -> None:
        self.names: dict[tuple[object, ...], int] = {}
        self.next_var = 1
        self.clauses: list[Clause] = []

    def var(self, *name: object) -> int:
        key = tuple(name)
        if key not in self.names:
            self.names[key] = self.next_var
            self.next_var += 1
        return self.names[key]

    def add(self, *lits: int) -> None:
        assert lits and all(lit != 0 for lit in lits)
        self.clauses.append(list(lits))

    def and_gate(self, a: int, b: int, *name: object) -> int:
        out = self.var(*name)
        self.add(-out, a)
        self.add(-out, b)
        self.add(out, -a, -b)
        return out

    def or_gate(self, a: int, b: int, *name: object) -> int:
        out = self.var(*name)
        self.add(-a, out)
        self.add(-b, out)
        self.add(a, b, -out)
        return out

    def at_most_one(self, xs: list[int], *name: object) -> None:
        """Sinz sequential encoding."""
        if len(xs) <= 1:
            return
        prefix = [self.var(*name, "prefix", i) for i in range(len(xs) - 1)]
        self.add(-xs[0], prefix[0])
        for i in range(1, len(xs) - 1):
            self.add(-xs[i], prefix[i])
            self.add(-prefix[i - 1], prefix[i])
            self.add(-xs[i], -prefix[i - 1])
        self.add(-xs[-1], -prefix[-1])

    def exactly(self, xs: list[int], target: int, *name: object) -> None:
        """Exact cardinality via exact threshold recurrence up to target+1."""
        assert 0 <= target <= len(xs)
        if target == 0:
            for x in xs:
                self.add(-x)
            return
        if target == len(xs):
            for x in xs:
                self.add(x)
            return
        prev: dict[int, int] = {}
        for i, x in enumerate(xs):
            curr: dict[int, int] = {1: x if 1 not in prev else
                self.or_gate(prev[1], x, *name, i, "ge", 1)}
            for j in range(2, min(target + 1, i + 1) + 1):
                if j - 1 not in prev:
                    continue
                both = self.and_gate(prev[j - 1], x, *name, i, "both", j)
                curr[j] = (both if j not in prev else
                    self.or_gate(prev[j], both, *name, i, "ge", j))
            prev = curr
        self.add(prev[target])
        self.add(-prev[target + 1])


def edge_var(cnf: CNF, u: int, v: int) -> int:
    assert u != v
    return cnf.var("a", min(u, v), max(u, v))


def defect_var(cnf: CNF, u: int, v: int) -> int:
    assert u != v and (u < LARGE) == (v < LARGE)
    return cnf.var("d", min(u, v), max(u, v))


def build(triangle_ambient_edges: int) -> CNF:
    assert triangle_ambient_edges in (0, 1)
    cnf = CNF()

    # Allocate semantic edge variables first in a stable lexicographic block.
    for u, v in combinations(range(ORDER), 2):
        edge_var(cnf, u, v)

    # Exact internal and cross-shore ambient degrees.
    for u in range(ORDER):
        own = range(0, LARGE) if u < LARGE else range(LARGE, ORDER)
        other = range(LARGE, ORDER) if u < LARGE else range(0, LARGE)
        cnf.exactly([edge_var(cnf, u, v) for v in own if v != u],
                    5 if u < LARGE else 3, "degree", u, "own")
        cnf.exactly([edge_var(cnf, u, v) for v in other],
                    3 if u < LARGE else 5, "degree", u, "cross")

    common: dict[tuple[int, int], list[int]] = {}
    for u, v in combinations(range(ORDER), 2):
        terms = []
        for w in range(ORDER):
            if w in (u, v):
                continue
            terms.append(cnf.and_gate(
                edge_var(cnf, u, w), edge_var(cnf, v, w),
                "common", u, v, w))
        common[u, v] = terms
        cnf.at_most_one(terms, "common-amo", u, v)
        if (u < LARGE) != (v < LARGE):
            cnf.clauses.append(terms.copy())

    # Internal defect is equivalent to absence of a common neighbor.
    for shore in (range(0, LARGE), range(LARGE, ORDER)):
        for u, v in combinations(shore, 2):
            d = defect_var(cnf, u, v)
            for witness in common[u, v]:
                cnf.add(-d, -witness)
            cnf.clauses.append([d, *common[u, v]])
        for u in shore:
            cnf.exactly([
                defect_var(cnf, u, v) for v in shore if v != u
            ], Q - 1, "defect-degree", u)

    # Displayed large-shore defect triangle and canonical ambient orbits.
    for u, v in ((0, 1), (1, 2), (0, 2)):
        cnf.add(defect_var(cnf, u, v))
    triangle_edges = {(0, 1)} if triangle_ambient_edges else set()
    for u, v in ((0, 1), (0, 2), (1, 2)):
        cnf.add(edge_var(cnf, u, v) * (1 if (u, v) in triangle_edges else -1))
    if triangle_ambient_edges == 0:
        internal = [set(range(3, 8)), set(range(8, 13)), set(range(13, 18))]
    else:
        internal = [{1, 3, 4, 5, 6}, {0, 7, 8, 9, 10}, set(range(11, 16))]
    external = [set(range(40, 43)), set(range(43, 46)), set(range(46, 49))]
    for u in range(3):
        for v in range(LARGE):
            if u != v:
                lit = edge_var(cnf, u, v)
                cnf.add(lit if v in internal[u] else -lit)
        for v in range(LARGE, ORDER):
            lit = edge_var(cnf, u, v)
            cnf.add(lit if v in external[u] else -lit)

    # Redundant carrier propagation: a defect hit in each other part.
    for i in range(3):
        for f in sorted(external[i]):
            for j in range(3):
                if i != j:
                    cnf.clauses.append([
                        defect_var(cnf, f, g) for g in sorted(external[j])
                    ])
    return cnf


def dimacs(cnf: CNF) -> bytes:
    lines = [f"p cnf {cnf.next_var - 1} {len(cnf.clauses)}"]
    lines.extend(" ".join(map(str, clause)) + " 0" for clause in cnf.clauses)
    return ("\n".join(lines) + "\n").encode()


def parse_kissat_model(path: Path) -> dict[int, bool]:
    status = []
    values: dict[int, bool] = {}
    for line in path.read_text().splitlines():
        if line.startswith("s "):
            status.append(line[2:].strip())
        if not line.startswith("v "):
            continue
        for raw in line[2:].split():
            lit = int(raw)
            if lit == 0:
                continue
            old = values.get(abs(lit))
            if old is not None and old != (lit > 0):
                raise ValueError(f"conflicting assignment for {abs(lit)}")
            values[abs(lit)] = lit > 0
    if status != ["SATISFIABLE"]:
        raise ValueError(f"expected one SATISFIABLE status, got {status}")
    return values


def verify_model(cnf: CNF, values: dict[int, bool], triangle_case: int) -> dict[str, object]:
    """Recompute every semantic condition from ambient edges only."""
    expected_vars = set(range(1, cnf.next_var))
    if set(values) != expected_vars:
        missing = sorted(expected_vars - set(values))
        extra = sorted(set(values) - expected_vars)
        raise ValueError(f"incomplete/out-of-range assignment: missing={missing[:8]} extra={extra[:8]}")
    if any(not any(values[abs(lit)] == (lit > 0) for lit in clause)
           for clause in cnf.clauses):
        raise ValueError("assignment does not satisfy the emitted CNF")
    sets = [set() for _ in range(ORDER)]
    for u, v in combinations(range(ORDER), 2):
        if values[edge_var(cnf, u, v)]:
            sets[u].add(v)
            sets[v].add(u)
    assert all(len(sets[u] & set(range(LARGE))) == (5 if u < LARGE else 5)
               for u in range(ORDER))
    assert all(len(sets[u] & set(range(LARGE, ORDER))) == (3 if u < LARGE else 3)
               for u in range(ORDER))
    common = {(u, v): len(sets[u] & sets[v])
              for u, v in combinations(range(ORDER), 2)}
    assert max(common.values()) <= 1
    assert all(common[u, v] == 1
               for u in range(LARGE) for v in range(LARGE, ORDER))
    defect = {(u, v): common[u, v] == 0
              for shore in (range(LARGE), range(LARGE, ORDER))
              for u, v in combinations(shore, 2)}
    assert all(sum(defect[min(u, v), max(u, v)]
                   for v in shore if v != u) == Q - 1
               for shore in (range(LARGE), range(LARGE, ORDER)) for u in shore)
    assert all(defect[pair] for pair in ((0, 1), (1, 2), (0, 2)))
    expected_triangle = {(0, 1)} if triangle_case else set()
    assert {pair for pair in ((0, 1), (0, 2), (1, 2))
            if pair[1] in sets[pair[0]]} == expected_triangle
    if triangle_case == 0:
        internal = [set(range(3, 8)), set(range(8, 13)), set(range(13, 18))]
    else:
        internal = [{1, 3, 4, 5, 6}, {0, 7, 8, 9, 10}, set(range(11, 16))]
    assert all(internal[i] == (sets[i] & set(range(LARGE)))
               for i in range(3))
    external = [set(range(40, 43)), set(range(43, 46)), set(range(46, 49))]
    assert all(external[i] == (sets[i] & set(range(LARGE, ORDER)))
               for i in range(3))
    assert all(any(defect[min(f, g), max(f, g)] for g in external[j])
               for i in range(3) for f in external[i]
               for j in range(3) if i != j)
    neighbors = [sorted(row) for row in sets]
    raw = json.dumps(neighbors, separators=(",", ":")).encode()
    return {"model_sha256": hashlib.sha256(raw).hexdigest(),
            "carrier_support": sorted(set.union(*external))}


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--triangle-ambient-edges", type=int, choices=(0, 1), required=True)
    parser.add_argument("--output", type=Path)
    parser.add_argument("--verify-model", type=Path)
    args = parser.parse_args()
    cnf = build(args.triangle_ambient_edges)
    payload = dimacs(cnf)
    report: dict[str, object] = {
        "triangle_ambient_edges": args.triangle_ambient_edges,
        "variables": cnf.next_var - 1,
        "clauses": len(cnf.clauses),
        "sha256": hashlib.sha256(payload).hexdigest(),
    }
    if args.output is not None:
        args.output.write_bytes(payload)
        report["output"] = str(args.output)
    if args.verify_model is not None:
        report.update(verify_model(
            cnf, parse_kissat_model(args.verify_model),
            args.triangle_ambient_edges))
        report["model_verified"] = True
    print(json.dumps(report, sort_keys=True))


if __name__ == "__main__":
    main()
