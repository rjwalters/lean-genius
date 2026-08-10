#!/usr/bin/env python3
"""Independently verify an H-lift SAT assignment on its edge variables.

Usage:
    python3 verify_hlift_assignment.py kissat-output.txt

The verifier deliberately ignores every encoding auxiliary.  It rebuilds
the fixed service/defect graph A from the committed witness, extracts the
first C(192,2) edge variables in the encoder's documented order, and checks
the mathematical relaxation directly:

* H is simple and 13-regular;
* each A-pair has zero common H-neighbors;
* every other distinct pair has exactly one common H-neighbor;
* |E(H) intersect E(A)| = 264;
* each local A-incidence count has odd parity.

Passing this verifier proves only that the fixed-service H-relaxation is
SAT.  It does not promote the assignment to a full extremal graph witness.
"""
from itertools import combinations
import os
import sys


def load_fixed_instance():
    """Execute only the encoder's data-construction preamble, not its CNF."""
    path = os.path.join(os.path.dirname(__file__), "model4444_hlift.py")
    with open(path, encoding="utf-8") as source:
        prefix = source.read().split("RULE_COUNTS = {}", 1)[0]
    ns = {}
    exec(prefix, ns)
    return ns["N"], ns["zero_pairs"], ns["all_pairs"]


def parse_kissat_assignment(path):
    values = {}
    status = None
    with open(path, encoding="utf-8", errors="replace") as stream:
        for line in stream:
            if line.startswith("s "):
                status = line[2:].strip()
            if not line.startswith("v "):
                continue
            for token in line[2:].split():
                lit = int(token)
                if lit:
                    values[abs(lit)] = lit > 0
    if status != "SATISFIABLE":
        raise ValueError(f"expected `s SATISFIABLE`, got {status!r}")
    return values


def verify_structure(n, zero_pairs, all_pairs, edge_values,
                     expected_degree, expected_A_edges):
    if len(edge_values) != len(all_pairs):
        raise ValueError(f"need {len(all_pairs)} edge values, "
                         f"got {len(edge_values)}")
    neighbors = [set() for _ in range(n)]
    for pair, present in zip(all_pairs, edge_values):
        if not present:
            continue
        u, v = sorted(pair)
        neighbors[u].add(v)
        neighbors[v].add(u)

    degrees = [len(row) for row in neighbors]
    bad_degrees = [(v, d) for v, d in enumerate(degrees)
                   if d != expected_degree]
    if bad_degrees:
        raise ValueError(f"degree failures: {bad_degrees[:10]}")

    for pair in all_pairs:
        u, v = sorted(pair)
        actual = len(neighbors[u] & neighbors[v])
        expected = 0 if pair in zero_pairs else 1
        if actual != expected:
            raise ValueError("common-neighbor failure at "
                             f"({u},{v}): got {actual}, expect {expected}")

    A_edges = sum(pair in zero_pairs and present
                  for pair, present in zip(all_pairs, edge_values))
    if A_edges != expected_A_edges:
        raise ValueError(f"H-intersection-A edges {A_edges}, "
                         f"expect {expected_A_edges}")

    for v in range(n):
        a_v = sum(frozenset((v, w)) in zero_pairs for w in neighbors[v])
        if a_v % 2 != expected_degree % 2:
            raise ValueError(f"local parity failure at {v}: a_v={a_v}")
    return {"vertices": n, "edges": sum(degrees) // 2,
            "A_edges": A_edges}


def self_test():
    # C5 has degree two.  Adjacent pairs have zero common neighbors and
    # distance-two pairs have one, so A is exactly its five edge pairs.
    n = 5
    all_pairs = [frozenset(p) for p in combinations(range(n), 2)]
    cycle = {frozenset((v, (v + 1) % n)) for v in range(n)}
    values = [pair in cycle for pair in all_pairs]
    result = verify_structure(n, cycle, all_pairs, values, 2, 5)
    assert result == {"vertices": 5, "edges": 5, "A_edges": 5}
    broken = values.copy()
    broken[0] = not broken[0]
    try:
        verify_structure(n, cycle, all_pairs, broken, 2, 5)
    except ValueError:
        pass
    else:
        raise AssertionError("tampered self-test assignment was accepted")
    print("SELF-TEST OK")


def main():
    if len(sys.argv) == 2 and sys.argv[1] == "--self-test":
        self_test()
        return
    if len(sys.argv) != 2:
        raise SystemExit(f"usage: {sys.argv[0]} ASSIGNMENT | --self-test")
    n, zero_pairs, all_pairs = load_fixed_instance()
    assignment = parse_kissat_assignment(sys.argv[1])
    edge_values = []
    for var in range(1, len(all_pairs) + 1):
        if var not in assignment:
            raise ValueError(f"missing edge variable {var}")
        edge_values.append(assignment[var])
    result = verify_structure(n, zero_pairs, all_pairs, edge_values, 13, 264)
    print("VERIFIED", result)


if __name__ == "__main__":
    main()
