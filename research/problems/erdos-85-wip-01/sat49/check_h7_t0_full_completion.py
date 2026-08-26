#!/usr/bin/env python3
"""Complete the reviewed F=7 H7/T0 quotient witness to all 49 vertices.

The copy-indexed local relaxation has a deterministic SAT witness.  This
script fixes that witness and asks whether its seven high vertices, seven
empty-support vertices, fourteen actual singleton copies, and twenty-one
pair-support vertices can be completed by P-P, P-S, and S-S edges.

All support edges and E-sector edges are fixed.  Unknown edges are exactly
P-P, P-S, and S-S.  CNF constraints impose the graph-facing profiles

  P root with e E-neighbours: #P=e+2, #S=3-2e
  S root with e E-neighbours: #P=e+1, #S=5-2e

and at most one common neighbour for every pair among all 49 vertices.  Thus
a SAT assignment is a genuine C4-free 49-vertex graph with degree sequence
8^7 7^42.  UNSAT eliminates only this one quotient witness, not the full H7
stratum.  Verdict mode does not produce a checkable UNSAT certificate.
"""

from __future__ import annotations

import argparse
import itertools
import subprocess
import tempfile
from pathlib import Path


HIGH = tuple(range(7))
EMPTY = tuple(range(7, 14))
SINGLETON = tuple(range(14, 28))
PAIR = tuple(range(28, 49))
VERTICES = tuple(range(49))
LABEL_PAIRS = tuple(itertools.combinations(range(7), 2))
PAIR_VERTEX = {labels: 28 + i for i, labels in enumerate(LABEL_PAIRS)}

# The independently reviewed SAT_RELAXATION witness from 4298b67769.
EMPTY_EDGES = ((0, 1), (0, 2), (0, 3), (1, 2), (1, 4), (2, 5), (3, 6))
EMPTY_COPIES = (
    (0,),
    (1,),
    (2,),
    (0, 6, 9),
    (5, 7, 9, 11, 12),
    (3, 4, 6, 8, 10),
    (1, 2, 5, 8, 13),
)
EMPTY_PAIRS = (
    ((1, 2), (3, 4), (5, 6)),
    ((1, 3), (2, 5), (4, 6)),
    ((0, 2), (3, 6), (4, 5)),
    ((1, 5), (2, 6)),
    ((0, 1),),
    ((0, 6),),
    ((3, 5),),
)


def normalized_edge(left: int, right: int) -> tuple[int, int]:
    assert left != right
    return (left, right) if left < right else (right, left)


def fixed_true_edges() -> set[tuple[int, int]]:
    edges: set[tuple[int, int]] = set()
    # High-to-singleton support edges: copy index is 2*label+copy.
    for copy in range(14):
        edges.add(normalized_edge(copy // 2, 14 + copy))
    # High-to-pair support edges.
    for labels, vertex in PAIR_VERTEX.items():
        for label in labels:
            edges.add(normalized_edge(label, vertex))
    # Empty graph and its chosen singleton/pair neighbours.
    for left, right in EMPTY_EDGES:
        edges.add(normalized_edge(7 + left, 7 + right))
    for empty in range(7):
        for copy in EMPTY_COPIES[empty]:
            edges.add(normalized_edge(7 + empty, 14 + copy))
        for labels in EMPTY_PAIRS[empty]:
            edges.add(normalized_edge(7 + empty, PAIR_VERTEX[labels]))
    return edges


FIXED_TRUE = fixed_true_edges()
UNKNOWN_EDGES = tuple(itertools.combinations(PAIR, 2)) + tuple(
    normalized_edge(pair, singleton) for pair in PAIR for singleton in SINGLETON
) + tuple(itertools.combinations(SINGLETON, 2))
assert len(UNKNOWN_EDGES) == 210 + 294 + 91 == 595
EDGE_VAR = {edge: i + 1 for i, edge in enumerate(UNKNOWN_EDGES)}


class Cnf:
    def __init__(self) -> None:
        self.variable_count = len(EDGE_VAR)
        self.clauses: list[tuple[int, ...]] = []

    def add(self, clause) -> None:
        self.clauses.append(tuple(clause))

    def exactly(self, variables: list[int], target: int) -> None:
        """Naive exact-cardinality CNF; all candidate sets are at most 21."""
        assert 0 <= target <= len(variables)
        for chosen in itertools.combinations(variables, target + 1):
            self.add(-variable for variable in chosen)
        for chosen in itertools.combinations(variables, len(variables) - target + 1):
            self.add(chosen)

    def write(self, path: Path) -> None:
        with path.open("w", encoding="ascii") as handle:
            handle.write(f"p cnf {self.variable_count} {len(self.clauses)}\n")
            for clause in self.clauses:
                handle.write(" ".join(map(str, clause)) + " 0\n")


def edge_status(left: int, right: int) -> bool | int:
    if left == right:
        return False
    edge = normalized_edge(left, right)
    if edge in FIXED_TRUE:
        return True
    return EDGE_VAR.get(edge, False)


def fixed_empty_degrees() -> tuple[list[int], list[int]]:
    singleton = [0] * 14
    pair = [0] * 21
    for empty in range(7):
        for copy in EMPTY_COPIES[empty]:
            singleton[copy] += 1
        for labels in EMPTY_PAIRS[empty]:
            pair[LABEL_PAIRS.index(labels)] += 1
    return singleton, pair


def add_profile_constraints(cnf: Cnf) -> None:
    singleton_e, pair_e = fixed_empty_degrees()
    for copy, vertex in enumerate(SINGLETON):
        e_degree = singleton_e[copy]
        ss = [EDGE_VAR[normalized_edge(vertex, other)] for other in SINGLETON if other != vertex]
        ps = [EDGE_VAR[normalized_edge(vertex, other)] for other in PAIR]
        cnf.exactly(ss, 5 - 2 * e_degree)
        cnf.exactly(ps, 1 + e_degree)
    for index, vertex in enumerate(PAIR):
        e_degree = pair_e[index]
        pp = [EDGE_VAR[normalized_edge(vertex, other)] for other in PAIR if other != vertex]
        ps = [EDGE_VAR[normalized_edge(vertex, other)] for other in SINGLETON]
        cnf.exactly(pp, 2 + e_degree)
        cnf.exactly(ps, 3 - 2 * e_degree)


def add_c4_constraints(cnf: Cnf) -> int:
    added = 0
    for left in range(49):
        for right in range(left + 1, 49):
            candidates = [v for v in VERTICES if v != left and v != right]
            for first, second in itertools.combinations(candidates, 2):
                statuses = (
                    edge_status(left, first),
                    edge_status(right, first),
                    edge_status(left, second),
                    edge_status(right, second),
                )
                if False in statuses:
                    continue
                clause = [-status for status in statuses if status is not True]
                cnf.add(clause)
                added += 1
    return added


def build_cnf(omit_profiles: bool = False, omit_c4: bool = False) -> tuple[Cnf, int]:
    cnf = Cnf()
    if not omit_profiles:
        add_profile_constraints(cnf)
    c4_clauses = 0 if omit_c4 else add_c4_constraints(cnf)
    return cnf, c4_clauses


def parse_assignment(output: str) -> set[int] | None:
    if "s SATISFIABLE" not in output:
        return None
    positive: set[int] = set()
    for line in output.splitlines():
        if not line.startswith("v "):
            continue
        for token in line[2:].split():
            literal = int(token)
            if literal > 0:
                positive.add(literal)
    return positive


def validate_graph(
    positive: set[int], *, validate_profiles: bool, validate_c4: bool
) -> None:
    edges = set(FIXED_TRUE)
    edges.update(edge for edge, variable in EDGE_VAR.items() if variable in positive)
    degrees = [0] * 49
    neighbors = [set() for _ in VERTICES]
    for left, right in edges:
        degrees[left] += 1
        degrees[right] += 1
        neighbors[left].add(right)
        neighbors[right].add(left)
    assert degrees[:7] == [8] * 7
    if validate_profiles:
        assert degrees[7:] == [7] * 42
    if validate_c4:
        for left in VERTICES:
            for right in range(left + 1, 49):
                assert len(neighbors[left] & neighbors[right]) <= 1


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--solver", default="kissat")
    parser.add_argument("--time", type=int, default=1800)
    parser.add_argument("--keep-cnf", type=Path)
    parser.add_argument("--omit-profiles", action="store_true")
    parser.add_argument("--omit-c4", action="store_true")
    args = parser.parse_args()

    cnf, c4_clauses = build_cnf(args.omit_profiles, args.omit_c4)
    if args.keep_cnf:
        path = args.keep_cnf
        cnf.write(path)
        temporary = None
    else:
        temporary = tempfile.TemporaryDirectory(prefix="h7-full-completion-")
        path = Path(temporary.name) / "completion.cnf"
        cnf.write(path)
    print(f"variables={cnf.variable_count}")
    print(f"clauses={len(cnf.clauses)}")
    print(f"c4_clauses={c4_clauses}")
    print(f"cnf={path}")
    completed = subprocess.run(
        [args.solver, "-q", "--no-factor", "--no-preprocessfactor", f"--time={args.time}", str(path)],
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        check=False,
    )
    print(completed.stdout, end="")
    positive = parse_assignment(completed.stdout)
    if positive is not None:
        validate_graph(
            positive,
            validate_profiles=not args.omit_profiles,
            validate_c4=not args.omit_c4,
        )
        if args.omit_profiles or args.omit_c4:
            enabled = []
            if not args.omit_profiles:
                enabled.append("PROFILES")
            if not args.omit_c4:
                enabled.append("C4")
            print(f"validated=SAT_ABLATION_{'_AND_'.join(enabled)}")
        else:
            print("validated=SAT_FULL_GRAPH")
    elif "s UNSATISFIABLE" in completed.stdout:
        print("validated=UNSAT_ONE_QUOTIENT_WITNESS_VERDICT_ONLY")
    else:
        print("validated=UNKNOWN")
    if temporary is not None:
        temporary.cleanup()


if __name__ == "__main__":
    main()
