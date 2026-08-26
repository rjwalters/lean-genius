#!/usr/bin/env python3
"""Emit one canonical H7/T0 empty-mask parent as native OPB.

The 861 semantic low-low edge variables and their order are exactly those of
``check_h7_t0_canonical_completion``.  Exact low degrees stay as native
pseudo-Boolean equalities.  Every canonical C4 clause and empty-mask unit is
translated literally to an equivalent pseudo-Boolean inequality; no
sequential-counter or other auxiliary variable is introduced.
"""

from __future__ import annotations

import argparse
import hashlib
import subprocess
import tempfile
from pathlib import Path

import check_h7_t0_canonical_completion as canonical
import check_h7_t0_by_empty_graph as empty_graph


class PseudoBoolean:
    def __init__(self) -> None:
        self.variable_count = 0
        self.constraints: list[tuple[tuple[tuple[int, int], ...], str, int]] = []

    def variable(self) -> int:
        self.variable_count += 1
        return self.variable_count

    def add(self, *literals: int) -> None:
        """Translate a disjunction literally as ``sum(literals) >= 1``."""
        assert literals
        coefficients: dict[int, int] = {}
        negative_count = 0
        for literal in literals:
            variable = abs(literal)
            coefficient = 1 if literal > 0 else -1
            coefficients[variable] = coefficients.get(variable, 0) + coefficient
            negative_count += literal < 0
        terms = tuple(
            (coefficient, variable)
            for variable, coefficient in sorted(coefficients.items())
            if coefficient
        )
        self.constraints.append((terms, ">=", 1 - negative_count))

    def exactly(self, literals: list[int], target: int) -> None:
        assert all(literal > 0 for literal in literals)
        terms = tuple((1, literal) for literal in literals)
        self.constraints.append((terms, "=", target))

    def write(self, path: Path) -> None:
        with path.open("w", encoding="ascii") as handle:
            handle.write(
                f"* #variable= {self.variable_count} "
                f"#constraint= {len(self.constraints)} "
                f"#equal= {sum(op == '=' for _, op, _ in self.constraints)} "
                "intsize= 32\n"
            )
            for terms, operator, rhs in self.constraints:
                body = " ".join(f"{coefficient:+d} x{variable}" for coefficient, variable in terms)
                handle.write(f"{body} {operator} {rhs} ;\n")


def build_parent(
    edge_count: int, type_index: int
) -> tuple[PseudoBoolean, int, tuple[tuple[int, int], ...]]:
    representatives = empty_graph.graph_representatives(edge_count)
    if not 0 <= type_index < len(representatives):
        raise ValueError(f"type index must be below {len(representatives)}")
    mask = representatives[type_index]
    pb, edge_variables, c4_count = canonical.build_cnf(PseudoBoolean)
    empty_graph.add_empty_cube(pb, edge_variables, mask)
    empty_edges = tuple(
        edge
        for index, edge in enumerate(empty_graph.quotient.EDGES)
        if (mask >> index) & 1
    )
    assert pb.variable_count == 861
    assert c4_count == 687260
    assert len(pb.constraints) == 42 + 687260 + 21
    return pb, c4_count, empty_edges


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--edge-count", type=int, choices=range(6, 10), default=7)
    parser.add_argument("--type-index", type=int, default=0)
    parser.add_argument("--keep-opb", type=Path)
    parser.add_argument("--emit-only", action="store_true")
    parser.add_argument("--solver", type=Path)
    parser.add_argument("--time", type=int, default=60)
    parser.add_argument("--proof-prefix", type=Path)
    args = parser.parse_args()

    try:
        pb, c4_count, empty_edges = build_parent(args.edge_count, args.type_index)
    except ValueError as error:
        parser.error(str(error))
    if args.keep_opb:
        path = args.keep_opb
        temporary = None
    else:
        temporary = tempfile.TemporaryDirectory(prefix="h7-pb-")
        path = Path(temporary.name) / "parent.opb"
    pb.write(path)
    print(f"F={args.edge_count}")
    print(f"type_index={args.type_index}")
    print(f"empty_edges={empty_edges}")
    print(f"variables={pb.variable_count}")
    print(f"constraints={len(pb.constraints)}")
    print(f"degree_equalities=42")
    print(f"c4_inequalities={c4_count}")
    print(f"sha256={hashlib.sha256(path.read_bytes()).hexdigest()}")
    print(f"opb={path}")
    if args.emit_only:
        if temporary is not None:
            temporary.cleanup()
        return
    if args.solver is None:
        parser.error("--solver is required unless --emit-only is used")
    command = [str(args.solver), str(path), f"--time-limit={args.time}"]
    if args.proof_prefix:
        command.append(f"--proof-log={args.proof_prefix}")
    completed = subprocess.run(command, text=True, check=False)
    print(f"solver_exit={completed.returncode}")
    if temporary is not None:
        temporary.cleanup()


if __name__ == "__main__":
    main()
