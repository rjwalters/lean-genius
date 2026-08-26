#!/usr/bin/env python3
"""Solve one empty-sector cube of the canonical H7/T0 CNF.

The base instance is byte-for-byte the reviewed canonical completion CNF.
This script appends 21 unit clauses fixing the E-E edges to one of the 43
seven-vertex graph types enumerated by ``probe_h7_t0_quotient_scale.py``.
Thus these are genuine cubes of the single canonical instance.  Covering the
43 representatives requires the S7 relabeling argument; alternatively all
84,612 labeled cubes can be emitted without graph-isomorphism reduction.
"""

from __future__ import annotations

import argparse
import hashlib
import itertools
import subprocess
import tempfile
from pathlib import Path

import check_h7_t0_canonical_completion as canonical
import check_h7_t0_canonical_compact as compact
import check_h7_t0_copy_quotient as quotient
import probe_h7_t0_quotient_scale as scale


def graph_representatives(edge_count: int) -> list[int]:
    representatives = []
    seen: set[int] = set()
    for indices in itertools.combinations(range(21), edge_count):
        mask = scale.edge_mask(indices)
        if mask in seen:
            continue
        adjacency, degrees = scale.graph_data(mask)
        if not quotient.passes_graph_filters(adjacency, degrees):
            continue
        representatives.append(mask)
        seen.update(scale.orbit(mask))
    return representatives


def add_empty_cube(
    cnf: canonical.Cnf,
    edge_variables: dict[tuple[int, int], int],
    empty_mask: int,
) -> None:
    for index, (left, right) in enumerate(quotient.EDGES):
        variable = edge_variables[(7 + left, 7 + right)]
        cnf.add(variable if (empty_mask >> index) & 1 else -variable)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--edge-count", type=int, choices=range(6, 10), default=7)
    parser.add_argument("--type-index", type=int, default=0)
    parser.add_argument("--solver", default="kissat")
    parser.add_argument("--time", type=int, default=1800)
    parser.add_argument("--keep-cnf", type=Path)
    parser.add_argument("--emit-only", action="store_true")
    parser.add_argument(
        "--compact",
        action="store_true",
        help="cube the formally reified compact canonical instance",
    )
    args = parser.parse_args()

    representatives = graph_representatives(args.edge_count)
    if not 0 <= args.type_index < len(representatives):
        parser.error(f"type index must be below {len(representatives)}")
    empty_mask = representatives[args.type_index]
    empty_edges = tuple(
        edge for index, edge in enumerate(quotient.EDGES) if (empty_mask >> index) & 1
    )

    cnf_factory = compact.CompactCnf if args.compact else canonical.Cnf
    cnf, edge_variables, c4_clauses = canonical.build_cnf(cnf_factory)
    add_empty_cube(cnf, edge_variables, empty_mask)
    assert cnf.variable_count == (17633 if args.compact else 71463)
    assert len(cnf.clauses) == (720825 if args.compact else 830123)
    if args.keep_cnf:
        path = args.keep_cnf
        temporary = None
    else:
        temporary = tempfile.TemporaryDirectory(prefix="h7-empty-cube-")
        path = Path(temporary.name) / "cube.cnf"
    cnf.write(path)
    print(f"F={args.edge_count}")
    print(f"type_index={args.type_index}/{len(representatives)}")
    print(f"empty_edges={empty_edges}")
    print(f"encoding={'compact' if args.compact else 'baseline'}")
    print(f"variables={cnf.variable_count}")
    print(f"clauses={len(cnf.clauses)}")
    print(f"c4_clauses={c4_clauses}")
    print(f"sha256={hashlib.sha256(path.read_bytes()).hexdigest()}")
    print(f"cnf={path}")
    if args.emit_only:
        if temporary is not None:
            temporary.cleanup()
        return
    completed = subprocess.run(
        [args.solver, "-q", f"--time={args.time}", str(path)],
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        check=False,
    )
    print(completed.stdout, end="")
    positive = canonical.parse_assignment(completed.stdout)
    if positive is not None:
        canonical.validate(edge_variables, positive)
        for index, (left, right) in enumerate(quotient.EDGES):
            variable = edge_variables[(7 + left, 7 + right)]
            assert (variable in positive) == bool((empty_mask >> index) & 1)
        print("validated=SAT_GENUINE_H7_T0_GRAPH_IN_CUBE")
    elif "s UNSATISFIABLE" in completed.stdout:
        print("validated=UNSAT_ONE_EMPTY_GRAPH_CUBE_VERDICT_ONLY")
    else:
        print("validated=UNKNOWN")
    if temporary is not None:
        temporary.cleanup()


if __name__ == "__main__":
    main()
