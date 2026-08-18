#!/usr/bin/env python3
"""Generate transparent exterior-grid CNFs for the 18 fixed-K cases.

The manifest is produced by the K-symmetry enumeration.  Variable allocation
and sequential counters deliberately match `Erdos85MuThreeAllTfNativeCnf`:
1128 edge variables, followed by row/column hit counters and the explicit
common-neighbour/C4 blocks.
"""

from __future__ import annotations

import argparse
import json
from dataclasses import dataclass, field
from pathlib import Path


ORDER = 8


@dataclass
class State:
    top: int
    clauses: list[list[int]] = field(default_factory=list)

    def fresh(self) -> int:
        self.top += 1
        return self.top


def atmost_core(state: State, variables: list[int], bound: int) -> None:
    if not (0 < bound and bound + 1 < len(variables)):
        return
    ids: dict[tuple[int, int], int] = {}

    def y(key: tuple[int, int]) -> int:
        if key not in ids:
            ids[key] = state.fresh()
        return ids[key]

    for j in range(len(variables) - bound):
        s0j = y((0, j))
        state.clauses.append([-variables[j], s0j])
        for k in range(bound - 1):
            skj = y((k, j))
            if j < len(variables) - bound - 1:
                state.clauses.append([-skj, y((k, j + 1))])
            state.clauses.append([-variables[j + k + 1], -skj, y((k + 1, j))])
        stj = y((bound - 1, j))
        if j < len(variables) - bound - 1:
            state.clauses.append([-stj, y((bound - 1, j + 1))])
        state.clauses.append([-variables[j + bound], -stj])


def atmost(state: State, variables: list[int], bound: int) -> None:
    if bound == 0:
        state.clauses.extend([[-v] for v in variables])
    elif bound + 1 == len(variables):
        state.clauses.append([-v for v in variables])
    else:
        atmost_core(state, variables, bound)


def equals(state: State, variables: list[int], bound: int) -> None:
    atmost(state, [-v for v in variables], len(variables) - bound)
    atmost(state, variables, bound)


def build(record: dict) -> State:
    h_edges = {tuple(edge) for edge in record["H"]}
    cells = [tuple(cell) for cell in record["cells"]]
    assert len(cells) == 48 and len(set(cells)) == 48
    index = {cell: i for i, cell in enumerate(cells)}
    pairs = [(u, v) for u in range(48) for v in range(u + 1, 48)]
    edge_ids = {pair: i + 1 for i, pair in enumerate(pairs)}

    def edge(u: int, v: int) -> int:
        return edge_ids[(u, v) if u < v else (v, u)]

    state = State(top=len(edge_ids))
    for u, (xu, yu) in enumerate(cells):
        for x in range(ORDER):
            variables = [edge(u, index[cell]) for cell in cells
                         if cell[0] == x and index[cell] != u]
            equals(state, variables, 0 if (x, yu) in h_edges else 1)
        for y in range(ORDER):
            variables = [edge(u, index[cell]) for cell in cells
                         if cell[1] == y and index[cell] != u]
            equals(state, variables, 0 if (xu, y) in h_edges else 1)

    for u in range(48):
        for v in range(u + 1, 48):
            common: list[int] = []
            for m in range(48):
                if m in (u, v):
                    continue
                aux = state.fresh()
                eum, evm = edge(u, m), edge(v, m)
                state.clauses.extend(([-aux, eum], [-aux, evm], [-eum, -evm, aux]))
                common.append(aux)
            atmost(state, common, 1)
    return state


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("manifest", type=Path)
    parser.add_argument("index", type=int)
    parser.add_argument("output", type=Path)
    args = parser.parse_args()
    records = json.loads(args.manifest.read_text())
    record = records[args.index]
    state = build(record)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    with args.output.open("w", encoding="ascii", newline="\n") as stream:
        stream.write(f"c fixedK index={args.index} shape={record['shape']} sector={record['sector']}\n")
        stream.write(f"p cnf {state.top} {len(state.clauses)}\n")
        for clause in state.clauses:
            stream.write(" ".join(map(str, clause)) + " 0\n")
    print(f"index={args.index} variables={state.top} clauses={len(state.clauses)} output={args.output}")


if __name__ == "__main__":
    main()
