#!/usr/bin/env python3
"""Generate the Lean-mirror CNF for an all-tf mu=3 exterior grid.

Unlike the smaller Z3-generated audit CNF, this encoding has a transparent
allocation order intended for direct transcription into Lean:

* the 1128 exterior-edge variables come first in lexicographic pair order;
* row/column exact-cardinality blocks use the repository's sequential counter;
* each common-neighbour conjunction has an explicit fresh variable and three
  defining clauses; and
* each pairwise C4 bound uses the same sequential at-most-one counter.
"""

from __future__ import annotations

import argparse
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
            state.clauses.append(
                [-variables[j + k + 1], -skj, y((k + 1, j))]
            )
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


def atleast(state: State, variables: list[int], bound: int) -> None:
    atmost(state, [-v for v in variables], len(variables) - bound)


def equals(state: State, variables: list[int], bound: int) -> None:
    atleast(state, variables, bound)
    atmost(state, variables, bound)


def internal_neighbours(shape: str) -> dict[int, set[int]]:
    if shape == "C16":
        return {i: {i, (i - 1) % 8} for i in range(8)}
    if shape == "C10C6":
        result = {i: {i, (i - 1) % 5} for i in range(5)}
        result.update({5 + i: {5 + i, 5 + ((i - 1) % 3)} for i in range(3)})
        return result
    if shape == "C8C8":
        result: dict[int, set[int]] = {}
        for i in range(4):
            result[i] = {i, (i - 1) % 4}
            result[4 + i] = {4 + i, 4 + ((i - 1) % 4)}
        return result
    raise ValueError(shape)


def build(shape: str) -> tuple[State, int, int]:
    nhx = internal_neighbours(shape)
    nhy = {j: {i for i in range(ORDER) if j in nhx[i]} for j in range(ORDER)}
    cells = [(x, y) for x in range(ORDER) for y in range(ORDER) if y not in nhx[x]]
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
            equals(state, variables, 0 if yu in nhx[x] else 1)
        for y in range(ORDER):
            variables = [edge(u, index[cell]) for cell in cells
                         if cell[1] == y and index[cell] != u]
            equals(state, variables, 0 if xu in nhy[y] else 1)

    common_variables = 0
    for u in range(48):
        for v in range(u + 1, 48):
            common: list[int] = []
            for m in range(48):
                if m in (u, v):
                    continue
                aux = state.fresh()
                common_variables += 1
                eum, evm = edge(u, m), edge(v, m)
                state.clauses.extend(([-aux, eum], [-aux, evm], [-eum, -evm, aux]))
                common.append(aux)
            atmost(state, common, 1)
    return state, len(edge_ids), common_variables


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("shape", choices=("C16", "C10C6", "C8C8"))
    parser.add_argument("output", type=Path)
    args = parser.parse_args()
    state, edges, common = build(args.shape)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    with args.output.open("w", encoding="ascii", newline="\n") as stream:
        stream.write(f"p cnf {state.top} {len(state.clauses)}\n")
        for clause in state.clauses:
            stream.write(" ".join(map(str, clause)) + " 0\n")
    print(
        f"shape={args.shape} edges={edges} common={common} "
        f"variables={state.top} clauses={len(state.clauses)}"
    )


if __name__ == "__main__":
    main()
