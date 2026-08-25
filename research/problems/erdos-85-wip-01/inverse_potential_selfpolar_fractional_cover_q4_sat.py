#!/usr/bin/env python3
"""Search all partial self-polar fractional transversal covers at q=4.

There are four cells of size three (the 12-point collinearity layer) and
four external points, for the exact square-order budget 16.  Each labelled
block is a four-point transversal.  We impose:

* distinct point labels and looplessness;
* symmetric incidence between labelled blocks;
* pairwise block intersection at most one;
* positive rational weights covering every cell point with weight one.

Any model with at least four blocks is nonintegral because every block has
size four, so the total block weight is three.  This remains a relaxation of
the ambient graph: rows for labels outside the selected family are absent.
"""

import argparse

from z3 import And, Distinct, If, Int, Or, Real, Solver, Sum, sat


Q = 4
CELL_SIZE = 3
CELL_POINTS = Q * CELL_SIZE
POINTS = Q * Q


def point(cell: int, value) -> object:
    return CELL_SIZE * cell + value


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--blocks", type=int, required=True)
    parser.add_argument("--timeout-ms", type=int, default=300_000)
    parser.add_argument(
        "--root-stratum",
        action="store_true",
        help="restrict labels to R for the unique deg_T(root)>0 q=4 stratum",
    )
    args = parser.parse_args()
    m = args.blocks
    if not 4 <= m <= 12:
        parser.error("blocks must lie in [4,12]")

    solver = Solver()
    solver.set(timeout=args.timeout_ms)
    labels = [Int(f"label_{i}") for i in range(m)]
    choices = [[Int(f"choice_{i}_{cell}") for cell in range(Q)] for i in range(m)]
    weights = [Real(f"weight_{i}") for i in range(m)]

    solver.add(Distinct(labels))
    # At q=4 and deg_T(y)>0, the root has exactly one triangle.  Up to cell
    # and symbol permutations, cells 0 and 1 belong to the two triangle-
    # supported sources, and points 0 and 3 are those source labels.  A
    # perfect sink p inside C_y must lie in one of these two cells: its unique
    # source neighbor belongs to N(p) subset C_y.  Among the four points
    # outside C_y, only point 12 lies in R (the other three are y and the two
    # unmatched sources).  Hence these are exactly the possible labels of
    # off-diagonal negative perfect sinks.
    allowed_root_labels = {1, 2, 4, 5, 12}
    for i in range(m):
        solver.add(And(labels[i] >= 0, labels[i] < POINTS))
        if args.root_stratum:
            solver.add(Or([labels[i] == value for value in allowed_root_labels]))
        solver.add(And(weights[i] > 0, weights[i] <= 1))
        for cell in range(Q):
            solver.add(And(choices[i][cell] >= 0, choices[i][cell] < CELL_SIZE))
        solver.add(And([
            labels[i] != point(cell, choices[i][cell]) for cell in range(Q)
        ]))

    def incident(label, block_index: int):
        return Or([
            label == point(cell, choices[block_index][cell]) for cell in range(Q)
        ])

    for i in range(m):
        for j in range(i + 1, m):
            solver.add(incident(labels[i], j) == incident(labels[j], i))
            solver.add(Sum([
                If(choices[i][cell] == choices[j][cell], 1, 0) for cell in range(Q)
            ]) <= 1)

    for cell in range(Q):
        for value in range(CELL_SIZE):
            solver.add(Sum([
                If(choices[i][cell] == value, weights[i], 0) for i in range(m)
            ]) == 1)

    result = solver.check()
    print(f"blocks={m} result={result}")
    if result != sat:
        return
    model = solver.model()
    label_values = [model.eval(label).as_long() for label in labels]
    choice_values = [
        [model.eval(choice).as_long() for choice in row] for row in choices
    ]
    weight_values = [model.eval(weight) for weight in weights]
    print("labels =", label_values)
    print("choices =", choice_values)
    print("weights =", weight_values)

    assert len(set(label_values)) == m
    for i in range(m):
        block_i = {point(cell, choice_values[i][cell]) for cell in range(Q)}
        assert label_values[i] not in block_i
        assert weight_values[i].as_fraction() > 0
        assert weight_values[i].as_fraction() <= 1
        for j in range(m):
            block_j = {point(cell, choice_values[j][cell]) for cell in range(Q)}
            assert (label_values[i] in block_j) == (label_values[j] in block_i)
            if i != j:
                assert len(block_i & block_j) <= 1
    for cell in range(Q):
        for value in range(CELL_SIZE):
            cover = sum(
                weight_values[i].as_fraction()
                for i in range(m) if choice_values[i][cell] == value
            )
            assert cover == 1
    assert sum(value.as_fraction() for value in weight_values) == 3
    assert any(value.as_fraction() != 1 for value in weight_values)
    print("verified: nonintegral partial self-polar exact cover")


if __name__ == "__main__":
    main()
