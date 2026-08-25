#!/usr/bin/env python3
"""Even-q falsifier for the faithful P15 fractional-cover abstraction.

For root triangle count r with 0 < r < q/2, the collinearity layer has q
cells of size q-1.  A negative perfect sink can be labelled only by one of
the q-2 nonsource points in each of the 2r triangle-supported cells, or by
one of the 2r-1 points in R outside the collinearity layer.  We quantify over
all transversal blocks, impose loopless symmetric labelled incidence,
pairwise intersection at most one, and solve for a positive rational exact
cover.  A model with more than q-1 blocks refutes abstract integrality.
"""

import argparse

from z3 import And, If, Int, Or, Real, Solver, Sum, sat


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--q", type=int, required=True)
    parser.add_argument("--triangles", type=int, required=True)
    parser.add_argument("--blocks", type=int, required=True)
    parser.add_argument("--timeout-ms", type=int, default=300_000)
    args = parser.parse_args()
    q, r, m = args.q, args.triangles, args.blocks
    if q < 4 or q % 2 or not 0 < r < q // 2:
        parser.error("require even q >= 4 and 0 < triangles < q/2")
    if m <= q - 1:
        parser.error("a fractional support must have more than q-1 blocks")

    cell_size = q - 1
    cell_points = q * cell_size
    point_count = q * q

    def point(cell: int, value) -> object:
        return cell_size * cell + value

    # Value zero in each supported cell is its unique partner-source label;
    # values 1,...,q-2 are the R-points eligible to label perfect sinks.
    allowed_labels = {
        int(point(cell, value))
        for cell in range(2 * r) for value in range(1, cell_size)
    }
    # The first 2r-1 points outside C_y represent R\C_y.  The other outside
    # points are y and unsupported sources.
    allowed_labels.update(range(cell_points, cell_points + 2 * r - 1))
    assert len(allowed_labels) == 2 * r * (q - 1) - 1
    if m > len(allowed_labels):
        print(f"q={q} r={r} blocks={m} result=unsat (label count)")
        return

    solver = Solver()
    solver.set(timeout=args.timeout_ms)
    labels = [Int(f"label_{i}") for i in range(m)]
    choices = [[Int(f"choice_{i}_{cell}") for cell in range(q)] for i in range(m)]
    weights = [Real(f"weight_{i}") for i in range(m)]
    # Block indices carry no data.  Increasing labels removes the full m!
    # permutation symmetry while still representing every unlabelled model.
    for i in range(m - 1):
        solver.add(labels[i] < labels[i + 1])
    for i in range(m):
        solver.add(Or([labels[i] == value for value in sorted(allowed_labels)]))
        solver.add(And(weights[i] > 0, weights[i] <= 1))
        for cell in range(q):
            solver.add(And(choices[i][cell] >= 0, choices[i][cell] < cell_size))
        solver.add(And([
            labels[i] != point(cell, choices[i][cell]) for cell in range(q)
        ]))

    def incident(label, block_index: int):
        return Or([
            label == point(cell, choices[block_index][cell]) for cell in range(q)
        ])

    for i in range(m):
        for j in range(i + 1, m):
            solver.add(incident(labels[i], j) == incident(labels[j], i))
            solver.add(Sum([
                If(choices[i][cell] == choices[j][cell], 1, 0)
                for cell in range(q)
            ]) <= 1)
    for cell in range(q):
        for value in range(cell_size):
            solver.add(Sum([
                If(choices[i][cell] == value, weights[i], 0) for i in range(m)
            ]) == 1)

    result = solver.check()
    print(f"q={q} r={r} blocks={m} result={result}")
    if result != sat:
        return
    model = solver.model()
    label_values = [model.eval(label).as_long() for label in labels]
    choice_values = [
        [model.eval(choice).as_long() for choice in row] for row in choices
    ]
    weight_values = [model.eval(weight).as_fraction() for weight in weights]
    print("labels =", label_values)
    print("choices =", choice_values)
    print("weights =", weight_values)

    assert len(set(label_values)) == m and set(label_values) <= allowed_labels
    for i in range(m):
        block_i = {int(point(cell, choice_values[i][cell])) for cell in range(q)}
        assert label_values[i] not in block_i
        assert 0 < weight_values[i] <= 1
        for j in range(m):
            block_j = {int(point(cell, choice_values[j][cell])) for cell in range(q)}
            assert (label_values[i] in block_j) == (label_values[j] in block_i)
            if i != j:
                assert len(block_i & block_j) <= 1
    for cell in range(q):
        for value in range(cell_size):
            assert sum(
                weight_values[i]
                for i in range(m) if choice_values[i][cell] == value
            ) == 1
    assert sum(weight_values) == q - 1
    print("verified: faithful-location nonintegral P15 countermodel")


if __name__ == "__main__":
    main()
