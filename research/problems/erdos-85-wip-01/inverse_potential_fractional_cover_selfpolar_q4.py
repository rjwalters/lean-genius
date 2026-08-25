#!/usr/bin/env python3
"""Test self-polar labels on the nonintegral q=4 transversal cover.

The twelve cell points are P^1(F_3) x F_3 and the nine blocks are graphs of
the projective affine functions (a,b).  Four extra points model labels lying
outside the collinearity layer.  We ask for distinct loopless point labels
for all nine blocks such that incidence is symmetric between labelled
blocks.  This deliberately tests only the label-placement abstraction, not
completion to a 4-regular C4-free graph on sixteen vertices.
"""

import argparse

from z3 import And, Distinct, Int, Or, Solver, sat


Q = 4
FIELD = range(3)
BLOCK_KEYS = [(a, b) for a in FIELD for b in FIELD]


def point(cell: int, value: int) -> int:
    return 3 * cell + value


def block(a: int, b: int) -> set[int]:
    # Cells 0,1,2 are finite t; cell 3 is infinity.
    return {point(t, (a * t + b) % 3) for t in FIELD} | {point(3, a)}


BLOCKS = [block(a, b) for a, b in BLOCK_KEYS]
def member(label, points: set[int]):
    return Or([label == value for value in sorted(points)])


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--extra-points", type=int, default=4)
    args = parser.parse_args()
    if args.extra_points < 0:
        parser.error("extra-points must be nonnegative")
    point_count = 12 + args.extra_points

    assert all(len(points) == Q for points in BLOCKS)
    assert all(
        len(BLOCKS[i] & BLOCKS[j]) == 1
        for i in range(9) for j in range(i + 1, 9)
    )
    assert all(sum(value in points for points in BLOCKS) == 3 for value in range(12))

    labels = [Int(f"label_{index}") for index in range(9)]
    solver = Solver()
    solver.add(Distinct(labels))
    for index, label in enumerate(labels):
        solver.add(And(label >= 0, label < point_count))
        solver.add(~member(label, BLOCKS[index]))  # looplessness
    for i in range(9):
        for j in range(i + 1, 9):
            solver.add(member(labels[i], BLOCKS[j]) == member(labels[j], BLOCKS[i]))

    result = solver.check()
    print(f"extra_points={args.extra_points} result={result}")
    if result != sat:
        return
    model = solver.model()
    values = [model.eval(label).as_long() for label in labels]
    print("labels:", values)
    for i in range(9):
        assert values[i] not in BLOCKS[i]
        for j in range(9):
            assert (values[i] in BLOCKS[j]) == (values[j] in BLOCKS[i])
    print("verified: distinct loopless labels and symmetric labelled incidence")


if __name__ == "__main__":
    main()
