#!/usr/bin/env python3
"""Audit whether the Fin16 [6,2] calibration admits an exterior block.

This is an experimental boundary checker, not a proof artifact.  The small
component has internal graph H with cyclic steps ±2 and exterior-pair graph R
with steps ±5, ±6, ±7.  The 48 exterior vertices are identified with E(R).

We ask for a simple 6-regular graph C on E(R) satisfying the exact cross-block
equation H B + B C = J, where B is the unsigned vertex-edge incidence matrix
of R.  That system is satisfiable.  Adding the remaining C4-free condition on
pairs of exterior vertices makes it unsatisfiable.

Requires the Python `z3-solver` package.
"""

from z3 import And, Bool, PbEq, PbLe, Solver, sat, unsat


ORDER = 16


def cyclic_step(a: int, b: int) -> int:
    return (b - a) % ORDER


def internal_adj(a: int, b: int) -> bool:
    return cyclic_step(a, b) in (2, 14)


def exterior_pair_adj(a: int, b: int) -> bool:
    return cyclic_step(a, b) in (5, 6, 7, 9, 10, 11)


EXTERIOR = [
    (a, b)
    for a in range(ORDER)
    for b in range(a + 1, ORDER)
    if exterior_pair_adj(a, b)
]


def make_solver(require_c4_free: bool) -> Solver:
    count = len(EXTERIOR)
    variables = {
        (i, j): Bool(f"c_{i}_{j}")
        for i in range(count)
        for j in range(i + 1, count)
    }

    def edge(i: int, j: int):
        assert i != j
        return variables[(i, j) if i < j else (j, i)]

    solver = Solver()

    # Every exterior vertex has six exterior neighbors.
    for i in range(count):
        solver.add(PbEq([(edge(i, j), 1) for j in range(count) if j != i], 6))

    # Pointwise HB + BC = J.  An exterior label is an edge of R, so B(u,e)
    # records incidence.  The sum over C-neighbors incident with u must be
    # one minus the number of H-neighbors of u among the endpoints of e.
    for u in range(ORDER):
        for i, endpoints in enumerate(EXTERIOR):
            through_h = sum(internal_adj(u, a) for a in endpoints)
            assert through_h <= 1
            incident_neighbors = [
                j
                for j, other in enumerate(EXTERIOR)
                if j != i and u in other
            ]
            solver.add(
                PbEq(
                    [(edge(i, j), 1) for j in incident_neighbors],
                    1 - through_h,
                )
            )

    if require_c4_free:
        # Two exterior vertices already have one common small neighbor exactly
        # when their R-edges intersect.  Their number of common C-neighbors is
        # therefore at most one minus that intersection indicator.
        for i in range(count):
            for j in range(i + 1, count):
                common_small = len(set(EXTERIOR[i]) & set(EXTERIOR[j]))
                common_exterior = [
                    And(edge(i, k), edge(j, k))
                    for k in range(count)
                    if k not in (i, j)
                ]
                solver.add(
                    PbLe([(term, 1) for term in common_exterior], 1 - common_small)
                )

    return solver


def main() -> None:
    assert len(EXTERIOR) == 48
    base = make_solver(require_c4_free=False).check()
    full = make_solver(require_c4_free=True).check()
    print(f"exterior vertices: {len(EXTERIOR)}")
    print(f"degree + HB+BC=J: {base}")
    print(f"degree + HB+BC=J + C4-free: {full}")
    assert base == sat
    assert full == unsat


if __name__ == "__main__":
    main()
