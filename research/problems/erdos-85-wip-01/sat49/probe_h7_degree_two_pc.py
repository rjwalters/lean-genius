#!/usr/bin/env python3
"""Probe the degree-two polynomial-calculus relaxation of one H7 parent.

The calculation is over GF(2) in the squarefree Boolean quotient.  It includes
the parity reduction of every exact degree equation and all its variable
multiples, every quadratic C4 monomial, and every empty-mask unit together
with all its variable multiples.  Quartic C4 monomials first enter at degree
four and are deliberately outside this bounded probe.
"""

from __future__ import annotations

import argparse
import collections
import time

import z3

import check_h7_t0_pseudo_boolean as pseudo_boolean


Monomial = tuple[int, int]


class SparseGF2Eliminator:
    """Incremental exact elimination; column zero stores the affine constant."""

    def __init__(self) -> None:
        self.pivots: dict[int, set[int]] = {}
        self.inconsistent = False
        self.maximum_pivot_width = 0

    def add(self, columns: set[int], rhs: bool = False) -> None:
        if self.inconsistent:
            return
        row = set(columns)
        if rhs:
            row.add(0)
        while row and max(row) != 0:
            leading = max(row)
            pivot = self.pivots.get(leading)
            if pivot is None:
                self.pivots[leading] = row
                self.maximum_pivot_width = max(self.maximum_pivot_width, len(row))
                return
            row.symmetric_difference_update(pivot)
        if row == {0}:
            self.inconsistent = True


def toggle(items: set[Monomial], item: Monomial) -> None:
    if item in items:
        items.remove(item)
    else:
        items.add(item)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--edge-count", type=int, choices=range(6, 10), default=6)
    parser.add_argument("--type-index", type=int, default=2)
    parser.add_argument("--seconds", type=int, default=60)
    parser.add_argument("--backend", choices=("sparse", "z3"), default="sparse")
    args = parser.parse_args()

    started = time.monotonic()
    parent, _, _ = pseudo_boolean.build_parent(args.edge_count, args.type_index)
    degree = parent.constraints[:42]
    c4 = parent.constraints[42:-21]
    units = parent.constraints[-21:]
    histogram = collections.Counter(len(terms) for terms, _, _ in c4)

    variables: dict[Monomial, z3.BoolRef] = {}

    def variable(monomial: Monomial) -> z3.BoolRef:
        if monomial not in variables:
            left, right = monomial
            name = f"x{left}" if left == right else f"y{left}_{right}"
            variables[monomial] = z3.Bool(name)
        return variables[monomial]

    solver = z3.Solver()
    solver.set(timeout=args.seconds * 1000)
    equation_count = 0
    eliminator = SparseGF2Eliminator()

    def column(monomial: Monomial) -> int:
        left, right = monomial
        assert 1 <= left <= right <= parent.variable_count
        return right * (right - 1) // 2 + left

    def add_equation(monomials: set[Monomial], rhs: bool = False) -> None:
        nonlocal equation_count
        equation_count += 1
        if args.backend == "sparse":
            eliminator.add({column(monomial) for monomial in monomials}, rhs)
            return
        expressions = [variable(monomial) for monomial in sorted(monomials)]
        if not expressions:
            solver.add(z3.BoolVal(not rhs))
        elif len(expressions) == 1:
            solver.add(expressions[0] == rhs)
        else:
            parity = z3.Xor(expressions[0], expressions[1])
            for expression in expressions[2:]:
                parity = z3.Xor(parity, expression)
            solver.add(parity == rhs)

    # Linear degree parities and all degree-one multiples.
    for terms, operator, rhs in degree:
        assert operator == "=" and all(coefficient == 1 for coefficient, _ in terms)
        incident = [index for _, index in terms]
        add_equation({(index, index) for index in incident}, bool(rhs & 1))
        for multiplier in range(1, parent.variable_count + 1):
            row: set[Monomial] = set()
            for index in incident:
                toggle(row, tuple(sorted((index, multiplier))))
            if rhs & 1:
                toggle(row, (multiplier, multiplier))
            add_equation(row)

    # A two-literal all-negative C4 clause is exactly x_i*x_j = 0.
    quadratic_count = 0
    for terms, operator, rhs in c4:
        if len(terms) != 2:
            continue
        assert operator == ">=" and rhs == -1
        assert all(coefficient == -1 for coefficient, _ in terms)
        indices = [index for _, index in terms]
        add_equation({tuple(sorted(indices))})
        quadratic_count += 1

    # Decode each mask unit, then include it and all its variable multiples.
    for terms, operator, rhs in units:
        assert operator == ">=" and len(terms) == 1
        coefficient, index = terms[0]
        value = coefficient == 1
        assert (coefficient, rhs) in ((1, 1), (-1, 0))
        add_equation({(index, index)}, value)
        for multiplier in range(1, parent.variable_count + 1):
            row = {tuple(sorted((index, multiplier)))}
            if value:
                toggle(row, (multiplier, multiplier))
            add_equation(row)

    built = time.monotonic()
    verdict = (
        z3.unsat if eliminator.inconsistent else z3.sat
    ) if args.backend == "sparse" else solver.check()
    finished = time.monotonic()
    print(f"F={args.edge_count}")
    print(f"type_index={args.type_index}")
    print(f"c4_degree_histogram={dict(sorted(histogram.items()))}")
    print(f"quadratic_c4_equations={quadratic_count}")
    print(f"macaulay_variables={parent.variable_count * (parent.variable_count + 1) // 2}")
    print(f"macaulay_equations={equation_count}")
    if args.backend == "sparse":
        print(f"macaulay_rank={len(eliminator.pivots)}")
        print(f"maximum_pivot_width={eliminator.maximum_pivot_width}")
    print(f"build_seconds={built - started:.3f}")
    print(f"solve_seconds={finished - built:.3f}")
    print(f"verdict={verdict}")
    if verdict == z3.sat and args.backend == "z3":
        model = solver.model()
        true_count = sum(z3.is_true(model.eval(value, model_completion=True)) for value in variables.values())
        print(f"model_true_monomials={true_count}")
    elif verdict == z3.unknown:
        print(f"reason_unknown={solver.reason_unknown()}")


if __name__ == "__main__":
    main()
