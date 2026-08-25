#!/usr/bin/env python3
"""Bounded probe for the NONBIP-CONNECTED Jacobian-pairing route.

If an integral symmetric matrix ``A`` preserves the zero-sum lattice and
``A^2 = L_D`` there, then the image of ``A`` in ``Jac(D)`` is isotropic for
the monodromy pairing.  When ``A`` is nonsingular it has order
``sqrt(|Jac(D)|)``, hence is a metabolizer.  This is stronger than merely
asking that the tree number of ``D`` be a square.

This script checks that the strengthening is genuine but is not a generic
consequence of connected odd regularity:

* ``K4`` has square tree number and metabolic monodromy pairing;
* ``K3,3`` has square tree number and non-metabolic monodromy pairing.

Thus a terminal must use the special defect/incidence structure, not only
the order, odd degree, and square-tree-number consequences already banked.
The instances are deliberately tiny so the quotient and every subgroup are
enumerated exactly, without a solver or floating-point arithmetic.
"""

from fractions import Fraction
from itertools import product
from math import isqrt

import networkx as nx
from sympy import Matrix


Vector = tuple[int, ...]


def reduced_laplacian(graph: nx.Graph) -> Matrix:
    vertices = sorted(graph.nodes())
    laplacian = Matrix(
        nx.laplacian_matrix(graph, nodelist=vertices).toarray().tolist()
    )
    return laplacian[:-1, :-1]


def quotient_representatives(laplacian: Matrix) -> tuple[list[Vector], Matrix]:
    """Enumerate Z^r / L Z^r using exact membership in the column lattice."""
    inverse = laplacian.inv()
    order = abs(int(laplacian.det()))
    rank = laplacian.rows

    def equivalent(left: Vector, right: Vector) -> bool:
        difference = Matrix([left[i] - right[i] for i in range(rank)])
        return all(entry.q == 1 for entry in inverse * difference)

    # The two fixed examples close by side length three.  Keep a defensive
    # bound so a future larger example cannot silently turn this into a grind.
    for side in range(1, 7):
        representatives: list[Vector] = []
        for candidate in product(range(side), repeat=rank):
            if not any(equivalent(candidate, old) for old in representatives):
                representatives.append(candidate)
            if len(representatives) == order:
                return representatives, inverse
    raise AssertionError(f"quotient enumeration exceeded bounded box; order={order}")


def is_metabolic(graph: nx.Graph) -> tuple[int, bool]:
    laplacian = reduced_laplacian(graph)
    order = abs(int(laplacian.det()))
    root = isqrt(order)
    assert root * root == order
    representatives, inverse = quotient_representatives(laplacian)
    rank = laplacian.rows

    def equivalent(left: Vector, right: Vector) -> bool:
        difference = Matrix([left[i] - right[i] for i in range(rank)])
        return all(entry.q == 1 for entry in inverse * difference)

    def normalize(vector: Vector) -> Vector:
        return next(rep for rep in representatives if equivalent(vector, rep))

    def add(left: Vector, right: Vector) -> Vector:
        return normalize(tuple(left[i] + right[i] for i in range(rank)))

    def pairing(left: Vector, right: Vector) -> Fraction:
        value = sum(
            Fraction(left[i])
            * Fraction(int(inverse[i, j].p), int(inverse[i, j].q))
            * right[j]
            for i in range(rank)
            for j in range(rank)
        )
        return value % 1

    zero = (0,) * rank

    def closure(generators: tuple[Vector, ...]) -> frozenset[Vector]:
        subgroup = {zero}
        changed = True
        while changed:
            changed = False
            for element in tuple(subgroup):
                for generator in generators:
                    new = add(element, generator)
                    if new not in subgroup:
                        subgroup.add(new)
                        changed = True
        return frozenset(subgroup)

    isotropic = tuple(rep for rep in representatives if pairing(rep, rep) == 0)
    subgroups = {frozenset({zero})}
    changed = True
    while changed:
        changed = False
        for subgroup in tuple(subgroups):
            for generator in isotropic:
                candidate = closure(tuple(subgroup) + (generator,))
                if len(candidate) > root:
                    continue
                if not all(pairing(x, y) == 0 for x in candidate for y in candidate):
                    continue
                if candidate not in subgroups:
                    subgroups.add(candidate)
                    changed = True
        if any(len(subgroup) == root for subgroup in subgroups):
            return order, True
    return order, False


def main() -> None:
    cases = (
        ("K4", nx.complete_graph(4), 16, True),
        ("K3,3", nx.complete_bipartite_graph(3, 3), 81, False),
    )
    for name, graph, expected_order, expected_metabolic in cases:
        assert nx.is_connected(graph)
        degrees = {degree for _, degree in graph.degree()}
        assert len(degrees) == 1 and next(iter(degrees)) % 2 == 1
        order, metabolic = is_metabolic(graph)
        assert (order, metabolic) == (expected_order, expected_metabolic)
        print(f"{name}: tree_number={order}, metabolic={metabolic}")


if __name__ == "__main__":
    main()
