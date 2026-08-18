#!/usr/bin/env python3
"""Exact defect-factor ledger for every cycle occurring in H16.

For the adjacency characteristic polynomial ``P_r(x)`` of ``C_r``, the
resultant with ``x^2 + y - 7`` is the characteristic polynomial of the
transformed defect eigenvalues ``y = 7 - x^2``.  The asserted factorizations
make the degree-{2,3,5,6} terminal dispatch independently reproducible.
"""

from __future__ import annotations

import sympy as sp


X, Y = sp.symbols("x y")

EXPECTED = {
    3: (Y - 3) * (Y - 6) ** 2,
    5: (Y - 3) * (Y**2 - 11*Y + 29) ** 2,
    6: (Y - 3) ** 2 * (Y - 6) ** 4,
    7: (Y - 3) * (Y**3 - 16*Y**2 + 83*Y - 139) ** 2,
    8: (Y - 3) ** 2 * (Y - 5) ** 4 * (Y - 7) ** 2,
    9: ((Y - 3) * (Y - 6) ** 2
        * (Y**3 - 15*Y**2 + 72*Y - 111) ** 2),
    10: (Y - 3) ** 2 * (Y**2 - 11*Y + 29) ** 4,
    11: ((Y - 3)
         * (Y**5 - 26*Y**4 + 266*Y**3 - 1337*Y**2
            + 3298*Y - 3191) ** 2),
    13: ((Y - 3)
         * (Y**6 - 31*Y**5 + 395*Y**4 - 2646*Y**3
            + 9821*Y**2 - 19138*Y + 15289) ** 2),
    16: ((Y - 3) ** 2 * (Y - 5) ** 4 * (Y - 7) ** 2
         * (Y**2 - 10*Y + 23) ** 4),
}


def cycle_charpoly(order: int) -> sp.Poly:
    adjacency = sp.zeros(order)
    for vertex in range(order):
        adjacency[vertex, (vertex - 1) % order] = 1
        adjacency[vertex, (vertex + 1) % order] = 1
    return sp.Poly(adjacency.charpoly(X).as_expr(), X, domain=sp.ZZ)


def main() -> int:
    nonlinear_degrees: set[int] = set()
    for order, expected in EXPECTED.items():
        transformed = sp.Poly(
            sp.resultant(cycle_charpoly(order).as_expr(), X**2 + Y - 7, X),
            Y, domain=sp.ZZ,
        )
        if transformed != sp.Poly(expected, Y, domain=sp.ZZ):
            raise AssertionError(f"unexpected transformed factorization at C_{order}")
        for factor, _multiplicity in sp.factor_list(transformed.as_expr())[1]:
            degree = sp.degree(factor, Y)
            if degree > 1:
                if not sp.Poly(factor, Y, domain=sp.QQ).is_irreducible:
                    raise AssertionError(f"reducible ledger factor at C_{order}")
                nonlinear_degrees.add(int(degree))
    if nonlinear_degrees != {2, 3, 5, 6}:
        raise AssertionError(f"unexpected nonlinear degrees: {nonlinear_degrees}")
    print(
        f"cycle_orders={len(EXPECTED)} "
        "nonlinear_primary_degrees=2,3,5,6 all_factorizations_verified"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
