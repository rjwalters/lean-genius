#!/usr/bin/env python3
"""Exact spectral certificate for the d=12 quotient exception.

For defect-cycle orders (15,60,60), the component-orthogonal relation is

    A^2 = 11 I - D.

This script factors the two cycle resolvents after deleting the constant
cycle direction.  Every rational irreducible factor is even, so every
rational A-invariant factor supported there has zero X^(degree-1)
coefficient, hence zero trace.  The quotient matrix has trace 12, contradicting
the zero trace of a simple-graph adjacency matrix.

SymPy is used only as a reproducible exploratory certificate; the intended
publishable artifact is a Lean proof of the displayed polynomial identities
and the even-factor trace lemma.
"""

import sympy as sp


X, Y = sp.symbols("X Y")


def cycle_resolvent(order):
    cycle_charpoly = sp.expand(2 * (sp.chebyshevt(order, X / 2) - 1))
    # Divide out the constant eigenvalue X=2, then substitute X=11-Y^2.
    return sp.Poly(
        sp.cancel(cycle_charpoly.subs(X, 11 - Y**2) / (9 - Y**2)),
        Y,
        domain=sp.QQ,
    )


def checked_factorization(order):
    resolvent = cycle_resolvent(order)
    coefficient, factors = sp.factor_list(resolvent.as_expr())
    reconstructed = sp.Poly(coefficient, Y, domain=sp.QQ)
    for factor, exponent in factors:
        polynomial = sp.Poly(factor, Y, domain=sp.QQ)
        assert polynomial.is_irreducible
        assert polynomial.as_expr().subs(Y, -Y) == polynomial.as_expr()
        reconstructed *= polynomial**exponent
    assert reconstructed == resolvent
    return coefficient, factors


def main():
    quotient = sp.Matrix([[4, 4, 4], [1, 4, 7], [1, 7, 4]])
    assert quotient.charpoly(Y).as_expr().factor() == (Y - 12) * (Y - 3) * (Y + 3)
    assert quotient.trace() == 12
    for order in (15, 60):
        coefficient, factors = checked_factorization(order)
        print(f"C_{order} coefficient {coefficient}")
        for factor, exponent in factors:
            print(f"  ({factor})^{exponent}")
    print("quotient charpoly", quotient.charpoly(Y).as_expr().factor())
    print("quotient trace", quotient.trace())
    print("component-orthogonal rational trace forced to 0")
    print("full adjacency trace would be 12: contradiction")


if __name__ == "__main__":
    main()
