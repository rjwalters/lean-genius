#!/usr/bin/env python3
"""Exact q=4 control for the NONBIP-CONNECTED discriminant-form route.

For the connected nonbipartite cubic circulant D from
q_generic_connected_defect_spectral_countermodel.py, put B=L_D+J.  This
verifier proves that the finite linking pairing on coker(B) is metabolic by
exhibiting a full isotropic subgroup of order sqrt(det(B)).  The companion
verifier proves that B nevertheless has no rational trace-zero square root.
Thus metabolicity is strictly weaker than the incidence square root needed
by A-REG.
"""

from __future__ import annotations

from fractions import Fraction
from math import isqrt

import sympy as sp
from sympy.polys.domains import ZZ
from sympy.polys.matrices import DomainMatrix
from sympy.polys.matrices.normalforms import smith_normal_decomp

from q_generic_connected_defect_spectral_countermodel import circulant_defect


def fractional_part(value: sp.Rational) -> Fraction:
    numerator, denominator = value.as_numer_denom()
    return Fraction(int(numerator) % int(denominator), int(denominator))


def main() -> None:
    q = 4
    n = q * q
    defect = circulant_defect(q)
    corrected = (q - 1) * sp.eye(n) - defect + sp.ones(n)

    domain_matrix = DomainMatrix.from_list(
        [[int(corrected[i, j]) for j in range(n)] for i in range(n)], ZZ
    )
    smith_dm, left_dm, right_dm = smith_normal_decomp(domain_matrix)
    smith = sp.Matrix(smith_dm.to_Matrix())
    left = sp.Matrix(left_dm.to_Matrix())
    right = sp.Matrix(right_dm.to_Matrix())
    assert left * corrected * right == smith
    invariants = [abs(int(smith[i, i])) for i in range(n)]
    assert invariants == [1] * 14 + [1552, 24832]

    determinant = int(corrected.det())
    assert determinant == 38_539_264
    assert isqrt(determinant) == 6208

    left_inverse = left.inv()
    corrected_inverse = corrected.inv()

    def representative(c14: int, c15: int) -> sp.Matrix:
        coordinates = sp.zeros(n, 1)
        coordinates[14] = c14
        coordinates[15] = c15
        return left_inverse * coordinates

    def pairing(x: sp.Matrix, y: sp.Matrix) -> Fraction:
        return fractional_part((x.T * corrected_inverse * y)[0])

    # The 2-primary part is C_16 x C_256.  In its natural generators
    # (97 e_14, 97 e_15), the elements (0,16) and (4,0) generate an
    # isotropic C_16 x C_4 of order 64.
    two_u = representative(0, 16 * 97)
    two_v = representative(4 * 97, 0)
    assert pairing(two_u, two_u) == 0
    assert pairing(two_u, two_v) == 0
    assert pairing(two_v, two_v) == 0

    # The 97-primary part is C_97 x C_97.  Relative to generators
    # (16 e_14, 256 e_15), (1,46) spans an isotropic subgroup of order 97.
    odd_w = representative(16, 46 * 256)
    assert pairing(odd_w, odd_w) == 0

    # Primary parts pair orthogonally.  Their direct sum has order
    # 64*97=sqrt(det B), hence is a Lagrangian for the nondegenerate pairing.
    assert pairing(two_u, odd_w) == 0
    assert pairing(two_v, odd_w) == 0
    assert 16 * 4 * 97 == isqrt(determinant)

    print("verified connected nonbipartite q=4 discriminant control")
    print("SNF(B) = 1^14, 1552, 24832")
    print("Lagrangian order = 16 * 4 * 97 = 6208 = sqrt(det(B))")


if __name__ == "__main__":
    main()
