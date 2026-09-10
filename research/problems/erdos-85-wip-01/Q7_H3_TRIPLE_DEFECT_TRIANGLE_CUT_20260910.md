# Fixed psi3: exclude the secondary two-edge case

For the fixed residual polynomial psi3 of the reviewed higher local-moment note, the triple-support vertex z satisfies delta_z<=1 whenever its local mixed overlap (CD²)zz=2. Here delta_z is the number of defect triangles through z. Combined with the universal secondary ledger, this excludes e(C[R8])=2 for this polynomial; only3 or4 edges remain. It does not exclude the polynomial or the whole H3 triple profile.

The secondary ledger in `Q7_H3_TRIPLE_SECONDARY_LEDGER_20260910.md` proves2<=e(R8)<=4 and shows that the two-edge case forces (CD²)zz=2 and delta_z>=2. That graph argument is a separate prerequisite. This note supplies the incompatible spectrum-specific upper bound.

At z, support t=3 and low triangle incidence tau=0. Use the exact residual diagonal moment targets r0,...,r6 from `Q7_H3_LOCAL_GALOIS_MEASURES_20260910.md`, with R=2 and variable delta. Define

    p(x)=-814049641/3590000 +(1206/359)x +(93867/718)x²
         -(8375/359)x⁴ -(67/718)x⁵ +(469/359)x⁶.

The standalone SymPy verifier `verify_q7_h3_triple_defect_triangle_cut.py` evaluates p at every exact residual root and checks that it is nonnegative. Spectral diagonal weights are nonnegative, so sum_j p_j r_j>=0. Exact substitution yields

    0 <= 508202539/120265000 -(938/359)delta,
    delta <= 508202539/314230000 < 2.

Since delta is an integer, delta<=1. This contradicts the lower bound2 in the secondary two-edge case.

The verifier uses exact rational/algebraic arithmetic, with no optimizer. Numerical dual discovery was followed by rational reconstruction and exact root-sign checks; numerical infeasibility is not evidence here. The imports identify the fixed polynomial and recompute the local targets. The proof has not been formalized as a Lean graph theorem. No conclusion about other residual polynomials is asserted.
