# H3 higher local moment witnesses

Both H3 support profiles admit exact rational/Galois-compatible local spectral measures with integral pure-C diagonal moments through degree12, adjacency parity through12, and nonnegative integral mixed C^i D^j diagonals for i+2j<=12. The global multiplicities, support census and totals T=29, R=274, defect triangles=6 match the fixed psi3 in the reviewed degree-six note `Q7_H3_LOCAL_GALOIS_MEASURES_20260910.md`.

This strengthens that local relaxation control. It does not construct a graph, common projectors or an integral symmetric matrix. The two separately certified seventh-moment local cuts remain valid; the new allocations avoid those types.

## Exact verification

Run `python3 verify_q7_h3_higher_local_moments.py` with SymPy. The JSON stores positive integer group counts and **per-vertex** rational spectral coordinates, unlike the aggregate coordinates in the earlier degree-six JSON. Each quadratic pair uses increasing roots and weights u-v sqrt(d), u+v sqrt(d); positivity is checked exactly. Group counts multiply these weights only when computing global totals.

The verifier imports the reviewed polynomial, quotient and degree-six targets. It recomputes residual moments0..12 from the stored rational coordinates. It checks the local type constraints, all initial targets, support censuses (25,18,3,0)/(24,21,0,1), totals (sum tau,sum R,sum delta)=(87,274,18), and each global eigenvalue multiplicity.

For local row a=[1,t], Gram inverse G^-1 and quotient Q from that note, the mixed diagonal is computed as

    sum_lambda w_lambda lambda^i (6-lambda²)^j
      + a Q^i (Q-I)^j G^-1 a^T
      + indicator(i=0) z (-1)^j,
    z=t(3-t)/21.

Every such value with i+2j<=12 is checked to be a nonnegative integer. When i,j have opposite parity the value is also even: after grouping the even powers it is an integer quadratic form in an odd power of one symmetric zero-diagonal matrix. The verifier separately checks pure-C even-power parity (C^(2k))vv = (C^k 1)v mod2. It also checks the simple-D fourth-walk baseline D4>=63-16t+t², obtained from d_D=6-t and Dt=3-t.

## All-degree pure-C integrality

Let f be the product of the six **distinct** residual factors, of total degree10. The full support of each local C measure is annihilated by

    P(x)=x(x²-7x+3)f(x),

a monic integer polynomial of degree13. The verifier checks its degree, integer coefficients, and vanishing on all residual and fixed sectors. Hence each local moment sequence obeys the associated integer recurrence. Since moments0..12 are integers, all subsequent pure-C moments are integers as well. This does not by itself prove all-degree positivity or parity, and those are not claimed beyond the verified range.

## Discovery scope

Numerical interval enumeration of even seventh and parity-constrained eighth and ninth moments produced940 local candidates through12. Exact rational reconstruction of each candidate's ten residual coordinates verified its complete moment targets and positivity. Enforcing mixed nonnegativity removed52 candidates with negative D5, leaving888. A bounded integer census search then selected groups for each profile; exact rational substitution verified the retained integer allocations.

Only the retained certificates support the compatibility claim. Numerical enumeration is not claimed exhaustive or used to reject a whole polynomial/profile. Higher mixed moments, common off-diagonal projector entries, orthogonality, rank constraints, lattice realization and 0/1 adjacency conditions remain open.
