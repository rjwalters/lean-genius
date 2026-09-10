# Two H3 local cuts from seventh-walk parity

For the fixed residual polynomial psi3 in `Q7_H3_LOCAL_GALOIS_MEASURES_20260910.md`, the local types (t,tau,R,delta)=(1,1,2,1) and (1,2,2,0) are impossible in an actual graph. This excludes two local types, not either complete H3 profile or the polynomial.

The exact verifier `verify_q7_h3_seventh_local_cuts.py` uses the roots, quotient matrix, Gram inverse and local moment targets of that note. Its JSON contains rational dual coefficients; no optimizer is required. Run it with Python and SymPy from this directory.

For each type let r0,...,r6 be its residual diagonal moments and q7 its quotient seventh moment. For each sign epsilon=+1,-1 the certificate gives rational y0,...,y6 such that

    epsilon lambda^7 - sum(j=0..6) yj lambda^j >= 0

at every residual eigenvalue lambda. The verifier checks each algebraic sign exactly. Because spectral diagonal weights are nonnegative, epsilon*r7 >= sum yj*rj. Consequently the two certificates bound the full diagonal q7+r7. The zero-C sector contributes zero to this moment.

The resulting exact rational bounds lie strictly inside these intervals:

| Local type (t,tau,R,delta) | Full seventh diagonal interval |
| --- | --- |
| (1,1,2,1) | 9012 < (C^7)vv < 9014 |
| (1,2,2,0) | 9240 < (C^7)vv < 9242 |

For a symmetric integer zero-diagonal matrix C, every odd diagonal power is even: (C^(2j+1))vv equals a^T C a with a=C^j e_v, and the off-diagonal terms pair. Thus neither displayed open interval can contain the required diagonal.

Discovery used numerical LP duals followed by rational approximation and a conservative constant adjustment. Only the exact final sign and interval checks support the cuts. The bounds are approximately (9012.22147,9013.29056) and (9240.22147,9241.29056); these decimals are explanatory, not proof data.

A subsequent numerical allocation over 154 locally feasible even-C7 refinements of the remaining types was feasible for both H3 profiles. This is a diagnostic, not an exact realization certificate. Earlier infeasibility for degree-eight tests with fixed degree-six group counts therefore gives no global exclusion. No exhaustive claim about other residual polynomials is made.
