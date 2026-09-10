# H3 triple profile: secondary empty-support partition

In the universal H3 triple profile, the24 empty-support vertices split into a distinguished vertex u, three sets U1,U2,U3 of size5, and a set R of size8. The induced graph C[R] has **between2 and4 edges**. The argument uses the q7 block identities and C4-freeness, with no residual spectrum assumption. It gives necessary constraints, not a profile exclusion.

## Forced partition

Let z be the unique triple-support vertex. By the reviewed H3 support ledger, its four low neighbors are u (empty support) and three single-support vertices s1,s2,s3. Each si has five empty neighbors and no other low neighbors besides z. Write Ui for those five empty neighbors.

The Ui are pairwise disjoint: si,sj already have common neighbor z, so a shared empty neighbor would form a C4. Also u has no neighbor in any Ui: u and si already share z. Thus E, the set of24 empties, is the disjoint union {u}, U=U1 union U2 union U3, and R of size8. The six empty neighbors N of u all lie in R. Write T=R minus N, so |T|=2.

Every empty vertex other than u has degree4 in C[E], while u has degree6. Every empty vertex has at most one neighbor in each Ui, since two would be common neighbors with si. Therefore C[Ui] is a matching with at most2 edges, and there are at most5 edges between each pair Ui,Uj. Consequently

    e(U)<=3*2+3*5=21.

Let r=e(R) and q=e(U,R). Degree sums over R and U give

    32=6+2r+q,    60=2e(U)+q,
    q=26-2r,     e(U)=17+r.

Thus r<=4. The at-most-three U-neighbors of each R vertex also gives q<=24 and the preliminary r>=1.

## Sharper lower bound and small parameters

C4-freeness makes C[N] a matching. Write m=e(N), with0<=m<=3. Each vertex in N has three further empty neighbors besides u. These18 length-two endpoints are pairwise distinct, since a repeated endpoint from two different N vertices would form a C4 through u. If m=0, all18 endpoints would lie in U union T, a set of17 vertices. Hence **1<=m<=3**.

For T={v1,v2}, put epsilon=1 if v1,v2 are adjacent and0 otherwise, and let ki count neighbors of vi in N. Again C4-freeness through u gives ki in {0,1}. Since vi has four empty neighbors and at most three in U,

    ki+epsilon>=1.

All edges of R are accounted for by

    r=m+k1+k2+epsilon.

If epsilon=0 then k1=k2=1, giving r>=3. If epsilon=1 then m>=1 gives r>=2. Combined with the upper bound, **2<=r<=4**. The boundary r=2 forces m=1, epsilon=1 and k1=k2=0.

## Exact defect neighborhood of z

For an empty vertex v, the C-common-neighbor count with z is

    (C²)zv=indicator(v in N)+indicator(v in U).

Indeed N_C(z)={u,s1,s2,s3}, and these supports are disjoint on E. The defect identity D=J+6I-B^T B-C² therefore gives

    N_D(z)={u,v1,v2}.

There are no other D-neighbors, since D has degree3 at z and Dt=0 there. Within this set, u has no C-edge to vi, and the only possible C-edge is v1-v2. Consequently

    (CD²)zz=2epsilon.

Here one can use CD=DC to rewrite CD²=DCD, the directed C-edge count inside the D-neighborhood. Also D_uvi=1-ki: u has C-neighbors z and N, and vi has exactly ki neighbors in N. Hence if delta_z counts D-triangles through z,

    delta_z>=2-k1-k2.

In particular r=2 forces delta_z>=2. This is a universal conditional statement; it is not itself a contradiction. Applying a spectrum-specific upper bound on delta_z would require a separately verified bound.

## Verification and limits

`verify_q7_h3_triple_secondary_ledger.py` checks the rational/integer degree ledger and finite scalar implications, including the r=2 boundary. The graph-to-partition and C4 arguments above are paper derivations, not Lean theorems supplied by that verifier. No realizability of the scalar parameter cases is asserted. The Ui-pair capacities, matching condition, and defect neighborhood are necessary even though further C4 restrictions may eliminate more parameter cases.
