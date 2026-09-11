# Deficiency identities in the remaining N80/F2 case

Use accepted2219. Write u,v for the two fixed vertices, A=N_G(u), B=N_G(v), and R for the60 residual vertices. Both attached sets have9 vertices, comprising an isolated3-orbit I_A or I_B and two3-orbits joined by an internal perfect matching. The A--B cross matching has m=6or9 edges. Let M be the80-by80 adjacency matrix.

Define E=8I+J-M^2. Since G is9regular and C4-free, E is the adjacency matrix of the graph joining distinct vertices with no common G-neighbor. Its degree is8+80-81=7. Also ME=EM, because M commutes with both I and J.

## Exact deficiency neighborhoods of u and v

There is no common G-neighbor of u and v: any unique common neighbor would be fixed by the order-three action, but the only fixed vertices are u,v and neither can be its own neighbor. Thus E_uv=1.

For x in A, the common G-neighbors of u,x are exactly the internal neighbors of x in A. Consequently x is an E-neighbor of u precisely when x belongs to I_A. For x in B or R, it is an E-neighbor of u precisely when it has no G-neighbor in A. The analogous assertions hold with u,A and v,B exchanged.

If m=6, let U_A and U_B be the unmatched3-orbits of the cross matching, each contained in its indicated attached set. Equality in2219 ensures every R vertex meets both A and B. Therefore

    N_E(u) = {v} disjoint-union I_A disjoint-union U_B,
    N_E(v) = {u} disjoint-union I_B disjoint-union U_A.

If m=9, let Z_A and Z_B be the residual3-orbits missing an A or B neighbor. Then

    N_E(u) = {v} disjoint-union I_A disjoint-union Z_A,
    N_E(v) = {u} disjoint-union I_B disjoint-union Z_B.

These formulas account for all seven deficiency neighbors. Also E has no edges within A or within B, since each pair in A already shares u, and each pair in B shares v.

## Deficiency edges between the attached sets

For x in B, commutation at entry(u,x) gives

    |N_E(x) intersect A| = 1 + |N_G(x) intersect I_A|
                              + |N_G(x) intersect T_A|,

where T_A=U_B in the six-edge case and T_A=Z_A in the nine-edge case. The term1 is the G-edge x--v. This is an exact pointwise equality; a symmetric equality holds for x in A.

For m=6 set epsilon_A=0 if U_A=I_A, otherwise1, and similarly epsilon_B. The I_A--B matching has3*epsilon_A edges. The internal degree sum on U_B is3*epsilon_B. Summing the displayed equality over x in B gives

    e_E(A,B) = 9 + 3*epsilon_A + 3*epsilon_B.

For m=9 the I_A--B matching has3 edges. Every vertex in Z_A has a B neighbor unless it also belongs to Z_B, hence e_G(Z_A,B)=3-|Z_A intersect Z_B|. Therefore

    e_E(A,B) = 15 - |Z_A intersect Z_B|,

which is12 for identical missing orbits and15 for disjoint missing orbits. These are counts of actual deficiency edges, not merely quotient weights.

## An explicit pair of integer eigenvalues in one six-edge case

Suppose m=6 and U_A=I_A, U_B=I_B. The pointwise formula then gives exactly one E-neighbor in A for every B vertex, and conversely, so E[A,B] is a perfect matching. More particularly, u and v are adjacent vertices with identical deficiency neighbors outside their pair:

    N_E(u) minus {v} = I_A union I_B = N_E(v) minus {u}.

Let f=e_u-e_v and g=1_A-1_B=Mf. Then Ef=-f and Jf=0. From M^2=8I+J-E we obtain M^2 f=9f. Thus

    M(g+3f)=3(g+3f),
    M(g-3f)=-3(g-3f).

Both vectors are nonzero, because f and g have disjoint nonempty supports. Hence the adjacency matrix has eigenvalues3 and-3, with explicit integer eigenvectors. No claim is made that these eigenvalues are impossible.

This is additional necessary structure for the N80/F2 order-three case. It performs no graph enumeration or solver run and excludes neither the six-edge nor nine-edge case. The deficiency graph need not be C4-free; no such assumption is used.
