# Four prescribed H3 eigenvector allocations fail joint neighborhoods

The four snapshots in `q7_h3_joint_neighborhood_cuts.json` cannot be realized by a low adjacency matrix C and its defect matrix D obeying the q7 block identities. The result is conditional on the **specified signed eigenvector coordinates and vertex-type/support allocation**. It excludes these four assignments, not the fixed psi3 polynomial, either H3 profile, or all allocations in the two discovery square classes.

Run `python3 verify_q7_h3_joint_neighborhood_cuts.py`. This standalone verifier uses only Python's standard-library Fraction arithmetic. One rational Farkas certificate per snapshot proves an impossible inequality 0<=-1. No optimizer is part of verification.

## Prescribed data and graph requirements

Each group has positive integer count, high support mask in {0,...,7}, t=popcount(mask), low triangle incidence tau, and a signed coordinate x_v=a+b sqrt(29). A group assigns this same coordinate and type to every vertex in the group. The class labels0/8 are opaque discovery labels, not a claim of an exhaustive classification.

The two mask censuses are (25,6,6,1,6,1,1,0) and (24,7,7,0,7,0,0,1). The verifier confirms that each prescribed nonzero vector is orthogonal to1 and all three high-support rows and that it is orthogonal to its field conjugate. These are necessary rank-one eigenspace conditions, not sufficient adjacency conditions.

Set lambda=(1+sqrt(29))/2, so lambda²=lambda+7. The presumed eigenspace satisfies

    Cx=lambda x,    Dx=(6-lambda²)x=(-1-lambda)x.

For a target vertex v, its C-neighborhood has size7-t and its D-neighborhood has size6-t. The block identities BC=J and BD=J-B imply that the C-neighbor masks cover each high vertex exactly once, whereas the D-neighbor masks cover precisely the complement of v's mask once. Finally

    |N_C(v) intersect N_D(v)|=(CD)vv=7-2t-2tau.

These identities are the q7 setup used in the reviewed local-moment notes.

## Linear infeasibility certificate

For every group introduce three nonnegative variables: the number of vertices in C-only, D-only, and both neighborhoods. Their sum is at most the group's count, reduced by one for the target's own group. This accounts for both matrices being simple and having no loops. Neighbor choices outside both sets need no variable.

There are13 equality rows: C-degree, three C-support counts, two rational coefficients of Cx; the six corresponding D rows; and the neighborhood intersection count. Multiplication by lambda sends (a,b) to ((a+29b)/2,(a+b)/2). Multiplication by -1-lambda sends it to ((-3a-29b)/2,(-a-3b)/2). Thus every row coefficient and right side is rational.

Write the equalities E n=e and capacity inequalities U n<=u, with n>=0. The stored dual vector consists of unrestricted y on the13 equalities and z>=0 on the capacity rows. The verifier rebuilds all rows and checks

    E^T y+U^T z>=0,    e^T y+u^T z=-1.

For any feasible n, the nonnegative linear combination on the left would be at most -1. This is a rational contradiction even before imposing integer neighbor counts.

## Scope and provenance

The snapshots were discovered by refining the higher local-moment types into common square classes in Q(sqrt29), assigning signed square roots, and enforcing global multiplicities and orthogonality. Their separate C-neighborhood tests passed; joint C/D feasibility exposed the contradiction. The standalone exclusion needs only the retained snapshot and block/eigenvector requirements above; it does not rely on numerical completeness of that discovery or on the earlier moment checks.

The proof is stronger than a numerical infeasibility status but narrower than eliminating a square class: changing group counts, support masks, signs, or coordinates can change the neighborhood constraints. No universal reallocation obstruction is claimed.
