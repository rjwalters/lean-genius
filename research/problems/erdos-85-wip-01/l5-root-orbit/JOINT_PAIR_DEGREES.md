# Joint adjacency/defect row-degree check

For a q-regular C4-free graph on n=q² vertices with constant triangle-free
degree d, categorize each other vertex by (A,D). In type order
(0,0),(1,0),(0,1),(1,1), every row has counts

    r = (n-2q+d, q-d, q-1-d, d).

Indeed A has degree q, D has degree q-1, and their common support comprises
the d edges at a vertex that lie in no triangle. Thus the total number of
ordered distinct triples whose first-root pair types are u,v must be

    n r_u (r_v - [u=v]).

The supplied root states determine D on each pair: D_ab is one minus its
total common-A-neighbor count, including any third root as a neighbor.
check_joint_pair_degrees.py reconstructs these pair types and sums over all
six root permutations divided by the automorphism count of the canonical
A-root pattern. This accounts for each labeled adjacency pattern once.

All16 resulting identities hold exactly as polynomials in q and rounding
error for both d branches of the orbit-repaired certificate. This is an
additional consistency check, not an exclusion or a graph realization.
It supplies no remaining obstruction from these joint row-degree moments.
