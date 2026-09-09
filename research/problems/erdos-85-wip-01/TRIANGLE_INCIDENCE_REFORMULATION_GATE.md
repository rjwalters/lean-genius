# Round114 S2: the first incidence bound is unchanged

Let G be q-regular and C4-free. Every edge belongs to at most one triangle:
two triangles sharing an edge would give two common neighbors of its endpoints.
Use one block of size3 for each triangle and one block of size2 for every
remaining edge. The point-block incidence graph has girth at least10.
A 4-cycle repeats a point pair in two blocks. A 6-cycle gives a triangle
whose three edges belong to three distinct blocks, contrary to the block
construction. An 8-cycle gives a C4 in G.

For a root point v with t_v incident triangles, its incident blocks are
t_v triples and q-2t_v pairs. There are q point vertices at incidence
distance2. If u is one of them and B_vu its block with v, the number of
point continuations through other blocks at u is q-(|B_vu|-1).
Girth at least10 makes these distance4 point vertices all distinct and
disjoint from v and the distance2 shell. Therefore the left-vertex census is

    1 + q + sum_{u~v}[q-(|B_vu|-1)]
      = 1 + q + q² - [4t_v + (q-2t_v)]
      = q² + 1 - 2t_v.

At |V|=q² this merely says t_v>=1, the existing radius-two inequality.
Thus the proposed incidence reformulation alone gives no stronger bound.
It does not establish regularity of either incidence shore or equality in
a Moore bound, so a generalized-polygon equality theorem cannot simply be
applied. No claim is made that all possible irregular-excess theorems are
unavailable. A continuation would need to name a stronger theorem with
verified hypotheses; absent that, S2 is cut at its current formulation.

This is a uniform elementary derivation. No finite search or Lean result
is claimed.
