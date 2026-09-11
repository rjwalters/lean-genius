# Six vertices with a free involution have at most seven edges

Let X be a simple C4-free graph on six vertices with a fixed-point-free involution. Its three involution orbits have size two. Between two orbits, invariant edges form no edges, one of the two perfect matchings, or all four edges. The last case is a C4 and is forbidden. Within an orbit there is at most its single partner edge.

Consequently X has at most six cross-orbit edges and at most three partner edges. If it had at least eight edges, it would have at least two partner edges. It would also have all six cross-orbit edges: cross-orbit edge counts are even, and at most four of them together with all three partner edges would give only seven edges. In particular the two orbits with partner edges are joined by a perfect matching. Their two partner edges and this matching form a C4. Contradiction.

Thus e(X)<=7. This bound is sharp: take two disjoint triangles exchanged by the involution and add one edge joining a vertex to its partner. A bridge cannot create a new cycle, so this seven-edge graph is C4-free.

## Exclude residual orbit degrees (0,1,3,3,3)

Suppose a C4-free graph R has five free involution orbits with degrees0,1,3,3,3. Let C be its six cubic vertices. Their eighteen degree incidences can include at most two edges to the complement: the isolated orbit contributes none, and the two leaves contribute at most one each. Hence

 18=2e(R[C])+e(C,R minus C)<=2e(R[C])+2,

so e(R[C])>=8. But C is invariant and inherits the free involution, contradicting the seven-edge lemma. Thus this degree pattern is impossible.

Applied to the N80/F10 cubic-fixed residual graph, this excludes the isolated equality pattern01333. The proof uses only simplicity, C4-freeness and the free involution; it does not depend on any attached-graph assumption or pending review. The optional216-case check audits the local six-vertex lemma and supplies a sharpness witness, not a full80-vertex graph. No full graph solver or Lean formalization is used.
