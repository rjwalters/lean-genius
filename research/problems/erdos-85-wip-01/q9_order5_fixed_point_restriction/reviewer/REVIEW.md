# Review 2166 — PASS

codex-sol-2, 2026-09-11. All submitted source pins verified. Live accepted premises 2140, 2153, 2161, 2162 and 2163 checked and recorded in results.json.

For a permutation of prime order five, every moved orbit has five distinct vertices. If a moved vertex has two fixed neighbours, its whole orbit shares them, contradicting C4-freeness. Thus the moved induced graph has minimum degree eight and at least 57 vertices by the length-two-walk bound. Every fixed vertex has either zero or five moved neighbours, giving fixed induced degrees nine or four. When the fixed set is nonempty it therefore has at least 13 vertices.

The boundary count 5b <= M and fixed-induced ordered-walk count 12b + 72(F-b) <= F(F-1) are valid without assumptions on connectivity, transitivity or the shape of the fixed graph. Independent direct integer enumeration of these original inequalities (not the eliminated quadratic inequality) over all 1 <= F < N and 0 <= b <= F leaves exactly (F,b,M)=(13,13,65) at N78 and no candidates at N80.

In the remaining 13-vertex 4-regular graph, the 156 non-returning ordered length-two walks exhaust the 156 ordered distinct pairs, each permitted at most once. Thus every edge lies in exactly one triangle. Distinct triangles then share no edge, and every edge is covered; the edge count 26 must be a multiple of three, contradiction. A free order-five action cannot occur at 78 because its vertex orbits would all have size five.

Conclusion: a hypothetical N78/minDegree9/C4-free graph has no order-five automorphism; at N80 every order-five automorphism is free. Combined with accepted 2163 and Cauchy, prime support is {2,3,7} at 78 and remains {2,3,5,7} at 80. This does not exclude the free Z5 case at 80, any asymmetric graph, or all graphs at either order. No graph solver, new quotient search, or Lean result is claimed.
