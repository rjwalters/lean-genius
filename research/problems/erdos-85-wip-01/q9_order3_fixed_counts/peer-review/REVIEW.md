# Review 2176 — PASS

codex-sol-2, 2026-09-11. All three submitted pins verified. The paper and arithmetic were independently audited; no producer script or graph search was run.

## Fixed graph reduction

The moved-vertex bound and prime-order orbit decomposition give M>=57 and M divisible by three. The fixed graph degrees are 0,3,6,9. Counting boundary edges from both sides yields S>=10F-N. The ordered common-neighbour bound and Cauchy give S²-FS<=F²(F-1). For the seven listed large fixed counts, L=10F-N>F/2 makes this quadratic increasing for S>=L. Every reported positive excess is correct.

On the remaining nonisolated fixed components, minimum degree is three and order is at most twelve. The asymmetric layer bound gives at least 1+2D vertices at a degree-D vertex, excluding degrees six and nine. The components are therefore cubic. Their order is at least seven and even, hence at least eight. At order eight, each vertex's three neighbours induce at most one edge; the distance-two count 10-2t<=8 forces exactly one. Every vertex then belongs to exactly one triangle, so triangles partition eight vertices, a contradiction. Thus each nonempty cubic component has at least ten vertices. This reasoning does not assume the fixed graph is connected.

## Exceptional F11 case

At (N,F,b)=(80,11,10), the fixed graph is a cubic ten-vertex component plus one isolated vertex. Its boundary has 69=M edges, forcing exactly one fixed neighbour for every moved vertex, and moved degree eight. The fixed-neighbour groups partition the moved vertices into one group of size nine and ten groups of size six.

For a moved x in the group of v, at most one neighbour can lie in each fixed-neighbour group O_u: two such neighbours would be common to distinct x and fixed u. When u is a fixed neighbour of v, there can be none, since fixed v already supplies that common neighbour. The ten nonisolated fixed vertices each forbid three groups. Their moved neighbours must therefore fill all eight allowed groups, including the nine-vertex group O_a. This forces sixty external edges into O_a. Its total moved degree is 72, leaving internal degree sum twelve, although each of its nine vertices has internal degree at most one. The contradiction is valid even though the moved order is 69; no below-64 regularity assumption is being smuggled in.

## Independent fixed-set refinement

For a fixed v, its 72 non-returning two-step walks have distinct endpoints. Hence precisely N-73 other vertices have zero common-neighbour count with v. This includes all F-1 other fixed vertices once the fixed graph is independent. Its neighbourhood is a matching plus isolated vertices; the isolated count U is positive and odd. The order-three action preserves this set and acts freely on it, so U is divisible by three. Therefore U>=3 and F<=N-75. Enumerating its possible odd multiples of three under the remaining budgets forces U=3, hence three triangles through each fixed vertex.

Independent arithmetic audit enumerated degree multiplicities from moved counts, reproduced every one of the 14+16 initial profiles and all seven Cauchy exclusions, then checked the component/boundary reductions and matching-size budgets. It obtains exactly F in {0,3} at N78 and F in {2,5} at N80. The submitted 57 bound suffices; proposed stronger theorem 2174 is not required for this review.

Scope: necessary order-three fixed-point restrictions, independence of the fixed set, and exactly three triangles through each fixed vertex. The surviving actions and unrestricted graphs are not excluded. No graph solver, full quotient enumeration, or Lean verification of this complete paper chain is claimed.
