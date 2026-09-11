# Review2397: PASS two single-four-orbit S4 exclusions

All six payload/input hashes and fresh2257/2376 PASS checked. The independent audit selected the exact unique character multiset for each pattern and inspected every underlying subgroup: the six-orbit stabilizers are cyclicC4, the special12 stabilizers double-transpositionC2, and the other two12 stabilizers transpositionC2. No choice of representative loses an action.

None of the stabilizers contains the normal double-transposition V4. Its three nonidentity elements each fix6 vertices, and their fixed sets are pairwise disjoint with unionS of size18. Any cross-edge between different fixed sets gives a C4 under the two commuting involutions, as all four endpoints are distinct. The union is A-invariant.

For three cyclicC4 six-orbits, a square-root four-cycle fixes all6 vertices fixed by its square; every outside cycle has length4. Fixed degrees1/3 therefore reduce to1 by degree9 modulo4. In the other pattern the four-cycle fixes exactly two vertices of the six-orbit X within its square's fixed set. On the six-fixed graph it induces an involution. If this graph were triangle-with-leaves, its three cubic vertices would have an odd number of fixed points. But the only two fixed vertices have equal degree inG[S] by transitivity onX and invariance ofS, hence equal degree within that fixed graph. They contribute0 or2 fixed cubic vertices, a contradiction. Thus both patterns give a matchingS and144 outgoing edges.

Every outside vertex has at most one neighbor in each fixed set, so S-degree<=3. The naturalS3 point stabilizer acts freely on the cyclicC4 and doubleC2 orbits inS. Any F-toS attachment then violates the four-point pair capacity. F is independent. Direct balance/capacity arithmetic independently gives exterior degrees0/2 intoV8,0/3 into each12 and0/6 intoU24. Degree9 forces exactly6 intoU and3 into one12, and none intoV or the other12.

Let u,b,c,v be the exterior orbit S-degrees. A fixed f has6u+3b two-step endpoints inS, all distinct by C4-freeness, giving2u+b<=6. Therefore outgoingS edges equal24u+12b+12c+8v<=72+36+24=132, contradicting144. All counts are uniform by A-transitivity, and the endpoint set is disjoint fromF.

This excludes both complete displayed orbit-size patterns under accepted2376. No new graph enumeration, capped negative, other S4 exclusion or Lean claim is involved.
