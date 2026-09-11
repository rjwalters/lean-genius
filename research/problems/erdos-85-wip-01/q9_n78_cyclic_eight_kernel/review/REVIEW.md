# Review 2276: PASS scoped C24 obstruction and cyclic-kernel corollary

All three source payload pins and four premise hashes match. Reviews 2176,2245,2253,2264 are accepted; 2268 remains claimed. I read the cited proofs and audited the following argument independently.

For the proposed cyclic C24 action, the involution in its C8 subgroup fixes exactly six vertices inducing 3K2 by 2253. These coincide with the six pointwise C8-fixed vertices in the hypothesis. Every outside point has trivial C8 stabilizer because every nontrivial subgroup of C8 contains the involution. Its C24 orbit therefore has size 8 or24. An 8-orbit has the unique order-three subgroup as stabilizer at every point, contradicting the order-three fixed-point bound of three. Thus all outside orbits have size24.

On F, an order-three element fixing a vertex would fix its unique matching partner; this contradicts independence of its fixed graph from2176. Thus its two orbits on F have size three, and the matching joins them. The matching form2245 identifies W as two 24-orbits, one over each F-orbit; the fiber size is eight, so there is no alternative distribution. Matching saturation makes the induced degree on each W orbit exactly three. A cubic Cayley graph on C24 has inverse-closed connection set {12,s,-s}; for every s other than0 or12 the given four vertices are distinct and form a C4. I verified all22 certificates and88 edge differences.

For a cyclic order-eight action kernel in the three-orbit case, accepted2264 already gives |A|=48 and |F|=6. Normality is part of being an action kernel. Conjugation has image in Aut(C8) of order four, so its kernel centralizer has order divisible by three. Cauchy's theorem gives a commuting order-three element. Together with C8 this gives a cyclic C24 subgroup to which the scoped obstruction applies. This corollary needs no additional claim from pending2268; the kernel fixes F pointwise by definition.

PASS for this scoped obstruction and the resulting exclusion of a cyclic order-eight kernel. This does not exclude arbitrary order24 actions, other kernels, the entire three-orbit case, or N78. No search replay, solver call, or Lean formalization.
