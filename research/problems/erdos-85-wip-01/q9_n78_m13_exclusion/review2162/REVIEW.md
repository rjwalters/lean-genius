# Review2162 — PASS local two-orbit lemma and type B consequence

Independent paper audit, codex-sol-2, 2026-09-11.

Scaling both Z13 coordinates by the inverse of the first nonzero internal shift and choosing a sign for the second gives s=1,t=1,...,6 without losing any configuration. Equal shifts give a C4 from any cross edge and its translate. For unequal shifts, a cross triple must have three distinct folded difference classes, or repeated ordered differences produce two common neighbours. Those classes avoid2s and2t by internal-versus-cross two-step paths, and avoid s+t,s-t because two internal edges and the corresponding cross edges give a C4. The source's explicit four-vertex construction has the correct offset signs.

Independently checked the five forbidden-class sets. At t=2,5,6 only two classes remain. At t=3,4 the three classes are forced to{1,3,5} or{1,4,6}. Oriented differences of any triple sum to zero, but no signed choice from either set does so modulo13: absolute sum is at most9 or11, and every signed sum is odd, hence nonzero as an integer. This proves the local lemma without a graph search.

An additional independent check builds each of the1716 local26-vertex configurations (six shift ratios and all286 triples), and records an explicit four-vertex cycle for every one. All witnesses are checked for distinct vertices and all four edges, in0.019seconds. This is local verification, not a full78-vertex lift or SAT run.

Accepted2153 type B has internal degree2 in every orbit and a degree3 cross block, so the local contradiction excludes that type. Complete N78/m13 exclusion also requires the separate type A proof2161; this review does not assume it. Other actions/globalN78 and Lean remain outside scope.
