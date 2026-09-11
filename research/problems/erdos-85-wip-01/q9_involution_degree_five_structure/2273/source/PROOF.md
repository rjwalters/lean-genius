# Necessary incidence feasibility for the remaining degree-five shapes

This check is conditional on the 24 marked fixed-graph cases in submitted review 2272. It handles each case for t=0 and t=1 separately, for 48 roots in total. A witness is only a missed-orbit incidence matrix, not a graph.

Let Y_fj indicate that attached group B_f misses residual orbit j. There are five residual orbits, with central orbit zero. The group types 111,211,221,311 have respectively two, one, zero, zero missed orbits. Set delta_f=2-sum_j Y_fj. Thus delta lies in {0,1,2}. The fixed set's zero-codegree graph has degree three, so the number of attached E-neighbors of f is 2 delta_f. It is invariant under the free involution and consists of delta_f orbits.

For any residual vertex r, its adjacency into each attached involution orbit is at most one, by C4-freeness. Therefore T_fr=(E_FW A_WR)_fr lies between zero and delta_f. Commutation AE=EA at (f,r) gives

    (A_FW E_WR)_fr = (YQ-HY)_fj + T_fr >= 0.

Consequently every row satisfies

    (HY)_fj <= (YQ)_fj + delta_f.

For ordinary rows delta=0 this is the exact nonnegative inequality used in review 2270. For special rows it is only a relaxation: the check does not assert that a compatible T or attached graph exists.

The central column is fixed to Y_f0=1[f outside P]. Review 2272 also gives deg_P(f)<=1+delta_f. Column sums are six at the central orbit and two at every leaf orbit for t=0; for t=1 the two matched leaf orbits have column sum three and the other two have column sum two. These follow from residual degrees five and one/two. Q is the binary star quotient with its central loop and, for t=1, an edge between leaf orbits 1 and 2.

The script enumerates the at most 32 binary row masks for each fixed center, imposing these row and central constraints. A finite recursive search chooses an unassigned row with the smallest remaining domain. It rejects only column overshoots, empty domains, violated nonnegative neighbor-sum upper bounds, or column targets outside the sum of remaining per-row minima and maxima. At a complete assignment it requires exact column sums. These rejection rules are necessary, so an exhausted root proves infeasibility of the stated incidence relaxation. The search stops at the first witness in a feasible root.

Original limits: 30 seconds aggregate, 500,000 aggregate recursive nodes, 100,000 nodes per root. A limit inside a root yields UNKNOWN; roots not begun after an aggregate limit yield UNVISITED. No limit outcome is an exclusion. The saved result records every root and its terminal status. No repeated attempt, full-graph solver, or Lean formalization is involved.
