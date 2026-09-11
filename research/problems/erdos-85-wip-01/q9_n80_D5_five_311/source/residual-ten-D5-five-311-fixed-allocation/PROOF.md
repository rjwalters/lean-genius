# Fixed-highmatching aggregate constraints for D5/s5

Use the43 explicit packing representatives in2468 and every surviving high matching from2467. There are601 representative packing/matching cases. This is a stronger necessary model than2464, with the high matching now fixed; it does not resume any capped calculation.

Retain the involution-identified binary-relaxed high defect variables Q[v,e], aggregate low defect variables L[r,e], exact residual columns, residual-middle zeros, endpoint upper bounds, and all45 RR commutator equations from2464. High variable bounds are now the coordinate minima/maxima of the complete conditional domains in2467. Each unmatched high vertex has exact Q row size2; each matched high vertex has exact row size0.

Let C_v be the residual endpoints covered through residual or high middle vertices, and let a_r count the high vertices with r outside C_v. A high vertex requires a low neighbor supported at r precisely when r is outside C_v and its defect row. Therefore the exact number of high-to-low demands at r is a_r minus the high-Q column sum at r. A low vertex has endpoint budget2 and all high neighbors cost2, so it has at most one high neighbor. Consequently exactly u_r=n_r-a_r+sum_v Q[v,r] of the low vertices at r have no high neighbor.

Each low vertex with a high neighbor has zero residual defect neighbors. Each of the u_r others has exactly two residual defect neighbors. Impose the exact aggregate row equation

 sum_e L[r,e] - 2 sum_v Q[v,r] = 2(n_r-a_r).

Furthermore L[r,e]<=u_r, since each of these u_r low vertices contributes at most one defect edge to any fixed endpoint. Equivalently impose2L[r,e]<=sum_j L[r,j] for every cell. The saved inequality lower bound -2n_r is harmless because all cells are nonnegative and the row upper bound is2n_r. These are necessary linear constraints; they relax the actual binary/integer allocations.

Model construction completes all601 cases in3.055696 seconds under its original30-second cap. A separate original30-second run completes in5.367234 seconds, producing202 exact rational Farkas contradictions and399 exact rational witnesses. Exact Fraction checks verify all certificates against original labeled inequalities; solver infeasibility alone is not an exclusion. Every model carries class, original packing index, global packing-root identifier and matching index, with exact coverage of all601 representative cases.

The202 exclusions apply to their full symmetry images conditional on2468 and independent acceptance of this model. The399 rational witnesses do not establish integral defect assignments or graph realizations. No fulls5, D5, global Erdős85 or Lean theorem is claimed.
