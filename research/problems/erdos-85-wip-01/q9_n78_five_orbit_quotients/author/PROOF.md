# Five-orbit necessary degree quotients

Assume a simple C4-free nine-regular graph on78 vertices with exactly five full automorphism orbits. Accepted2264 gives group order dividing48 and2315 gives vertex stabilizer at most8. Orders at most12 cannot cover78 vertices in five orbits. Enumerate orders16,24,48, nondecreasing orbit sizes n_i dividing the group order with stabilizer order at most8, and sum78. There are no order16 partitions and seven others, all recorded.

For equitable adjacency degrees q_ij, require integer nonnegative entries, row sums9, q_ii<n_i, and n_i q_ij=n_j q_ji. Each distinct vertex pair has at mostone common neighbor, so

    sum_j n_j choose(q_ji,2) <= choose(n_i,2),
    sum_j n_j q_ji q_jk <= n_i n_k (i != k).

The checker exhausts off-diagonal pairs in lexicographic order. With g=gcd(n_i,n_j), each pair is (n_j/g*t,n_i/g*t) over every nonnegative t within remaining row-degree bounds. After the last off-diagonal entry of row i it forces its diagonal from degree9. The final row is forced at the leaf. Unknown entries remain zero: all capacity summands are nonnegative and nondecreasing on nonnegative integers, so partial capacity violations cannot be repaired later. Pruning is therefore necessary only and exhaustive. Each surviving matrix is saved. The original aggregate30-second budget was declared before execution; output is COMPLETE in0.014seconds with no UNKNOWN/unvisited case.

Raw quotient counts in partition order are12,12,0,10,2,12,0. In particular (6,6,6,12,48) and (6,16,16,16,24) are impossible already at this arithmetic level. The saved parity-filter.json additionally removes quotients with odd n_i*q_ii, impossible by the handshaking lemma; this deterministic filter performs no new search and does not alter raw output.

Accepted2332 independently excludes the two mixed8 orbit partitions by Sylow3 incidence. Combining it with the zero quotient result leaves only sizes (3,3,24,24,24) at group order24 and (6,12,12,24,24) at order24 or48. Every order3 element is free in these cases. The full surviving matrices remain necessary conditions only. This does not exclude five or more orbits generally, all78-vertex graphs, N80, or Erdős85; there is no full graph search or Lean claim.
