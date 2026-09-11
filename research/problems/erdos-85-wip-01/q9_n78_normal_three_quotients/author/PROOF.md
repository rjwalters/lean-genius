# Partial completion of the normal-C3 seven-orbit quotient domain

Accepted2368 leaves three orbit-size patterns for order24 automorphism groups with normal Sylow3 subgroup. This packet records one original30-second necessary equitable-quotient check on those three patterns. Its global status is INCOMPLETE. The first two cases completed; the third is UNKNOWN, with partial positives that are not a complete cover.

For orbit sizes n_i, a quotient entry q_ij counts the neighbors in orbit j of a vertex in orbit i. Each row sums to9, n_i*q_ij=n_j*q_ji, diagonal entries lie between0 and n_i-1, and n_i*q_ii is even. Pair counting in a C4-free graph gives

 sum_j n_j*choose(q_ji,2) <= choose(n_i,2),
 sum_j n_j*q_ji*q_jk <= n_i*n_k  (i != k).

The program enumerates all balanced nonnegative off-diagonal pairs by their gcd step. At the last off-diagonal entry in a row it fills the diagonal to make degree9, and checks simplicity and parity. Every partial capacity sum is nonnegative and can only increase as further entries are filled. Therefore pruning an exceeded pair bound is safe. Every quotient satisfying these necessary conditions occurs exactly once in the complete traversal. No claim of sufficient graph realizability is made.

The terminal results are:

- (3,3,12,12,12,12,24): COMPLETE,6431 nodes, zero quotients.
- (6,6,6,12,12,12,24): COMPLETE,81764 nodes,264 quotients.
- (6,12,12,12,12,12,12): UNKNOWN,1069533 nodes,1929 partial positives.

The original global cap was reached at30.000019 seconds. The UNKNOWN domain is frozen without restart or cap enlargement. Only the completed first case supports an exclusion, and only the completed second case supports a full necessary quotient list. Independent review of those two completed domains is requested. The third case's partial output supports neither exclusion nor complete coverage. A separate paper argument submitted2371 addresses that pattern independently; it is not a reinterpretation of UNKNOWN as negative.

This is a quotient calculation, not a full graph solver or Lean formalization. It does not exclude the surviving264 quotients, all normal-Sylow actions, or the global Erdős problem.
