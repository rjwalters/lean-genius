# Knowledge Base: sperner-ndim-oq-03

## Problem Understanding

Prove the Brouwer fixed point theorem for the standard d-simplex by connecting
it to the n-dimensional Sperner's lemma via the displacement coloring construction.

The displacement coloring assigns each grid vertex v the index k of the most
negative barycentric displacement component d_k = f(v/N)_k - v_k/N.

## Core Result (Fully Verified)

**`displacementColoring_isSperner`**: The displacement coloring satisfies the
Sperner boundary condition for arbitrary dimension d.

Proof structure (3 steps, no sorries):
1. On face k, d_k >= 0 (face geometry: k-th bary coord of v is 0, f maps to simplex)
2. When f(v) != v, some d_j < 0 (sum-to-zero + nonzero implies negative component)
3. argmin <= d_j < 0 <= d_k, so k != argmin

## Insights

- The proof is dimension-independent: identical structure for d = 2 and d = 100
- On face k, the k-th barycentric coordinate of v is 0, so d_k = f(v)_k >= 0
- The barycentric displacements sum to 0 (barycentric coordinates sum to 1)
- If all displacements >= 0 and sum = 0, then all = 0, meaning f(v) = v (contradiction)
- Any tie-breaking rule works for the argmin (Sperner condition holds regardless)
- The 2D proof in BrouwerFixedPointOQ02OQ01 generalizes cleanly to n dimensions

## Remaining Work (2 sorries)

1. `approximate_fixed_point`: Choose N with mesh < delta(eps), apply Sperner's lemma to
   get fully-colored simplex, transfer displacement bounds via UC between vertices.
   Generalizes BrouwerFixedPointOQ02OQ01.lean lines 922-1071.

2. `brouwer_simplex`: Standard compactness argument -- approximate fixed points form a
   sequence in the compact simplex, subsequence converges to exact fixed point.

## Dead Ends

None encountered -- the displacement coloring approach is clean and direct.
