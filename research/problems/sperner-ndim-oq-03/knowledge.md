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

## Approximate Fixed Points (Fully Proved)

**`approximate_fixed_point`**: For any ε > 0, there exists an ε-approximate
fixed point of f in the simplex (assuming Sperner's lemma).

Proof structure:
1. UC of f on compact cube [0,1]^d → get δ for tolerance ε/(2*(d+1))
2. Choose N with 1/N < min(δ, ε/(2*(d+1)))
3. Grid fixed point case: trivial
4. No grid FP: displacement coloring is Sperner → FC simplex via Sperner
5. Pick color-(last d) vertex v₀: ∑(f_j - p_j) > 0
6. Transfer from each color-(castSucc j) vertex: f(p₀)_j - p₀_j < ε/(d+1)
7. Lower bound from sum condition: f(p₀)_j - p₀_j > -ε

## Brouwer Fixed Point (Fully Proved)

**`brouwer_simplex`**: Every continuous self-map of the d-simplex has a fixed point.

Proof structure:
1. Simplex is compact (closed subset of compact cube) and nonempty (0 ∈ Δ)
2. dist(f(·), ·) achieves its minimum m on the compact simplex
3. If m > 0, approximate_fixed_point with ε = m gives contradiction
4. So m = 0, minimizer is exact fixed point

## Infrastructure Lemmas

- `countPerm_le_one`: countPerm values in {0,1} (permutation injectivity)
- `gridToReal_mem_cube`: grid vertices map into [0,1]^d
- `fsimplex_gridToReal_dist`: FSimplex vertices have L∞ distance <= 1/N

## Insights

- The proof is dimension-independent: identical structure for d = 2 and d = 100
- On face k, the k-th barycentric coordinate of v is 0, so d_k = f(v)_k >= 0
- The barycentric displacements sum to 0 (barycentric coordinates sum to 1)
- If all displacements >= 0 and sum = 0, then all = 0, meaning f(v) = v (contradiction)
- Any tie-breaking rule works for the argmin (Sperner condition holds regardless)
- The 2D proof in BrouwerFixedPointOQ02OQ01 generalizes cleanly to n dimensions
- Transfer argument: pick color-(last d) vertex for sum condition, transfer upper
  bounds from color-(castSucc j) vertices, derive lower bounds via sum constraint
- Key bound: (d-1)*ε/(d+1) < ε gives coordinate-wise approximation

## Remaining Work

**None in SpernerNDimOQ03.lean** — 0 sorries, 0 axioms.

The file depends on `sperner_ndim` from SpernerNDim.lean (which still has 1 sorry),
but `approximate_fixed_point` and `brouwer_simplex` take Sperner's lemma as a
hypothesis parameter, so they are independently verified.

## Dead Ends

None encountered — the displacement coloring approach is clean and direct.
