# Literature: Erdős #268 — Interior of Harmonic Subseries Points

## Key References

### Primary Results

1. **Kovač (2024)**: "On the existence of harmonic subseries with a prescribed density function"
   - Proved that X_d (d=3) has nonempty interior
   - Construction: explicit subseries using Dirichlet-like density arguments

2. **Kovač-Tao (2024)**: "Harmonic subseries and multidimensional point sets"
   - Extended Kovač's result to all d ≥ 1
   - The main `erdos_268_solved` axiom encodes this result
   - Path-connectedness is NOT directly addressed in their work

### Background

3. **Erdős (1962)**: Original problem statement in "Some problems on the distribution of prime numbers"
   - Asks whether X ⊆ ℝ has nonempty interior for d=1

4. **Greedy algorithm for subseries**: Standard technique in real analysis
   - Given target s > 0, construct A greedily: add n to A if current partial sum < s
   - This constructs a subseries converging to s (for s ≤ Σ 1/n = ∞)

## Mathlib Resources

- `IsPathConnected`: `Mathlib.Topology.PathConnected`
- `isPathConnected_Ioi`: open ray (0, ∞) is path-connected
- `Summable.tendsto_atTop_zero`: terms of convergent series → 0
- `tsum_le_tsum`: comparison for convergent series
- `Finset.sum_le_sum`: finite sum bounds

## Notes on Path-Connectedness Approach

The key insight for d=1:
- X₁ = {Σ_{n∈A} 1/n : A ⊆ ℕ infinite, Σ_{n∈A} 1/n < ∞}
- Every such sum is in (0, ∞) (positive since at least one term 1/n > 0)
- Every s ∈ (0, ∞) is achievable by greedy construction
- (0, ∞) is path-connected (it's a convex subset of ℝ)

For d≥2, the analogous X_d likely has interior (proved by Kovač-Tao) but
path-connectedness is subtler since we must simultaneously control d coordinates.
