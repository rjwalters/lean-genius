# Problem: Erdős #268 — Path-Connectedness of Harmonic Subseries Points

**Slug**: erdos-268
**Created**: 2026-04-21
**Status**: Active
**Source**: gallery-incomplete

## Problem Statement

### Formal Statement

```lean
theorem harmonicPointSet_path_connected (d : ℕ) :
    IsPathConnected (harmonicPointSet d) := by sorry
```

where `harmonicPointSet d` is the set of all vectors
`(Σ_{n∈A} 1/n, Σ_{n∈A} 1/(n+1), ..., Σ_{n∈A} 1/(n+d-1))` as `A` ranges over
infinite subsets of ℕ with `Σ_{n∈A} 1/n < ∞`.

### Plain Language

The proof file `Erdos268Problem.lean` is nearly complete (1 axiom + 1 sorry).
The axiom `erdos_268_solved` encodes the Kovač-Tao 2024 result (nonempty interior of X).
The one remaining sorry is that X is **path-connected**.

A path in X requires a continuous function `γ : [0,1] → X` connecting two arbitrary
points, where each `γ(t)` must be a harmonic subseries point — i.e., come from some
infinite A_t ⊆ ℕ with convergent harmonic subseries.

### Why This Matters

- Completing `Erdos268Problem.lean` achieves full formalization of Erdős #268
- Path-connectedness (together with nonempty interior) gives a clean geometric
  picture of the harmonic subseries point set
- For d=1 this is completely tractable: X₁ = (0, ∞) which is path-connected

## Known Results

### What's Already Proven

- `harmonicPointSet_nonempty`: X is non-empty (powers of 2 example)
- `harmonicPointSet_dense_somewhere`: X has nonempty interior (uses the axiom)
- `contains_open_ball`: X contains an open ball
- `coordinate_decreasing`: coordinate is decreasing in shift
- All coordinate projection and density lemmas

### What We're Proving

- `harmonicPointSet_path_connected (d : ℕ) : IsPathConnected (harmonicPointSet d)`

The approach is inductive / special-case:
- **d = 0**: `harmonicPointSet 0` is a singleton `{()}` (empty product), trivially path-connected
- **d = 1**: `harmonicPointSet 1 = Set.Ioi 0` (all positive reals), which is path-connected
  because it is an open interval. Proving X₁ = (0,∞) uses:
  - Any s ∈ (0,∞) can be written as Σ_{n∈A} 1/n for some A (greedy algorithm argument)
  - `IsPathConnected (Set.Ioi (0 : ℝ))` is in Mathlib
- **d ≥ 2**: Hard. Requires controlling d coordinate sums simultaneously along a path.
  Convexity is non-obvious. The Kovač-Tao 2024 structure theorem may help.

### Our Goal

Prove the d=0 and d=1 cases, establishing partial path-connectedness.
The d=0 case is trivial. The d=1 case requires:
1. Show X₁ ⊆ (0,∞): any convergent harmonic subseries has positive sum
2. Show (0,∞) ⊆ X₁: greedy construction — given s > 0, build A inductively
3. Conclude via `IsPathConnected.mono` or direct from `isPathConnected_Ioi`

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| `erdos-268` | The main gallery entry | Functional analysis, harmonic series |
| `harmonic-series` | Background on Σ 1/n divergence | Cauchy condensation test |

## Initial Thoughts

### Potential Approaches

1. **d=0 trivial case**: `harmonicPointSet 0` should reduce to `{fun _ => 0}` or similar empty
   product space. Use `subsingleton_iff` or direct definition unfolding. `IsPathConnected`
   for a singleton follows from `isPathConnected_singleton`.

2. **d=1 via interval characterization**:
   - Prove `harmonicPointSet 1 = Set.Ioi 0`
   - For ⊆: any x ∈ harmonicPointSet 1 satisfies x = Σ 1/n > 0 (at least one term)
   - For ⊇: given s > 0, construct A by greedy algorithm (add n to A if Σ_{k≤n,k∈A} 1/k < s)
   - Then `Set.Ioi 0` is path-connected in Mathlib

3. **General d via product**: If X_d has a product structure, path-connectedness could
   follow from path-connectedness of each factor. But X_d is NOT a Cartesian product
   of independent sets — the same A determines all d coordinates.

### Key Difficulties

- The discrete nature of A makes continuous paths non-obvious
- For d=1: the greedy construction is a real analysis argument not directly in Mathlib
- For d≥2: convexity fails; no obvious product structure

### What Would a Proof Need?

- Key lemma for d=1: `harmonicPointSet_one_eq_Ioi : harmonicPointSet 1 = Set.Ioi 0`
- Mathlib: `isPathConnected_Ioi` or derive from `isConnected_Ioi` + `isPathConnected_iff`
- For greedy: `Summable.tendsto_atTop` style argument to show partial sums converge to s

## Tractability Assessment

**Difficulty for d=0,1**: Low — tractable with current Mathlib

**Difficulty for d≥2**: High — requires new mathematical ideas

**Justification**:
- d=0 case: definition unfolding + `isPathConnected_singleton`
- d=1 case: greedy construction + real analysis + `isPathConnected_Ioi`
- d≥2 case: requires the full Kovač-Tao 2024 analysis (path construction in ℝ^d)

**Estimated Effort**:
- d=0 case: 1-2 hours
- d=1 case: 4-8 hours (greedy + real analysis machinery)
- d≥2 case: days to weeks (deep mathematics)

## Files

- `proofs/Proofs/Erdos268Problem.lean` — main formalization (1 sorry, 1 axiom)
- `proofs/Proofs/Erdos268Aristotle.lean` — Aristotle companion
- `proofs/Proofs/Erdos268ProblemAristotle.lean` — companion for supporting lemmas
- `src/data/proofs/erdos-268/meta.json` — gallery metadata
