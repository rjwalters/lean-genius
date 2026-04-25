# Problem: Complete Erdős Problem #1 — Distinct Subset Sums (WIP Extension)

## Statement

### Plain Language

Erdős Problem #1 (1931, $500 prize): If A ⊆ {1,...,N} with |A| = n and all 2^n
subset sums are distinct, must N ≥ c·2^n for some absolute constant c > 0?

The gallery entry `erdos-1` proves the **weaker counting bound** N ≥ (2^n - 1)/n
and the maximum element bound max(A) ≥ 2^(n-1). These are fully verified with 0 sorries.

The **WIP extension** (`erdos-1-wip-01`) targets:
1. Formalizing the **Dubroff-Fox-Xu (2021) lower bound**: N ≥ √(2/π)·2^n/√n
2. Or proving **intermediate bounds** that improve on 2^(n-1)
3. Or formalizing the **Conway-Guy construction** upper bound

### Formal Statement

The conjecture (open, axiomatized):
```lean
-- The $500 conjecture: N ≥ c·2^n for some absolute constant c > 0
theorem erdos_1_conjecture (A : Finset ℕ) (N : ℕ) (hA : A ⊆ Finset.range N)
    (hdss : hasDistinctSubsetSums A) :
    ∃ c : ℝ, c > 0 ∧ (N : ℝ) ≥ c * 2^A.card := by
  sorry
```

Current best proven bound (already in gallery):
```lean
-- Counting bound: 2^(n-1) ≤ N (proved by Aristotle)
theorem erdos_1_lower_bound (A : Finset ℕ) (N : ℕ) (hA : A ⊆ Finset.range N)
    (hdss : hasDistinctSubsetSums A) :
    2^(A.card - 1) ≤ N
```

Dubroff-Fox-Xu target:
```lean
-- DFX 2021: N ≥ √(2/π)·2^n/√n (open in Lean)
theorem erdos_1_dfx_bound (A : Finset ℕ) (N : ℕ) (hA : A ⊆ Finset.range N)
    (hdss : hasDistinctSubsetSums A) :
    (N : ℝ) ≥ Real.sqrt (2 / Real.pi) * 2^A.card / Real.sqrt A.card := by
  sorry
```

## Key Context

### What the Gallery Already Proves

From `Proofs/Erdos1Problem.lean` (0 sorries, 0 axioms):
- `hasDistinctSubsetSums A`: A has all 2^|A| subset sums distinct
- `erdos_1_lower_bound`: 2^(|A|-1) ≤ N (counting/pigeonhole bound)
- `max_element_bound`: 2^(|A|-1) ≤ max(A)
- `subset_sums_spacing`: S ≠ T (subsets of A) → sum(S) ≠ sum(T)

### Known Dead Ends

1. **Vacuously true definition (fixed)**: Old version used injectivity on ALL Finset ℕ — trivially false.
   Current definition restricts to subsets of A.
2. **False claim N ≥ 2^(n-1)**: {3,5,6,7} is a 4-element DSS set with N=7 < 8 = 2^3.
   Correct bound is N ≥ 2^(n-1) (max element, not N itself).

### Mathematical Landscape

| Bound | Result | Source |
|-------|--------|--------|
| Trivial | N ≥ (2^n-1)/n | Counting |
| Better | N ≥ 2^(n-1) | Counting + pigeonhole |
| Best known | N ≥ √(2/π)·2^n/√n | Dubroff-Fox-Xu 2021 |
| Conway-Guy UB | N < 0.22002·2^n | Conway-Guy 1968 |
| **Conjecture** | **N ≥ c·2^n** | **Erdős 1931 ($500)** |

## Alternative Approaches to Explore

### Approach A: Entropy/Information Method (DFX 2021)
- Dubroff, Fox, and Xu use entropy methods + subset sum structure
- Key: Consider random subset S of A; the entropy H(sum(S)) ≤ log(nN+1)
- Combined with H(S) = n (each element independently included)
- Yields N ≥ 2^n / (n+1) → with refinement, N ≥ √(2/π)·2^n/√n
- Mathlib: Does `MeasureTheory.measureEntropy` or similar entropy API exist?

### Approach B: Stronger Counting Argument
- All 2^n subset sums are distinct integers in [0, nN]
- This gives 2^n ≤ nN+1, so N ≥ (2^n-1)/n (already proved)
- Can second-moment method improve this?

### Approach C: Freiman/Additive Structure
- DSS sets are thin Sidon-like sets
- Apply Freiman's theorem or additive energy bounds
- Connection to Mathlib's `Mathlib.Combinatorics.AdditiveCombinatorics`?

### Approach D: Axiomatize the Conjecture (Practical)
- Formally state the $500 conjecture as an axiom
- Prove consequences: optimal c ≤ 0.22, connection to Conway-Guy
- More gallery value than a failed attempt

## Classification

```yaml
tier: A
significance: 9
tractability: 6
tags:
  - erdos
  - additive-combinatorics
  - subset-sums
  - extremal-combinatorics
  - wip
  - number-theory
```

**Significance**: 9/10 — Erdős's "$500 first serious problem" (1931). Fundamental in
additive combinatorics. Connections to Sidon sets, information theory, complexity.

**Tractability**: 6/10 — The main conjecture is open. However, intermediate steps
(entropy bound formalization, DFX framework setup) are tractable. A clean formal
statement of the DFX bound with key lemmas axiomatized has value.

## Related Proofs in Gallery

- `erdos-1`: Parent proof (counting bound, spacing property) — 0 sorries
- `erdos-1-oq-01` through `erdos-1-oq-04`: Related open questions
