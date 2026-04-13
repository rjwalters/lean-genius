# Erdős Problem #748: The Cameron-Erdős Conjecture on Sum-Free Sets

**Lean file**: `proofs/Proofs/Erdos748Problem.lean`
**Sorries**: 4
**Status**: available
**Tier**: A | **Significance**: 8/10 | **Tractability**: 5/10

## Problem Statement

Let f(n) count sum-free subsets A ⊆ {1,...,n}. Conjecture: f(n) = 2^{(1+o(1))n/2}.

**Status**: PROVED — Green (2004) and Sapozhenko (2003).

## The Sorries

### Easy: Base Cases (Sorries 2-4)
```lean
theorem f_1 : f 1 = 2 := by sorry   -- f(1) = |{{}, {1}}| = 2
theorem f_2 : f 2 = 3 := by sorry   -- f(2) = |{{}, {1}, {2}}| = 3
theorem f_3 : f 3 = 6 := by sorry   -- f(3) = |{{},{1},{2},{3},{1,3},{2,3}}| = 6
```
These are computable! Count sum-free subsets of {1,2,3} directly.

### Hard: Main Theorem (Sorry 1)
```lean
theorem cameron_erdos : ∀ ε > 0, ∀ᶠ n in atTop,
    |Real.log (f n) - (n/2 * Real.log 2)| ≤ ε * n := by
  sorry -- Full proof requires careful asymptotic analysis
```

## Approach: Start with Base Cases

For `f_1 : f 1 = 2`:
- Sum-free subsets of {1}: {} and {1} (trivially sum-free since no triple a,b,c)
- Try `decide` if `f` is computable, or explicit enumeration

For `f_2 : f 2 = 3`:
- Subsets: {}, {1}, {2}, {1,2}. Is {1,2} sum-free? 1+1=2 ∈ {1,2} → NO. So 3 sum-free subsets.

For `f_3 : f 3 = 6`:
- Need to enumerate all 8 subsets and check sum-free condition

## Key Questions

1. Is `f` computable in the Lean file? If yes, try `native_decide` or `decide`
2. What is the definition of sum-free in this file?
3. Are there auxiliary lemmas already proved?

## Related Gallery Proof

- `src/data/proofs/erdos-748/` — Erdős Problem #748
- `proofs/Proofs/Erdos748Problem.lean` — file with sorries

## First Steps (OBSERVE phase)

1. Read `Erdos748Problem.lean` fully
2. Check if `f` is `Decidable` / computable
3. Try `decide` or `native_decide` on the base cases first
4. For main theorem: read Green's proof structure in the file comments
