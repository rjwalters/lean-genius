# Problem: D(n) = round(n!/e) as an Integer Identity in Lean

**Slug**: derangements-convergence-oq-03
**Created**: 2026-04-24
**Status**: Active
**Source**: gallery-gap — from `derangements-convergence` OQ3

## Problem Statement

### Formal Statement

For all n ≥ 2, the number of derangements equals the nearest integer to n!/e:

```lean
theorem derangements_round_eq (n : ℕ) (hn : 2 ≤ n) :
    (Nat.numDerangements n : ℤ) = Int.round (↑(n !) / Real.exp 1) := ...
```

Or equivalently, using the Nat rounding direction:

```lean
theorem derangements_round_eq' (n : ℕ) (hn : 1 ≤ n) :
    (Nat.numDerangements n : ℝ) = Real.round (↑(n !) / Real.exp 1) := ...
```

### Plain Language

The count of derangements of n objects (permutations fixing no element) equals
the nearest integer to n!/e, for n ≥ 2. This is a striking identity because it
connects a purely combinatorial quantity (an integer) to a transcendental constant.

For example:
- D(2) = 1, 2!/e ≈ 0.736, round(0.736) = 1 ✓
- D(3) = 2, 3!/e ≈ 2.207, round(2.207) = 2 ✓
- D(4) = 9, 4!/e ≈ 8.829, round(8.829) = 9 ✓

### Why This Matters

- Extends the convergence formalization to a computationally useful integer identity
- Demonstrates the practical strength of the sharp error bound |D(n)/n! - e⁻¹| ≤ 1/(n+1)!
- Serves as a template for similar "nearest-integer" formulas involving transcendental constants
- The gallery proof already has the hard analysis; this bridges it to discrete math

## Known Results

### What's Already Proven

- **Gallery**: `derangements_convergence_rate`: |D(n)/n! - e⁻¹| ≤ 1/(n+1)! (the key bound)
- **Gallery**: `numDerangements_eq_factorial_mul_altSum`: identity D(n) = n! · Σ_{k≤n} (-1)^k/k!
- **Mathlib**: `Real.round` and `Int.round` with `round_eq`, `abs_sub_round`
- **Mathlib**: `Int.round_cast`, `Int.abs_sub_round_le`

### What's Still Open

Formalizing the integer rounding statement itself. The key chain is:
1. `|D(n)/n! - e⁻¹| ≤ 1/(n+1)!`   (gallery)
2. `|D(n) - n!/e| ≤ 1/(n+1)`        (multiply by n!)
3. `1/(n+1) ≤ 1/2` for n ≥ 1         (arithmetic)
4. `|D(n) - round(n!/e)| < 1/2`       (rounding characterization)
5. Therefore `D(n) = round(n!/e)`      (integers differing by < 1/2 are equal)

The mathematical argument is complete; the challenge is Lean 4 formalization,
particularly step 4→5: from a real-valued bound to an integer equality.

### Our Goal

Prove `derangements_round_eq` by importing from the gallery and applying the
rounding characterization from Mathlib.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| `derangements-convergence` | Parent: sharp error bound already proved | Alternating series, Taylor |
| `derangements-oq-03-oq-02` | Sibling: Poisson TV convergence | Probability coupling |

## Initial Thoughts

### Potential Approaches

1. **Direct import + round characterization** (recommended)
   - Import `DerangementsConvergence.derangements_convergence_rate`
   - Multiply inequality by n! to get |D(n) - n!/e| ≤ 1/(n+1)
   - Apply `Int.round_eq` or `abs_sub_round_le` from Mathlib
   - Arithmetic: 1/(n+1) < 1/2 for n ≥ 1
   - Why it might work: all ingredients exist; purely assembly work
   - Risk: Lean type coercions (ℕ → ℝ, n! vs (n! : ℝ), Real.round vs Int.round)

2. **Via alternating sum identity**
   - Use `numDerangements_eq_factorial_mul_altSum` directly
   - Show the partial sum is within 1/(n+1) of e⁻¹ · n!
   - Shorter but may duplicate gallery work

### Key Lean Issues

- Coercion from `ℕ` to `ℝ`: `Nat.cast_numDerangements`
- `Real.exp 1` vs `e`: use `Real.exp_one_gt_d9` bounds or exact API
- `Real.round` (rounds ℝ → ℝ) vs `Int.round` (rounds ℝ → ℤ): choose consistent approach
- `abs_sub_round_le` in Mathlib: `|x - round x| ≤ 1/2`

### Minimal Key Lemma Chain

```lean
-- Step 1: get the real-valued bound
have h1 : |↑(Nat.numDerangements n) / ↑(n !) - (Real.exp 1)⁻¹| ≤ 1 / ↑(n + 1)! :=
  derangements_convergence_rate n

-- Step 2: multiply by n! to get absolute distance
have h2 : |↑(Nat.numDerangements n) - ↑(n !) / Real.exp 1| ≤ 1 / ↑(n + 1) := ...

-- Step 3: 1/(n+1) ≤ 1/2 for n ≥ 1
have h3 : (1 : ℝ) / (n + 1) ≤ 1 / 2 := by norm_cast; omega

-- Step 4: combine with round characterization
exact Int.round_eq ... h2 h3
```

## Tractability Assessment

**Difficulty**: Easy-Medium

**Justification**:
- All hard mathematics is already in the gallery proof
- No new mathematical ideas required
- Pure Lean API assembly: coercions, norm_cast, field_simp
- Main challenge: navigating Lean's round/cast API

**Estimated Effort**:
- Exploration: 1-2 hours (read gallery proof, find Mathlib round lemmas)
- Implementation: 1-3 hours (assemble the chain)
- Main risk: subtle type coercion issues in Lean

## References

### Gallery
- `Proofs/DerangementsConvergence.lean` — parent proof with sharp error bound
- `derangements_convergence_rate` — the key lemma to import

### Mathlib
- `Mathlib.Algebra.Order.Round` — `Int.round`, `Real.round`, `abs_sub_round_le`
- `Mathlib.Combinatorics.Derangements.Basic` — `Nat.numDerangements`
- `Mathlib.Analysis.SpecialFunctions.ExpDeriv` — `Real.exp 1`

## Metadata

```yaml
tags:
  - combinatorics
  - derangements
  - integer-rounding
  - transcendental-constants
  - lean-api
related_proofs:
  - derangements-convergence
difficulty: easy-medium
source: gallery-gap
created: 2026-04-24
```

**Significance**: 7/10
**Tractability**: 8/10
