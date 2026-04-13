# Problem: Dedekind's Theorem: mod-p Factorization to Galois Cycle Types

**Slug**: inverse-galois-oq-06-oq-01
**Created**: 2026-04-04T02:46:02-07:00
**Status**: Active
**Source**: inverse-galois-oq-06 <!-- gallery-gap -->

## Problem Statement

Formalize Dedekind's theorem (mod-p factorization ↦ cycle types in Gal) in Mathlib, eliminating the last axiom `three_dvd_gal_card` and making the A₅-realizability entry fully verified.

Dedekind's theorem: if f(x) ∈ ℤ[x] is irreducible and factors mod p as f ≡ f₁·…·fₙ (mod p) where deg fᵢ = dᵢ, then Gal(f/ℚ) contains a permutation of cycle type (d₁,...,dₙ).

### Formal Goal

```lean
theorem dedekind_cycle_type (f : ℤ[X]) (p : ℕ) [hp : Fact (Nat.Prime p)] 
    (h : Irreducible f)
    (factors : (f.map (Int.castRingHom (ZMod p))) = ∏ i, f_i i) :
    ∃ σ ∈ Gal(f.SplittingField, ℚ), 
      cycleType σ = (factors.map Polynomial.natDegree).toFinset := by
  sorry
```

## Context

- Source proof: `inverse-galois-oq-06` (Inverse Galois OQ-06: A₅ is Realizable over ℚ)
- Category: extension
- Tractability: challenging
- This would eliminate the last `axiom` in the A₅ realizability proof

## First Steps

1. Check current Mathlib `NumberField.Galois` for Frobenius element support
2. Check `Mathlib.FieldTheory.Galois` for cycle type tools
3. Survey Dedekind criterion formulations in Lean/Mathlib PRs
