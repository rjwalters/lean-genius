/-
Copyright (c) 2026 RJ Walters. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RJ Walters
-/

/-!
# Heartbeat Optimization Proposal for SpernerMathlib4.lean

## Summary

This file documents a proposed optimization for the
`Finset.even_card_of_fpf_invol` theorem in `SpernerMathlib4.lean`.

## Problem

`SpernerMathlib4.lean` uses `maxHeartbeats 1600000` (8x default).
The main blocker for Mathlib acceptance is reducing this to ≤ 400000.

The most expensive proof in the file is `Finset.even_card_of_fpf_invol`
(lines 57–109), which uses `Finset.strongInduction`. This is known to
be slow in Lean elaboration.

## Proposed Fix: Use `Finset.sum_involution` from Mathlib

`Finset.sum_involution` lives in
`Mathlib.Algebra.BigOperators.Group.Finset.Basic`. It states:

  If `g : ∀ a ∈ s, ι` is an involution on `s` with `f a + f (g a ha) = 0`
  and `f a ≠ 0 → g a ha ≠ a`, then `∑ x ∈ s, f x = 0`.

We apply this with:
  - `s = S`
  - `f = fun _ => (1 : ZMod 2)`
  - `g = fun a _ => invol a` (our fixed-point-free involution)

Then `∑ _ ∈ S, (1 : ZMod 2) = S.card • 1 = (S.card : ZMod 2)`.
Getting this equal to 0 gives `Even S.card`.

## Optimized Proof (~12 lines vs 53 lines)

```lean
/-- A fixed-point-free involution on a finset has even
cardinality. Proof via `Finset.sum_involution` in `ZMod 2`. -/
theorem Finset.even_card_of_fpf_invol {α : Type*}
    [DecidableEq α] (S : Finset α) (f : α → α)
    (hInv : ∀ x ∈ S, f (f x) = x)
    (hMem : ∀ x ∈ S, f x ∈ S)
    (hNe : ∀ x ∈ S, f x ≠ x) :
    Even S.card := by
  -- Strategy: ∑ _ ∈ S, (1 : ZMod 2) = 0, so S.card ≡ 0 [MOD 2]
  have hsum : ∑ _ ∈ S, (1 : ZMod 2) = 0 :=
    Finset.sum_involution (fun a _ => f a)
      (fun _ _ => by decide)           -- 1 + 1 = 0 in ZMod 2
      (fun a ha _ => hNe a ha)         -- f a ≠ a (since 1 ≠ 0)
      hMem                              -- f a ∈ S for a ∈ S
      hInv                              -- f (f a) = a for a ∈ S
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one] at hsum
  rw [Nat.even_iff, ← Nat.dvd_iff_mod_eq_zero]
  exact (ZMod.natCast_zmod_eq_zero_iff_dvd _ 2).mp hsum
```

## Key Insight

The `strongInduction` used in the original proof is expensive to elaborate
because it constructs an explicit recursion scheme over Finsets.
`Finset.sum_involution` delegates this to a pre-compiled Mathlib lemma,
avoiding the elaboration overhead in our file.

Expected heartbeat reduction: 30-50% of the total (since the involution
proof is a large fraction of the file's proof obligations).

## Other Potential Optimizations

1. **`exists_of_sum_eq_one`** (lines 143–163):
   May be replaceable by `Finset.sum_eq_one_iff_of_nonneg` or similar.
   Estimated savings: minor.

2. **`surjection_unique_dup_fiber`** (lines 168–226):
   Long proof, but mostly `omega`-solvable steps. Adding type annotations
   to help elaboration may help more than restructuring.

3. **Granular imports** instead of `import Mathlib`:
   For Mathlib PRs, specific imports reduce compilation time.
   Needed imports:
   - `Mathlib.Data.Finset.Card`
   - `Mathlib.Data.Finset.Basic`
   - `Mathlib.Data.ZMod.Basic`
   - `Mathlib.Algebra.BigOperators.Group.Finset.Basic`
   This alone could reduce heartbeats by 20-30%.

## Next Steps

1. Test the optimized `even_card_of_fpf_invol` proof.
2. If successful, replace in `SpernerMathlib4.lean`.
3. Switch from `import Mathlib` to granular imports.
4. Re-measure heartbeats.
5. Target: ≤ 400000 heartbeats total.

## Status

- [ ] Test `Finset.sum_involution` approach
- [ ] Profile which sections are most expensive (using `set_option profiler true`)
- [ ] Switch to granular imports
- [ ] Submit revised PR

## References

- `Mathlib.Algebra.BigOperators.Group.Finset.Basic` line 673: `prod_involution`
  (additive dual: `sum_involution`)
- mathlib4#25231: current PR (Sperner's lemma)
- Dillies/SproutSeeds: reviewer contact
-/
