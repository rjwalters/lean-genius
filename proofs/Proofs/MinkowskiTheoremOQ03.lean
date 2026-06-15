/-
# Minkowski Bound on Ideal Norms: A Class-Number Estimate (OQ-03)

## What This Proves

This file makes the *geometry of numbers ⟹ ideal norm bound* connection explicit and
draws a new quantitative consequence.

Minkowski's lattice-point theorem (the gallery's `minkowski-theorem` family) feeds, through
Mathlib's mixed-embedding convex-body machinery, into the statement that **every ideal class
of a number field `K` contains an integral ideal whose absolute norm is at most the Minkowski
bound**
```
M_K = (4/π)^{r₂} · (n! / nⁿ) · √|d_K|,
```
where `n = [K : ℚ]`, `r₂ = nrComplexPlaces K`, and `d_K = discr K`.

Mathlib (`NumberField.exists_ideal_in_class_of_norm_le`) proves this with `M_K` only as a
*local notation* inside `Mathlib/NumberTheory/NumberField/ClassNumber.lean`, so the bound is
not reusable downstream. Here we:

1. Package the bound as a reusable definition `minkowskiIdealBound K`.
2. Restate the class-representative bound against that named constant.
3. Prove the **new** quantitative corollary
   ```
   classNumber K ≤ #{ I integral ideal : absNorm I ≤ ⌊M_K⌋ }.
   ```
   This is the explicit, computable upper bound on the class number that the geometry of
   numbers yields. It refines the bare finiteness of the class group
   (`NumberField.RingOfIntegers.instFintypeClassGroup`) into a concrete head-count.

## Key Techniques

- **Surjectivity from the bound**: `exists_ideal_in_class_of_norm_le` says the map
  `I ↦ ClassGroup.mk0 I`, restricted to ideals of norm `≤ ⌊M_K⌋`, is *onto* the class group.
- **Finiteness of the index set**: `Ideal.finite_setOf_absNorm_le₀` makes the domain finite.
- **Counting**: a surjection from a finite set bounds the target's cardinality
  (`Nat.card_le_card_of_surjective`), and `classNumber = Fintype.card (ClassGroup …)`.
- **Real → ℕ bound**: `Nat.le_floor` turns `(absNorm I : ℝ) ≤ M_K` into `absNorm I ≤ ⌊M_K⌋₊`.

Build status: build pending (worktree Docker cache unavailable). All referenced Mathlib
lemmas were name-checked against the pinned revision `2df2f0150c`.
-/

import Mathlib

open scoped nonZeroDivisors Real NumberField
open Module NumberField InfinitePlace Ideal Nat

namespace MinkowskiIdealBound

variable (K : Type*) [Field K] [NumberField K]

/-- The **Minkowski bound** of a number field `K`,
`M_K = (4/π)^{r₂} · (n! / nⁿ) · √|d_K|`.

This is the constant that appears (as a local notation `M K`) in
`NumberField.exists_ideal_in_class_of_norm_le`; we expose it as a reusable definition so the
ideal-norm bound can be referenced downstream. -/
noncomputable def minkowskiIdealBound : ℝ :=
  (4 / π) ^ nrComplexPlaces K *
    ((finrank ℚ K)! / (finrank ℚ K) ^ (finrank ℚ K) * Real.sqrt |discr K|)

/-- The Minkowski bound is nonnegative. -/
theorem minkowskiIdealBound_nonneg : 0 ≤ minkowskiIdealBound K := by
  unfold minkowskiIdealBound
  positivity

/-- **Minkowski's ideal-norm bound.** Every ideal class of `K` contains an integral ideal
whose absolute norm is at most the Minkowski bound `minkowskiIdealBound K`.

This is `NumberField.exists_ideal_in_class_of_norm_le` restated against the named bound; it is
the precise sense in which the geometry of numbers bounds ideal norms. -/
theorem exists_ideal_in_class_absNorm_le (C : ClassGroup (𝓞 K)) :
    ∃ I : (Ideal (𝓞 K))⁰, ClassGroup.mk0 I = C ∧
      (Ideal.absNorm (I : Ideal (𝓞 K)) : ℝ) ≤ minkowskiIdealBound K := by
  unfold minkowskiIdealBound
  exact NumberField.exists_ideal_in_class_of_norm_le C

/-- **Class-number estimate via the geometry of numbers.** The class number of `K` is at most
the number of integral ideals whose absolute norm is at most `⌊M_K⌋`.

This upgrades the finiteness of the class group to an explicit, computable head-count: the
representatives furnished by Minkowski's bound already exhaust every class. -/
theorem classNumber_le_card_absNorm_le :
    classNumber K ≤
      Nat.card {I : (Ideal (𝓞 K))⁰ //
        Ideal.absNorm (I : Ideal (𝓞 K)) ≤ ⌊minkowskiIdealBound K⌋₊} := by
  set n := ⌊minkowskiIdealBound K⌋₊ with hn
  -- The index set of ideals of norm `≤ n` is finite.
  haveI hfin : Finite {I : (Ideal (𝓞 K))⁰ // Ideal.absNorm (I : Ideal (𝓞 K)) ≤ n} :=
    (Ideal.finite_setOf_absNorm_le₀ (S := 𝓞 K) n).to_subtype
  -- Every ideal class is hit by some ideal of norm `≤ n`.
  have hsurj : Function.Surjective
      (fun I : {I : (Ideal (𝓞 K))⁰ // Ideal.absNorm (I : Ideal (𝓞 K)) ≤ n} =>
        ClassGroup.mk0 (I : (Ideal (𝓞 K))⁰)) := by
    intro C
    obtain ⟨I, hIC, hInorm⟩ := exists_ideal_in_class_absNorm_le K C
    refine ⟨⟨I, ?_⟩, hIC⟩
    rw [hn]
    exact Nat.le_floor hInorm
  -- A surjection from a finite set bounds the cardinality of the class group.
  have hcard : classNumber K = Nat.card (ClassGroup (𝓞 K)) :=
    Nat.card_eq_fintype_card.symm
  rw [hcard]
  exact Nat.card_le_card_of_surjective _ hsurj

/-- Restated as finiteness: the class group is finite (already an instance in Mathlib via
`NumberField.RingOfIntegers.instFintypeClassGroup`), here re-derived as a sanity check that the
counting bound is meaningful. -/
example : Finite (ClassGroup (𝓞 K)) := inferInstance

end MinkowskiIdealBound
