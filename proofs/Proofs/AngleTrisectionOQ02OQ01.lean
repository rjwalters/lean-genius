/-
  Angle Trisection - Open Question 02 - Sub-question 01:
  Connecting Galois Groups to Degree Conditions via Mathlib

  Main contribution: Proves `galois_2group_implies_degree_pow2` — currently an axiom
  in AngleTrisectionOQ02.lean — by generalizing Mathlib's `prime_degree_dvd_card`
  to show that natDegree divides |Gal| for ALL irreducible polynomials.

  Parent: AngleTrisectionOQ02.lean (6 axioms → 5 after this file)
  Related: AngleTrisectionOQ01.lean (degree characterization, 0 axioms)
-/

import Mathlib
import Proofs.AngleTrisectionOQ01

open Polynomial

open scoped IntermediateField

namespace AngleTrisectionOQ02OQ01

/-
## Part I: natDegree Divides |Gal| for Irreducible Polynomials
-/

/-- For any irreducible polynomial over a CharZero field, natDegree(p) divides |Gal(p)|.
    Generalizes `Polynomial.Gal.prime_degree_dvd_card` to all degrees.

    Proof: tower law on F ⊂ F⟮α⟯ ⊂ SplittingField(p). -/
theorem natDegree_dvd_card_gal {F : Type*} [Field F] [CharZero F]
    {p : F[X]} (p_irr : Irreducible p) :
    p.natDegree ∣ Nat.card p.Gal := by
  rw [Gal.card_of_separable p_irr.separable]
  have hp : p.degree ≠ 0 := by
    intro h
    exact absurd (natDegree_eq_zero_iff_degree_le_zero.mpr (le_of_eq h))
      (Irreducible.natDegree_pos p_irr).ne'
  -- In v4.26.0, rootOfSplits takes (hf : f.Splits) (hfd : f.degree ≠ 0)
  -- where f = p.map (algebraMap F E) and hf = SplittingField.splits p
  have hp' : (p.map (algebraMap F p.SplittingField)).degree ≠ 0 := by
    rwa [degree_map_eq_of_injective (RingHom.injective (algebraMap F p.SplittingField))]
  let α : p.SplittingField :=
    rootOfSplits (SplittingField.splits p) hp'
  have hα : IsIntegral F α := .of_finite F α
  use Module.finrank F⟮α⟯ p.SplittingField
  suffices (minpoly F α).natDegree = p.natDegree by
    letI _ : AddCommGroup F⟮α⟯ := Ring.toAddCommGroup
    rw [← Module.finrank_mul_finrank F F⟮α⟯ p.SplittingField,
      IntermediateField.adjoin.finrank hα, this]
  suffices minpoly F α ∣ p by
    have key := (minpoly.irreducible hα).dvd_symm p_irr this
    apply le_antisymm
    · exact natDegree_le_of_dvd this p_irr.ne_zero
    · exact natDegree_le_of_dvd key (minpoly.ne_zero hα)
  apply minpoly.dvd F α
  -- α is a root of p: aeval α p = eval₂ (algebraMap F E) α p = (p.map f).eval α
  rw [aeval_def, eval₂_eq_eval_map]
  exact eval_rootOfSplits (SplittingField.splits p) hp'

/-
## Part II: 2-Group Galois → Degree Divides Power of 2
-/

/-- If Gal(minpoly(ℚ,α)) is a 2-group, then natDegree(minpoly ℚ α) divides 2^n
    for some n. Eliminates axiom `galois_2group_implies_degree_pow2` from OQ02. -/
theorem galois_2group_implies_degree_pow2 (α : ℝ) (hα : IsIntegral ℚ α)
    (hGal : IsPGroup 2 (minpoly ℚ α).Gal) :
    ∃ n : ℕ, (minpoly ℚ α).natDegree ∣ 2 ^ n := by
  have hirr := minpoly.irreducible hα
  have hdvd := natDegree_dvd_card_gal hirr
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hGal
  exact ⟨n, dvd_trans hdvd (hn ▸ dvd_refl _)⟩

/-- Stronger: natDegree IS a power of 2.
    Uses `dvd_pow_two_is_pow_two` from AngleTrisectionOQ01. -/
theorem galois_2group_implies_degree_is_pow2 (α : ℝ) (hα : IsIntegral ℚ α)
    (hGal : IsPGroup 2 (minpoly ℚ α).Gal) :
    ∃ k : ℕ, (minpoly ℚ α).natDegree = 2 ^ k := by
  obtain ⟨n, hdvd⟩ := galois_2group_implies_degree_pow2 α hα hGal
  have hpos : 0 < (minpoly ℚ α).natDegree :=
    Irreducible.natDegree_pos (minpoly.irreducible hα)
  exact AngleTrisectionOQ01.dvd_pow_two_is_pow_two _ n hpos hdvd

/-
## Part III: Connecting OQ02 to OQ01
-/

/-- α ∈ ℝ is constructible from ℚ if it lies in a finite extension K of ℚ inside ℝ
    with [K:ℚ] a power of 2. (From OQ02 for self-containedness.) -/
def IsConstructibleFromQ (α : ℝ) : Prop :=
  ∃ (K : IntermediateField ℚ ℝ),
    FiniteDimensional ℚ K ∧
    (∃ n : ℕ, Module.finrank ℚ K = 2 ^ n) ∧
    α ∈ K

/-- The Galois criterion (2-group Gal) implies the degree criterion (degree = 2^k). -/
theorem galois_criterion_implies_degree_criterion (α : ℝ) (hα : IsIntegral ℚ α)
    (hGal : IsPGroup 2 (minpoly ℚ α).Gal) :
    ∃ k : ℕ, (minpoly ℚ α).natDegree = 2 ^ k :=
  galois_2group_implies_degree_is_pow2 α hα hGal

/-
## Summary

### Theorems proved (0 sorries, 0 axioms):
1. `natDegree_dvd_card_gal` — natDegree | |Gal| for irreducible polys over CharZero
2. `galois_2group_implies_degree_pow2` — 2-group Gal → natDegree | 2^n
3. `galois_2group_implies_degree_is_pow2` — 2-group Gal → natDegree = 2^k (stronger)
4. `galois_criterion_implies_degree_criterion` — connects OQ02 to OQ01

### Axiom eliminated from OQ02: 1 of 6
- `galois_2group_implies_degree_pow2` is now proved
-/

end AngleTrisectionOQ02OQ01
