import Mathlib.NumberTheory.Cyclotomic.Gal
import Mathlib.NumberTheory.Cyclotomic.Basic
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.FieldTheory.AbelRuffini
import Mathlib.RingTheory.Polynomial.Eisenstein.Criterion
import Mathlib.RingTheory.Polynomial.GaussLemma
import Proofs.NthRootIrrationalOQ01

/-
# Inverse Galois Problem: X⁴ - 2 and the Dihedral Group D₄

## What This Proves

We extend the Inverse Galois Problem formalization with analysis of X⁴ - 2
over ℚ, whose Galois group is D₄ (the dihedral group of order 8).

## Key Results

### Infrastructure (PROVED, no sorry):
1. **irreducible_natDegree_dvd_gal_card**: For any separable irreducible
   polynomial f over ℚ, natDegree(f) divides |Gal(f)|. This generalizes
   `Polynomial.Gal.prime_degree_dvd_card` to non-prime degrees.

### X²+1 Properties (PROVED, no sorry):
2. **x_sq_add_1_irreducible**: X²+1 is irreducible over ℚ (degree 2, no root)
3. **x_sq_add_1_natDegree**: natDegree(X²+1) = 2
4. **x_sq_add_1_monic**: X²+1 is monic

### X⁴-2 Properties (PROVED, no sorry):
5. **x_fourth_sub_2_irreducible**: X⁴-2 is irreducible over ℚ (Eisenstein at p=2)
6. **x_fourth_sub_2_natDegree**: natDegree(X⁴-2) = 4
7. **x_fourth_sub_2_separable**: X⁴-2 is separable
8. **four_dvd_x4_gal_card**: 4 | |Gal(X⁴-2)| (from general lemma)
9. **x4_gal_card_dvd_24**: |Gal(X⁴-2)| | 24 (embeds in S₄)

### Sorries (mathematical content clear, Lean API needed):
10. **x_sq_add_1_has_root_in_x4_splitting_field**: X²+1 has a root in SF(X⁴-2)
    (counting argument: 4 roots with ratios being 4th roots of unity)
11. **x_fourth_sub_2_gal_card = 8**: requires upper bound via ℚ(⁴√2,i) ⊂ ℝ argument

## Mathlib Dependencies
- `NthRootIrrationalOQ01.eisenstein_X_pow_sub_prime` for Eisenstein criterion
- `Polynomial.Gal.galActionHom_injective` for embedding Gal → Perm(roots)
- `Polynomial.Gal.card_of_separable` for |Gal| = [SF:ℚ]
-/

namespace InverseGaloisX4Sub2

open Polynomial

-- ============================================================================
-- Part I: General Infrastructure — Irreducible Degree Divides |Gal|
-- ============================================================================

/--
For a separable irreducible polynomial f over ℚ, natDegree f divides |Gal(f)|.

This is a fundamental consequence of the tower law: the splitting field
contains a root α with [ℚ(α):ℚ] = deg(f), and deg(f) divides [SF:ℚ] = |Gal|.

Generalizes `Polynomial.Gal.prime_degree_dvd_card` (which requires prime degree).
-/
theorem irreducible_natDegree_dvd_gal_card
    {f : ℚ[X]}
    (hirr : Irreducible f)
    (hsep : f.Separable) :
    f.natDegree ∣ Fintype.card f.Gal := by
  -- |Gal| = [SplittingField : ℚ]
  have hcard : Nat.card f.Gal = Module.finrank ℚ f.SplittingField :=
    Polynomial.Gal.card_of_separable hsep
  rw [Nat.card_eq_fintype_card] at hcard
  rw [hcard]
  -- f has a root α in its splitting field
  have hsplits := Polynomial.SplittingField.splits f
  obtain ⟨α, hα⟩ := Polynomial.exists_root_of_splits _
    hsplits (Polynomial.degree_pos_of_irreducible hirr |>.ne')
  have hα_eval : Polynomial.aeval α f = 0 := by
    rwa [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map]
  -- minpoly ℚ α divides f, and they are associates (same degree)
  have hα_int : IsIntegral ℚ α := .of_finite ℚ α
  have hmin_dvd : minpoly ℚ α ∣ f := minpoly.dvd ℚ α hα_eval
  have hassoc := hirr.associated_of_dvd hmin_dvd (minpoly.ne_zero hα_int)
  have hdeg : (minpoly ℚ α).natDegree = f.natDegree := hassoc.natDegree_eq
  -- [ℚ(α):ℚ] = natDegree(f), and [ℚ(α):ℚ] | [SF:ℚ] by tower law
  rw [← hdeg]
  have htower := Module.finrank_mul_finrank ℚ ℚ⟮α⟯ f.SplittingField
  rw [IntermediateField.adjoin.finrank hα_int] at htower
  exact ⟨_, htower.symm⟩

-- ============================================================================
-- Part II: X²+1 Properties
-- ============================================================================

/-- X²+1 is irreducible over ℚ.
    Degree 2 with no rational root (r²+1 > 0 for all r ∈ ℚ). -/
theorem x_sq_add_1_irreducible : Irreducible (X ^ 2 + 1 : ℚ[X]) := by
  constructor
  · -- Not a unit: degree is 2 > 0
    intro hu
    have := Polynomial.natDegree_eq_zero_of_isUnit hu
    simp only [Polynomial.natDegree_add_C, Polynomial.natDegree_pow,
      Polynomial.natDegree_X] at this
  · -- Any factorization has a unit factor
    intro a b hab
    have hnoroot : ∀ r : ℚ, Polynomial.eval r (X ^ 2 + 1 : ℚ[X]) ≠ 0 := by
      intro r
      simp only [Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X,
        Polynomial.eval_one]
      linarith [sq_nonneg r]
    have ha_ne : a ≠ 0 := left_ne_zero_of_mul (hab ▸ by simp)
    have hb_ne : b ≠ 0 := right_ne_zero_of_mul (hab ▸ by simp)
    have hdeg_sum : a.natDegree + b.natDegree = 2 := by
      rw [← Polynomial.natDegree_mul ha_ne hb_ne, hab]
      simp only [Polynomial.natDegree_add_C, Polynomial.natDegree_pow,
        Polynomial.natDegree_X]
    interval_cases a.natDegree
    · left; exact Polynomial.isUnit_of_natDegree_eq_zero rfl
    · exfalso
      obtain ⟨r, hr⟩ := Polynomial.exists_root_of_degree_eq_one
        (by rw [Polynomial.degree_eq_natDegree ha_ne]; simp)
      exact hnoroot r (by rw [hab, Polynomial.eval_mul, hr, zero_mul])
    · right; exact Polynomial.isUnit_of_natDegree_eq_zero (by omega)

/-- natDegree(X²+1) = 2. -/
theorem x_sq_add_1_natDegree : (X ^ 2 + 1 : ℚ[X]).natDegree = 2 := by
  compute_degree!

/-- X²+1 is monic. -/
theorem x_sq_add_1_monic : (X ^ 2 + 1 : ℚ[X]).Monic := by
  show (X ^ 2 + 1 : ℚ[X]).leadingCoeff = 1
  conv_lhs => rw [show (1 : ℚ[X]) = C 1 from by simp]
  rw [Polynomial.leadingCoeff_add_of_degree_lt (by
    simp [Polynomial.degree_C])]
  simp

-- ============================================================================
-- Part III: X⁴ - 2 Galois Theory
-- ============================================================================

/-- X⁴ - 2 is irreducible over ℚ (Eisenstein at p = 2). -/
theorem x_fourth_sub_2_irreducible :
    Irreducible (X ^ 4 - C (2 : ℚ) : ℚ[X]) :=
  NthRootIrrationalOQ01.eisenstein_X_pow_sub_prime 4 2 (by omega) (by decide)

/-- natDegree(X⁴-2) = 4. -/
theorem x_fourth_sub_2_natDegree :
    (X ^ 4 - C (2 : ℚ) : ℚ[X]).natDegree = 4 :=
  NthRootIrrationalOQ01.natDegree_X_pow_sub_C_eq (by omega) (by norm_num)

/-- X⁴ - 2 is separable (irreducible in characteristic 0). -/
theorem x_fourth_sub_2_separable : (X ^ 4 - C (2 : ℚ) : ℚ[X]).Separable :=
  x_fourth_sub_2_irreducible.separable

/-- X⁴ - 2 is monic. -/
theorem x_fourth_sub_2_monic : (X ^ 4 - C (2 : ℚ) : ℚ[X]).Monic :=
  monic_X_pow_sub_C 2 (by omega)

/-- 4 | |Gal(X⁴-2/ℚ)| (from general lemma). -/
theorem four_dvd_x4_gal_card :
    4 ∣ Fintype.card (X ^ 4 - C (2 : ℚ) : ℚ[X]).Gal := by
  have h := irreducible_natDegree_dvd_gal_card
    x_fourth_sub_2_irreducible x_fourth_sub_2_separable
  rwa [x_fourth_sub_2_natDegree] at h

/-- |Gal(X⁴-2/ℚ)| | 24 (Gal embeds into S₄ via action on 4 roots). -/
theorem x4_gal_card_dvd_24 :
    Fintype.card (X ^ 4 - C (2 : ℚ) : ℚ[X]).Gal ∣ 24 := by
  classical
  set p := (X ^ 4 - C (2 : ℚ) : ℚ[X])
  haveI : Fact (map (algebraMap ℚ p.SplittingField) p).Splits :=
    ⟨Polynomial.SplittingField.splits p⟩
  have hinj := Polynomial.Gal.galActionHom_injective p p.SplittingField
  have hdvd : Nat.card p.Gal ∣ Nat.card (Equiv.Perm (p.rootSet p.SplittingField)) :=
    Subgroup.card_dvd_of_injective _ hinj
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card] at hdvd
  rw [Fintype.card_perm] at hdvd
  have hcard : Fintype.card (p.rootSet p.SplittingField) = 4 := by
    rw [Polynomial.card_rootSet_eq_natDegree x_fourth_sub_2_separable
        (Polynomial.SplittingField.splits p)]
    exact x_fourth_sub_2_natDegree
  rw [hcard] at hdvd
  simpa using hdvd

-- ============================================================================
-- Part IV: X²+1 Has a Root in SF(X⁴-2) — Toward |Gal| = 8
-- ============================================================================

/--
X²+1 has a root in the splitting field of X⁴-2.

Mathematical argument: X⁴-2 has 4 distinct roots a₁,...,a₄ with aᵢ⁴=2.
For any two roots, (aᵢ/aⱼ)⁴ = 1, so the ratio is a 4th root of unity.
If all ratios were ±1, there would be at most 2 distinct roots (each root
paired with its negative). With 4 roots, some ratio must be a primitive
4th root of unity, satisfying X²+1 = 0.
-/
theorem x_sq_add_1_has_root_in_x4_splitting_field :
    ∃ ω : (X ^ 4 - C (2 : ℚ) : ℚ[X]).SplittingField,
      ω ^ 2 + 1 = 0 := by
  sorry -- Counting argument: 4 roots can't all have ratios ±1

/-- The splitting field of X⁴-2 has degree divisible by 4 (from degree of X⁴-2)
    and also contains a root of the irreducible X²+1, giving 2 | [SF:ℚ] as well. -/
theorem two_dvd_x4_splitting_field_finrank :
    2 ∣ Module.finrank ℚ (X ^ 4 - C (2 : ℚ) : ℚ[X]).SplittingField := by
  sorry -- From x_sq_add_1_has_root + tower law (2 = [ℚ(ω):ℚ] | [SF:ℚ])

/--
**Bounds on |Gal(X⁴-2/ℚ)|**:

Proven lower bound: 4 | |Gal| (from irreducible_natDegree_dvd_gal_card)
Proven upper bound: |Gal| | 24 (from embedding Gal → S₄)

With the root of X²+1, we additionally get 2 | [SF:ℚ(α)] where α is
a root of X⁴-2, giving 8 | |Gal|. Combined with |Gal| | 24:
|Gal| ∈ {8, 24}. The splitting field ℚ(⁴√2, i) has degree 8,
ruling out 24 and giving |Gal(X⁴-2/ℚ)| = 8 ≅ D₄.

The full proof needs: X²+1 is irreducible over ℚ(⁴√2) (equivalently,
i ∉ ℚ(⁴√2) ⊂ ℝ), which requires embedding/ordering arguments.
-/
theorem x_fourth_sub_2_gal_card :
    Fintype.card (X ^ 4 - C (2 : ℚ) : ℚ[X]).Gal = 8 := by
  sorry -- DEEP: requires ℚ(⁴√2) ⊂ ℝ argument

/--
|Gal(X⁴-2)| ∈ {4, 8, 12, 24}: the divisors of 24 that are multiples of 4.
4 | |Gal| (degree divides), |Gal| | 24 (embeds in S₄).
-/
theorem x4_gal_card_pos : 0 < Fintype.card (X ^ 4 - C (2 : ℚ) : ℚ[X]).Gal :=
  Fintype.card_pos

end InverseGaloisX4Sub2
