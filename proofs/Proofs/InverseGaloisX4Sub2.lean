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

1. **x_fourth_sub_2_irreducible**: X⁴-2 is irreducible over ℚ (Eisenstein at p=2)
2. **x_fourth_sub_2_natDegree**: natDegree(X⁴-2) = 4
3. **x_fourth_sub_2_separable**: X⁴-2 is separable
4. **four_dvd_x4_gal_card**: 4 | |Gal(X⁴-2)| (from degree divides Gal order)
5. **x4_gal_card_dvd_24**: |Gal(X⁴-2)| | 24 (embeds in S₄)
6. **x_sq_add_1_has_root_in_x4_splitting_field**: X²+1 has a root in SF(X⁴-2) (NEW)

## Mathlib Dependencies
- `NthRootIrrationalOQ01.eisenstein_X_pow_sub_prime` for Eisenstein criterion
- `Polynomial.Gal.galActionHom_injective` for embedding Gal → Perm(roots)
- `Polynomial.Gal.card_of_separable` for |Gal| = [SF:ℚ]
-/

namespace InverseGaloisX4Sub2

open Polynomial

-- ============================================================================
-- Part I: X⁴ - 2 Galois Theory (all proved, no sorry)
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

-- ============================================================================
-- Part II: Degree divides |Gal| and |Gal| divides 24
-- ============================================================================

/-- 4 | |Gal(X⁴-2/ℚ)| (degree of irreducible polynomial divides Galois group order).

    Uses the tower law: [SF:ℚ] = [SF:ℚ(α)]·[ℚ(α):ℚ] where
    [ℚ(α):ℚ] = deg(f) = 4. -/
theorem four_dvd_x4_gal_card :
    4 ∣ Fintype.card (X ^ 4 - C (2 : ℚ) : ℚ[X]).Gal := by
  set p := (X ^ 4 - C (2 : ℚ) : ℚ[X])
  -- Use prime_degree_dvd_card generalized: for irreducible separable f,
  -- natDegree f divides |Gal(f)|.
  -- We prove this using the tower law.
  have hcard := Polynomial.Gal.card_of_separable x_fourth_sub_2_separable
  rw [Nat.card_eq_fintype_card] at hcard
  rw [hcard]
  -- Get a root from rootSet
  have hsplit := Polynomial.SplittingField.splits p
  have hcard_root : Fintype.card (p.rootSet p.SplittingField) = 4 :=
    (Polynomial.card_rootSet_eq_natDegree x_fourth_sub_2_separable hsplit).trans
      x_fourth_sub_2_natDegree
  obtain ⟨⟨α, hα⟩⟩ := Fintype.card_pos_iff.mp (by rw [hcard_root]; omega)
  have hα_eval : Polynomial.aeval α p = 0 := (Polynomial.mem_rootSet.mp hα).2
  have hα_int : IsIntegral ℚ α := .of_finite ℚ α
  -- [ℚ(α):ℚ] = natDegree(minpoly ℚ α)
  -- minpoly ℚ α divides f (since α is a root of f)
  have hmin_dvd : minpoly ℚ α ∣ p := minpoly.dvd ℚ α hα_eval
  -- Since f is irreducible and minpoly divides it, natDegree(minpoly) = natDegree(f) = 4
  have hmin_ndeg : (minpoly ℚ α).natDegree = 4 := by
    have h := x_fourth_sub_2_irreducible.eq_one_or_self_of_associated_of_dvd
      (minpoly.irreducible hα_int) hmin_dvd
    rcases h with h | h
    · exact absurd h (minpoly.ne_one ℚ α)
    · rw [← x_fourth_sub_2_natDegree]; exact h.natDegree_eq
  -- [ℚ(α):ℚ] = 4 divides [SF:ℚ] by tower law
  rw [show (4 : ℕ) = (minpoly ℚ α).natDegree from hmin_ndeg.symm]
  have htower := Module.finrank_mul_finrank ℚ ℚ⟮α⟯ p.SplittingField
  rw [IntermediateField.adjoin.finrank hα_int] at htower
  exact ⟨_, htower.symm⟩

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
-- Part III: X²+1 Has a Root in SF(X⁴-2)
-- ============================================================================

/--
**X²+1 has a root in the splitting field of X⁴-2.**

Mathematical argument: If a, b are distinct roots of X⁴-2 with b ≠ 0,
then (a/b)⁴ = a⁴/b⁴ = 2/2 = 1. So a/b is a 4th root of unity.
Since a ≠ b, a/b ≠ 1. If a/b = -1 then a = -b.
With 4 distinct roots, at most 2 can be ±b, so some root a satisfies
a/b ∉ {1, -1}, giving (a/b)⁴ = 1, (a/b)² ≠ 1.
From (a/b)⁴ - 1 = ((a/b)² - 1)((a/b)² + 1) = 0, we get (a/b)² + 1 = 0.
-/
theorem x_sq_add_1_has_root_in_x4_splitting_field :
    ∃ ω : (X ^ 4 - C (2 : ℚ) : ℚ[X]).SplittingField,
      ω ^ 2 + 1 = 0 := by
  set p := (X ^ 4 - C (2 : ℚ) : ℚ[X])
  have hsep := x_fourth_sub_2_separable
  have hsplit := Polynomial.SplittingField.splits p
  have hcard : Fintype.card (p.rootSet p.SplittingField) = 4 :=
    (Polynomial.card_rootSet_eq_natDegree hsep hsplit).trans x_fourth_sub_2_natDegree
  -- Get two distinct roots a, b
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩, hab⟩ :=
    Fintype.exists_pair_of_one_lt_card (by rw [hcard]; omega)
  have ha_eval : Polynomial.aeval a p = 0 := (Polynomial.mem_rootSet.mp ha).2
  have hb_eval : Polynomial.aeval b p = 0 := (Polynomial.mem_rootSet.mp hb).2
  -- Compute: aeval x p = x⁴ - 2
  have aeval_eq : ∀ x : p.SplittingField,
      Polynomial.aeval x p = x ^ 4 - algebraMap ℚ _ 2 := by
    intro x; simp [p, map_sub, map_pow, aeval_X, aeval_C]
  have ha4 : a ^ 4 = algebraMap ℚ _ 2 :=
    sub_eq_zero.mp (by rw [← aeval_eq]; exact ha_eval)
  have hb4 : b ^ 4 = algebraMap ℚ _ 2 :=
    sub_eq_zero.mp (by rw [← aeval_eq]; exact hb_eval)
  -- b ≠ 0 (since b⁴ = 2 ≠ 0)
  have hb_ne : b ≠ 0 := by
    intro h; simp [h] at hb4
  -- The ratio c = a * b⁻¹ satisfies c⁴ = 1
  set c := a * b⁻¹ with hc_def
  have hc4 : c ^ 4 = 1 := by
    rw [hc_def, mul_pow, inv_pow, ha4, hb4]
    exact mul_inv_cancel₀ (by simp [hb4])
  -- c ≠ 1 (since a ≠ b)
  have hc_ne_1 : c ≠ 1 := by
    intro h
    have := congr_arg (· * b) h
    simp [hc_def, mul_assoc, inv_mul_cancel₀ hb_ne] at this
    exact hab (Subtype.ext this)
  -- From c⁴ - 1 = (c² - 1)(c² + 1) = 0
  have hc4_sub : c ^ 4 - 1 = 0 := by rw [hc4]; ring
  have hfactor : c ^ 4 - 1 = (c ^ 2 - 1) * (c ^ 2 + 1) := by ring
  rw [hfactor] at hc4_sub
  rcases mul_eq_zero.mp hc4_sub with h | h
  · -- Case c² = 1, so c = ±1
    -- c ≠ 1, and if c = -1 then a = -b
    -- We need to handle this case by getting a THIRD root
    -- that isn't ±b, which exists since there are 4 distinct roots.
    -- For now, if c² = 1 but c ≠ 1, then c = -1.
    have hc_neg1 : c = -1 := by
      have : c ^ 2 = 1 := by linarith
      have : (c - 1) * (c + 1) = 0 := by nlinarith
      rcases mul_eq_zero.mp this with h1 | h1
      · exact absurd (sub_eq_zero.mp h1) hc_ne_1
      · linarith
    -- c = -1 means a = -b. Get a third root different from ±b.
    -- There are 4 roots, and ±b accounts for at most 2.
    -- We need a root r with r ≠ b and r ≠ -b = a.
    -- rootSet has card 4, so there's a third distinct element.
    have hcard3 : 2 < Fintype.card (p.rootSet p.SplittingField) := by
      rw [hcard]; omega
    -- The elements b, a are distinct in rootSet. Get a third.
    have : ∃ ⟨r, hr⟩ : p.rootSet p.SplittingField, r ≠ a ∧ r ≠ b := by
      by_contra hall
      push_neg at hall
      -- Every root is either a or b
      have : Fintype.card (p.rootSet p.SplittingField) ≤ 2 := by
        rw [show (2 : ℕ) = Finset.card {(⟨a, ha⟩ : p.rootSet p.SplittingField),
            ⟨b, hb⟩} from by simp [Subtype.mk_ne_mk.mpr (Subtype.coe_injective.ne (by
              intro h; exact hab (Subtype.ext h)))]]
        exact Fintype.card_le_of_surjective (fun x => ⟨x, Finset.mem_insert.mpr
          (by rcases hall x with h | h <;> simp [Subtype.ext h])⟩) (fun ⟨x, hx⟩ => by
          simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with rfl | rfl
          · exact ⟨⟨a, ha⟩, by simp⟩
          · exact ⟨⟨b, hb⟩, by simp⟩)
      omega
    obtain ⟨⟨r, hr⟩, hr_ne_a, hr_ne_b⟩ := this
    have hr_eval : Polynomial.aeval r p = 0 := (Polynomial.mem_rootSet.mp hr).2
    have hr4 : r ^ 4 = algebraMap ℚ _ 2 :=
      sub_eq_zero.mp (by rw [← aeval_eq]; exact hr_eval)
    -- d = r * b⁻¹ is a 4th root of unity
    set d := r * b⁻¹
    have hd4 : d ^ 4 = 1 := by
      rw [mul_pow, inv_pow, hr4, hb4]; exact mul_inv_cancel₀ (by simp [hb4])
    have hd_ne_1 : d ≠ 1 := by
      intro h
      have := congr_arg (· * b) h
      simp [mul_assoc, inv_mul_cancel₀ hb_ne] at this
      exact hr_ne_b this
    -- d ≠ -1 (since r ≠ -b = a)
    have hd_ne_neg1 : d ≠ -1 := by
      intro h
      have := congr_arg (· * b) h
      simp [mul_assoc, inv_mul_cancel₀ hb_ne] at this
      have : r = a := by linarith [hc_neg1, show a = -(1 : _) * b from by
        rw [← hc_def, hc_neg1]; ring]
      exact hr_ne_a this
    -- d⁴ = 1, d ≠ ±1, so d² ≠ 1
    have hd2_ne_1 : d ^ 2 ≠ 1 := by
      intro h
      have : (d - 1) * (d + 1) = 0 := by nlinarith
      rcases mul_eq_zero.mp this with h1 | h1
      · exact hd_ne_1 (sub_eq_zero.mp h1)
      · exact hd_ne_neg1 (by linarith)
    -- d⁴ - 1 = (d² - 1)(d² + 1) = 0, so d² + 1 = 0
    have hd4_sub : d ^ 4 - 1 = 0 := by rw [hd4]; ring
    have : (d ^ 2 - 1) * (d ^ 2 + 1) = 0 := by nlinarith
    exact ⟨d, by
      rcases mul_eq_zero.mp this with h1 | h1
      · exact absurd (by linarith : d ^ 2 = 1) hd2_ne_1
      · linarith⟩
  · -- Case c² + 1 = 0, so ω = c works
    exact ⟨c, by linarith⟩

-- ============================================================================
-- Part IV: Remaining Results
-- ============================================================================

/-- The splitting field of X⁴-2 has degree divisible by 2 (contains a root of X²+1). -/
theorem two_dvd_x4_splitting_field_finrank :
    2 ∣ Module.finrank ℚ (X ^ 4 - C (2 : ℚ) : ℚ[X]).SplittingField := by
  have hcard := Polynomial.Gal.card_of_separable x_fourth_sub_2_separable
  rw [Nat.card_eq_fintype_card] at hcard
  have h4 : 4 ∣ Module.finrank ℚ (X ^ 4 - C (2 : ℚ) : ℚ[X]).SplittingField := by
    rw [← hcard]; exact four_dvd_x4_gal_card
  exact dvd_trans (⟨2, rfl⟩ : (2 : ℕ) ∣ 4) h4

/-- |Gal(X⁴-2/ℚ)| = 8 (the dihedral group D₄). -/
theorem x_fourth_sub_2_gal_card :
    Fintype.card (X ^ 4 - C (2 : ℚ) : ℚ[X]).Gal = 8 := by
  sorry -- DEEP: requires ℚ(⁴√2) ⊂ ℝ argument

/-- |Gal(X⁴-2)| > 0. -/
theorem x4_gal_card_pos : 0 < Fintype.card (X ^ 4 - C (2 : ℚ) : ℚ[X]).Gal :=
  Fintype.card_pos

end InverseGaloisX4Sub2
