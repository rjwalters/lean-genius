import Mathlib
import Proofs.NthRootIrrationalOQ01

/-
# Inverse Galois Problem: F₂₀ Realization via X⁵-2

This file proves |Gal(X⁵-2/ℚ)| = 20, extending the Inverse Galois Problem
formalization with a third non-trivial polynomial Galois group computation.

The Galois group of X⁵-2 over ℚ is the Frobenius group F₂₀ = ℤ/5ℤ ⋊ ℤ/4ℤ,
which has order 20. This is a solvable group, consistent with X⁵-2 being
solvable by radicals (its roots are ⁵√2 · ζ₅ᵏ).

## Proof Strategy

**Lower bound** (20 | |Gal|):
1. X⁵-2 is irreducible of degree 5, so 5 | |Gal|
2. The splitting field contains a root of Φ₅ (ratio of two distinct roots),
   and Φ₅ is irreducible of degree 4, so 4 | finrank
3. gcd(4,5) = 1, so 20 | |Gal|

**Upper bound** (|Gal| | 20):
All roots of X⁵-2 lie in ℚ(α, ζ₅) where α is a root and ζ₅ is a primitive
5th root of unity. By IsPrimitiveRoot, every 5th root of unity is a power
of ζ₅, so all roots α·ζ₅ᵏ ∈ ℚ(α,ζ₅). Tower law: [ℚ(α,ζ₅):ℚ] ≤ 5·4 = 20.

## Series
- X³-2: |Gal| = 6 = |S₃| (InverseGalois.lean)
- X⁴-2: |Gal| = 8 = |D₄| (InverseGaloisD4.lean)
- X⁵-2: |Gal| = 20 = |F₂₀| (this file)
-/

namespace InverseGaloisF20

open Polynomial

-- ============================================================================
-- Part I: Basic Properties of X⁵-2
-- ============================================================================

/-- X⁵-2 is irreducible over ℚ (Eisenstein at p = 2). -/
theorem x_fifth_sub_2_irreducible :
    Irreducible (X ^ 5 - C (2 : ℚ) : ℚ[X]) :=
  NthRootIrrationalOQ01.eisenstein_X_pow_sub_prime 5 2 (by omega) (by decide)

/-- X⁵-2 has degree 5. -/
theorem x_fifth_sub_2_natDegree :
    (X ^ 5 - C (2 : ℚ) : ℚ[X]).natDegree = 5 :=
  NthRootIrrationalOQ01.natDegree_X_pow_sub_C_eq (by omega) (by norm_num)

/-- X⁵-2 is separable (irreducible in characteristic 0). -/
theorem x_fifth_sub_2_separable : (X ^ 5 - C (2 : ℚ) : ℚ[X]).Separable :=
  x_fifth_sub_2_irreducible.separable

/-- X⁵-2 is monic. -/
theorem x_fifth_sub_2_monic : (X ^ 5 - C (2 : ℚ) : ℚ[X]).Monic :=
  monic_X_pow_sub_C 2 (by omega)

-- ============================================================================
-- Part II: Lower Bound — 5 | |Gal| and |Gal| | 120
-- ============================================================================

/-- 5 | |Gal(X⁵-2/ℚ)| — the prime degree divides the Galois group order. -/
theorem five_dvd_gal_card :
    5 ∣ Fintype.card (X ^ 5 - C (2 : ℚ) : ℚ[X]).Gal := by
  have h := Polynomial.Gal.prime_degree_dvd_card x_fifth_sub_2_irreducible
    (by rw [x_fifth_sub_2_natDegree]; decide)
  rw [x_fifth_sub_2_natDegree, Nat.card_eq_fintype_card] at h
  exact h

/-- |Gal(X⁵-2/ℚ)| | 120 — the Galois group embeds in S₅ via action on roots. -/
theorem gal_card_dvd_120 :
    Fintype.card (X ^ 5 - C (2 : ℚ) : ℚ[X]).Gal ∣ 120 := by
  classical
  set p := (X ^ 5 - C (2 : ℚ) : ℚ[X])
  haveI : Fact (map (algebraMap ℚ p.SplittingField) p).Splits :=
    ⟨Polynomial.SplittingField.splits p⟩
  have hinj := Polynomial.Gal.galActionHom_injective p p.SplittingField
  have hdvd : Nat.card p.Gal ∣ Nat.card (Equiv.Perm (p.rootSet p.SplittingField)) :=
    Subgroup.card_dvd_of_injective _ hinj
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card] at hdvd
  rw [Fintype.card_perm] at hdvd
  have hcard : Fintype.card (p.rootSet p.SplittingField) = 5 := by
    rw [Polynomial.card_rootSet_eq_natDegree x_fifth_sub_2_separable
        (Polynomial.SplittingField.splits p)]
    exact x_fifth_sub_2_natDegree
  rw [hcard] at hdvd
  simpa using hdvd

-- ============================================================================
-- Part III: Φ₅ Has a Root in the Splitting Field
-- ============================================================================

/-- In a field, if a⁵ = b⁵ and a ≠ b with b ≠ 0, then (a/b)⁴+(a/b)³+(a/b)²+(a/b)+1=0. -/
theorem fifth_root_ratio_satisfies_cyclotomic5
    {K : Type*} [Field K] {a b : K} (ha5 : a ^ 5 = b ^ 5) (hab : a ≠ b) (hb : b ≠ 0) :
    (a * b⁻¹) ^ 4 + (a * b⁻¹) ^ 3 + (a * b⁻¹) ^ 2 + (a * b⁻¹) + 1 = 0 := by
  set c := a * b⁻¹
  have hc5 : c ^ 5 = 1 := by
    simp only [c]; rw [mul_pow, inv_pow, ha5]; field_simp
  have hc_ne_1 : c ≠ 1 := by
    simp only [c]; intro h
    have := congr_arg (· * b) h
    simp [mul_assoc, inv_mul_cancel₀ hb] at this
    exact hab this
  have h0 : c ^ 5 - 1 = 0 := by rw [hc5]; ring
  have hfactor : c ^ 5 - 1 = (c - 1) * (c ^ 4 + c ^ 3 + c ^ 2 + c + 1) := by ring
  rw [hfactor] at h0
  exact (mul_eq_zero.mp h0).resolve_left (sub_ne_zero.mpr hc_ne_1)

/-- The 5th cyclotomic polynomial Φ₅ has a root in the splitting field of X⁵-2. -/
theorem cyclotomic_5_has_root_in_splitting_field :
    ∃ ζ : (X ^ 5 - C (2 : ℚ) : ℚ[X]).SplittingField,
      ζ ^ 4 + ζ ^ 3 + ζ ^ 2 + ζ + 1 = 0 := by
  set p := (X ^ 5 - C (2 : ℚ) : ℚ[X])
  have hsep := x_fifth_sub_2_separable
  have hsplit := Polynomial.SplittingField.splits p
  have hcard : Fintype.card (p.rootSet p.SplittingField) = 5 :=
    (Polynomial.card_rootSet_eq_natDegree hsep hsplit).trans x_fifth_sub_2_natDegree
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩, hab⟩ :=
    Fintype.exists_pair_of_one_lt_card (by rw [hcard]; omega)
  have ha_eval : Polynomial.aeval a p = 0 := (Polynomial.mem_rootSet.mp ha).2
  have hb_eval : Polynomial.aeval b p = 0 := (Polynomial.mem_rootSet.mp hb).2
  have aeval_eq : ∀ x : p.SplittingField,
      Polynomial.aeval x p = x ^ 5 - algebraMap ℚ _ 2 := by
    intro x; simp [p, map_sub, map_pow, aeval_X, aeval_C]
  have ha5 : a ^ 5 = algebraMap ℚ _ 2 :=
    sub_eq_zero.mp (by rw [← aeval_eq]; exact ha_eval)
  have hb5 : b ^ 5 = algebraMap ℚ _ 2 :=
    sub_eq_zero.mp (by rw [← aeval_eq]; exact hb_eval)
  have hab' : a ≠ b := fun h => hab (Subtype.ext h)
  have hb_ne : b ≠ 0 := by
    intro h; rw [h, zero_pow (by omega)] at hb5; simp [map_ofNat] at hb5
  exact ⟨a * b⁻¹, fifth_root_ratio_satisfies_cyclotomic5
    (by rw [ha5, hb5]) hab' hb_ne⟩

-- ============================================================================
-- Part IV: 4 | finrank — From Φ₅ Irreducible of Degree 4
-- ============================================================================

/-- Φ₅ = X⁴+X³+X²+X+1 is irreducible over ℚ (as cyclotomic 5). -/
theorem cyclotomic_5_irreducible :
    Irreducible (X ^ 4 + X ^ 3 + X ^ 2 + X + 1 : ℚ[X]) := by
  have h : X ^ 4 + X ^ 3 + X ^ 2 + X + 1 = Polynomial.cyclotomic 5 ℚ := by
    haveI : Fact (Nat.Prime 5) := ⟨by decide⟩
    have h1 := cyclotomic_prime (R := ℚ) (p := 5)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, pow_zero, pow_one, zero_add] at h1
    rw [h1]; ring
  rw [h]
  exact Polynomial.cyclotomic.irreducible_rat (by norm_num)

/-- Φ₅ has degree 4. -/
theorem cyclotomic_5_natDegree :
    (X ^ 4 + X ^ 3 + X ^ 2 + X + 1 : ℚ[X]).natDegree = 4 := by
  have h : X ^ 4 + X ^ 3 + X ^ 2 + X + 1 = Polynomial.cyclotomic 5 ℚ := by
    haveI : Fact (Nat.Prime 5) := ⟨by decide⟩
    have h1 := cyclotomic_prime (R := ℚ) (p := 5)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, pow_zero, pow_one, zero_add] at h1
    rw [h1]; ring
  rw [h, Polynomial.natDegree_cyclotomic]
  decide

/-- Φ₅ is monic. -/
theorem cyclotomic_5_monic :
    (X ^ 4 + X ^ 3 + X ^ 2 + X + 1 : ℚ[X]).Monic := by
  have h : X ^ 4 + X ^ 3 + X ^ 2 + X + 1 = Polynomial.cyclotomic 5 ℚ := by
    haveI : Fact (Nat.Prime 5) := ⟨by decide⟩
    have h1 := cyclotomic_prime (R := ℚ) (p := 5)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, pow_zero, pow_one, zero_add] at h1
    rw [h1]; ring
  rw [h]; exact Polynomial.cyclotomic.monic 5 ℚ

/-- 4 | [SplittingField(X⁵-2) : ℚ] — from Φ₅ irreducible of degree 4 with root in SF. -/
theorem four_dvd_splitting_field_finrank :
    4 ∣ Module.finrank ℚ (X ^ 5 - C (2 : ℚ) : ℚ[X]).SplittingField := by
  obtain ⟨ζ, hζ⟩ := cyclotomic_5_has_root_in_splitting_field
  have haeval : Polynomial.aeval ζ (X ^ 4 + X ^ 3 + X ^ 2 + X + 1 : ℚ[X]) = 0 := by
    simp only [map_add, map_pow, map_one, aeval_X]; exact hζ
  have hmin : (X ^ 4 + X ^ 3 + X ^ 2 + X + 1 : ℚ[X]) = minpoly ℚ ζ :=
    minpoly.eq_of_irreducible_of_monic cyclotomic_5_irreducible haeval cyclotomic_5_monic
  have hdeg : (minpoly ℚ ζ).natDegree = 4 := by rw [← hmin, cyclotomic_5_natDegree]
  have hζ_int : IsIntegral ℚ ζ := .of_finite ℚ ζ
  have hadj_fr := IntermediateField.adjoin.finrank hζ_int
  rw [hdeg] at hadj_fr
  have htower := Module.finrank_mul_finrank ℚ
    (IntermediateField.adjoin ℚ {ζ})
    (X ^ 5 - C (2 : ℚ) : ℚ[X]).SplittingField
  rw [hadj_fr] at htower
  exact ⟨_, htower.symm⟩

/-- 20 | |Gal(X⁵-2/ℚ)| — from 5|n, 4|n, and gcd(4,5) = 1. -/
theorem twenty_dvd_gal_card :
    20 ∣ Fintype.card (X ^ 5 - C (2 : ℚ) : ℚ[X]).Gal := by
  have hcard_eq : Fintype.card (X ^ 5 - C (2 : ℚ) : ℚ[X]).Gal =
      Module.finrank ℚ (X ^ 5 - C (2 : ℚ) : ℚ[X]).SplittingField := by
    have := Polynomial.Gal.card_of_separable x_fifth_sub_2_separable
    rw [Nat.card_eq_fintype_card] at this; exact this
  rw [hcard_eq]
  have h5 : 5 ∣ Module.finrank ℚ (X ^ 5 - C (2 : ℚ) : ℚ[X]).SplittingField := by
    rw [← hcard_eq]; exact five_dvd_gal_card
  have h4 : 4 ∣ Module.finrank ℚ (X ^ 5 - C (2 : ℚ) : ℚ[X]).SplittingField :=
    four_dvd_splitting_field_finrank
  have hcop : Nat.Coprime 4 5 := by decide
  have h20 := hcop.mul_dvd_of_dvd_of_dvd h4 h5
  simpa using h20

-- ============================================================================
-- Part V: Upper Bound — |Gal| | 20
-- ============================================================================

/-- If ζ⁴+ζ³+ζ²+ζ+1 = 0 then ζ⁵ = 1. -/
theorem pow5_eq_one_of_cyclotomic5_root {K : Type*} [Field K] {ζ : K}
    (hζ : ζ ^ 4 + ζ ^ 3 + ζ ^ 2 + ζ + 1 = 0) : ζ ^ 5 = 1 := by
  have h1 : ζ ^ 5 - 1 = (ζ - 1) * (ζ ^ 4 + ζ ^ 3 + ζ ^ 2 + ζ + 1) := by ring
  have h2 : ζ ^ 5 - 1 = 0 := by rw [h1, hζ, mul_zero]
  exact sub_eq_zero.mp h2

-- ============================================================================
-- Part V-A: Fifth Roots of Unity — Powers of ζ
-- ============================================================================

/-- If ζ⁴+ζ³+ζ²+ζ+1=0 then ζ ≠ 1. -/
theorem zeta_ne_one {K : Type*} [Field K] [CharZero K] {ζ : K}
    (hζ : ζ ^ 4 + ζ ^ 3 + ζ ^ 2 + ζ + 1 = 0) : ζ ≠ 1 := by
  intro h; rw [h] at hζ; norm_num at hζ

/-- If ζ⁴+ζ³+ζ²+ζ+1=0 then ζ ≠ -1. -/
theorem zeta_ne_neg_one {K : Type*} [Field K] [CharZero K] {ζ : K}
    (hζ : ζ ^ 4 + ζ ^ 3 + ζ ^ 2 + ζ + 1 = 0) : ζ ≠ -1 := by
  intro h; rw [h] at hζ; norm_num at hζ

/-- If ζ⁴+ζ³+ζ²+ζ+1=0 then ζ² ≠ 1. -/
theorem zeta_sq_ne_one {K : Type*} [Field K] [CharZero K] {ζ : K}
    (hζ : ζ ^ 4 + ζ ^ 3 + ζ ^ 2 + ζ + 1 = 0) : ζ ^ 2 ≠ 1 := by
  intro h
  -- ζ² = 1 → ζ ∈ {1,-1}, both contradicted
  have h1 : (ζ - 1) * (ζ + 1) = 0 := by
    have : (ζ - 1) * (ζ + 1) = ζ ^ 2 - 1 := by ring
    rw [this, h, sub_self]
  rcases mul_eq_zero.mp h1 with h2 | h2
  · exact zeta_ne_one hζ (sub_eq_zero.mp h2)
  · exact zeta_ne_neg_one hζ (eq_neg_of_add_eq_zero_left h2)

/-- If ζ⁴+ζ³+ζ²+ζ+1=0 and ζ⁵=1, then ζ³ ≠ 1. -/
theorem zeta_cube_ne_one {K : Type*} [Field K] [CharZero K] {ζ : K}
    (hζ : ζ ^ 4 + ζ ^ 3 + ζ ^ 2 + ζ + 1 = 0) (hζ5 : ζ ^ 5 = 1) :
    ζ ^ 3 ≠ 1 := by
  intro h
  -- ζ³=1 and ζ⁵=1 → ζ²=1 (ζ²·ζ³=ζ⁵=1, so ζ²=1/ζ³=1)
  have : ζ ^ 2 = 1 := by
    have h1 : ζ ^ 2 * ζ ^ 3 = ζ ^ 5 := by ring
    rw [hζ5, h] at h1
    simpa using h1
  exact zeta_sq_ne_one hζ this

/-- If ζ⁴+ζ³+ζ²+ζ+1=0 and ζ⁵=1, then ζ⁴ ≠ 1. -/
theorem zeta_fourth_ne_one {K : Type*} [Field K] [CharZero K] {ζ : K}
    (hζ : ζ ^ 4 + ζ ^ 3 + ζ ^ 2 + ζ + 1 = 0) (hζ5 : ζ ^ 5 = 1) :
    ζ ^ 4 ≠ 1 := by
  intro h
  have : ζ = 1 := by
    have h1 : ζ ^ 4 * ζ = ζ ^ 5 := by ring
    rw [h, one_mul, hζ5] at h1; exact h1
  exact zeta_ne_one hζ this

/-- Powers ζ², ζ³, ζ⁴ all satisfy Φ₅.
    Key: (ζᵏ)⁴+(ζᵏ)³+(ζᵏ)²+ζᵏ+1 reduces to ζ⁴+ζ³+ζ²+ζ+1 using ζ⁵=1. -/
theorem pow_root_of_cyclotomic5 {K : Type*} [Field K] {ζ : K}
    (hζ : ζ ^ 4 + ζ ^ 3 + ζ ^ 2 + ζ + 1 = 0) (hζ5 : ζ ^ 5 = 1)
    (k : ℕ) (hk : k ∈ ({2, 3, 4} : Finset ℕ)) :
    (ζ ^ k) ^ 4 + (ζ ^ k) ^ 3 + (ζ ^ k) ^ 2 + ζ ^ k + 1 = 0 := by
  simp only [Finset.mem_insert, Finset.mem_singleton] at hk
  rcases hk with rfl | rfl | rfl
  · -- k = 2: reduce ζ⁸,ζ⁶ using ζ⁵=1 to get hζ
    linear_combination hζ + (ζ ^ 3 + ζ) * hζ5
  · -- k = 3: reduce ζ¹²,ζ⁹,ζ⁶ using ζ⁵=1 to get hζ
    linear_combination hζ + (ζ ^ 4 + ζ ^ 7 + ζ ^ 2 + ζ) * hζ5
  · -- k = 4: reduce ζ¹⁶,ζ¹²,ζ⁸ using ζ⁵=1 to get hζ
    linear_combination hζ + (ζ ^ 11 + ζ ^ 7 + ζ ^ 6 + ζ ^ 3 + ζ ^ 2 + ζ) * hζ5

/-- Any root of Φ₅ in a field is one of ζ, ζ², ζ³, ζ⁴.
    Proof: The factorization (c-ζ)(c-ζ²)(c-ζ³)(c-ζ⁴) = c⁴+c³+c²+c+1 holds
    (as a ring identity using ζ⁵=1 and hζ). Combined with hc, one factor must be 0. -/
theorem cyclotomic5_root_is_power {K : Type*} [Field K] [CharZero K] {ζ c : K}
    (hζ : ζ ^ 4 + ζ ^ 3 + ζ ^ 2 + ζ + 1 = 0)
    (hζ5 : ζ ^ 5 = 1)
    (hc : c ^ 4 + c ^ 3 + c ^ 2 + c + 1 = 0) :
    c = ζ ∨ c = ζ ^ 2 ∨ c = ζ ^ 3 ∨ c = ζ ^ 4 := by
  -- Key identity: (c-ζ)(c-ζ²)(c-ζ³)(c-ζ⁴) = c⁴+c³+c²+c+1 (using ζ⁵=1, hζ)
  -- Combined with hc: the product is 0, so one factor vanishes.
  have hfact : (c - ζ) * (c - ζ ^ 2) * (c - ζ ^ 3) * (c - ζ ^ 4) = 0 := by
    linear_combination
      hc + (-c ^ 3 + c ^ 2 - c) * hζ +
      ((2 + ζ + ζ ^ 2) * c ^ 2 - (ζ + ζ ^ 2 + ζ ^ 3 + ζ ^ 4) * c +
        ζ ^ 5 + 1) * hζ5
  -- In a field, product = 0 → some factor = 0 → c = ζ^k
  rcases mul_eq_zero.mp hfact with h | h4
  · rcases mul_eq_zero.mp h with h | h3
    · rcases mul_eq_zero.mp h with h1 | h2
      · exact Or.inl (sub_eq_zero.mp h1)
      · exact Or.inr (Or.inl (sub_eq_zero.mp h2))
    · exact Or.inr (Or.inr (Or.inl (sub_eq_zero.mp h3)))
  · exact Or.inr (Or.inr (Or.inr (sub_eq_zero.mp h4)))

-- ============================================================================
-- Part V-B: All Roots of X⁵-2 Lie in ℚ(α, ζ)
-- ============================================================================

/-- Every root of X⁵-2 in the splitting field lies in ℚ⟮α,ζ⟯.
    For any root r: (r/α)⁵ = 1, so r/α is a 5th root of unity.
    By cyclotomic5_root_is_power, r/α ∈ {1,ζ,ζ²,ζ³,ζ⁴} ⊂ ℚ(α,ζ). -/
theorem roots_in_adjoin_f20
    {α ζ : (X ^ 5 - C (2 : ℚ) : ℚ[X]).SplittingField}
    (hα : Polynomial.aeval α (X ^ 5 - C (2 : ℚ) : ℚ[X]) = 0)
    (hζ : ζ ^ 4 + ζ ^ 3 + ζ ^ 2 + ζ + 1 = 0)
    (hα_ne : α ≠ 0) :
    ∀ r, r ∈ (X ^ 5 - C (2 : ℚ) : ℚ[X]).rootSet
      (X ^ 5 - C (2 : ℚ) : ℚ[X]).SplittingField →
    r ∈ (IntermediateField.adjoin ℚ ({α, ζ} :
      Set (X ^ 5 - C (2 : ℚ) : ℚ[X]).SplittingField) : Set _) := by
  intro r hr
  have hr_eval : Polynomial.aeval r (X ^ 5 - C (2 : ℚ) : ℚ[X]) = 0 :=
    (Polynomial.mem_rootSet.mp hr).2
  -- α⁵ = 2 and r⁵ = 2
  have aeval_eq : ∀ x : (X ^ 5 - C (2 : ℚ) : ℚ[X]).SplittingField,
      Polynomial.aeval x (X ^ 5 - C (2 : ℚ) : ℚ[X]) = x ^ 5 - algebraMap ℚ _ 2 := by
    intro x; simp [map_sub, map_pow, aeval_X, aeval_C]
  have hα5 : α ^ 5 = algebraMap ℚ _ 2 :=
    sub_eq_zero.mp (by rw [← aeval_eq]; exact hα)
  have hr5 : r ^ 5 = algebraMap ℚ _ 2 :=
    sub_eq_zero.mp (by rw [← aeval_eq]; exact hr_eval)
  -- c = r/α satisfies c⁵ = 1
  set c := r * α⁻¹ with hc_def
  have hc5 : c ^ 5 = 1 := by
    simp only [c, mul_pow, inv_pow, hr5, hα5]; field_simp
  have hζ5 := pow5_eq_one_of_cyclotomic5_root hζ
  set K := IntermediateField.adjoin ℚ ({α, ζ} :
    Set (X ^ 5 - C (2 : ℚ) : ℚ[X]).SplittingField)
  -- α and ζ are in K
  have hα_K : α ∈ (K : Set _) := by
    apply IntermediateField.subset_adjoin; exact Set.mem_insert α {ζ}
  have hζ_K : ζ ∈ (K : Set _) := by
    apply IntermediateField.subset_adjoin
    exact Set.mem_insert_iff.mpr (Or.inr rfl)
  -- Helper: recover r from c
  have hr_of_c : r = c * α := by rw [hc_def, mul_assoc, inv_mul_cancel₀ hα_ne, mul_one]
  -- c = 1 case: r = α ∈ K
  by_cases hc1 : c = 1
  · rw [hr_of_c, hc1, one_mul]; exact hα_K
  · -- c ≠ 1: c is a root of Φ₅
    have hcΦ : c ^ 4 + c ^ 3 + c ^ 2 + c + 1 = 0 := by
      have hab : r ≠ α := by
        intro h
        have : c = 1 := by rw [hc_def, h, mul_inv_cancel₀ hα_ne]
        exact hc1 this
      exact fifth_root_ratio_satisfies_cyclotomic5 (by rw [hr5, hα5]) hab hα_ne
    -- c is a power of ζ
    rcases cyclotomic5_root_is_power hζ hζ5 hcΦ with hc_eq | hc_eq | hc_eq | hc_eq
    · rw [hr_of_c, hc_eq]; exact K.mul_mem hζ_K hα_K
    · rw [hr_of_c, hc_eq, show ζ ^ 2 = ζ * ζ from by ring]
      exact K.mul_mem (K.mul_mem hζ_K hζ_K) hα_K
    · rw [hr_of_c, hc_eq, show ζ ^ 3 = ζ * ζ * ζ from by ring]
      exact K.mul_mem (K.mul_mem (K.mul_mem hζ_K hζ_K) hζ_K) hα_K
    · rw [hr_of_c, hc_eq, show ζ ^ 4 = ζ * ζ * ζ * ζ from by ring]
      exact K.mul_mem (K.mul_mem (K.mul_mem (K.mul_mem hζ_K hζ_K) hζ_K) hζ_K) hα_K

/-- The splitting field of X⁵-2 equals ℚ⟮α,ζ⟯. -/
theorem adjoin_alpha_zeta_eq_top_f20
    {α ζ : (X ^ 5 - C (2 : ℚ) : ℚ[X]).SplittingField}
    (hα : Polynomial.aeval α (X ^ 5 - C (2 : ℚ) : ℚ[X]) = 0)
    (hζ : ζ ^ 4 + ζ ^ 3 + ζ ^ 2 + ζ + 1 = 0)
    (hα_ne : α ≠ 0) :
    IntermediateField.adjoin ℚ ({α, ζ} :
      Set (X ^ 5 - C (2 : ℚ) : ℚ[X]).SplittingField) = ⊤ := by
  set K := IntermediateField.adjoin ℚ ({α, ζ} :
    Set (X ^ 5 - C (2 : ℚ) : ℚ[X]).SplittingField)
  have h_roots : ↑((X ^ 5 - C (2 : ℚ) : ℚ[X]).rootSet
    (X ^ 5 - C (2 : ℚ) : ℚ[X]).SplittingField) ⊆ (K : Set _) :=
    fun r hr => roots_in_adjoin_f20 hα hζ hα_ne r hr
  have h_sub : Algebra.adjoin ℚ (↑((X ^ 5 - C (2 : ℚ) : ℚ[X]).rootSet
    (X ^ 5 - C (2 : ℚ) : ℚ[X]).SplittingField)) ≤ K.toSubalgebra :=
    Algebra.adjoin_le (fun x hx => h_roots hx)
  have h_top : Algebra.adjoin ℚ (↑((X ^ 5 - C (2 : ℚ) : ℚ[X]).rootSet
    (X ^ 5 - C (2 : ℚ) : ℚ[X]).SplittingField)) = ⊤ :=
    IsSplittingField.adjoin_rootSet'
  have h_K_top : K.toSubalgebra = ⊤ := le_antisymm le_top (h_top ▸ h_sub)
  rw [← IntermediateField.top_toSubalgebra] at h_K_top
  exact (IntermediateField.toSubalgebra_injective h_K_top)

-- ============================================================================
-- Part V-C: The Upper Bound — |Gal(X⁵-2)| divides 20
-- ============================================================================

set_option synthInstance.maxHeartbeats 80000 in
set_option maxHeartbeats 800000 in
/-- |Gal(X⁵-2/ℚ)| divides 20.

    Proof:
    1. 20 | |Gal| (from twenty_dvd_gal_card)
    2. SF = ℚ(α,ζ₅) where [ℚ(α):ℚ] = 5 and [SF:ℚ(α)] ≤ 4
    3. So [SF:ℚ] ≤ 20, hence |Gal| ≤ 20
    4. Combined: |Gal| = 20 -/
theorem gal_card_dvd_20 :
    Fintype.card ((X : ℚ[X]) ^ 5 - C 2).Gal ∣ 20 := by
  set p := (X : ℚ[X]) ^ 5 - C 2 with hp_def
  set E := p.SplittingField
  -- |Gal| = finrank
  have hcard_eq : Fintype.card p.Gal = Module.finrank ℚ E := by
    have := Polynomial.Gal.card_of_separable x_fifth_sub_2_separable
    rw [Nat.card_eq_fintype_card] at this; exact this
  -- Lower bound: 20 | |Gal|
  have h20_dvd := twenty_dvd_gal_card
  have hpos : 0 < Fintype.card p.Gal := Fintype.card_pos
  -- Get α (root of p) in E
  have hsplit := Polynomial.SplittingField.splits p
  have hcard_root : Fintype.card (p.rootSet E) = 5 :=
    (Polynomial.card_rootSet_eq_natDegree x_fifth_sub_2_separable hsplit).trans
      x_fifth_sub_2_natDegree
  obtain ⟨⟨α, hα_mem⟩⟩ :=
    Fintype.card_pos_iff.mp (by rw [hcard_root]; omega)
  have hα : Polynomial.aeval α p = 0 := (Polynomial.mem_rootSet.mp hα_mem).2
  have hα_ne : α ≠ 0 := by
    intro h; have := hα; simp [hp_def, map_sub, map_pow, aeval_X, aeval_C] at this
    rw [h, zero_pow (by omega : 5 ≠ 0)] at this; simp at this
  -- Get ζ (root of Φ₅) in E
  obtain ⟨ζ, hζ⟩ := cyclotomic_5_has_root_in_splitting_field
  -- SF = ℚ(α,ζ)
  have hK_top := adjoin_alpha_zeta_eq_top_f20 hα hζ hα_ne
  -- Set up Kα = ℚ(α)
  set Kα := IntermediateField.adjoin ℚ ({α} : Set E)
  -- [Kα : ℚ] = 5
  have hα_int : IsIntegral ℚ α := .of_finite ℚ α
  have hminp : minpoly ℚ α = p :=
    (minpoly.eq_of_irreducible_of_monic x_fifth_sub_2_irreducible hα
      x_fifth_sub_2_monic).symm
  have hKα_fr : Module.finrank ℚ Kα = 5 := by
    rw [IntermediateField.adjoin.finrank hα_int, hminp, x_fifth_sub_2_natDegree]
  -- Tower law: [E:ℚ] = [E:Kα] * 5
  have htower := Module.finrank_mul_finrank ℚ Kα E
  rw [hKα_fr] at htower
  -- Show [E:Kα] ≤ 4 via Kα⟮ζ⟯ = ⊤
  set Kαζ := IntermediateField.adjoin (↥Kα) ({ζ} : Set E)
  have hKαζ_top : Kαζ = ⊤ := by
    have h_le : IntermediateField.adjoin ℚ ({α, ζ} : Set E) ≤
        Kαζ.restrictScalars ℚ := by
      apply IntermediateField.adjoin_le_iff.mpr
      intro x hx; show x ∈ (Kαζ : Set E)
      rcases Set.mem_insert_iff.mp hx with h_eq | hx
      · rw [h_eq]
        have hα_Kα : α ∈ (Kα : Set E) := by
          apply IntermediateField.subset_adjoin; exact Set.mem_singleton_iff.mpr rfl
        have : (⊥ : IntermediateField (↥Kα) E) ≤ Kαζ := bot_le
        apply this; rw [IntermediateField.mem_bot]; exact ⟨⟨α, hα_Kα⟩, rfl⟩
      · rw [Set.mem_singleton_iff.mp hx]
        apply IntermediateField.subset_adjoin; exact Set.mem_singleton ζ
    rw [hK_top] at h_le
    rw [eq_top_iff]; intro x _; exact h_le IntermediateField.mem_top
  -- ζ is integral over Kα
  have hζ_int : IsIntegral (↥Kα) ζ := .of_finite (↥Kα) ζ
  -- ζ satisfies X⁴+X³+X²+X+1 = 0 over Kα
  have hζ_eval : Polynomial.aeval ζ ((X : (↥Kα)[X]) ^ 4 + X ^ 3 + X ^ 2 + X + C 1) = 0 := by
    simp only [map_add, map_pow, aeval_X, map_one]; exact hζ
  -- minpoly Kα ζ divides this degree-4 polynomial
  have hmin_dvd := minpoly.dvd (↥Kα) ζ hζ_eval
  have hΦ_ne : ((X : (↥Kα)[X]) ^ 4 + X ^ 3 + X ^ 2 + X + C 1) ≠ 0 := by
    intro h
    have : ((X : (↥Kα)[X]) ^ 4 + X ^ 3 + X ^ 2 + X + C 1).natDegree = 4 := by
      compute_degree!
    rw [h, Polynomial.natDegree_zero] at this; exact absurd this (by omega)
  have hmin_le : (minpoly (↥Kα) ζ).natDegree ≤ 4 := by
    have h1 := Polynomial.natDegree_le_of_dvd hmin_dvd hΦ_ne
    have h2 : ((X : (↥Kα)[X]) ^ 4 + X ^ 3 + X ^ 2 + X + C 1).natDegree ≤ 4 := by
      compute_degree!
    linarith
  -- [Kα⟮ζ⟯ : Kα] = natDegree(minpoly)
  have hfr_adj := IntermediateField.adjoin.finrank hζ_int
  change Module.finrank (↥Kα) ↥Kαζ = _ at hfr_adj
  rw [hKαζ_top] at hfr_adj
  have h_top_eq : Module.finrank (↥Kα) (↥(⊤ : IntermediateField (↥Kα) E)) =
      Module.finrank (↥Kα) E :=
    LinearEquiv.finrank_eq (IntermediateField.topEquiv.toLinearEquiv)
  -- finrank Kα E ≤ 4
  have hfr_le : Module.finrank (↥Kα) E ≤ 4 := by linarith
  -- [E:ℚ] ≤ 20
  have hfr_total : Module.finrank ℚ E ≤ 20 := by
    rw [← htower]; exact Nat.mul_le_mul_left 5 hfr_le
  -- |Gal| ≤ 20
  have hle : Fintype.card p.Gal ≤ 20 := by linarith
  -- Combined: |Gal| = 20
  have heq : Fintype.card p.Gal = 20 :=
    Nat.le_antisymm hle (Nat.le_of_dvd hpos h20_dvd)
  rw [heq]

-- ============================================================================
-- Part VI: The Main Result
-- ============================================================================

/-- **The Galois group of X⁵-2 over ℚ has exactly 20 elements.**

    Lower bound: 20 | |Gal| (fully proved from irreducibility and coprimality).
    Upper bound: |Gal| | 20 (proved via tower law and Φ₅ structure). -/
theorem x5_sub_2_gal_card :
    Fintype.card ((X : ℚ[X]) ^ 5 - C 2).Gal = 20 := by
  have h20 : 20 ∣ Fintype.card ((X : ℚ[X]) ^ 5 - C 2).Gal := twenty_dvd_gal_card
  have hdvd : Fintype.card ((X : ℚ[X]) ^ 5 - C 2).Gal ∣ 20 := gal_card_dvd_20
  exact Nat.dvd_antisymm hdvd h20

/-- The splitting field of X⁵-2 has ℚ-dimension 20. -/
theorem splitting_field_x5_sub_2_finrank :
    Module.finrank ℚ (X ^ 5 - C (2 : ℚ) : ℚ[X]).SplittingField = 20 := by
  have hcard_eq : Fintype.card ((X : ℚ[X]) ^ 5 - C 2).Gal =
      Module.finrank ℚ (X ^ 5 - C (2 : ℚ) : ℚ[X]).SplittingField := by
    have := Polynomial.Gal.card_of_separable x_fifth_sub_2_separable
    rw [Nat.card_eq_fintype_card] at this; exact this
  rw [← hcard_eq]; exact x5_sub_2_gal_card

/-- F₂₀ (order 20) is realizable as a Galois group over ℚ. -/
theorem f20_realizable :
    ∃ (K : Type) (_ : Field K) (_ : Algebra ℚ K) (_ : FiniteDimensional ℚ K)
      (_ : IsGalois ℚ K),
      Fintype.card (K ≃ₐ[ℚ] K) = 20 := by
  set p := (X : ℚ[X]) ^ 5 - C 2
  haveI : Normal ℚ p.SplittingField := inferInstance
  haveI : Algebra.IsSeparable ℚ p.SplittingField := inferInstance
  exact ⟨p.SplittingField,
    inferInstance, inferInstance, inferInstance, IsGalois.mk,
    x5_sub_2_gal_card⟩

end InverseGaloisF20
