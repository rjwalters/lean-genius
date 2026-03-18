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

/-- c⁵ = 1 implies c = 1 or Φ₅(c) = 0. -/
theorem fifth_root_unity_cases {K : Type*} [Field K] {c : K} (h : c ^ 5 = 1) :
    c = 1 ∨ c ^ 4 + c ^ 3 + c ^ 2 + c + 1 = 0 := by
  have h0 : (c - 1) * (c ^ 4 + c ^ 3 + c ^ 2 + c + 1) = 0 := by
    have : (c - 1) * (c ^ 4 + c ^ 3 + c ^ 2 + c + 1) = c ^ 5 - 1 := by ring
    rw [this, h, sub_self]
  rcases mul_eq_zero.mp h0 with h1 | h2
  · left; exact sub_eq_zero.mp h1
  · right; exact h2

/-- Any root c of Φ₅ equals ζᵏ for some k ∈ {1,2,3,4}.

    The polynomial identity (c-ζ)(c-ζ²)(c-ζ³)(c-ζ⁴) = c⁴+c³+c²+c+1
    uses ζ⁵=1 and Φ₅(ζ)=0 (elementary symmetric polynomials: σ₁=-1, σ₂=1, σ₃=-1, σ₄=1). -/
theorem cyclotomic5_root_is_power {K : Type*} [Field K] [CharZero K]
    {ζ c : K} (hζ : ζ ^ 4 + ζ ^ 3 + ζ ^ 2 + ζ + 1 = 0)
    (hc : c ^ 4 + c ^ 3 + c ^ 2 + c + 1 = 0) :
    c = ζ ∨ c = ζ ^ 2 ∨ c = ζ ^ 3 ∨ c = ζ ^ 4 := by
  have h5 := pow5_eq_one_of_cyclotomic5_root hζ
  have hprod : (c - ζ) * (c - ζ ^ 2) * (c - ζ ^ 3) * (c - ζ ^ 4) = 0 := by
    have key : (c - ζ) * (c - ζ ^ 2) * (c - ζ ^ 3) * (c - ζ ^ 4) =
        c ^ 4 + c ^ 3 + c ^ 2 + c + 1 := by
      linear_combination
        (-c ^ 3 + c ^ 2 - c) * hζ +
        ((ζ ^ 2 + ζ + 2) * c ^ 2 - (ζ ^ 4 + ζ ^ 3 + ζ ^ 2 + ζ) * c +
          ζ ^ 5 + 1) * h5
    rw [key, hc]
  rcases mul_eq_zero.mp hprod with h | h
  · rcases mul_eq_zero.mp h with h | h
    · rcases mul_eq_zero.mp h with h | h
      · left; exact sub_eq_zero.mp h
      · right; left; exact sub_eq_zero.mp h
    · right; right; left; exact sub_eq_zero.mp h
  · right; right; right; exact sub_eq_zero.mp h

/-- Every root of X⁵-2 lies in ℚ⟮α,ζ⟯. For any root r: (r/α)⁵=1,
    so r/α = 1 or a power of ζ. -/
theorem f20_roots_in_adjoin
    {α ζ : (X ^ 5 - C (2 : ℚ) : ℚ[X]).SplittingField}
    (hα : Polynomial.aeval α (X ^ 5 - C (2 : ℚ) : ℚ[X]) = 0)
    (hζ : ζ ^ 4 + ζ ^ 3 + ζ ^ 2 + ζ + 1 = 0) (hα_ne : α ≠ 0) :
    ∀ r, r ∈ (X ^ 5 - C (2 : ℚ) : ℚ[X]).rootSet
      (X ^ 5 - C (2 : ℚ) : ℚ[X]).SplittingField →
    r ∈ (IntermediateField.adjoin ℚ ({α, ζ} :
      Set (X ^ 5 - C (2 : ℚ) : ℚ[X]).SplittingField) : Set _) := by
  intro r hr
  set K := IntermediateField.adjoin ℚ ({α, ζ} :
    Set (X ^ 5 - C (2 : ℚ) : ℚ[X]).SplittingField)
  have hα_K : (α : (X ^ 5 - C (2 : ℚ) : ℚ[X]).SplittingField) ∈ K := by
    apply IntermediateField.subset_adjoin; exact Set.mem_insert α {ζ}
  have hζ_K : (ζ : (X ^ 5 - C (2 : ℚ) : ℚ[X]).SplittingField) ∈ K := by
    apply IntermediateField.subset_adjoin
    exact Set.mem_insert_of_mem α rfl
  have hr_eval : Polynomial.aeval r (X ^ 5 - C (2 : ℚ) : ℚ[X]) = 0 :=
    (Polynomial.mem_rootSet.mp hr).2
  have hα5 : α ^ 5 = algebraMap ℚ _ 2 := by
    have h := hα; rw [map_sub, map_pow, aeval_X, aeval_C] at h; exact sub_eq_zero.mp h
  have hr5 : r ^ 5 = algebraMap ℚ _ 2 := by
    have h := hr_eval; rw [map_sub, map_pow, aeval_X, aeval_C] at h; exact sub_eq_zero.mp h
  set c := r * α⁻¹
  have hc5 : c ^ 5 = 1 := by
    simp only [c]; rw [mul_pow, inv_pow, hr5, hα5]; field_simp
  rcases fifth_root_unity_cases hc5 with hc1 | hc_phi
  · have : r = α := by
      have h2 : r = c * α := by
        show r = r * α⁻¹ * α
        rw [mul_assoc, inv_mul_cancel₀ hα_ne, mul_one]
      rw [h2, hc1, one_mul]
    rw [this]; exact hα_K
  · have hr_c : r = c * α := by
      show r = r * α⁻¹ * α
      rw [mul_assoc, inv_mul_cancel₀ hα_ne, mul_one]
    have hc_K : c ∈ K := by
      rcases cyclotomic5_root_is_power hζ hc_phi with h | h | h | h
      · rw [h]; exact hζ_K
      · rw [h]; exact pow_mem hζ_K 2
      · rw [h]; exact pow_mem hζ_K 3
      · rw [h]; exact pow_mem hζ_K 4
    rw [hr_c]; exact K.mul_mem hc_K hα_K

/-- SF(X⁵-2) = ℚ⟮α,ζ⟯. -/
theorem f20_adjoin_eq_top
    {α ζ : (X ^ 5 - C (2 : ℚ) : ℚ[X]).SplittingField}
    (hα : Polynomial.aeval α (X ^ 5 - C (2 : ℚ) : ℚ[X]) = 0)
    (hζ : ζ ^ 4 + ζ ^ 3 + ζ ^ 2 + ζ + 1 = 0) (hα_ne : α ≠ 0) :
    IntermediateField.adjoin ℚ ({α, ζ} :
      Set (X ^ 5 - C (2 : ℚ) : ℚ[X]).SplittingField) = ⊤ := by
  set K := IntermediateField.adjoin ℚ ({α, ζ} :
    Set (X ^ 5 - C (2 : ℚ) : ℚ[X]).SplittingField)
  have h_sub : Algebra.adjoin ℚ (↑((X ^ 5 - C (2 : ℚ) : ℚ[X]).rootSet
    (X ^ 5 - C (2 : ℚ) : ℚ[X]).SplittingField)) ≤ K.toSubalgebra :=
    Algebra.adjoin_le (fun x hx => f20_roots_in_adjoin hα hζ hα_ne x hx)
  have h_top : Algebra.adjoin ℚ (↑((X ^ 5 - C (2 : ℚ) : ℚ[X]).rootSet
    (X ^ 5 - C (2 : ℚ) : ℚ[X]).SplittingField)) = ⊤ :=
    IsSplittingField.adjoin_rootSet'
  have h_K_top : K.toSubalgebra = ⊤ := le_antisymm le_top (h_top ▸ h_sub)
  rw [← IntermediateField.top_toSubalgebra] at h_K_top
  exact IntermediateField.toSubalgebra_injective h_K_top

set_option synthInstance.maxHeartbeats 80000 in
set_option maxHeartbeats 800000 in
/-- |Gal(X⁵-2/ℚ)| divides 20. SF = ℚ(α,ζ₅) with tower law. -/
theorem gal_card_dvd_20 :
    Fintype.card ((X : ℚ[X]) ^ 5 - C 2).Gal ∣ 20 := by
  set p := (X : ℚ[X]) ^ 5 - C 2 with hp_def
  set E := p.SplittingField
  have hcard_eq : Fintype.card p.Gal = Module.finrank ℚ E := by
    have := Polynomial.Gal.card_of_separable x_fifth_sub_2_separable
    rw [Nat.card_eq_fintype_card] at this; exact this
  rw [hcard_eq]
  have hsplit := Polynomial.SplittingField.splits p
  have hcard_root : Fintype.card (p.rootSet E) = 5 :=
    (Polynomial.card_rootSet_eq_natDegree x_fifth_sub_2_separable hsplit).trans
      x_fifth_sub_2_natDegree
  obtain ⟨⟨α, hα_mem⟩⟩ := Fintype.card_pos_iff.mp (by rw [hcard_root]; omega)
  have hα : Polynomial.aeval α p = 0 := (Polynomial.mem_rootSet.mp hα_mem).2
  have hα_ne : α ≠ 0 := by
    intro h; have h2 := hα; rw [map_sub, map_pow, aeval_X, aeval_C, h,
      zero_pow (by omega)] at h2; simp at h2
  obtain ⟨ζ, hζ⟩ := cyclotomic_5_has_root_in_splitting_field
  have hK_top := f20_adjoin_eq_top hα hζ hα_ne
  set Kα := IntermediateField.adjoin ℚ ({α} : Set E)
  have hα_int : IsIntegral ℚ α := .of_finite ℚ α
  have hminp : minpoly ℚ α = p :=
    (minpoly.eq_of_irreducible_of_monic x_fifth_sub_2_irreducible hα x_fifth_sub_2_monic).symm
  have hKα_fr : Module.finrank ℚ Kα = 5 := by
    rw [IntermediateField.adjoin.finrank hα_int, hminp, x_fifth_sub_2_natDegree]
  have htower := Module.finrank_mul_finrank ℚ Kα E
  rw [hKα_fr] at htower
  suffices h4 : Module.finrank Kα E ∣ 4 by
    rw [← htower]; exact mul_dvd_mul_left 5 h4
  set Kαζ := IntermediateField.adjoin (↥Kα) ({ζ} : Set E)
  have hKαζ_top : Kαζ = ⊤ := by
    have h_le : IntermediateField.adjoin ℚ ({α, ζ} : Set E) ≤
        Kαζ.restrictScalars ℚ := by
      apply IntermediateField.adjoin_le_iff.mpr
      intro x hx; show x ∈ (Kαζ : Set E)
      rcases hx with h_eq | hx
      · rw [h_eq]
        apply (bot_le : (⊥ : IntermediateField (↥Kα) E) ≤ Kαζ)
        rw [IntermediateField.mem_bot]
        refine ⟨⟨α, ?_⟩, rfl⟩
        apply IntermediateField.subset_adjoin; exact Set.mem_singleton α
      · rw [Set.mem_singleton_iff.mp hx]
        apply IntermediateField.subset_adjoin; exact Set.mem_singleton ζ
    rw [hK_top] at h_le; rw [eq_top_iff]; exact fun x _ => h_le IntermediateField.mem_top
  have hζ_int : IsIntegral (↥Kα) ζ := .of_finite (↥Kα) ζ
  have hζ_eval : Polynomial.aeval ζ ((X : (↥Kα)[X]) ^ 4 + X ^ 3 + X ^ 2 + X + 1) = 0 := by
    simp only [map_add, map_pow, aeval_X, map_one]; exact hζ
  have hmin_dvd := minpoly.dvd (↥Kα) ζ hζ_eval
  have hphi5_ne : ((X : (↥Kα)[X]) ^ 4 + X ^ 3 + X ^ 2 + X + 1) ≠ 0 := by
    intro h
    have : ((X : (↥Kα)[X]) ^ 4 + X ^ 3 + X ^ 2 + X + 1).natDegree = 0 := by
      rw [h]; exact Polynomial.natDegree_zero
    have h4 : ((X : (↥Kα)[X]) ^ 4 + X ^ 3 + X ^ 2 + X + 1).natDegree = 4 := by
      rw [show (X : (↥Kα)[X]) ^ 4 + X ^ 3 + X ^ 2 + X + 1 =
        Polynomial.cyclotomic 5 (↥Kα) from by
          haveI : Fact (Nat.Prime 5) := ⟨by decide⟩
          have h1 := cyclotomic_prime (R := (↥Kα)) (p := 5)
          simp only [Finset.sum_range_succ, Finset.sum_range_zero, pow_zero, pow_one,
            zero_add] at h1
          rw [h1]; ring]
      rw [Polynomial.natDegree_cyclotomic]; decide
    omega
  have hmin_le : (minpoly (↥Kα) ζ).natDegree ≤ 4 := by
    have hdeg4 : ((X : (↥Kα)[X]) ^ 4 + X ^ 3 + X ^ 2 + X + 1).natDegree = 4 := by
      rw [show (X : (↥Kα)[X]) ^ 4 + X ^ 3 + X ^ 2 + X + 1 =
        Polynomial.cyclotomic 5 (↥Kα) from by
          haveI : Fact (Nat.Prime 5) := ⟨by decide⟩
          have h1 := cyclotomic_prime (R := (↥Kα)) (p := 5)
          simp only [Finset.sum_range_succ, Finset.sum_range_zero, pow_zero, pow_one,
            zero_add] at h1
          rw [h1]; ring]
      rw [Polynomial.natDegree_cyclotomic]; decide
    calc (minpoly (↥Kα) ζ).natDegree
        ≤ ((X : (↥Kα)[X]) ^ 4 + X ^ 3 + X ^ 2 + X + 1).natDegree :=
          Polynomial.natDegree_le_of_dvd hmin_dvd hphi5_ne
      _ = 4 := hdeg4
  have hfr_adj := IntermediateField.adjoin.finrank hζ_int
  change Module.finrank (↥Kα) ↥Kαζ = _ at hfr_adj
  rw [hKαζ_top] at hfr_adj
  have h_top_eq : Module.finrank (↥Kα) (↥(⊤ : IntermediateField (↥Kα) E)) =
      Module.finrank (↥Kα) E :=
    LinearEquiv.finrank_eq (IntermediateField.topEquiv.toLinearEquiv)
  have hfr_le : Module.finrank (↥Kα) E ≤ 4 := by linarith
  have hfr_pos : 0 < Module.finrank (↥Kα) E := Module.finrank_pos
  have h4dvd : 4 ∣ Module.finrank (↥Kα) E := by
    have := four_dvd_splitting_field_finrank
    rw [← htower] at this
    exact Nat.Coprime.dvd_of_dvd_mul_left (by decide : Nat.Coprime 4 5) this
  have hfr_eq : Module.finrank (↥Kα) E = 4 := by obtain ⟨k, hk⟩ := h4dvd; omega
  rw [hfr_eq]

-- ============================================================================
-- Part VI: The Main Result
-- ============================================================================

/-- **The Galois group of X⁵-2 over ℚ has exactly 20 elements.**

    Lower bound: 20 | |Gal| (fully proved from irreducibility and coprimality).
    Upper bound: |Gal| | 20 (sorry - requires symmetric polynomial computation). -/
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
