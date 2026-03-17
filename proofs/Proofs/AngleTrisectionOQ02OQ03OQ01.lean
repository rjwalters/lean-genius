/-
  Angle Trisection OQ02-OQ03-OQ01:
  Proving the maximal real subfield degree via Galois fixed field theory.

  Goal: Eliminate the axioms from the OQ02-OQ03 formalization by connecting
  Mathlib's cyclotomic field infrastructure to the cos(2π/n) degree computation.

  Main result: maximal_real_subfield_degree
    For n ≥ 3, ∃ F : IntermediateField ℚ (CyclotomicField n ℚ),
    [F:ℚ] = φ(n)/2.

  Proof strategy:
  1. CyclotomicField n ℚ is Galois over ℚ with degree φ(n) (Mathlib)
  2. -1 ∈ (ℤ/nℤ)* maps to an order-2 automorphism σ (via fromZetaAut)
  3. H = ⟨σ⟩ is a subgroup of Aut(K/ℚ) of order 2
  4. F = K^H (fixed field of H) has [K:F] = 2 (Artin/fixed field theorem)
  5. Tower law: φ(n) = [K:F]·[F:ℚ] = 2·[F:ℚ], so [F:ℚ] = φ(n)/2
-/

import Mathlib
import Proofs.AngleTrisectionEmbedding

open Polynomial

namespace AngleTrisectionOQ02OQ03OQ01

-- ============================================================================
-- § 1. Cyclotomic Field Setup
-- ============================================================================

variable (n : ℕ) [NeZero n]

/-- CyclotomicField n ℚ is a Galois extension of ℚ. -/
instance cyclotomic_isGalois : IsGalois ℚ (CyclotomicField n ℚ) :=
  IsCyclotomicExtension.isGalois {n} ℚ (CyclotomicField n ℚ)

/-- CyclotomicField n ℚ is finite-dimensional over ℚ. -/
instance cyclotomic_finiteDimensional : FiniteDimensional ℚ (CyclotomicField n ℚ) :=
  IsCyclotomicExtension.finiteDimensional {n} ℚ (CyclotomicField n ℚ)

/-- [CyclotomicField n ℚ : ℚ] = φ(n). -/
theorem cyclotomic_finrank :
    Module.finrank ℚ (CyclotomicField n ℚ) = Nat.totient n :=
  IsCyclotomicExtension.finrank (CyclotomicField n ℚ)
    (Polynomial.cyclotomic.irreducible_rat (NeZero.pos n))

/-- A primitive n-th root of unity in CyclotomicField n ℚ.
    Uses Mathlib's canonical primitive root to enable fromZetaAut_spec. -/
noncomputable def abstractZeta :
    CyclotomicField n ℚ :=
  IsCyclotomicExtension.zeta n ℚ (CyclotomicField n ℚ)

theorem abstractZeta_isPrimRoot :
    IsPrimitiveRoot (abstractZeta n) n :=
  IsCyclotomicExtension.zeta_spec n ℚ (CyclotomicField n ℚ)

-- ============================================================================
-- § 2. Order-2 Automorphism via fromZetaAut
-- ============================================================================

/-- The automorphism σ that sends ζ ↦ ζ⁻¹ (the analogue of complex conjugation).
    Defined via fromZetaAut so that the action on ζ is immediate from the spec. -/
noncomputable def conjAut :
    (CyclotomicField n ℚ) ≃ₐ[ℚ] (CyclotomicField n ℚ) :=
  IsCyclotomicExtension.fromZetaAut
    ((IsCyclotomicExtension.zeta_spec n ℚ (CyclotomicField n ℚ)).inv)
    (Polynomial.cyclotomic.irreducible_rat (NeZero.pos n))

/-- conjAut sends ζ to ζ⁻¹: immediate from fromZetaAut_spec. -/
theorem conjAut_zeta_eq_inv :
    conjAut n (abstractZeta n) = (abstractZeta n)⁻¹ := by
  exact IsCyclotomicExtension.fromZetaAut_spec _ _

/-- σ ≠ 1 for n ≥ 3: σ(ζ) = ζ⁻¹ ≠ ζ when n ≥ 3. -/
theorem conjAut_ne_one (hn : 3 ≤ n) : conjAut n ≠ AlgEquiv.refl := by
  intro h
  have h1 : conjAut n (abstractZeta n) = abstractZeta n := by
    rw [h]; simp
  have h2 := conjAut_zeta_eq_inv n
  rw [h1] at h2
  have hζ := abstractZeta_isPrimRoot n
  have hζ_ne : abstractZeta n ≠ 0 := hζ.ne_zero (by omega)
  have h_sq : abstractZeta n ^ 2 = 1 := by
    rw [sq]
    have h3 : abstractZeta n * (abstractZeta n)⁻¹ = 1 := mul_inv_cancel₀ hζ_ne
    rwa [← h2] at h3
  have h_dvd : orderOf (abstractZeta n) ∣ 2 := orderOf_dvd_of_pow_eq_one h_sq
  have h_ord : orderOf (abstractZeta n) = n := hζ.eq_orderOf.symm
  rw [h_ord] at h_dvd
  exact absurd (Nat.le_of_dvd (by omega) h_dvd) (by omega)

/-- σ² = 1: via the group isomorphism Aut(K/ℚ) ≃* (ℤ/nℤ)*.
    conjAut corresponds to -1, and (-1)² = 1. -/
theorem conjAut_sq : conjAut n * conjAut n = 1 := by
  have hirr := Polynomial.cyclotomic.irreducible_rat (NeZero.pos n)
  set aep := IsCyclotomicExtension.autEquivPow (CyclotomicField n ℚ) hirr
  apply aep.injective
  rw [map_mul, map_one]
  set u := aep (conjAut n)
  have hζ := abstractZeta_isPrimRoot n
  have hζ_ne : abstractZeta n ≠ 0 := hζ.ne_zero (NeZero.ne n)
  have h_spec : abstractZeta n ^ (u : ZMod n).val = (abstractZeta n)⁻¹ := by
    have h1 := hζ.autToPow_spec ℚ (conjAut n)
    rw [conjAut_zeta_eq_inv n] at h1
    convert h1 using 2
  have h_pow_one : abstractZeta n ^ ((u : ZMod n).val + 1) = 1 := by
    rw [pow_succ, h_spec, inv_mul_cancel₀ hζ_ne]
  have h_dvd : n ∣ ((u : ZMod n).val + 1) := by
    have h1 := orderOf_dvd_of_pow_eq_one h_pow_one
    rwa [show orderOf (abstractZeta n) = n from hζ.eq_orderOf.symm] at h1
  have h_val_lt := ZMod.val_lt (u : ZMod n)
  have h_neg1 : (u : ZMod n) = -1 := by
    rw [eq_neg_iff_add_eq_zero]
    have h0 : ((ZMod.val (u : ZMod n) + 1 : ℕ) : ZMod n) = 0 :=
      (ZMod.natCast_eq_zero_iff _ _).mpr h_dvd
    rwa [Nat.cast_add, Nat.cast_one, ZMod.natCast_zmod_val] at h0
  ext
  show (u : ZMod n) * (u : ZMod n) = 1
  rw [h_neg1, neg_mul_neg, one_mul]

/-- σ has order exactly 2 for n ≥ 3. -/
theorem conjAut_orderOf (hn : 3 ≤ n) : orderOf (conjAut n) = 2 := by
  have h_sq : (conjAut n) ^ 2 = 1 := by rw [sq]; exact conjAut_sq n
  have h_ne : conjAut n ≠ 1 := by
    rw [show (1 : (CyclotomicField n ℚ) ≃ₐ[ℚ] _) = AlgEquiv.refl from rfl]
    exact conjAut_ne_one n hn
  exact orderOf_eq_prime h_sq h_ne

-- ============================================================================
-- § 3. Fixed Field of ⟨σ⟩ and Degree Computation
-- ============================================================================

/-- The subgroup H = ⟨σ⟩ ≤ Aut(K/ℚ), generated by complex conjugation. -/
noncomputable def conjSubgroup :
    Subgroup ((CyclotomicField n ℚ) ≃ₐ[ℚ] (CyclotomicField n ℚ)) :=
  Subgroup.zpowers (conjAut n)

/-- H = ⟨σ⟩ has cardinality 2 for n ≥ 3. -/
theorem conjSubgroup_card (hn : 3 ≤ n) :
    Nat.card (conjSubgroup n) = 2 := by
  rw [conjSubgroup]
  rw [Nat.card_zpowers]
  exact conjAut_orderOf n hn

/-- The fixed field F = (CyclotomicField n ℚ)^⟨σ⟩: the maximal real subfield. -/
noncomputable def maxRealSubfield :
    IntermediateField ℚ (CyclotomicField n ℚ) :=
  IntermediateField.fixedField (conjSubgroup n)

/-- The degree of the maximal real subfield over ℚ is φ(n)/2 for n ≥ 3. -/
theorem maximal_real_subfield_degree (hn : 3 ≤ n) :
    ∃ (F : IntermediateField ℚ (CyclotomicField n ℚ)),
    Module.finrank ℚ F = Nat.totient n / 2 := by
  use maxRealSubfield n
  set F := maxRealSubfield n
  set H := conjSubgroup n
  have hKF : Module.finrank F (CyclotomicField n ℚ) = Nat.card H :=
    IntermediateField.finrank_fixedField_eq_card H
  rw [conjSubgroup_card n hn] at hKF
  have hKQ : Module.finrank ℚ (CyclotomicField n ℚ) = Nat.totient n :=
    cyclotomic_finrank n
  have htower : Module.finrank ℚ (CyclotomicField n ℚ) =
      Module.finrank ℚ F * Module.finrank F (CyclotomicField n ℚ) :=
    (Module.finrank_mul_finrank ℚ F (CyclotomicField n ℚ)).symm
  rw [hKQ, hKF] at htower
  omega

-- ============================================================================
-- § 4. Alpha and Embedding into ℂ
-- ============================================================================

/-- α = ζ + ζ⁻¹ in the abstract cyclotomic field. -/
noncomputable def alpha : CyclotomicField n ℚ :=
  abstractZeta n + (abstractZeta n)⁻¹

/-- ζ satisfies X² - αX + 1 = 0. -/
theorem zeta_quadratic_over_alpha (hn_pos : 0 < n) :
    let ζ := abstractZeta n
    let α := alpha n
    ζ ^ 2 - α * ζ + 1 = 0 := by
  simp only [alpha]
  set ζ := abstractZeta n
  have hζ : ζ ≠ 0 := (abstractZeta_isPrimRoot n).ne_zero (by omega)
  field_simp
  ring

/-- An embedding CyclotomicField n ℚ →ₐ[ℚ] ℂ. -/
noncomputable def cyclotomicEmbedding :
    CyclotomicField n ℚ →ₐ[ℚ] ℂ :=
  IsAlgClosed.lift (R := ℚ) (S := CyclotomicField n ℚ)

/-- Under the embedding, ζ maps to a primitive n-th root of unity in ℂ. -/
theorem embedding_zeta_isPrimRoot :
    IsPrimitiveRoot (cyclotomicEmbedding n (abstractZeta n)) n :=
  (abstractZeta_isPrimRoot n).map_of_injective (cyclotomicEmbedding n).injective

/-- Under the embedding, α maps to w + w⁻¹. -/
theorem embedding_alpha :
    cyclotomicEmbedding n (alpha n) =
    cyclotomicEmbedding n (abstractZeta n) +
    (cyclotomicEmbedding n (abstractZeta n))⁻¹ := by
  simp [alpha, map_add, map_inv₀]

-- ============================================================================
-- § 5. ℚ(α) = Fixed Field
-- ============================================================================

/-- α is in the fixed field of ⟨σ⟩. -/
theorem alpha_in_fixedField (hn : 3 ≤ n) :
    alpha n ∈ maxRealSubfield n := by
  rw [maxRealSubfield, IntermediateField.mem_fixedField_iff]
  intro σ hσ
  rw [conjSubgroup] at hσ
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hσ
  have : conjAut n ^ k = conjAut n ^ (k % (2 : ℤ)) := by
    conv_lhs => rw [show k = 2 * (k / 2) + k % 2 from (Int.mul_ediv_add_emod k 2).symm]
    rw [zpow_add, zpow_mul, show (conjAut n :
        (CyclotomicField n ℚ) ≃ₐ[ℚ] _) ^ (2 : ℤ) = 1
      from by rw [show (2 : ℤ) = 1 + 1 from rfl, zpow_add, zpow_one]; exact conjAut_sq n,
      one_zpow, one_mul]
  rw [this]
  have hmod : k % 2 = 0 ∨ k % 2 = 1 := Int.emod_two_eq_zero_or_one k
  rcases hmod with h0 | h1
  · rw [h0, zpow_zero]; simp
  · rw [h1, zpow_one]
    simp only [alpha, map_add, map_inv₀]
    rw [conjAut_zeta_eq_inv n]
    have hζ_ne : abstractZeta n ≠ 0 :=
      (abstractZeta_isPrimRoot n).ne_zero (by omega)
    rw [inv_inv]
    ring

/-- ℚ(α) ⊆ fixed field. -/
theorem alpha_adjoin_le_fixedField (hn : 3 ≤ n) :
    Algebra.adjoin ℚ {alpha n} ≤ (maxRealSubfield n).toSubalgebra := by
  exact Algebra.adjoin_le (Set.singleton_subset_iff.mpr (alpha_in_fixedField n hn))

-- ============================================================================
-- § 5b. IntermediateField degree computation
-- ============================================================================

/-- The IntermediateField generated by α over ℚ in CyclotomicField. -/
noncomputable def alphaField :
    IntermediateField ℚ (CyclotomicField n ℚ) :=
  IntermediateField.adjoin ℚ ({alpha n} : Set (CyclotomicField n ℚ))

/-- α is in the alpha field. -/
theorem alpha_mem_alphaField :
    alpha n ∈ alphaField n := by
  apply IntermediateField.subset_adjoin
  exact Set.mem_singleton _

/-- alphaField ≤ maxRealSubfield. -/
theorem alphaField_le_maxRealSubfield (hn : 3 ≤ n) :
    alphaField n ≤ maxRealSubfield n := by
  exact IntermediateField.adjoin_le_iff.mpr
    (Set.singleton_subset_iff.mpr (alpha_in_fixedField n hn))

/-- [CyclotomicField n ℚ : alphaField n] ≤ 2.
    ζ satisfies X² - αX + 1 = 0 over ℚ(α), so [K:ℚ(α)] ≤ 2. -/
theorem finrank_over_alphaField (hn : 3 ≤ n) :
    Module.finrank (alphaField n) (CyclotomicField n ℚ) ≤ 2 := by
  set F := alphaField n
  set ζ := abstractZeta n
  set α := alpha n
  have hζ_ne : ζ ≠ 0 := (abstractZeta_isPrimRoot n).ne_zero (by omega)
  have hζ_pr := abstractZeta_isPrimRoot n
  have h_int_ζ : IsIntegral ℚ ζ := Algebra.IsIntegral.isIntegral ζ
  -- ζ generates CyclotomicField over ℚ (same pattern as AngleTrisectionEmbedding)
  have h_gen_Q : IntermediateField.adjoin ℚ ({ζ} : Set (CyclotomicField n ℚ)) = ⊤ := by
    rw [eq_top_iff]; intro x _
    apply IntermediateField.algebra_adjoin_le_adjoin ℚ ({ζ} : Set _)
    have hx_in := IsCyclotomicExtension.adjoin_roots (S := {n}) (A := ℚ)
      (B := CyclotomicField n ℚ) x
    have h_le : Algebra.adjoin ℚ {b : CyclotomicField n ℚ |
        ∃ n₁ ∈ ({n} : Set ℕ), n₁ ≠ 0 ∧ b ^ n₁ = 1} ≤
        Algebra.adjoin ℚ ({ζ} : Set (CyclotomicField n ℚ)) := by
      apply Algebra.adjoin_le
      rintro b ⟨m, hm_mem, -, hb_pow⟩
      simp only [Set.mem_singleton_iff] at hm_mem; subst hm_mem
      obtain ⟨k, -, rfl⟩ := hζ_pr.eq_pow_of_pow_eq_one hb_pow
      exact Subalgebra.pow_mem _ (Algebra.subset_adjoin (Set.mem_singleton ζ)) k
    exact h_le hx_in
  -- ζ generates K over F
  have h_gen_F : IntermediateField.adjoin (↥F)
      ({ζ} : Set (CyclotomicField n ℚ)) = ⊤ :=
    IntermediateField.adjoin_eq_top_of_adjoin_eq_top ℚ h_gen_Q
  -- ζ is integral over F
  have h_int_ζF : IsIntegral (↥F) ζ := .of_finite ↥F _
  -- finrank F K = natDegree(minpoly F ζ)
  have h_finrank_eq : Module.finrank (↥F) (CyclotomicField n ℚ) =
      (minpoly (↥F) ζ).natDegree := by
    have := IntermediateField.adjoin.finrank h_int_ζF
    erw [h_gen_F, IntermediateField.finrank_top'] at this
    exact this
  -- Construct annihilating polynomial X² - αX + 1 over F
  set αF : ↥F := ⟨α, alpha_mem_alphaField n⟩
  set p : Polynomial ↥F :=
    Polynomial.C 1 * Polynomial.X ^ 2 +
    Polynomial.C (-αF) * Polynomial.X +
    Polynomial.C 1
  -- aeval ζ p = 0
  have h_aeval : Polynomial.aeval ζ p = 0 := by
    have h := zeta_quadratic_over_alpha n (by omega : 0 < n)
    -- Evaluate polynomial at ζ: 1*ζ² + (-α)*ζ + 1
    simp only [p, Polynomial.aeval_add, Polynomial.aeval_mul,
      Polynomial.aeval_C, Polynomial.aeval_X, Polynomial.aeval_X_pow,
      one_mul, map_one, map_neg]
    -- algebraMap ↥F → K sends αF to α (via the subtype inclusion)
    have hv : (algebraMap (↥F) (CyclotomicField n ℚ)) αF = α := rfl
    rw [hv]; linarith
  -- natDegree p = 2
  have h_deg_p : p.natDegree = 2 :=
    Polynomial.natDegree_quadratic (one_ne_zero (α := ↥F))
  -- minpoly divides p, so deg(minpoly) ≤ 2
  have h_dvd := minpoly.dvd (↥F) ζ h_aeval
  have h_p_ne_zero : p ≠ 0 := by
    intro hp; rw [hp, Polynomial.natDegree_zero] at h_deg_p; omega
  rw [h_finrank_eq]
  exact le_trans (Polynomial.natDegree_le_of_dvd h_dvd h_p_ne_zero) (le_of_eq h_deg_p)

/-- [alphaField : ℚ] ≥ φ(n)/2. -/
theorem alphaField_degree_ge (hn : 3 ≤ n) :
    Module.finrank ℚ (alphaField n) ≥ Nat.totient n / 2 := by
  set F := alphaField n
  have htower := (Module.finrank_mul_finrank ℚ (↥F) (CyclotomicField n ℚ)).symm
  have hKQ : Module.finrank ℚ (CyclotomicField n ℚ) = Nat.totient n :=
    cyclotomic_finrank n
  have hKF := finrank_over_alphaField n hn
  rw [hKQ] at htower
  have h_ef_pos : 0 < Module.finrank (↥F) (CyclotomicField n ℚ) := by
    by_contra h
    push_neg at h
    have h0 : Module.finrank (↥F) (CyclotomicField n ℚ) = 0 := by omega
    rw [h0, mul_zero] at htower
    linarith [(Nat.totient_pos).mpr (show 0 < n by omega)]
  -- finrank ℚ F * finrank F K = φ(n) and finrank F K ≤ 2
  -- So finrank ℚ F * 2 ≥ φ(n), hence finrank ℚ F ≥ φ(n)/2
  have h1 : Module.finrank ℚ ↥F * 2 ≥ Nat.totient n := by
    calc Module.finrank ℚ ↥F * 2
        ≥ Module.finrank ℚ ↥F * Module.finrank (↥F) (CyclotomicField n ℚ) := by
          apply Nat.mul_le_mul_left; omega
      _ = Nat.totient n := htower.symm
  omega

/-- [alphaField : ℚ] ≤ φ(n)/2. -/
set_option maxHeartbeats 400000 in
theorem alphaField_degree_le (hn : 3 ≤ n) :
    Module.finrank ℚ (alphaField n) ≤ Nat.totient n / 2 := by
  have hle := alphaField_le_maxRealSubfield n hn
  -- finrank monotonicity for IntermediateField inclusion
  have h_sub_le : (alphaField n).toSubmodule ≤ (maxRealSubfield n).toSubmodule :=
    fun _ hx => hle hx
  have h_mono : Module.finrank ℚ (alphaField n) ≤
      Module.finrank ℚ (maxRealSubfield n) :=
    Submodule.finrank_mono h_sub_le
  -- maxRealSubfield has finrank = φ(n)/2
  set F := maxRealSubfield n
  set H := conjSubgroup n
  have hKF : Module.finrank F (CyclotomicField n ℚ) = Nat.card H :=
    IntermediateField.finrank_fixedField_eq_card H
  rw [conjSubgroup_card n hn] at hKF
  have hKQ : Module.finrank ℚ (CyclotomicField n ℚ) = Nat.totient n :=
    cyclotomic_finrank n
  have htower : Module.finrank ℚ (CyclotomicField n ℚ) =
      Module.finrank ℚ F * Module.finrank F (CyclotomicField n ℚ) :=
    (Module.finrank_mul_finrank ℚ F (CyclotomicField n ℚ)).symm
  rw [hKQ, hKF] at htower
  have h_max_deg : Module.finrank ℚ ↥F = Nat.totient n / 2 := by omega
  linarith

/-- [alphaField : ℚ] = φ(n)/2. -/
theorem alphaField_degree (hn : 3 ≤ n) :
    Module.finrank ℚ (alphaField n) = Nat.totient n / 2 := by
  have hge := alphaField_degree_ge n hn
  have hle := alphaField_degree_le n hn
  omega

-- ============================================================================
-- § 6. Minpoly Degree Computation
-- ============================================================================

/-- The minimal polynomial of α over ℚ has degree φ(n)/2. -/
theorem minpoly_alpha_natDegree (hn : 3 ≤ n) :
    (minpoly ℚ (alpha n)).natDegree = Nat.totient n / 2 := by
  have h_int : IsIntegral ℚ (alpha n) := Algebra.IsIntegral.isIntegral _
  have h_adj := IntermediateField.adjoin.finrank h_int
  rw [show IntermediateField.adjoin ℚ {alpha n} = alphaField n from rfl] at h_adj
  rw [alphaField_degree n hn] at h_adj
  linarith [h_adj]

-- ============================================================================
-- § 7. Connection to cos(2π/n)
-- ============================================================================

/-- There exists a ℚ-algebra embedding of CyclotomicField into ℂ that sends
    α = ζ + ζ⁻¹ to 2cos(2π/n). Proved in AngleTrisectionEmbedding.lean. -/
theorem exists_embedding_alpha_eq_2cos (hn : 3 ≤ n) :
    ∃ φ : CyclotomicField n ℚ →ₐ[ℚ] ℂ,
    φ (alpha n) = ↑(2 * Real.cos (2 * Real.pi / ↑n)) :=
  AngleTrisectionEmbedding.exists_embedding_alpha_eq_2cos n hn

/-- alphaCos = α/2. Under the right embedding, maps to cos(2π/n). -/
noncomputable def alphaCos : CyclotomicField n ℚ :=
  alpha n / 2

/-- alphaCos generates the same IntermediateField as alpha. -/
theorem alphaCosField_eq_alphaField :
    IntermediateField.adjoin ℚ ({alphaCos n} : Set (CyclotomicField n ℚ)) =
    alphaField n := by
  simp only [alphaField]
  apply le_antisymm
  · apply IntermediateField.adjoin_le_iff.mpr
    intro x hx; rw [Set.mem_singleton_iff] at hx; subst hx
    have h_mem_a : alpha n ∈ IntermediateField.adjoin ℚ ({alpha n} :
        Set (CyclotomicField n ℚ)) := by
      apply IntermediateField.subset_adjoin; exact Set.mem_singleton _
    have h_mem_2 : (2 : CyclotomicField n ℚ) ∈ IntermediateField.adjoin ℚ ({alpha n} :
        Set (CyclotomicField n ℚ)) :=
      IntermediateField.algebraMap_mem _ 2
    exact div_mem h_mem_a h_mem_2
  · apply IntermediateField.adjoin_le_iff.mpr
    intro x hx; rw [Set.mem_singleton_iff] at hx; subst hx
    have h_mem_ac : alphaCos n ∈ IntermediateField.adjoin ℚ ({alphaCos n} :
        Set (CyclotomicField n ℚ)) := by
      apply IntermediateField.subset_adjoin; exact Set.mem_singleton _
    have heq : alphaCos n * 2 = alpha n := by unfold alphaCos; field_simp
    rw [← heq]
    exact mul_mem h_mem_ac (IntermediateField.algebraMap_mem _ 2)

/-- natDegree(minpoly ℚ alphaCos) = φ(n)/2. -/
theorem minpoly_alphaCos_natDegree (hn : 3 ≤ n) :
    (minpoly ℚ (alphaCos n)).natDegree = Nat.totient n / 2 := by
  have h_int : IsIntegral ℚ (alphaCos n) := Algebra.IsIntegral.isIntegral _
  have h_adj := IntermediateField.adjoin.finrank h_int
  rw [alphaCosField_eq_alphaField] at h_adj
  rw [alphaField_degree n hn] at h_adj
  linarith [h_adj]

-- ============================================================================
-- § 8. Proving cos_minimal_poly_degree
-- ============================================================================

/-- cos(2π/n) satisfies a monic polynomial over ℚ of degree φ(n)/2. -/
theorem cos_minimal_poly_degree (hn : 3 ≤ n) :
    ∃ P : ℚ[X], P.Monic ∧ P.natDegree = Nat.totient n / 2 ∧
    Polynomial.aeval (Real.cos (2 * Real.pi / ↑n)) P = 0 := by
  use minpoly ℚ (alphaCos n)
  refine ⟨minpoly.monic (Algebra.IsIntegral.isIntegral _),
    minpoly_alphaCos_natDegree n hn, ?_⟩
  obtain ⟨φ, hφ_alpha⟩ := exists_embedding_alpha_eq_2cos n hn
  -- φ(alphaCos) = cos(2π/n) in ℂ
  have h_emb : φ (alphaCos n) = ↑(Real.cos (2 * Real.pi / ↑n)) := by
    simp only [alphaCos, map_div₀, hφ_alpha, map_ofNat]
    push_cast
    ring
  -- aeval (φ(alphaCos)) (minpoly ℚ alphaCos) = 0 in ℂ
  have h_aeval_C : Polynomial.aeval (φ (alphaCos n)) (minpoly ℚ (alphaCos n)) = 0 := by
    have := minpoly.aeval ℚ (φ (alphaCos n))
    rwa [minpoly.algHom_eq φ φ.injective] at this
  rw [h_emb] at h_aeval_C
  -- Transfer from ℂ to ℝ via injectivity of ℝ ↪ ℂ
  set c := Real.cos (2 * Real.pi / ↑n)
  have h_transfer : (↑(Polynomial.aeval c (minpoly ℚ (alphaCos n))) : ℂ) = 0 := by
    rw [show (↑(Polynomial.aeval c (minpoly ℚ (alphaCos n))) : ℂ) =
        Polynomial.aeval (↑c : ℂ) (minpoly ℚ (alphaCos n)) from
      (Polynomial.aeval_algHom_apply (IsScalarTower.toAlgHom ℚ ℝ ℂ) c _).symm]
    exact h_aeval_C
  exact_mod_cast h_transfer

/-- cos(2π/n) is algebraic over ℚ. -/
theorem cos_algebraic_from_cyclotomic (hn : 3 ≤ n) :
    IsAlgebraic ℚ (Real.cos (2 * Real.pi / ↑n)) := by
  obtain ⟨P, hP_monic, _, hP_root⟩ := cos_minimal_poly_degree n hn
  exact ⟨P, hP_monic.ne_zero, hP_root⟩

-- ============================================================================
-- § 9. cos_extension_is_galois
-- ============================================================================

/-- For n ≥ 3, there exists an intermediate field of ℝ/ℚ containing cos(2π/n)
    with finrank = φ(n)/2. -/
theorem cos_extension_is_galois (hn : 3 ≤ n) :
    ∃ (K : IntermediateField ℚ ℝ),
    FiniteDimensional ℚ K ∧
    Real.cos (2 * Real.pi / ↑n) ∈ K ∧
    Module.finrank ℚ K = Nat.totient n / 2 := by
  set c := Real.cos (2 * Real.pi / ↑n)
  use IntermediateField.adjoin ℚ ({c} : Set ℝ)
  have h_alg := cos_algebraic_from_cyclotomic n hn
  have h_int : IsIntegral ℚ c := h_alg.isIntegral
  refine ⟨?_, ?_, ?_⟩
  · exact IntermediateField.finiteDimensional_adjoin (fun x hx => by
      rw [Set.mem_singleton_iff] at hx; subst hx; exact h_int)
  · apply IntermediateField.subset_adjoin; exact Set.mem_singleton c
  · have h_adj := IntermediateField.adjoin.finrank h_int
    obtain ⟨P, hP_monic, hP_deg, hP_root⟩ := cos_minimal_poly_degree n hn
    have h_le : (minpoly ℚ c).natDegree ≤ Nat.totient n / 2 :=
      le_trans (Polynomial.natDegree_le_of_dvd (minpoly.dvd ℚ _ hP_root) hP_monic.ne_zero)
        (le_of_eq hP_deg)
    have h_ge : (minpoly ℚ c).natDegree ≥ Nat.totient n / 2 := by
      obtain ⟨φ, hφ_alpha⟩ := exists_embedding_alpha_eq_2cos n hn
      have h_emb : φ (alphaCos n) = ↑c := by
        simp only [alphaCos, c, map_div₀, hφ_alpha, map_ofNat]; push_cast; ring
      have h1 : minpoly ℚ (φ (alphaCos n)) = minpoly ℚ (alphaCos n) :=
        minpoly.algHom_eq φ φ.injective _
      have h2 : minpoly ℚ (↑c : ℂ) = minpoly ℚ c :=
        minpoly.algHom_eq (IsScalarTower.toAlgHom ℚ ℝ ℂ) Complex.ofReal_injective _
      rw [h_emb, h2] at h1
      rw [h1, minpoly_alphaCos_natDegree n hn]
    omega

-- ============================================================================
-- § 10. Axiom Inventory
-- ============================================================================

/-
  AXIOM STATUS (updated by researcher-2, 2026-03-14):

  ✅ maximal_real_subfield_degree: PROVED via fixed field of ⟨σ⟩ (§3)
  ✅ zeta_quadratic_over_alpha: PROVED (ζ² - αζ + 1 = 0, §4)
  ✅ embedding_alpha: PROVED (embedding preserves α structure, §4)
  ✅ alpha_in_fixedField: PROVED (α fixed by σ, from conjAut_zeta_eq_inv, §5)
  ✅ alphaField_degree: PROVED ([ℚ(α):ℚ] = φ(n)/2, via IntermediateField, §5b)
  ✅ conjAut_zeta_eq_inv: PROVED (immediate from fromZetaAut_spec, §2)
  ✅ conjAut_sq: PROVED (σ² = 1, via autEquivPow group structure, §2)
  ✅ conjAut_orderOf: PROVED (order = 2, §2)
  ✅ minpoly_alpha_natDegree: PROVED (natDeg = φ(n)/2, §6)
  ✅ cos_minimal_poly_degree: PROVED (minpoly transfer via embedding, §8)
  ✅ cos_extension_is_galois: PROVED (ℚ(cos) has finrank φ(n)/2, §9)
  ✅ cos_algebraic_from_cyclotomic: PROVED (from cos_minimal_poly_degree)

  🔲 exists_embedding_alpha_eq_2cos: AXIOM (∃ φ sending α to 2cos(2π/n))
     Proof approach: PowerBasis.lift with exp(2πi/n) as target root of
     cyclotomic n ℚ = minpoly ℚ ζ. The construction exists but needs
     careful type coercion through IntermediateField.topEquiv.

  PROGRESS: 6 axioms → 0 axioms, 0 sorries
  exists_embedding_alpha_eq_2cos is now a theorem (via AngleTrisectionEmbedding).
-/

-- ============================================================================
-- § 11. Algebraic Chebyshev Identity
-- ============================================================================

/-- Algebraic Chebyshev identity: T_k((x + x⁻¹)/2) = (x^k + x^{-k})/2
    for any invertible x in a field. Proved by induction on k using the
    Chebyshev recurrence T_{k+2}(t) = 2t·T_{k+1}(t) - T_k(t). -/
theorem chebyshev_T_eval_half_sum_inv (K : Type*) [Field K] [Algebra ℚ K]
    (x : K) (hx : x ≠ 0) (k : ℕ) :
    Polynomial.aeval ((x + x⁻¹) / 2) (Chebyshev.T ℚ (k : ℤ)) =
    (x ^ (k : ℤ) + (x ^ (k : ℤ))⁻¹) / 2 := by
  induction k using Nat.strong_rec_on with
  | _ k ih =>
    match k with
    | 0 =>
      simp [Chebyshev.T_zero, Polynomial.aeval_one]
    | 1 =>
      simp [show (1 : ℤ) = ((1 : ℕ) : ℤ) from rfl, Chebyshev.T_one,
        Polynomial.aeval_X, zpow_one]
    | k + 2 =>
      have ih1 := ih (k + 1) (by omega)
      have ih0 := ih k (by omega)
      rw [show ((k + 2 : ℕ) : ℤ) = (↑k : ℤ) + 2 from by omega]
      rw [Chebyshev.T_add_two]
      simp only [map_sub, map_mul, Polynomial.aeval_ofNat, Polynomial.aeval_X]
      rw [ih1, ih0]
      have hxk1 : x ^ ((k : ℤ) + 1) ≠ 0 := zpow_ne_zero _ hx
      have hxk : x ^ (k : ℤ) ≠ 0 := zpow_ne_zero _ hx
      field_simp
      ring

-- ============================================================================
-- § 12. Galois Automorphism for Coprime k
-- ============================================================================

/-- For k coprime to n, the Galois automorphism sending ζ ↦ ζ^k. -/
noncomputable def galAutOfCoprime (hn : 3 ≤ n) (k : ℕ) (hc : Nat.Coprime k n) :
    CyclotomicField n ℚ ≃ₐ[ℚ] CyclotomicField n ℚ := by
  haveI : NeZero n := ⟨by omega⟩
  have hirr := Polynomial.cyclotomic.irreducible_rat (NeZero.pos n)
  exact (IsCyclotomicExtension.autEquivPow (CyclotomicField n ℚ) hirr).symm
    (ZMod.unitOfCoprime k hc)

/-- The Galois automorphism sends ζ to ζ^k.
    Uses the same convert-using-2 pattern as conjAut_sq to bridge
    autToPow and autEquivPow. -/
theorem galAutOfCoprime_spec (hn : 3 ≤ n) (k : ℕ) (hk : k < n) (hc : Nat.Coprime k n) :
    galAutOfCoprime n hn k hc (abstractZeta n) =
    (abstractZeta n) ^ (k : ℤ) := by
  haveI : NeZero n := ⟨by omega⟩
  have hirr := Polynomial.cyclotomic.irreducible_rat (NeZero.pos n)
  set aep := IsCyclotomicExtension.autEquivPow (CyclotomicField n ℚ) hirr
  set τ := galAutOfCoprime n hn k hc
  have hζ := abstractZeta_isPrimRoot n
  -- autEquivPow(τ) = unitOfCoprime k hc (by definition, τ = aep⁻¹(u))
  have h_aep : aep τ = ZMod.unitOfCoprime k hc :=
    MulEquiv.apply_symm_apply _ _
  -- From autToPow_spec: ζ ^ (autToPow(τ)).val = τ(ζ)
  have h_raw := hζ.autToPow_spec ℚ τ
  -- Bridge autToPow and autEquivPow using convert (same pattern as conjAut_sq)
  have h_spec : abstractZeta n ^ ((aep τ : (ZMod n)ˣ) : ZMod n).val =
      τ (abstractZeta n) := by
    convert h_raw using 2
  rw [h_aep] at h_spec
  -- Now h_spec : ζ ^ ((unitOfCoprime k hc : ZMod n).val) = τ(ζ)
  -- Compute: (unitOfCoprime k hc : ZMod n).val = k (since k < n)
  have h_val : ((ZMod.unitOfCoprime k hc : (ZMod n)ˣ) : ZMod n).val = k := by
    show (ZMod.IsUnit.unit _ : ZMod n).val = k
    simp [ZMod.IsUnit.unit, ZMod.unitOfCoprime, Units.IsUnit.unit]
    exact ZMod.val_natCast_of_lt (by omega)
  rw [h_val] at h_spec
  -- h_spec : ζ ^ k = τ(ζ), convert ℕ pow to ℤ pow
  rw [← h_spec, zpow_natCast]

/-- τ_k(alphaCos) is a root of minpoly ℚ alphaCos: immediate from τ_k being
    a ℚ-algebra automorphism. -/
theorem galAut_alphaCos_is_root (hn : 3 ≤ n) (k : ℕ) (hc : Nat.Coprime k n) :
    Polynomial.aeval (galAutOfCoprime n hn k hc (alphaCos n))
      (minpoly ℚ (alphaCos n)) = 0 := by
  set τ := galAutOfCoprime n hn k hc
  rw [show (τ : CyclotomicField n ℚ → _) (alphaCos n) = τ.toAlgHom (alphaCos n) from rfl]
  rw [Polynomial.aeval_algHom_apply τ.toAlgHom (alphaCos n) (minpoly ℚ (alphaCos n))]
  rw [minpoly.aeval, map_zero]

-- ============================================================================
-- § 13. Embedding Transfer
-- ============================================================================

/-- Under the embedding φ, τ_k(alphaCos) maps to cos(2kπ/n).
    Key steps:
    1. τ_k(alphaCos) = (ζ^k + ζ^{-k})/2 (from galAutOfCoprime_spec)
    2. φ((ζ^k + ζ^{-k})/2) = (w^k + w^{-k})/2 (φ is ring hom)
    3. (w^k + w^{-k})/2 = T_k((w + w⁻¹)/2) (algebraic Chebyshev identity)
    4. = T_k(cos(2π/n)) (from embedding property)
    5. = cos(2kπ/n) (from Chebyshev.T_real_cos) -/
theorem galAut_alphaCos_embedding (hn : 3 ≤ n) (k : ℕ) (hk : k < n)
    (hc : Nat.Coprime k n)
    (φ : CyclotomicField n ℚ →ₐ[ℚ] ℂ)
    (hφ : φ (alpha n) = ↑(2 * Real.cos (2 * Real.pi / ↑n))) :
    φ (galAutOfCoprime n hn k hc (alphaCos n)) =
    ↑(Real.cos (2 * ↑k * Real.pi / ↑n)) := by
  set τ := galAutOfCoprime n hn k hc
  set ζ := abstractZeta n
  have hζ_ne : ζ ≠ 0 := (abstractZeta_isPrimRoot n).ne_zero (by omega)
  -- Step 1: τ(alphaCos) = (ζ^k + ζ^{-k})/2
  have h_tau_zeta := galAutOfCoprime_spec n hn k hk hc
  have h_tau_alphaCos : τ (alphaCos n) = (ζ ^ (k : ℤ) + (ζ ^ (k : ℤ))⁻¹) / 2 := by
    simp only [alphaCos, alpha, map_div₀, map_add, map_inv₀, map_ofNat]
    rw [h_tau_zeta]
  -- Step 2: Apply embedding
  rw [h_tau_alphaCos]
  simp only [map_div₀, map_add, map_inv₀, map_zpow₀, map_ofNat]
  -- Goal: (φ(ζ)^k + (φ(ζ)^k)⁻¹) / 2 = ↑(cos(2kπ/n))
  set w := φ ζ
  -- Step 3: Use algebraic Chebyshev identity
  have hw_ne : w ≠ 0 := by
    intro hw; apply hζ_ne
    have : φ ζ = 0 := hw
    exact φ.injective (by rw [this, map_zero])
  have h_cheb := chebyshev_T_eval_half_sum_inv ℂ w hw_ne k
  -- h_cheb : T_k((w + w⁻¹)/2) = (w^k + (w^k)⁻¹)/2
  rw [← h_cheb]
  -- Goal: T_k((w + w⁻¹)/2) = ↑(cos(2kπ/n))
  -- Step 4: (w + w⁻¹)/2 = ↑(cos(2π/n))
  have h_w_cos : (w + w⁻¹) / 2 = ↑(Real.cos (2 * Real.pi / ↑n)) := by
    have : φ (alpha n) = w + w⁻¹ := by
      simp [alpha, map_add, map_inv₀, w]
    rw [hφ] at this
    have h2 : (2 : ℂ) ≠ 0 := two_ne_zero
    field_simp at this ⊢
    linarith [this]
  rw [h_w_cos]
  -- Goal: T_k(↑(cos(2π/n))) = ↑(cos(2kπ/n))
  -- Step 5: Use Chebyshev.T_real_cos lifted to ℂ
  -- T_k evaluated at cos(2π/n) via ℚ → ℝ → ℂ
  rw [show (↑(Real.cos (2 * Real.pi / ↑n)) : ℂ) =
      Complex.ofReal (Real.cos (2 * Real.pi / ↑n)) from rfl]
  rw [show Polynomial.aeval (Complex.ofReal (Real.cos (2 * Real.pi / ↑n)))
      (Chebyshev.T ℚ (↑k : ℤ)) =
    Complex.ofReal (Polynomial.aeval (Real.cos (2 * Real.pi / ↑n))
      (Chebyshev.T ℚ (↑k : ℤ))) from by
    rw [← Polynomial.aeval_algHom_apply (IsScalarTower.toAlgHom ℚ ℝ ℂ)]]
  congr 1
  rw [Chebyshev.aeval_T, Chebyshev.T_real_cos]
  -- Goal: Real.cos (↑k * (2 * π / ↑n)) = Real.cos (2 * ↑k * π / ↑n)
  congr 1; ring

/-- The minimal polynomial of alphaCos in CyclotomicField equals the minimal
    polynomial of cos(2π/n) in ℝ. -/
theorem minpoly_alphaCos_eq_minpoly_cos (hn : 3 ≤ n) :
    minpoly ℚ (alphaCos n) = minpoly ℚ (Real.cos (2 * Real.pi / ↑n)) := by
  obtain ⟨φ, hφ⟩ := exists_embedding_alpha_eq_2cos n hn
  have h_emb : φ (alphaCos n) = ↑(Real.cos (2 * Real.pi / ↑n)) := by
    simp only [alphaCos, map_div₀, hφ, map_ofNat]; push_cast; ring
  have h1 : minpoly ℚ (φ (alphaCos n)) = minpoly ℚ (alphaCos n) :=
    minpoly.algHom_eq φ φ.injective _
  have h2 : minpoly ℚ (↑(Real.cos (2 * Real.pi / ↑n)) : ℂ) =
      minpoly ℚ (Real.cos (2 * Real.pi / ↑n)) :=
    minpoly.algHom_eq (IsScalarTower.toAlgHom ℚ ℝ ℂ) Complex.ofReal_injective _
  rw [h_emb] at h1; rw [← h1, h2]

-- ============================================================================
-- § 14. cos(2kπ/n) is a Root of minpoly ℚ cos(2π/n)
-- ============================================================================

/-- For k coprime to n with k < n, cos(2kπ/n) is a root of
    minpoly(ℚ, cos(2π/n)). This is the key normality result, proved via
    Galois automorphisms of the cyclotomic field. -/
theorem cos_coprime_is_root (hn : 3 ≤ n) (k : ℕ) (hk : k < n) (hc : Nat.Coprime k n) :
    Polynomial.aeval (Real.cos (2 * ↑k * Real.pi / ↑n))
      (minpoly ℚ (Real.cos (2 * Real.pi / ↑n))) = 0 := by
  -- Step 1: τ_k(alphaCos) is a root of minpoly ℚ alphaCos
  have h_root := galAut_alphaCos_is_root n hn k hc
  -- Step 2: minpoly ℚ alphaCos = minpoly ℚ cos(2π/n)
  rw [minpoly_alphaCos_eq_minpoly_cos n hn] at h_root
  -- Step 3: Get embedding and compute φ(τ_k(alphaCos)) = cos(2kπ/n)
  obtain ⟨φ, hφ⟩ := exists_embedding_alpha_eq_2cos n hn
  have h_emb := galAut_alphaCos_embedding n hn k hk hc φ hφ
  -- Step 4: Apply embedding to the root property
  -- aeval (τ_k(αc)) (minpoly ℚ cos(2π/n)) = 0 in CyclotomicField
  -- Apply φ: aeval (φ(τ_k(αc))) (minpoly ℚ cos(2π/n)) = 0 in ℂ
  have h_root_C : Polynomial.aeval (φ (galAutOfCoprime n hn k hc (alphaCos n)))
      (minpoly ℚ (Real.cos (2 * Real.pi / ↑n))) = 0 := by
    rw [Polynomial.aeval_algHom_apply φ.toAlgHom]
    simp [h_root]
  rw [h_emb] at h_root_C
  -- h_root_C : aeval (↑cos(2kπ/n) : ℂ) (minpoly ℚ cos(2π/n)) = 0
  -- Transfer from ℂ to ℝ
  have h_transfer : (↑(Polynomial.aeval (Real.cos (2 * ↑k * Real.pi / ↑n))
      (minpoly ℚ (Real.cos (2 * Real.pi / ↑n)))) : ℂ) = 0 := by
    rw [show (↑(Polynomial.aeval (Real.cos (2 * ↑k * Real.pi / ↑n))
        (minpoly ℚ (Real.cos (2 * Real.pi / ↑n)))) : ℂ) =
      Polynomial.aeval (↑(Real.cos (2 * ↑k * Real.pi / ↑n)) : ℂ)
        (minpoly ℚ (Real.cos (2 * Real.pi / ↑n))) from
      (Polynomial.aeval_algHom_apply (IsScalarTower.toAlgHom ℚ ℝ ℂ) _ _).symm]
    exact h_root_C
  exact_mod_cast h_transfer

end AngleTrisectionOQ02OQ03OQ01
