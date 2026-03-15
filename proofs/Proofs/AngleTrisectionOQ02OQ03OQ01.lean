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
  2. -1 ∈ (ℤ/nℤ)* maps to an order-2 automorphism σ (via galCyclotomicEquivUnitsZMod)
  3. H = ⟨σ⟩ is a subgroup of Gal(K/ℚ) of order 2
  4. F = K^H (fixed field of H) has [K:F] = 2 (Artin/fixed field theorem)
  5. Tower law: φ(n) = [K:F]·[F:ℚ] = 2·[F:ℚ], so [F:ℚ] = φ(n)/2
-/

import Mathlib

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
-- § 2. Order-2 Automorphism via (ℤ/nℤ)* ≃ Gal(ℚ(ζₙ)/ℚ)
-- ============================================================================

/-- The Galois group of ℚ(ζₙ)/ℚ is isomorphic to (ℤ/nℤ)*.
    This comes from galCyclotomicEquivUnitsZMod with the cyclotomic polynomial
    being irreducible over ℚ. -/
noncomputable def galEquiv :
    (Polynomial.cyclotomic n ℚ).Gal ≃* (ZMod n)ˣ :=
  galCyclotomicEquivUnitsZMod
    (L := CyclotomicField n ℚ)
    (Polynomial.cyclotomic.irreducible_rat (NeZero.pos n))

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
  -- If conjAut = refl, then conjAut(ζ) = ζ, but conjAut(ζ) = ζ⁻¹
  have h1 : conjAut n (abstractZeta n) = abstractZeta n := by
    rw [h]; simp
  have h2 := conjAut_zeta_eq_inv n
  rw [h1] at h2
  -- h2 : abstractZeta n = (abstractZeta n)⁻¹, i.e., ζ = ζ⁻¹
  have hζ := abstractZeta_isPrimRoot n
  have hζ_ne : abstractZeta n ≠ 0 := hζ.ne_zero (by omega)
  -- From ζ = ζ⁻¹: ζ * ζ⁻¹ = 1, rewrite ζ⁻¹ → ζ to get ζ² = 1
  have h_sq : abstractZeta n ^ 2 = 1 := by
    rw [sq]
    have h3 : abstractZeta n * (abstractZeta n)⁻¹ = 1 := mul_inv_cancel₀ hζ_ne
    rwa [← h2] at h3
  -- orderOf ζ divides 2, but orderOf ζ = n ≥ 3: contradiction
  have h_dvd : orderOf (abstractZeta n) ∣ 2 := orderOf_dvd_of_pow_eq_one h_sq
  have h_ord : orderOf (abstractZeta n) = n := hζ.eq_orderOf.symm
  rw [h_ord] at h_dvd
  omega

/-- σ² = 1: via the group isomorphism Aut(K/ℚ) ≃* (ℤ/nℤ)*.
    conjAut corresponds to -1 ∈ (ℤ/nℤ)*, and (-1)² = 1. -/
theorem conjAut_sq : conjAut n * conjAut n = 1 := by
  have hirr := Polynomial.cyclotomic.irreducible_rat (NeZero.pos n)
  set aep := IsCyclotomicExtension.autEquivPow (CyclotomicField n ℚ) hirr
  -- Use injectivity of autEquivPow: σ₁ = σ₂ iff aep σ₁ = aep σ₂
  apply aep.injective
  rw [map_mul, map_one]
  -- Goal: aep(σ) * aep(σ) = 1 in (ZMod n)ˣ
  set u := aep (conjAut n)
  have hζ := abstractZeta_isPrimRoot n
  have hζ_ne : abstractZeta n ≠ 0 := hζ.ne_zero (NeZero.ne n)
  -- From autToPow_spec and conjAut_zeta_eq_inv: ζ ^ (u : ZMod n).val = ζ⁻¹
  have h_spec : abstractZeta n ^ (u : ZMod n).val = (abstractZeta n)⁻¹ := by
    have h1 := hζ.autToPow_spec ℚ (conjAut n)
    rw [conjAut_zeta_eq_inv n] at h1
    convert h1 using 2
  -- ζ^(k+1) = 1, so n | k+1
  have h_pow_one : abstractZeta n ^ ((u : ZMod n).val + 1) = 1 := by
    rw [pow_succ, h_spec, inv_mul_cancel₀ hζ_ne]
  have h_dvd : n ∣ ((u : ZMod n).val + 1) := by
    have h_ord := hζ.eq_orderOf  -- h_ord : n = orderOf ζ
    rw [h_ord]; exact orderOf_dvd_of_pow_eq_one h_pow_one
  -- k < n and n | k+1, so k = n-1, meaning (u : ZMod n) = -1
  have h_val_lt := ZMod.val_lt (u : ZMod n)
  have h_eq : (u : ZMod n).val = n - 1 := by omega
  -- (u : ZMod n) = -1: val(u) + 1 = n, so ↑(val u + 1) = 0 in ZMod n
  have h_neg1 : (u : ZMod n) = -1 := by
    rw [eq_neg_iff_add_eq_zero]
    have h0 : ((ZMod.val (u : ZMod n) + 1 : ℕ) : ZMod n) = 0 :=
      (ZMod.natCast_zmod_eq_zero_iff_dvd _ _).mpr h_dvd
    rwa [Nat.cast_add, Nat.cast_one, ZMod.natCast_zmod_val] at h0
  -- u * u = 1 since (-1)² = 1
  ext
  show (u : ZMod n) * (u : ZMod n) = 1
  rw [h_neg1, neg_mul_neg, one_mul]

/-- σ has order exactly 2 for n ≥ 3. -/
theorem conjAut_orderOf (hn : 3 ≤ n) : orderOf (conjAut n) = 2 := by
  have h_sq : (conjAut n) ^ 2 = 1 := by rw [sq]; exact conjAut_sq n
  have h_ne : conjAut n ≠ 1 := by
    rw [show (1 : (CyclotomicField n ℚ) ≃ₐ[ℚ] _) = AlgEquiv.refl from rfl]
    exact conjAut_ne_one n hn
  have h_dvd : orderOf (conjAut n) ∣ 2 := orderOf_dvd_of_pow_eq_one h_sq
  have h_ne_one : orderOf (conjAut n) ≠ 1 := by
    intro h
    have := orderOf_eq_one_iff.mp h
    exact h_ne this
  have h_pos := orderOf_pos (conjAut n)
  rcases h_dvd with ⟨k, hk⟩
  omega

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

/-- The degree of the maximal real subfield over ℚ is φ(n)/2 for n ≥ 3.

    Proof: By the fundamental theorem of Galois theory (fixed field theorem),
    [K : F] = |H| = 2, where K = CyclotomicField n ℚ and F = K^H.
    By the tower law, [K:ℚ] = [K:F]·[F:ℚ], so φ(n) = 2·[F:ℚ].
    Therefore [F:ℚ] = φ(n)/2. -/
theorem maximal_real_subfield_degree (hn : 3 ≤ n) :
    ∃ (F : IntermediateField ℚ (CyclotomicField n ℚ)),
    Module.finrank ℚ F = Nat.totient n / 2 := by
  use maxRealSubfield n
  set K := CyclotomicField n ℚ
  set F := maxRealSubfield n
  set H := conjSubgroup n
  -- Step 1: [K:F] = |H| = 2
  have hKF : Module.finrank F K = Nat.card H :=
    IntermediateField.finrank_fixedField_eq_card H
  rw [conjSubgroup_card n hn] at hKF
  -- Step 2: [K:ℚ] = φ(n)
  have hKQ : Module.finrank ℚ K = Nat.totient n := cyclotomic_finrank n
  -- Step 3: Tower law [K:ℚ] = [K:F] · [F:ℚ]
  have htower : Module.finrank ℚ K = Module.finrank ℚ F * Module.finrank F K :=
    (Module.finrank_mul_finrank ℚ F K).symm
  -- Step 4: Combine: φ(n) = [F:ℚ] * 2
  rw [hKQ, hKF] at htower
  -- htower : Nat.totient n = Module.finrank ℚ ↥F * 2
  omega

-- ============================================================================
-- § 4. Alpha and Embedding into ℂ
-- ============================================================================

-- abstractZeta and abstractZeta_isPrimRoot are defined in § 1 above.

/-- α = ζ + ζ⁻¹ in the abstract cyclotomic field. Under any embedding into ℂ,
    this maps to 2cos(2kπ/n) for some k coprime to n. -/
noncomputable def alpha : CyclotomicField n ℚ :=
  abstractZeta n + (abstractZeta n)⁻¹

/-- ζ satisfies X² - αX + 1 = 0: the quadratic relating ζ to α = ζ + ζ⁻¹. -/
theorem zeta_quadratic_over_alpha (hn_pos : 0 < n) :
    let ζ := abstractZeta n
    let α := alpha n
    ζ ^ 2 - α * ζ + 1 = 0 := by
  simp only [alpha]
  set ζ := abstractZeta n
  have hζ : ζ ≠ 0 := (abstractZeta_isPrimRoot n).ne_zero (by omega)
  field_simp
  ring

/-- An embedding CyclotomicField n ℚ →ₐ[ℚ] ℂ exists (since ℂ is algebraically closed
    and contains ℚ). Under this embedding, ζ maps to a primitive n-th root in ℂ. -/
noncomputable def cyclotomicEmbedding :
    CyclotomicField n ℚ →ₐ[ℚ] ℂ :=
  IsAlgClosed.lift (R := ℚ) (S := CyclotomicField n ℚ)

/-- Under the embedding, ζ maps to a primitive n-th root of unity in ℂ. -/
theorem embedding_zeta_isPrimRoot :
    IsPrimitiveRoot (cyclotomicEmbedding n (abstractZeta n)) n :=
  (abstractZeta_isPrimRoot n).map_of_injective (cyclotomicEmbedding n).injective

/-- Under the embedding, α = ζ + ζ⁻¹ maps to w + w⁻¹ where w is a primitive root in ℂ.
    Since w = exp(2πik/n) for some k coprime to n, this equals 2cos(2kπ/n). -/
theorem embedding_alpha :
    cyclotomicEmbedding n (alpha n) =
    cyclotomicEmbedding n (abstractZeta n) +
    (cyclotomicEmbedding n (abstractZeta n))⁻¹ := by
  simp [alpha, map_add, map_inv₀]

-- ============================================================================
-- § 5. ℚ(α) = Fixed Field: α generates the maximal real subfield
-- ============================================================================

/-- α = ζ + ζ⁻¹ is in the fixed field of ⟨σ⟩ (since σ(ζ) = ζ⁻¹). -/
theorem alpha_in_fixedField (hn : 3 ≤ n) :
    alpha n ∈ maxRealSubfield n := by
  -- α ∈ fixedField(H) iff ∀ σ ∈ H, σ α = α
  -- H = zpowers(conjAut n), so suffices: conjAut n α = α
  rw [maxRealSubfield, IntermediateField.mem_fixedField_iff]
  intro σ hσ
  -- σ ∈ zpowers(conjAut n), so σ = conjAut^k for some k
  rw [conjSubgroup] at hσ
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hσ
  -- Since conjAut has order 2, conjAut^k = 1 or conjAut
  have hord := conjAut_orderOf n hn
  have : conjAut n ^ k = conjAut n ^ (k % (2 : ℤ)) := by
    conv_lhs => rw [show k = 2 * (k / 2) + k % 2 from (Int.ediv_add_emod k 2).symm]
    rw [zpow_add, zpow_mul, show (conjAut n : (Polynomial.cyclotomic n ℚ).Gal) ^ (2 : ℤ) = 1
      from by rw [show (2 : ℤ) = 1 + 1 from rfl, zpow_add, zpow_one]; exact conjAut_sq n,
      one_zpow, one_mul]
  rw [this]
  -- k % 2 is 0 or 1
  have hmod : k % 2 = 0 ∨ k % 2 = 1 := Int.emod_two_eq_zero_or_one k
  rcases hmod with h0 | h1
  · -- σ = 1: trivial
    rw [h0, zpow_zero]; simp
  · -- σ = conjAut: need conjAut(α) = α
    rw [h1, zpow_one]
    -- conjAut(ζ + ζ⁻¹) = conjAut(ζ) + conjAut(ζ⁻¹) = ζ⁻¹ + (ζ⁻¹)⁻¹ = ζ⁻¹ + ζ = α
    simp only [alpha, map_add, map_inv₀]
    rw [conjAut_zeta_eq_inv n]
    -- ζ⁻¹ + (ζ⁻¹)⁻¹ = ζ⁻¹ + ζ (since ζ is a unit, (ζ⁻¹)⁻¹ = ζ)
    have hζ_ne : abstractZeta n ≠ 0 :=
      (abstractZeta_isPrimRoot n).ne_zero (by omega)
    rw [inv_inv]
    ring

/-- ℚ(α) ⊆ fixed field (from alpha_in_fixedField). -/
theorem alpha_adjoin_le_fixedField (hn : 3 ≤ n) :
    Algebra.adjoin ℚ {alpha n} ≤ (maxRealSubfield n).toSubalgebra := by
  exact Algebra.adjoin_le (Set.singleton_subset_iff.mpr (alpha_in_fixedField n hn))

-- ============================================================================
-- § 5b. IntermediateField approach to degree computation
-- ============================================================================

-- The Algebra.adjoin approach is blocked by missing Module.Free/Finite instances.
-- IntermediateField.adjoin has these instances automatically, so we use it instead.

/-- The IntermediateField generated by α over ℚ in CyclotomicField. -/
noncomputable def alphaField :
    IntermediateField ℚ (CyclotomicField n ℚ) :=
  IntermediateField.adjoin ℚ ({alpha n} : Set (CyclotomicField n ℚ))

/-- α is in the alpha field (trivial). -/
theorem alpha_mem_alphaField :
    alpha n ∈ alphaField n := by
  apply IntermediateField.subset_adjoin
  exact Set.mem_singleton _

/-- alphaField ≤ maxRealSubfield (from alpha_in_fixedField). -/
theorem alphaField_le_maxRealSubfield (hn : 3 ≤ n) :
    alphaField n ≤ maxRealSubfield n := by
  exact IntermediateField.adjoin_le_iff.mpr
    (Set.singleton_subset_iff.mpr (alpha_in_fixedField n hn))

/-- [CyclotomicField n ℚ : alphaField n] ≤ 2.
    ζ satisfies X² - αX + 1 = 0 over ℚ(α), so the minimal polynomial of ζ over
    ℚ(α) has degree ≤ 2. Since ζ generates K over ℚ(α), [K:ℚ(α)] ≤ 2. -/
theorem finrank_over_alphaField (hn : 3 ≤ n) :
    Module.finrank (alphaField n) (CyclotomicField n ℚ) ≤ 2 := by
  set K := CyclotomicField n ℚ
  set F := alphaField n
  set ζ := abstractZeta n
  set α := alpha n
  -- ζ as an element of K (the ambient field)
  -- Step A: ζ generates K over ℚ, hence also over F
  have hζ_ne : ζ ≠ 0 := (abstractZeta_isPrimRoot n).ne_zero (by omega)
  have h_int_ζ : IsIntegral ℚ ζ := Algebra.IsIntegral.isIntegral ζ
  -- Step B: ζ generates K over ℚ
  set ζK : ↥K := ⟨ζ, by exact SetLike.coe_mem _⟩
  have h_gen_Q : IntermediateField.adjoin ℚ ({ζK} : Set ↥K) = ⊤ := by
    -- ζ is integral over ℚ, so use PowerBasis
    have pb := IntermediateField.adjoin.powerBasis h_int_ζ
    have h_pb_gen : pb.gen = ζK := IntermediateField.adjoin.powerBasis_gen h_int_ζ
    have h_alg_top : Algebra.adjoin ℚ ({ζK} : Set ↥K) = ⊤ := by
      rw [← h_pb_gen]; exact pb.adjoin_gen_eq_top
    exact IntermediateField.adjoin_eq_top_of_algebra h_alg_top
  -- Step B': Lift to F: ζ generates K over F
  have h_gen_F : IntermediateField.adjoin (↥F) ({ζK} : Set ↥K) = ⊤ :=
    IntermediateField.adjoin_eq_top_of_adjoin_eq_top ℚ h_gen_Q
  -- Step C: ζ is integral over F (automatic from FiniteDimensional)
  have h_int_ζF : IsIntegral (↥F) ζK := .of_finite ↥F _
  -- Step D: finrank F K = natDegree(minpoly F ζ)
  have h_finrank_eq : Module.finrank (↥F) ↥K = (minpoly (↥F) ζK).natDegree := by
    have := IntermediateField.adjoin.finrank h_int_ζF
    erw [h_gen_F, IntermediateField.finrank_top'] at this
    exact this
  -- Step E: Construct the annihilating polynomial X² - αX + 1 over F
  set αF : ↥F := ⟨α, alpha_mem_alphaField n⟩
  set p : Polynomial ↥F :=
    Polynomial.C 1 * Polynomial.X ^ 2 +
    Polynomial.C (-αF) * Polynomial.X +
    Polynomial.C 1
  -- Step F: Show aeval ζ p = 0 (i.e., ζ² - αζ + 1 = 0)
  have h_aeval : Polynomial.aeval ζK p = 0 := by
    -- Use Subtype.ext to push to the base type K
    apply_fun (algebraMap ↥K K) using Subtype.val_injective
    simp only [p, map_zero, Polynomial.aeval_add, Polynomial.aeval_mul,
      Polynomial.aeval_C, Polynomial.aeval_X, Polynomial.aeval_X_pow,
      map_add, map_mul, map_pow, map_neg, map_one]
    -- After pushing through algebraMap, the goal should be ζ² - α*ζ + 1 = 0 in K
    -- This is exactly zeta_quadratic_over_alpha
    change (1 : K) * ζK.val ^ 2 + (-((algebraMap ↥F K) αF)) * ζK.val + 1 = 0
    have h_αF_val : (algebraMap ↥F K) αF = α := rfl
    rw [h_αF_val]
    have := zeta_quadratic_over_alpha n (by omega : 0 < n)
    -- zeta_quadratic_over_alpha: ζ ^ 2 - α * ζ + 1 = 0
    linarith
  -- Step G: natDegree p = 2
  have h_deg_p : p.natDegree = 2 :=
    Polynomial.natDegree_quadratic (one_ne_zero (M₀ := ↥F))
  -- Step H: minpoly divides p, so deg(minpoly) ≤ 2
  have h_dvd := minpoly.dvd (↥F) ζK h_aeval
  have h_p_ne_zero : p ≠ 0 := by
    intro hp; rw [hp, Polynomial.natDegree_zero] at h_deg_p; omega
  rw [h_finrank_eq]
  exact le_trans (Polynomial.natDegree_le_of_dvd h_dvd h_p_ne_zero) (le_of_eq h_deg_p)

/-- [alphaField : ℚ] ≥ φ(n)/2: from tower law [K:ℚ] = [K:F] * [F:ℚ]. -/
theorem alphaField_degree_ge (hn : 3 ≤ n) :
    Module.finrank ℚ (alphaField n) ≥ Nat.totient n / 2 := by
  set K := CyclotomicField n ℚ
  set F := alphaField n
  have htower := (Module.finrank_mul_finrank ℚ (↥F) K).symm
  have hKQ : Module.finrank ℚ K = Nat.totient n := cyclotomic_finrank n
  have hKF := finrank_over_alphaField n hn
  -- φ(n) = [F:ℚ] * [K:F] and [K:F] ≤ 2
  -- So [F:ℚ] ≥ φ(n)/2
  rw [hKQ] at htower
  -- htower : Nat.totient n = Module.finrank ℚ ↥F * Module.finrank ↥F K
  have h_ef_pos : 0 < Module.finrank (↥F) K := by
    by_contra h
    push_neg at h
    have h0 : Module.finrank (↥F) K = 0 := by omega
    rw [h0, mul_zero] at htower
    linarith [(Nat.totient_pos).mpr (show 0 < n by omega)]
  -- finrank ℚ F * finrank F K = φ(n) and finrank F K ≤ 2
  -- So finrank ℚ F ≥ φ(n) / 2
  omega

/-- [alphaField : ℚ] ≤ φ(n)/2: since alphaField ≤ maxRealSubfield and
    [maxRealSubfield : ℚ] = φ(n)/2. -/
theorem alphaField_degree_le (hn : 3 ≤ n) :
    Module.finrank ℚ (alphaField n) ≤ Nat.totient n / 2 := by
  have hle := alphaField_le_maxRealSubfield n hn
  have hmax := maximal_real_subfield_degree n hn
  obtain ⟨F_max, hF_max⟩ := hmax
  -- maxRealSubfield n = F_max (by the proof)
  -- alphaField ≤ maxRealSubfield, so [alphaField:ℚ] ≤ [maxRealSubfield:ℚ]
  calc Module.finrank ℚ (alphaField n)
      ≤ Module.finrank ℚ (maxRealSubfield n) :=
        Submodule.finrank_mono (IntermediateField.toSubmodule_le_iff.mpr hle)
    _ = Nat.totient n / 2 := by
        -- From maximal_real_subfield_degree proof
        set K := CyclotomicField n ℚ
        set F := maxRealSubfield n
        set H := conjSubgroup n
        have hKF : Module.finrank F K = Nat.card H :=
          IntermediateField.finrank_fixedField_eq_card H
        rw [conjSubgroup_card n hn] at hKF
        have hKQ : Module.finrank ℚ K = Nat.totient n := cyclotomic_finrank n
        have htower : Module.finrank ℚ K = Module.finrank ℚ F * Module.finrank F K :=
          (Module.finrank_mul_finrank ℚ F K).symm
        rw [hKQ, hKF] at htower
        omega

/-- [alphaField : ℚ] = φ(n)/2. -/
theorem alphaField_degree (hn : 3 ≤ n) :
    Module.finrank ℚ (alphaField n) = Nat.totient n / 2 := by
  have hge := alphaField_degree_ge n hn
  have hle := alphaField_degree_le n hn
  omega

-- Legacy Algebra.adjoin axioms eliminated (2026-03-14):
-- cyclotomic_degree_over_alpha, alpha_adjoin_degree_ge/le were redundant
-- with finrank_over_alphaField, alphaField_degree_ge/le above.
-- The IntermediateField versions are strictly better (auto Module.Free/Finite).

-- ============================================================================
-- § 6. Remaining Axioms (to be proved in future sessions)
-- ============================================================================

/-- cos(2π/n) satisfies a monic polynomial over ℚ of degree φ(n)/2. -/
axiom cos_minimal_poly_degree (hn : 3 ≤ n) :
    ∃ P : ℚ[X], P.Monic ∧ P.natDegree = Nat.totient n / 2 ∧
    Polynomial.aeval (Real.cos (2 * Real.pi / n)) P = 0

omit [NeZero n] in
/-- From cos_minimal_poly_degree, cos(2π/n) is algebraic over ℚ. -/
theorem cos_algebraic_from_cyclotomic (hn : 3 ≤ n) :
    IsAlgebraic ℚ (Real.cos (2 * Real.pi / n)) := by
  obtain ⟨P, hP_monic, _, hP_root⟩ := cos_minimal_poly_degree n hn
  exact ⟨P, hP_monic.ne_zero, hP_root⟩

/-- For n ≥ 3, the extension ℚ(cos(2π/n))/ℚ is Galois of degree φ(n)/2. -/
axiom cos_extension_is_galois (hn : 3 ≤ n) :
    ∃ (K : IntermediateField ℚ ℝ),
    FiniteDimensional ℚ K ∧
    Real.cos (2 * Real.pi / n) ∈ K ∧
    Module.finrank ℚ K = Nat.totient n / 2

-- ============================================================================
-- § 7. Axiom Inventory
-- ============================================================================

/-
  AXIOM STATUS (updated by researcher-1, 2026-03-14):

  ✅ maximal_real_subfield_degree: PROVED via fixed field of ⟨σ⟩ (§3)
  ✅ zeta_quadratic_over_alpha: PROVED (ζ² - αζ + 1 = 0, §4)
  ✅ embedding_alpha: PROVED (embedding preserves α structure, §4)
  ✅ alpha_in_fixedField: PROVED (α fixed by σ, from conjAut_zeta_eq_inv, §5)
  ✅ alpha_adjoin_le_fixedField: PROVED (ℚ(α) ⊆ fixed field, §5)
  ✅ alphaField_degree: PROVED ([ℚ(α):ℚ] = φ(n)/2, via IntermediateField, §5b)
  ✅ alphaField_degree_ge: PROVED (tower law, §5b)
  ✅ alphaField_degree_le: PROVED (finrank monotonicity for IntermediateField, §5b)

  ✅ conjAut_zeta_eq_inv: PROVED (immediate from fromZetaAut_spec, §2)
  ✅ conjAut_sq: PROVED (σ² = 1, via autEquivPow group structure, §2)
  ✅ conjAut_orderOf: PROVED (order = 2, from conjAut_sq + conjAut_ne_one, §2)
  🔲 cyclotomic_degree_over_alpha: AXIOM (Algebra.adjoin version, legacy)
  🔲 alpha_adjoin_degree_ge/le: AXIOMS (Algebra.adjoin version, legacy)
  ❌ cos_minimal_poly_degree: needs connection CyclotomicField → ℝ
  ❌ cos_extension_is_galois: needs normality of fixed field extension

  KEY INSIGHT: IntermediateField.adjoin bypasses the Module.Free/Finite issues that
  blocked Algebra.adjoin. The alphaField_degree proof uses tower law + inclusion
  monotonicity, both of which work for IntermediateField automatically.

  REMAINING WORK:
  - Legacy axioms (cyclotomic_degree_over_alpha, alpha_adjoin_degree_ge/le) could be
    eliminated by connecting IntermediateField ↔ Algebra.adjoin, but are non-critical.
  - cos_minimal_poly_degree and cos_extension_is_galois need embedding into ℝ.
-/

end AngleTrisectionOQ02OQ03OQ01
