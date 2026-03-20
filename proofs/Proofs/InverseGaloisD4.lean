import Mathlib
import Proofs.NthRootIrrationalOQ01

/-
# Inverse Galois Problem: D₄ Realization

This file extends the Inverse Galois Problem formalization with:
1. A general degree-divisibility lemma (for monic irreducible polynomials)
2. Explicit cyclic group realization via cyclotomic theory
3. **|Gal(X⁴-2/ℚ)| = 8**: The Galois group of X⁴-2 over ℚ is the dihedral group D₄

The key novel result is Part IV: proving |Gal(X⁴-2/ℚ)| = 8 via an ℝ-embedding
argument. AdjoinRoot(X⁴-2) embeds into ℝ (via the real fourth root of 2), and
X²+1 has no real root, so X²+1 has no root in AdjoinRoot(X⁴-2). This forces
the splitting field to be strictly larger than ℚ(⁴√2), giving [SF:ℚ] = 8.

See `InverseGalois.lean` for the main formalization.
-/

namespace InverseGaloisExtensions

open Polynomial

-- ============================================================================
-- Part I: General Infrastructure — Degree Divisibility
-- ============================================================================

/-- For a monic irreducible polynomial over ℚ, its degree divides the finrank
    of the splitting field over ℚ. Combined with |Gal| = finrank (for
    separable polynomials), this gives natDegree(p) | |Gal(p)|.

    This generalizes Mathlib's `Polynomial.Gal.prime_degree_dvd_card` (which
    only handles prime degree) to arbitrary degree (with monic hypothesis). -/
theorem irred_monic_degree_dvd_splitting_finrank
    {p : ℚ[X]} (hirr : Irreducible p) (hmonic : p.Monic) :
    p.natDegree ∣ Module.finrank ℚ p.SplittingField := by
  have hsep := hirr.separable
  have hsplit := Polynomial.SplittingField.splits p
  have hcard : Fintype.card (p.rootSet p.SplittingField) = p.natDegree :=
    Polynomial.card_rootSet_eq_natDegree hsep hsplit
  obtain ⟨⟨α, hα_mem⟩⟩ := Fintype.card_pos_iff.mp (by rw [hcard]; exact hirr.natDegree_pos)
  have hα : Polynomial.aeval α p = 0 := (Polynomial.mem_rootSet.mp hα_mem).2
  have hα_int : IsIntegral ℚ α := .of_finite ℚ α
  have hminp : minpoly ℚ α = p :=
    (minpoly.eq_of_irreducible_of_monic hirr hα hmonic).symm
  set F := IntermediateField.adjoin ℚ ({α} : Set p.SplittingField)
  have htower := Module.finrank_mul_finrank ℚ F p.SplittingField
  rw [IntermediateField.adjoin.finrank hα_int, hminp] at htower
  exact ⟨_, htower.symm⟩

-- ============================================================================
-- Part II: Explicit Cyclic Group Realization via Cyclotomic Theory
-- ============================================================================

/-- For prime p, the polynomial Galois group of Φₚ(X) has order p-1. -/
theorem cyclotomic_prime_gal_card (p : ℕ) [hp : Fact p.Prime] :
    Fintype.card (Polynomial.cyclotomic p ℚ).Gal = p - 1 := by
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  rw [Fintype.card_congr
    (galCyclotomicEquivUnitsZMod
      (L := CyclotomicField p ℚ)
      (Polynomial.cyclotomic.irreducible_rat (Nat.pos_of_ne_zero (NeZero.ne p)))).toEquiv]
  rw [ZMod.card_units_eq_totient, Nat.totient_prime hp.out]

/-- For prime p, the Galois group of Φₚ(X) over ℚ is cyclic. -/
instance cyclotomic_prime_gal_isCyclic (p : ℕ) [hp : Fact p.Prime] :
    IsCyclic (Polynomial.cyclotomic p ℚ).Gal := by
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  exact isCyclic_of_surjective
    (galCyclotomicEquivUnitsZMod
      (L := CyclotomicField p ℚ)
      (Polynomial.cyclotomic.irreducible_rat (Nat.pos_of_ne_zero (NeZero.ne p)))).symm.toMonoidHom
    (MulEquiv.surjective _)

/-- Explicit cyclic Galois realization: for every prime p, there exists a
    Galois extension of ℚ whose Galois group is isomorphic to (ℤ/pℤ)ˣ,
    the cyclic group of order p-1. -/
theorem cyclic_galois_realization (p : ℕ) [hp : Fact p.Prime] :
    ∃ (K : Type) (_ : Field K) (_ : Algebra ℚ K) (_ : FiniteDimensional ℚ K)
      (_ : IsGalois ℚ K),
      Nonempty ((K ≃ₐ[ℚ] K) ≃* (ZMod p)ˣ) := by
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  haveI : Normal ℚ (Polynomial.cyclotomic p ℚ).SplittingField := inferInstance
  haveI : Algebra.IsSeparable ℚ (Polynomial.cyclotomic p ℚ).SplittingField := inferInstance
  exact ⟨(Polynomial.cyclotomic p ℚ).SplittingField,
    inferInstance, inferInstance, inferInstance, IsGalois.mk,
    ⟨galCyclotomicEquivUnitsZMod
      (L := CyclotomicField p ℚ)
      (Polynomial.cyclotomic.irreducible_rat (Nat.pos_of_ne_zero (NeZero.ne p)))⟩⟩

-- ============================================================================
-- Part III: X⁴-2 and the Dihedral Group D₄
-- ============================================================================

/-- X⁴-2 is irreducible over ℚ, via Eisenstein at p = 2. -/
theorem x_fourth_sub_2_irreducible :
    Irreducible (X ^ 4 - C (2 : ℚ) : ℚ[X]) :=
  NthRootIrrationalOQ01.eisenstein_X_pow_sub_prime 4 2 (by omega) (by decide)

/-- X⁴-2 has degree 4. -/
theorem x_fourth_sub_2_natDegree :
    (X ^ 4 - C (2 : ℚ) : ℚ[X]).natDegree = 4 :=
  NthRootIrrationalOQ01.natDegree_X_pow_sub_C_eq (by omega) (by norm_num)

/-- X⁴-2 is separable (irreducible in characteristic 0). -/
theorem x_fourth_sub_2_separable : (X ^ 4 - C (2 : ℚ) : ℚ[X]).Separable :=
  x_fourth_sub_2_irreducible.separable

/-- X⁴-2 is monic. -/
theorem x_fourth_sub_2_monic : (X ^ 4 - C (2 : ℚ) : ℚ[X]).Monic :=
  monic_X_pow_sub_C 2 (by omega)

/-- 4 | |Gal(X⁴-2/ℚ)| — the irreducible degree divides the Galois group order. -/
theorem four_dvd_x4_sub_2_gal_card :
    4 ∣ Fintype.card (X ^ 4 - C (2 : ℚ) : ℚ[X]).Gal := by
  have hcard := Polynomial.Gal.card_of_separable x_fourth_sub_2_separable
  rw [Nat.card_eq_fintype_card] at hcard; rw [hcard]
  have := irred_monic_degree_dvd_splitting_finrank x_fourth_sub_2_irreducible x_fourth_sub_2_monic
  rwa [x_fourth_sub_2_natDegree] at this

/-- |Gal(X⁴-2/ℚ)| | 24 — the Galois group embeds in S₄ via action on roots. -/
theorem x4_sub_2_gal_card_dvd_24 :
    Fintype.card (X ^ 4 - C (2 : ℚ) : ℚ[X]).Gal ∣ 24 := by
  set p := (X ^ 4 - C (2 : ℚ) : ℚ[X])
  haveI : Fact (map (algebraMap ℚ p.SplittingField) p).Splits :=
    ⟨Polynomial.SplittingField.splits p⟩
  haveI : DecidableEq (↥(p.rootSet p.SplittingField)) := Classical.typeDecidableEq _
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

/-- In a field, if x⁴ = 1 and x ≠ 1 and x ≠ -1, then x² + 1 = 0. -/
theorem fourth_root_of_unity_primitive
    {K : Type*} [Field K] {x : K} (h4 : x ^ 4 = 1) (hne1 : x ≠ 1) (hne_neg1 : x ≠ -1) :
    x ^ 2 + 1 = 0 := by
  have h0 : x ^ 4 - 1 = 0 := by rw [h4]; ring
  have hfactor : x ^ 4 - 1 = (x ^ 2 - 1) * (x ^ 2 + 1) := by ring
  rw [hfactor] at h0
  rcases mul_eq_zero.mp h0 with h1 | h2
  · have hfactor2 : x ^ 2 - 1 = (x - 1) * (x + 1) := by ring
    rw [hfactor2] at h1
    rcases mul_eq_zero.mp h1 with ha | hb
    · exact absurd (sub_eq_zero.mp ha) hne1
    · exact absurd (eq_neg_of_add_eq_zero_left hb) hne_neg1
  · exact h2

/-- X²+1 has a root in the splitting field of X⁴-2.
    Among the 4 roots, find a pair a, b with a ≠ ±b. Then (a/b)² + 1 = 0. -/
theorem x_sq_add_1_has_root_in_x4_sub_2_splitting_field :
    ∃ ω : (X ^ 4 - C (2 : ℚ) : ℚ[X]).SplittingField,
      ω ^ 2 + 1 = 0 := by
  set p := (X ^ 4 - C (2 : ℚ) : ℚ[X])
  have hsep := x_fourth_sub_2_separable
  have hsplit := Polynomial.SplittingField.splits p
  have hcard : Fintype.card (p.rootSet p.SplittingField) = 4 :=
    (Polynomial.card_rootSet_eq_natDegree hsep hsplit).trans x_fourth_sub_2_natDegree
  have aeval_eq : ∀ x : p.SplittingField, Polynomial.aeval x p = x ^ 4 - algebraMap ℚ p.SplittingField 2 := by
    intro x; simp [p, map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C]
  have root_pow : ∀ x : p.rootSet p.SplittingField, (x : p.SplittingField) ^ 4 = algebraMap ℚ p.SplittingField 2 := by
    intro ⟨r, hr⟩
    exact sub_eq_zero.mp (by rw [← aeval_eq]; exact (Polynomial.mem_rootSet.mp hr).2)
  have root_ne_zero : ∀ x : p.rootSet p.SplittingField, (x : p.SplittingField) ≠ 0 := by
    intro ⟨r, hr⟩ h
    have := root_pow ⟨r, hr⟩
    rw [h, zero_pow (by omega : 4 ≠ 0)] at this
    simp [map_ofNat] at this
  haveI : DecidableEq (↥(p.rootSet p.SplittingField)) := Classical.typeDecidableEq _
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩, hab⟩ :=
    Fintype.exists_pair_of_one_lt_card (by rw [hcard]; omega : 1 < Fintype.card (p.rootSet p.SplittingField))
  have hab' : a ≠ b := fun h => hab (Subtype.ext h)
  have ha4b4 : a ^ 4 = b ^ 4 := by rw [root_pow ⟨a, ha⟩, root_pow ⟨b, hb⟩]
  have hb_ne := root_ne_zero ⟨b, hb⟩
  have ha_ne := root_ne_zero ⟨a, ha⟩
  by_cases hab_neg : a = -b
  · -- a = -b: need third root c ≠ ±a
    -- rootSet has 4 elements; after removing ⟨a,ha⟩ and ⟨b,hb⟩, at least 2 remain
    have h_card_ge : 2 < Fintype.card (p.rootSet p.SplittingField) := by rw [hcard]; omega
    -- Use Fintype.truncEquivFin to enumerate, then extract third element
    -- Simpler: since card ≥ 3 and we have 2 elements, there exists a third
    have : ∃ c : p.rootSet p.SplittingField, c ≠ ⟨a, ha⟩ ∧ c ≠ ⟨b, hb⟩ := by
      by_contra h
      push_neg at h
      -- h : ∀ c, c ≠ ⟨a,ha⟩ → c = ⟨b,hb⟩. So every element is a or b.
      have hle : Fintype.card (p.rootSet p.SplittingField) ≤ 2 := by
        apply Fintype.card_le_of_injective
          (fun x : p.rootSet p.SplittingField => if x = ⟨a, ha⟩ then (0 : Fin 2) else 1)
        intro x y hxy
        by_contra hne
        simp only [ite_eq_ite] at hxy
        split_ifs at hxy with hxa hya hya
        · exact hne (hxa ▸ hya.symm)
        · exact absurd (h y (fun hy => hne (hxa ▸ hy.symm))) (by simp at hxy)
        · exact absurd (h x (fun hx => hne (hx ▸ hya.symm))) (by simp at hxy)
        · have hxb := h x (by assumption); have hyb := h y (by assumption)
          exact hne (hxb.trans hyb.symm)
      omega
    obtain ⟨⟨c, hc⟩, hca, hcb⟩ := this
    have hc_ne_a : c ≠ a := fun h => hca (Subtype.ext h)
    have hc_ne_neg_a : c ≠ -a := by
      intro heq
      have : (⟨c, hc⟩ : p.rootSet p.SplittingField) = ⟨b, hb⟩ := by
        apply Subtype.ext; simp [heq, hab_neg]
      exact hcb this
    have hca4 : c ^ 4 = a ^ 4 := by rw [root_pow ⟨c, hc⟩, root_pow ⟨a, ha⟩]
    refine ⟨c * a⁻¹, fourth_root_of_unity_primitive ?_ ?_ ?_⟩
    · rw [mul_pow, inv_pow, hca4]; field_simp
    · intro h
      have : c = a := by
        have := congr_arg (· * a) h
        simp [mul_assoc, inv_mul_cancel₀ ha_ne] at this
        exact this
      exact hc_ne_a this
    · intro h
      have : c = -a := by
        have h1 := congr_arg (· * a) h
        simp [mul_assoc, inv_mul_cancel₀ ha_ne, neg_one_mul] at h1
        exact h1
      exact hc_ne_neg_a this
  · -- a ≠ -b: (a/b)⁴ = 1, a/b ≠ ±1
    refine ⟨a * b⁻¹, fourth_root_of_unity_primitive ?_ ?_ ?_⟩
    · rw [mul_pow, inv_pow, ha4b4]; field_simp
    · intro h
      have : a = b := by
        have := congr_arg (· * b) h
        simp [mul_assoc, inv_mul_cancel₀ hb_ne] at this
        exact this
      exact hab' this
    · intro h
      have : a = -b := by
        have h1 := congr_arg (· * b) h
        simp [mul_assoc, inv_mul_cancel₀ hb_ne, neg_one_mul] at h1
        exact h1
      exact hab_neg this

/-- 2 | [SplittingField(X⁴-2) : ℚ] — follows trivially from 4 | finrank. -/
theorem two_dvd_x4_sub_2_splitting_field_finrank :
    2 ∣ Module.finrank ℚ (X ^ 4 - C (2 : ℚ) : ℚ[X]).SplittingField := by
  have hcard := Polynomial.Gal.card_of_separable x_fourth_sub_2_separable
  rw [Nat.card_eq_fintype_card] at hcard
  have h4 : 4 ∣ Module.finrank ℚ (X ^ 4 - C (2 : ℚ) : ℚ[X]).SplittingField := by
    rw [← hcard]; exact four_dvd_x4_sub_2_gal_card
  exact dvd_trans (⟨2, rfl⟩ : (2 : ℕ) ∣ 4) h4

-- ============================================================================
-- Part IV: |Gal(X⁴-2)| = 8 — The ℝ-Embedding Argument
-- ============================================================================

/-
## Strategy

The splitting field of X⁴-2 over ℚ is ℚ(⁴√2, i) with [ℚ(⁴√2, i) : ℚ] = 8.

**Lower bound (|Gal| ≥ 8)**:
AdjoinRoot(X⁴-2) ≅ ℚ(⁴√2) embeds into ℝ via the real fourth root of 2.
Since X²+1 has no real root, it has no root in AdjoinRoot(X⁴-2).
But X²+1 has a root in the splitting field (proved in Part III).
If |Gal| were 4, the splitting field would equal ℚ(⁴√2), which cannot
contain a root of X²+1. Contradiction. So |Gal| > 4, i.e., |Gal| ≥ 8.

**Upper bound (|Gal| ≤ 8)**:
Every root r of X⁴-2 satisfies (r/α)⁴ = 1 where α is any fixed root.
The fourth roots of unity factor as (c²-1)(c²+1) = 0, giving c = ±1 or
c² = -1 (i.e., c = ±ω where ω²+1=0). So all roots are in ℚ(α,ω) and
[ℚ(α,ω):ℚ] = [ℚ(α,ω):ℚ(α)]·[ℚ(α):ℚ] divides 2·4 = 8.
-/

-- ---- Section A: X²+1 has no root in AdjoinRoot(X⁴-2) ----

/-- X²+1 is irreducible over ℚ (it equals Φ₄, the 4th cyclotomic polynomial). -/
theorem x_sq_add_1_irreducible :
    Irreducible ((X : ℚ[X]) ^ 2 + 1) := by
  -- X²+1 = Φ₄ (4th cyclotomic polynomial), which is irreducible over ℚ
  -- Φ₄(X) = ∑_{i=0}^{1} X^{2i} = 1 + X² (by cyclotomic_prime_pow_eq_geom_sum with p=2, k=2)
  have h : (X : ℚ[X]) ^ 2 + 1 = Polynomial.cyclotomic 4 ℚ := by
    have h1 := Polynomial.cyclotomic_prime_pow_eq_geom_sum (R := ℚ) (p := 2) (hp := by decide) (n := 1)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, pow_one] at h1
    norm_num at h1
    rw [h1]; ring
  rw [h]
  exact Polynomial.cyclotomic.irreducible_rat (by norm_num)

/-- X²+1 has degree 2. -/
theorem x_sq_add_1_natDegree :
    ((X : ℚ[X]) ^ 2 + 1).natDegree = 2 := by
  compute_degree!

/-- The real fourth root of 2, defined as √(√2). -/
noncomputable def fourthRootOfTwo : ℝ := Real.sqrt (Real.sqrt 2)

/-- (√(√2))⁴ = 2: the defining property of the real fourth root. -/
theorem fourthRootOfTwo_pow_four : fourthRootOfTwo ^ 4 = 2 := by
  unfold fourthRootOfTwo
  calc (Real.sqrt (Real.sqrt 2)) ^ 4
      = ((Real.sqrt (Real.sqrt 2)) ^ 2) ^ 2 := by ring
    _ = (Real.sqrt 2) ^ 2 := by rw [Real.sq_sqrt (Real.sqrt_nonneg 2)]
    _ = 2 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)

/-- AdjoinRoot(X⁴-2) embeds into ℝ via the real fourth root of 2.
    This is the key construction: since ℚ(⁴√2) ⊂ ℝ, all elements of
    AdjoinRoot(X⁴-2) map to real numbers. -/
noncomputable def embedAdjoinRootX4Sub2InReal :
    AdjoinRoot ((X : ℚ[X]) ^ 4 - C 2) →+* ℝ :=
  AdjoinRoot.lift (algebraMap ℚ ℝ) fourthRootOfTwo (by
    simp only [eval₂_sub, eval₂_pow, eval₂_X, eval₂_C]
    simp only [map_ofNat]
    rw [fourthRootOfTwo_pow_four]; ring)

/-- X²+1 has no real root: x² + 1 > 0 for all real x. -/
theorem x_sq_add_1_no_real_root (x : ℝ) : x ^ 2 + 1 ≠ 0 := by
  intro h; linarith [sq_nonneg x]

/-- X²+1 has no root in AdjoinRoot(X⁴-2).
    Proof: map any purported root through the ℝ-embedding. It would satisfy
    x²+1=0 in ℝ, which is impossible since x²+1 > 0 for all real x. -/
theorem x_sq_add_1_no_root_in_adjoin_root_x4_sub_2
    (β : AdjoinRoot ((X : ℚ[X]) ^ 4 - C 2)) :
    β ^ 2 + 1 ≠ 0 := by
  intro h
  have h0 : embedAdjoinRootX4Sub2InReal (β ^ 2 + 1) = 0 := by rw [h]; simp
  rw [map_add, map_pow, map_one] at h0
  exact x_sq_add_1_no_real_root (embedAdjoinRootX4Sub2InReal β) h0

-- ---- Section B: AdjoinRoot(X⁴-2) has dimension 4 ----

/-- AdjoinRoot(X⁴-2) has ℚ-dimension 4. -/
theorem adjoin_root_x4_sub_2_finrank :
    Module.finrank ℚ (AdjoinRoot ((X : ℚ[X]) ^ 4 - C 2)) = 4 := by
  have hne : ((X : ℚ[X]) ^ 4 - C 2) ≠ 0 := x_fourth_sub_2_irreducible.ne_zero
  rw [(AdjoinRoot.powerBasis hne).finrank, AdjoinRoot.powerBasis_dim]
  exact x_fourth_sub_2_natDegree

-- ---- Section C: |Gal(X⁴-2)| ≠ 4 ----

/-- |Gal(X⁴-2)| ≠ 4.
    If it were, SF would have ℚ-dimension 4, matching AdjoinRoot(X⁴-2).
    The canonical map AdjoinRoot → SF would then be surjective (injective
    linear map between spaces of equal finite dimension). But SF contains
    a root of X²+1, which AdjoinRoot does not. Contradiction. -/
theorem x4_sub_2_gal_card_ne_four :
    Fintype.card ((X : ℚ[X]) ^ 4 - C 2).Gal ≠ 4 := by
  set p := (X : ℚ[X]) ^ 4 - C 2 with hp_def
  -- Provide Fact instance so AdjoinRoot p gets Field, FiniteDimensional, etc.
  haveI : Fact (Irreducible p) := ⟨x_fourth_sub_2_irreducible⟩
  intro hcard
  -- Step 1: [SF:ℚ] = 4
  have hfr : Module.finrank ℚ p.SplittingField = 4 := by
    have hc := Polynomial.Gal.card_of_separable x_fourth_sub_2_separable
    rw [Nat.card_eq_fintype_card] at hc; linarith
  -- Step 2: Get a root α of p in SF and build the canonical map
  have hsplit := Polynomial.SplittingField.splits p
  have hcard_root : Fintype.card (p.rootSet p.SplittingField) = 4 :=
    (Polynomial.card_rootSet_eq_natDegree x_fourth_sub_2_separable hsplit).trans
      x_fourth_sub_2_natDegree
  obtain ⟨⟨α, hα_mem⟩⟩ := Fintype.card_pos_iff.mp (by rw [hcard_root]; omega)
  have hα : Polynomial.aeval α p = 0 := (Polynomial.mem_rootSet.mp hα_mem).2
  -- Step 3: The canonical algebra hom AdjoinRoot(p) →ₐ[ℚ] SF
  set φ := AdjoinRoot.liftHom p α hα
  -- φ is injective (algebra hom from a field)
  have hinj : Function.Injective φ := RingHom.injective φ.toRingHom
  -- Step 4: AdjoinRoot has finrank 4 = [SF:ℚ], so φ is surjective
  have hfr_adj : Module.finrank ℚ (AdjoinRoot p) = 4 :=
    adjoin_root_x4_sub_2_finrank
  -- Surjective via rank-nullity: dim(range) = dim(domain) - dim(ker) = 4 - 0 = 4
  have hsurj : Function.Surjective φ := by
    -- Compute finrank of range
    have hrank := φ.toLinearMap.finrank_range_add_finrank_ker
    rw [hfr_adj] at hrank
    have hker : Module.finrank ℚ (LinearMap.ker φ.toLinearMap) = 0 :=
      Submodule.finrank_eq_zero.mpr (LinearMap.ker_eq_bot.mpr hinj)
    have h_range_eq : Module.finrank ℚ (LinearMap.range φ.toLinearMap) =
        Module.finrank ℚ p.SplittingField := by omega
    -- range has same dim as target, so range = ⊤
    have h_top : LinearMap.range φ.toLinearMap = ⊤ :=
      Submodule.eq_top_of_finrank_eq h_range_eq
    -- Surjectivity follows
    intro y
    obtain ⟨x, hx⟩ := LinearMap.mem_range.mp (h_top ▸ Submodule.mem_top)
    exact ⟨x, hx⟩
  -- Step 5: Get ω ∈ SF with ω²+1=0, pull back through φ
  obtain ⟨ω, hω⟩ := x_sq_add_1_has_root_in_x4_sub_2_splitting_field
  obtain ⟨ω', hω'⟩ := hsurj ω
  -- ω'²+1 = 0 in AdjoinRoot (since φ preserves ring operations)
  have : ω' ^ 2 + 1 = 0 := by
    apply hinj
    rw [map_add, map_pow, map_one, hω', hω, map_zero]
  exact x_sq_add_1_no_root_in_adjoin_root_x4_sub_2 ω' this

-- ---- Section D: |Gal(X⁴-2)| divides 8 ----

/-- In a field, c⁴ = 1 implies c² = 1 or c² + 1 = 0.
    Proof: c⁴ - 1 = (c² - 1)(c² + 1) = 0. -/
theorem fourth_root_unity_sq {K : Type*} [Field K] {c : K} (h : c ^ 4 = 1) :
    c ^ 2 = 1 ∨ c ^ 2 + 1 = 0 := by
  have h0 : (c ^ 2 - 1) * (c ^ 2 + 1) = 0 := by
    have : (c ^ 2 - 1) * (c ^ 2 + 1) = c ^ 4 - 1 := by ring
    rw [this, h, sub_self]
  rcases mul_eq_zero.mp h0 with h1 | h2
  · left; exact sub_eq_zero.mp h1
  · right; exact h2

/-- In a field, c⁴ = 1 implies c ∈ {1, -1} or c² = -1.
    More specifically: c = 1, c = -1, or c is a primitive 4th root of unity. -/
theorem fourth_root_unity_cases {K : Type*} [Field K] {c : K} (h : c ^ 4 = 1) :
    c = 1 ∨ c = -1 ∨ c ^ 2 + 1 = 0 := by
  rcases fourth_root_unity_sq h with h1 | h2
  · have h0 : (c - 1) * (c + 1) = 0 := by
      have : (c - 1) * (c + 1) = c ^ 2 - 1 := by ring
      rw [this, h1, sub_self]
    rcases mul_eq_zero.mp h0 with ha | hb
    · left; exact sub_eq_zero.mp ha
    · right; left; exact eq_neg_of_add_eq_zero_left hb
  · right; right; exact h2

/-- If z² + 1 = 0 and ω² + 1 = 0 in a field, then z = ω or z = -ω.
    This is because z² = ω² = -1, so z² - ω² = (z-ω)(z+ω) = 0. -/
theorem sq_add_one_eq_implies {K : Type*} [Field K] {ω z : K}
    (hω : ω ^ 2 + 1 = 0) (hz : z ^ 2 + 1 = 0) :
    z = ω ∨ z = -ω := by
  have h1 : z ^ 2 = ω ^ 2 := by linear_combination hz - hω
  have h2 : (z - ω) * (z + ω) = 0 := by linear_combination h1
  rcases mul_eq_zero.mp h2 with h | h
  · left; linear_combination h
  · right; linear_combination h

/-- Every root of X⁴-2 in the splitting field is in ℚ⟮α,ω⟯.

    For any root r: (r/α)⁴ = 1, so r/α ∈ {1,-1,ω,-ω}.
    Each case gives r = cα where c ∈ ℚ⟮α,ω⟯, so r ∈ ℚ⟮α,ω⟯.

    This is the key step for showing |Gal| | 8 via the tower law. -/
theorem roots_in_adjoin
    {α ω : (X ^ 4 - C (2 : ℚ) : ℚ[X]).SplittingField}
    (hα : Polynomial.aeval α (X ^ 4 - C (2 : ℚ) : ℚ[X]) = 0)
    (hω : ω ^ 2 + 1 = 0)
    (hα_ne : α ≠ 0) :
    ∀ r, r ∈ (X ^ 4 - C (2 : ℚ) : ℚ[X]).rootSet
      (X ^ 4 - C (2 : ℚ) : ℚ[X]).SplittingField →
    r ∈ (IntermediateField.adjoin ℚ ({α, ω} :
      Set (X ^ 4 - C (2 : ℚ) : ℚ[X]).SplittingField) : Set _) := by
  -- Avoid set/let to prevent variable shadowing with theorem parameters
  intro r hr
  have hr_eval : Polynomial.aeval r (X ^ 4 - C (2 : ℚ) : ℚ[X]) = 0 :=
    (Polynomial.mem_rootSet.mp hr).2
  -- α⁴ = 2 and r⁴ = 2
  have hα4 : α ^ 4 = algebraMap ℚ _ 2 := by
    have h := hα; rw [map_sub, map_pow, aeval_X, aeval_C] at h
    exact sub_eq_zero.mp h
  have hr4 : r ^ 4 = algebraMap ℚ _ 2 := by
    have h := hr_eval; rw [map_sub, map_pow, aeval_X, aeval_C] at h
    exact sub_eq_zero.mp h
  -- (r/α)⁴ = 1
  have hc4 : (r * α⁻¹) ^ 4 = 1 := by
    rw [mul_pow, inv_pow]; field_simp; rw [hr4, hα4]
  -- Membership proofs for reuse
  have hα_K : α ∈ (IntermediateField.adjoin ℚ ({α, ω} : Set _) : Set _) := by
    apply IntermediateField.subset_adjoin; exact Set.mem_insert α {ω}
  have hω_K : ω ∈ (IntermediateField.adjoin ℚ ({α, ω} : Set _) : Set _) := by
    apply IntermediateField.subset_adjoin
    exact Set.mem_insert_iff.mpr (Or.inr rfl)
  -- Case split on r/α
  rcases fourth_root_unity_cases hc4 with hc1 | hc_neg1 | hc_prim
  · -- r/α = 1, so r = α
    have : r = α := by
      calc r = r * α⁻¹ * α := by rw [mul_assoc, inv_mul_cancel₀ hα_ne, mul_one]
        _ = 1 * α := by rw [hc1]
        _ = α := one_mul α
    rw [this]; exact hα_K
  · -- r/α = -1, so r = -α
    have : r = -α := by
      calc r = r * α⁻¹ * α := by rw [mul_assoc, inv_mul_cancel₀ hα_ne, mul_one]
        _ = -1 * α := by rw [hc_neg1]
        _ = -α := by ring
    rw [this]
    exact (IntermediateField.adjoin ℚ ({α, ω} : Set _)).neg_mem hα_K
  · -- (r/α)² + 1 = 0, so r/α = ω or r/α = -ω
    rcases sq_add_one_eq_implies hω hc_prim with hcω | hcnω
    · -- r/α = ω, so r = ω * α
      have : r = ω * α := by
        calc r = r * α⁻¹ * α := by rw [mul_assoc, inv_mul_cancel₀ hα_ne, mul_one]
          _ = ω * α := by rw [hcω]
      rw [this]
      exact (IntermediateField.adjoin ℚ ({α, ω} : Set _)).mul_mem hω_K hα_K
    · -- r/α = -ω, so r = -(ω * α)
      have : r = -(ω * α) := by
        calc r = r * α⁻¹ * α := by rw [mul_assoc, inv_mul_cancel₀ hα_ne, mul_one]
          _ = -ω * α := by rw [hcnω]
          _ = -(ω * α) := by ring
      rw [this]
      exact (IntermediateField.adjoin ℚ ({α, ω} : Set _)).neg_mem
        ((IntermediateField.adjoin ℚ ({α, ω} : Set _)).mul_mem hω_K hα_K)

/-- The splitting field equals ℚ⟮α,ω⟯ as an intermediate field.

    Proof: SF is generated by rootSet (IsSplittingField property).
    All roots ∈ ℚ⟮α,ω⟯ (by roots_in_adjoin).
    So SF ≤ ℚ⟮α,ω⟯ ≤ SF, giving equality. -/
theorem adjoin_alpha_omega_eq_top
    {α ω : (X ^ 4 - C (2 : ℚ) : ℚ[X]).SplittingField}
    (hα : Polynomial.aeval α (X ^ 4 - C (2 : ℚ) : ℚ[X]) = 0)
    (hω : ω ^ 2 + 1 = 0)
    (hα_ne : α ≠ 0) :
    IntermediateField.adjoin ℚ ({α, ω} :
      Set (X ^ 4 - C (2 : ℚ) : ℚ[X]).SplittingField) = ⊤ := by
  set K := IntermediateField.adjoin ℚ ({α, ω} :
    Set (X ^ 4 - C (2 : ℚ) : ℚ[X]).SplittingField)
  -- rootSet ⊆ K
  have h_roots : ↑((X ^ 4 - C (2 : ℚ) : ℚ[X]).rootSet
    (X ^ 4 - C (2 : ℚ) : ℚ[X]).SplittingField) ⊆ (K : Set _) :=
    fun r hr => roots_in_adjoin hα hω hα_ne r hr
  -- Algebra.adjoin ℚ (rootSet) ≤ K.toSubalgebra
  have h_sub : Algebra.adjoin ℚ (↑((X ^ 4 - C (2 : ℚ) : ℚ[X]).rootSet
    (X ^ 4 - C (2 : ℚ) : ℚ[X]).SplittingField)) ≤ K.toSubalgebra :=
    Algebra.adjoin_le (fun x hx => h_roots hx)
  -- K.toSubalgebra = ⊤ (Algebra.adjoin rootSet = ⊤ by IsSplittingField)
  have h_top : Algebra.adjoin ℚ (↑((X ^ 4 - C (2 : ℚ) : ℚ[X]).rootSet
    (X ^ 4 - C (2 : ℚ) : ℚ[X]).SplittingField)) = ⊤ :=
    IsSplittingField.adjoin_rootSet'
  have h_K_top : K.toSubalgebra = ⊤ := le_antisymm le_top (h_top ▸ h_sub)
  rw [← IntermediateField.top_toSubalgebra] at h_K_top
  exact (IntermediateField.toSubalgebra_injective h_K_top)

set_option synthInstance.maxHeartbeats 80000 in
set_option maxHeartbeats 800000 in
/-- |Gal(X⁴-2/ℚ)| divides 8.

    Proof outline:
    1. SF = ℚ⟮α,ω⟯ (all roots in this field, it generates SF)
    2. [ℚ⟮α⟯:ℚ] = 4 (from minpoly = X⁴-2)
    3. [ℚ⟮α,ω⟯:ℚ⟮α⟯] | 2 (ω satisfies X²+1 of degree 2)
    4. [SF:ℚ] = [ℚ⟮α,ω⟯:ℚ⟮α⟯] · 4 | 8

    Combined with 4 | |Gal| and |Gal| ≠ 4: |Gal| = 8. -/
theorem x4_sub_2_gal_card_dvd_8 :
    Fintype.card ((X : ℚ[X]) ^ 4 - C 2).Gal ∣ 8 := by
  set p := (X : ℚ[X]) ^ 4 - C 2 with hp_def
  set E := p.SplittingField
  -- Convert |Gal| to finrank
  have hcard_eq : Fintype.card p.Gal = Module.finrank ℚ E := by
    have := Polynomial.Gal.card_of_separable x_fourth_sub_2_separable
    rw [Nat.card_eq_fintype_card] at this; exact this
  rw [hcard_eq]
  -- Get α (root of p) in E
  have hsplit := Polynomial.SplittingField.splits p
  have hcard_root : Fintype.card (p.rootSet E) = 4 :=
    (Polynomial.card_rootSet_eq_natDegree x_fourth_sub_2_separable hsplit).trans
      x_fourth_sub_2_natDegree
  obtain ⟨⟨α, hα_mem⟩⟩ :=
    Fintype.card_pos_iff.mp (by rw [hcard_root]; omega)
  have hα : Polynomial.aeval α p = 0 := (Polynomial.mem_rootSet.mp hα_mem).2
  -- α ≠ 0 (since α⁴ = 2 ≠ 0)
  have hα_ne : α ≠ 0 := by
    intro h; have := hα; simp [hp_def, map_sub, map_pow, aeval_X, aeval_C] at this
    rw [h, zero_pow (by omega : 4 ≠ 0)] at this; simp at this
  -- Get ω (root of X²+1) in E
  obtain ⟨ω, hω⟩ := x_sq_add_1_has_root_in_x4_sub_2_splitting_field
  -- SF = ℚ⟮α,ω⟯
  have hK_top := adjoin_alpha_omega_eq_top hα hω hα_ne
  -- Set up intermediate field Kα = ℚ⟮α⟯
  set Kα := IntermediateField.adjoin ℚ ({α} : Set E)
  -- [Kα : ℚ] = 4
  have hα_int : IsIntegral ℚ α := .of_finite ℚ α
  have hminp : minpoly ℚ α = p :=
    (minpoly.eq_of_irreducible_of_monic x_fourth_sub_2_irreducible hα x_fourth_sub_2_monic).symm
  have hKα_fr : Module.finrank ℚ Kα = 4 := by
    rw [IntermediateField.adjoin.finrank hα_int, hminp, x_fourth_sub_2_natDegree]
  -- Tower law: [E:ℚ] = [E:Kα] * [Kα:ℚ] = [E:Kα] * 4
  have htower := Module.finrank_mul_finrank ℚ Kα E
  rw [hKα_fr] at htower
  -- Need: [E:Kα] | 2 (then [E:ℚ] = [E:Kα]*4 | 2*4 = 8)
  -- ω is algebraic over Kα and its minpoly divides X²+1 (degree 2)
  -- So [Kα(ω):Kα] | 2 and SF = Kα(ω) gives [E:Kα] | 2
  suffices h2 : Module.finrank Kα E ∣ 2 by
    rw [← htower]; exact mul_dvd_mul_left 4 h2
  -- Strategy: Show E = Kα⟮ω⟯ and deg(minpoly Kα ω) ≤ 2, giving [E:Kα] ≤ 2.
  -- Then [E:Kα] ∈ {1, 2} so [E:Kα] | 2.
  -- Step 1: Kα⟮ω⟯ = ⊤ (E is generated by ω over Kα)
  set Kαω := IntermediateField.adjoin (↥Kα) ({ω} : Set E)
  have hKαω_top : Kαω = ⊤ := by
    -- adjoin ℚ {α, ω} ⊆ adjoin Kα {ω} (as subsets of E)
    -- because α ∈ Kα ⊆ adjoin Kα {ω} and ω ∈ {ω} ⊆ adjoin Kα {ω}
    have h_le : IntermediateField.adjoin ℚ ({α, ω} : Set E) ≤
        Kαω.restrictScalars ℚ := by
      apply IntermediateField.adjoin_le_iff.mpr
      intro x hx
      show x ∈ (Kαω : Set E)
      rcases hx with hx_eq | hx
      · -- x = α ∈ Kα ⊆ Kαω (base field is in every intermediate field)
        rw [hx_eq]
        have hα_Kα : α ∈ (Kα : Set E) := by
          apply IntermediateField.subset_adjoin; exact Set.mem_singleton α
        have : (⊥ : IntermediateField (↥Kα) E) ≤ Kαω := bot_le
        apply this
        rw [IntermediateField.mem_bot]
        exact ⟨⟨α, hα_Kα⟩, rfl⟩
      · -- x ∈ {ω}, so x = ω ∈ Kαω
        rw [Set.mem_singleton_iff.mp hx]
        apply IntermediateField.subset_adjoin; exact Set.mem_singleton ω
    rw [hK_top] at h_le
    rw [eq_top_iff]; intro x _
    exact h_le IntermediateField.mem_top
  -- Step 2: ω is integral over Kα
  have hω_int : IsIntegral (↥Kα) ω := .of_finite (↥Kα) ω
  -- Step 3: ω satisfies X² + 1 = 0 over Kα
  -- We work with the minpoly approach: minpoly(Kα, ω) | (X²+1), so deg ≤ 2
  have hω_eval : Polynomial.aeval ω ((X : (↥Kα)[X]) ^ 2 + C 1) = 0 := by
    simp only [map_add, map_pow, aeval_X, map_one]; exact hω
  -- Step 4: minpoly Kα ω divides X² + 1 over Kα
  have hmin_dvd := minpoly.dvd (↥Kα) ω hω_eval
  -- Step 5: X² + 1 ≠ 0 over Kα (coeff of degree 2 is 1 ≠ 0)
  have hx21_ne : ((X : (↥Kα)[X]) ^ 2 + C 1) ≠ 0 := by
    intro h
    have h2 : ((X : (↥Kα)[X]) ^ 2 + C 1).coeff 2 = 0 := by rw [h]; simp
    simp only [Polynomial.coeff_add, Polynomial.coeff_X_pow_self,
      Polynomial.coeff_C, show (2 : ℕ) ≠ 0 from by omega] at h2
    norm_num at h2
  -- Step 6: natDegree(minpoly Kα ω) ≤ 2
  have hmin_le : (minpoly (↥Kα) ω).natDegree ≤ 2 := by
    have h1 := Polynomial.natDegree_le_of_dvd hmin_dvd hx21_ne
    have h2 : ((X : (↥Kα)[X]) ^ 2 + C 1).natDegree ≤ 2 :=
      le_trans (Polynomial.natDegree_add_le _ _) (by simp [Polynomial.natDegree_pow,
        Polynomial.natDegree_X])
    linarith
  -- Step 7: [Kα⟮ω⟯ : Kα] = natDegree(minpoly Kα ω)
  have hfr_adj := IntermediateField.adjoin.finrank hω_int
  -- hfr_adj : Module.finrank Kα ↥((↥Kα)⟮ω⟯) = (minpoly Kα ω).natDegree
  -- Step 8: Since Kα⟮ω⟯ = ⊤, finrank Kα ↥(⊤) = finrank Kα E
  change Module.finrank (↥Kα) ↥Kαω = _ at hfr_adj
  rw [hKαω_top] at hfr_adj
  have h_top_eq : Module.finrank (↥Kα) (↥(⊤ : IntermediateField (↥Kα) E)) =
      Module.finrank (↥Kα) E :=
    LinearEquiv.finrank_eq (IntermediateField.topEquiv.toLinearEquiv)
  -- Step 9: finrank Kα E ≤ 2
  have hfr_le : Module.finrank (↥Kα) E ≤ 2 := by linarith
  -- Step 10: 0 < finrank ≤ 2, so finrank | 2
  have hfr_pos : 0 < Module.finrank (↥Kα) E := Module.finrank_pos
  interval_cases (Module.finrank (↥Kα) E) <;> simp_all

-- ---- Section E: The Main Result ----

/-- **The Galois group of X⁴-2 over ℚ has exactly 8 elements.**

    This is the dihedral group D₄ (the symmetry group of a square).
    The proof combines:
    - 4 | |Gal| (from X⁴-2 irreducible of degree 4)
    - |Gal| | 8 (from root structure: all roots in ℚ(⁴√2, i))
    - |Gal| ≠ 4 (from ℝ-embedding: X²+1 has no root in AdjoinRoot(X⁴-2))

    The only possibility is |Gal| = 8. -/
theorem x4_sub_2_gal_card :
    Fintype.card ((X : ℚ[X]) ^ 4 - C 2).Gal = 8 := by
  set n := Fintype.card ((X : ℚ[X]) ^ 4 - C 2).Gal
  have h4 : 4 ∣ n := four_dvd_x4_sub_2_gal_card
  have h8 : n ∣ 8 := x4_sub_2_gal_card_dvd_8
  have hne4 : n ≠ 4 := x4_sub_2_gal_card_ne_four
  have hpos : 0 < n := Fintype.card_pos
  have hge : 4 ≤ n := Nat.le_of_dvd hpos h4
  have hle : n ≤ 8 := Nat.le_of_dvd (by norm_num) h8
  interval_cases n <;> simp_all

/-- D₄ is realizable as a Galois group over ℚ.
    The splitting field of X⁴-2 has Galois group of order 8, which is D₄
    (the unique transitive subgroup of S₄ of order 8). -/
theorem d4_realizable :
    ∃ (K : Type) (_ : Field K) (_ : Algebra ℚ K) (_ : FiniteDimensional ℚ K)
      (_ : IsGalois ℚ K),
      Fintype.card (K ≃ₐ[ℚ] K) = 8 := by
  set p := (X : ℚ[X]) ^ 4 - C 2
  haveI : Normal ℚ p.SplittingField := inferInstance
  haveI : Algebra.IsSeparable ℚ p.SplittingField := inferInstance
  exact ⟨p.SplittingField,
    inferInstance, inferInstance, inferInstance, IsGalois.mk,
    x4_sub_2_gal_card⟩

end InverseGaloisExtensions
