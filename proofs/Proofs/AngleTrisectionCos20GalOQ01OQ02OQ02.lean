/-
  Angle Trisection — General Galois Formula via IsCyclotomicExtension (OQ01-OQ02-OQ02)

  **Answer to the open question from AngleTrisectionCos20GalOQ01OQ02:**
  "Can gal_order_eq_totient_div2_general be proved using IsCyclotomicExtension?"

  **YES.** The key observation is that cos(π/n) = cos(2π/(2n)). Applying the
  AngleTrisectionOQ02OQ03OQ01 machinery (which works for cos(2π/m)) with m = 2n gives:

    natDegree(minpoly ℚ (cos(π/n))) = φ(2n)/2   [for all n ≥ 3]

  This directly proves the degree half of the formula. For the Galois group order,
  we need additionally that the splitting field of minpoly(cos(π/n)) has degree φ(2n)/2,
  which follows from ℚ(cos(π/n)) being Galois over ℚ (it is the fixed field of complex
  conjugation in CyclotomicField(2n,ℚ), which is Galois since conjSubgroup is normal
  in the abelian Galois group (ℤ/2nℤ)×).

  **Main results:**
  1. `cos_pi_minpoly_natDegree`: natDegree(minpoly ℚ (cos(π/n))) = φ(2n)/2 — PROVED
  2. `cos_pi_extension_degree`: ∃ K ⊆ ℝ with cos(π/n) ∈ K, [K:ℚ] = φ(2n)/2 — PROVED
  3. `cos_pi_gal_card`: |Gal(minpoly ℚ (cos(π/n)))| = φ(2n)/2 — proved modulo
     normality of ℚ(cos(π/n))/ℚ (documented sorry)

  **Gallery consistency checks** (n=5,7,9 verified against φ(2n)/2 formula):
    n=5: φ(10)/2 = 2  ✓   n=7: φ(14)/2 = 3  ✓   n=9: φ(18)/2 = 3  ✓
-/

import Mathlib
import Proofs.AngleTrisectionOQ02OQ03OQ01
import Proofs.AngleTrisectionCos20GalOQ01OQ02

open Polynomial IntermediateField FiniteDimensional Real

namespace AngleTrisectionCos20GalOQ01OQ02OQ02

-- ============================================================================
-- § 1. The Key Cosine Identity: cos(π/n) = cos(2π/(2n))
-- ============================================================================

/-- cos(π/n) = cos(2π/(2n)) for n ≥ 1.
    This is the arithmetic identity that connects the cos(π/n) family to the
    cos(2π/m) family (handled by AngleTrisectionOQ02OQ03OQ01) via m = 2n. -/
lemma cos_pi_eq_cos_2pi_div_2n (n : ℕ) (hn : 0 < n) :
    Real.cos (Real.pi / ↑n) = Real.cos (2 * Real.pi / ↑(2 * n)) := by
  congr 1
  push_cast
  ring

-- ============================================================================
-- § 2. The Degree Theorem (SORRY-FREE)
-- ============================================================================

/-- **Main Result**: For n ≥ 3, the minimal polynomial of cos(π/n) over ℚ has
    degree φ(2n)/2.

    Proof: cos(π/n) = cos(2π/(2n)), so its minimal polynomial is the same as
    that of cos(2π/(2n)). Applying AngleTrisectionOQ02OQ03OQ01 with m = 2n gives
    the degree φ(2n)/2.

    This answers "YES" to the question: IsCyclotomicExtension CAN prove the formula,
    via the (2n)-th cyclotomic field and the fixed field of complex conjugation. -/
theorem cos_pi_minpoly_natDegree (n : ℕ) (hn : 3 ≤ n) :
    (minpoly ℚ (Real.cos (Real.pi / ↑n))).natDegree = Nat.totient (2 * n) / 2 := by
  haveI : NeZero (2 * n) := ⟨by omega⟩
  have hn' : 3 ≤ 2 * n := by omega
  -- Step 1: Rewrite cos(π/n) as cos(2π/(2n))
  rw [cos_pi_eq_cos_2pi_div_2n n (by omega)]
  -- Step 2: minpoly ℚ (cos(2π/(2n))) = minpoly ℚ (alphaCos (2n)) via embedding
  rw [← AngleTrisectionOQ02OQ03OQ01.minpoly_alphaCos_eq_minpoly_cos (2 * n) hn']
  -- Step 3: natDegree = φ(2n)/2 from the cyclotomic field degree computation
  exact AngleTrisectionOQ02OQ03OQ01.minpoly_alphaCos_natDegree (2 * n) hn'

-- ============================================================================
-- § 3. The Extension Degree (SORRY-FREE)
-- ============================================================================

/-- For n ≥ 3, there is an intermediate field K of ℝ/ℚ containing cos(π/n)
    with [K:ℚ] = φ(2n)/2.

    This comes directly from AngleTrisectionOQ02OQ03OQ01.cos_extension_is_galois
    applied to m = 2n, noting that cos(2π/(2n)) = cos(π/n). -/
theorem cos_pi_extension_degree (n : ℕ) (hn : 3 ≤ n) :
    ∃ (K : IntermediateField ℚ ℝ),
    FiniteDimensional ℚ K ∧
    Real.cos (Real.pi / ↑n) ∈ K ∧
    Module.finrank ℚ K = Nat.totient (2 * n) / 2 := by
  haveI : NeZero (2 * n) := ⟨by omega⟩
  have hn' : 3 ≤ 2 * n := by omega
  obtain ⟨K, hfd, hcos, hdeg⟩ :=
    AngleTrisectionOQ02OQ03OQ01.cos_extension_is_galois (2 * n) hn'
  refine ⟨K, hfd, ?_, hdeg⟩
  -- hcos says: cos(2π/(2n)) ∈ K; we need cos(π/n) ∈ K
  rwa [cos_pi_eq_cos_2pi_div_2n n (by omega)]

-- ============================================================================
-- § 4. Splitting Field Degree (with sorry — normality step)
-- ============================================================================

/-- The splitting field of minpoly ℚ (cos(π/n)) has degree φ(2n)/2 over ℚ.

    **Proof sketch**:
    Let p = minpoly ℚ (cos(π/n)), with natDegree p = φ(2n)/2 (proved above).

    Lower bound: p.SplittingField ⊇ ℚ(root) for any root, so
    finrank ℚ SplittingField ≥ natDegree p = φ(2n)/2.

    Upper bound: ℚ(cos(π/n)) is Galois over ℚ (it is the fixed field of complex
    conjugation in CyclotomicField(2n,ℚ), and conjSubgroup is normal in the
    abelian Galois group (ℤ/2nℤ)×). By normality, p splits completely over
    ℚ(cos(π/n)). By Polynomial.SplittingField.lift, p.SplittingField → ℚ(cos(π/n)),
    giving finrank ℚ SplittingField ≤ φ(2n)/2.

    Both bounds yield finrank ℚ SplittingField = φ(2n)/2.

    **Remaining work**: Formalize that conjSubgroup(2n) is a normal subgroup of
    the Galois group of CyclotomicField(2n,ℚ), and derive IsGalois ℚ K for K =
    maxRealSubfield(2n). Estimated: ~80 lines using Mathlib's abelian group theory. -/
private theorem cos_pi_splitting_finrank (n : ℕ) (hn : 3 ≤ n) :
    Module.finrank ℚ (minpoly ℚ (Real.cos (Real.pi / ↑n))).SplittingField =
    Nat.totient (2 * n) / 2 := by
  set c := Real.cos (Real.pi / ↑n) with hc_def
  haveI : NeZero (2 * n) := ⟨by omega⟩
  have hn' : 3 ≤ 2 * n := by omega
  have h_alg : IsAlgebraic ℚ c := by
    rw [hc_def, cos_pi_eq_cos_2pi_div_2n n (by omega)]
    exact AngleTrisectionOQ02OQ03OQ01.cos_algebraic_from_cyclotomic (2 * n) (by omega)
  have h_int : IsIntegral ℚ c := h_alg.isIntegral
  have h_irred : Irreducible (minpoly ℚ c) := minpoly.irreducible h_int
  have h_sep : (minpoly ℚ c).Separable := h_irred.separable
  have h_deg : (minpoly ℚ c).natDegree = Nat.totient (2 * n) / 2 :=
    cos_pi_minpoly_natDegree n hn
  -- § A: Prove IsGalois ℚ (maxRealSubfield(2n)) via abelian Galois group
  haveI h_gal_cyc : IsGalois ℚ (CyclotomicField (2 * n) ℚ) :=
    AngleTrisectionOQ02OQ03OQ01.cyclotomic_isGalois (2 * n)
  have h_irr_cyc : Irreducible (Polynomial.cyclotomic (2 * n) ℚ) :=
    Polynomial.cyclotomic.irreducible_rat (NeZero.pos (2 * n))
  -- The Galois group is abelian (isomorphic to (ZMod(2n))ˣ via autEquivPow)
  let aep := IsCyclotomicExtension.autEquivPow (CyclotomicField (2 * n) ℚ) h_irr_cyc
  have hcomm : ∀ σ τ : (CyclotomicField (2 * n) ℚ) ≃ₐ[ℚ] (CyclotomicField (2 * n) ℚ),
      σ * τ = τ * σ := fun σ τ =>
    aep.injective (by simp only [map_mul, mul_comm])
  -- conjSubgroup is normal (subgroup of abelian group)
  haveI h_conj_normal : (AngleTrisectionOQ02OQ03OQ01.conjSubgroup (2 * n)).Normal :=
    ⟨fun x hx a => by
      have hab : a * x = x * a := hcomm a x
      have heq : a * x * a⁻¹ = x := by rw [hab]; group
      rw [heq]; exact hx⟩
  -- maxRealSubfield is Galois (fixedField of normal subgroup of Galois group)
  haveI h_gal_max : IsGalois ℚ (AngleTrisectionOQ02OQ03OQ01.maxRealSubfield (2 * n)) :=
    inferInstance
  -- § B: Compute finrank of maxRealSubfield(2n)
  have h_max_fr : Module.finrank ℚ (AngleTrisectionOQ02OQ03OQ01.maxRealSubfield (2 * n)) =
      Nat.totient (2 * n) / 2 := by
    set F := AngleTrisectionOQ02OQ03OQ01.maxRealSubfield (2 * n)
    set H := AngleTrisectionOQ02OQ03OQ01.conjSubgroup (2 * n)
    have hKF : Module.finrank F (CyclotomicField (2 * n) ℚ) = Nat.card H :=
      IntermediateField.finrank_fixedField_eq_card H
    rw [AngleTrisectionOQ02OQ03OQ01.conjSubgroup_card (2 * n) hn'] at hKF
    have hKQ := AngleTrisectionOQ02OQ03OQ01.cyclotomic_finrank (2 * n)
    have htower := (Module.finrank_mul_finrank ℚ F (CyclotomicField (2 * n) ℚ)).symm
    rw [hKF, hKQ] at htower; omega
  -- § C: alphaCos(2n) ∈ maxRealSubfield(2n)
  have h_ac_in : AngleTrisectionOQ02OQ03OQ01.alphaCos (2 * n) ∈
      AngleTrisectionOQ02OQ03OQ01.maxRealSubfield (2 * n) :=
    AngleTrisectionOQ02OQ03OQ01.alphaField_le_maxRealSubfield (2 * n) hn' (by
      rw [← AngleTrisectionOQ02OQ03OQ01.alphaCosField_eq_alphaField]
      exact IntermediateField.subset_adjoin ℚ (Set.mem_singleton _))
  set ac_m : ↥(AngleTrisectionOQ02OQ03OQ01.maxRealSubfield (2 * n)) :=
    ⟨AngleTrisectionOQ02OQ03OQ01.alphaCos (2 * n), h_ac_in⟩ with hac_m_def
  -- § D: minpoly ℚ c = minpoly ℚ (alphaCos(2n))
  have h_mp_eq : minpoly ℚ (AngleTrisectionOQ02OQ03OQ01.alphaCos (2 * n)) = minpoly ℚ c := by
    rw [AngleTrisectionOQ02OQ03OQ01.minpoly_alphaCos_eq_minpoly_cos (2 * n) hn']
    congr 1; exact (cos_pi_eq_cos_2pi_div_2n n (by omega)).symm
  -- § E: minpoly ℚ c splits in maxRealSubfield(2n) via Normal extension
  -- Connect minpoly ℚ ac_m (in maxRealSubfield) to minpoly ℚ (alphaCos(2n)) (in CyclotomicField)
  -- via the injective inclusion maxRealSubfield → CyclotomicField
  have h_mp_ac_m : minpoly ℚ ac_m =
      minpoly ℚ (AngleTrisectionOQ02OQ03OQ01.alphaCos (2 * n)) := by
    have incl := (AngleTrisectionOQ02OQ03OQ01.maxRealSubfield (2 * n)).toSubalgebra.val
    exact (minpoly.algHom_eq incl incl.injective ac_m).symm
  have h_splits : (minpoly ℚ c).Splits
      (algebraMap ℚ ↥(AngleTrisectionOQ02OQ03OQ01.maxRealSubfield (2 * n))) := by
    haveI : Normal ℚ (AngleTrisectionOQ02OQ03OQ01.maxRealSubfield (2 * n)) := inferInstance
    have h_norm_splits : (minpoly ℚ ac_m).Splits
        (algebraMap ℚ ↥(AngleTrisectionOQ02OQ03OQ01.maxRealSubfield (2 * n))) :=
      Normal.splits ac_m
    rwa [h_mp_ac_m, h_mp_eq] at h_norm_splits
  -- § F: Upper bound via lift SplittingField → maxRealSubfield
  -- IsSplittingField.lift: the splitting field (abstract) maps into any field where p splits
  have h_lift : (minpoly ℚ c).SplittingField →ₐ[ℚ]
      ↥(AngleTrisectionOQ02OQ03OQ01.maxRealSubfield (2 * n)) :=
    Polynomial.IsSplittingField.lift _ (minpoly ℚ c) h_splits
  have h_upper : Module.finrank ℚ (minpoly ℚ c).SplittingField ≤
      Nat.totient (2 * n) / 2 := by
    calc Module.finrank ℚ (minpoly ℚ c).SplittingField
        ≤ Module.finrank ℚ ↥(AngleTrisectionOQ02OQ03OQ01.maxRealSubfield (2 * n)) :=
          LinearMap.finrank_le_finrank_of_injective h_lift.injective
      _ = Nat.totient (2 * n) / 2 := h_max_fr
  -- § G: Lower bound via root in SplittingField
  have h_lower : Nat.totient (2 * n) / 2 ≤ Module.finrank ℚ (minpoly ℚ c).SplittingField := by
    -- p splits in SplittingField (by definition), so p has a root there
    have h_sf_splits := Polynomial.IsSplittingField.splits (minpoly ℚ c).SplittingField (minpoly ℚ c)
    have h_nd_pos : 0 < (minpoly ℚ c).natDegree := by
      rw [h_deg]; exact Nat.div_pos (Nat.totient_pos (by omega)) (by norm_num)
    have h_pos : (minpoly ℚ c).degree ≠ 0 := by
      rw [Polynomial.degree_eq_natDegree (minpoly.ne_zero h_int)]
      exact_mod_cast h_nd_pos.ne'
    obtain ⟨r, hr⟩ := Polynomial.exists_root_of_splits (algebraMap ℚ _) h_sf_splits h_pos
    -- r is a root: aeval r p = 0
    have hr_aeval : Polynomial.aeval r (minpoly ℚ c) = 0 := by
      rw [Polynomial.aeval_def]; exact hr
    -- r is integral over ℚ (witnessed by monic polynomial minpoly ℚ c)
    have h_int_r : IsIntegral ℚ r := ⟨minpoly ℚ c, minpoly.monic h_int, hr_aeval⟩
    -- minpoly ℚ r = minpoly ℚ c (irreducibility + r is a root)
    have h_mp_r : minpoly ℚ r = minpoly ℚ c :=
      minpoly.eq_of_irreducible_of_monic (minpoly.monic h_int) hr_aeval h_irred
    -- [ℚ(r):ℚ] = natDegree(minpoly ℚ r) = φ(2n)/2
    have h_fr_adj : Module.finrank ℚ (IntermediateField.adjoin ℚ ({r} :
        Set (minpoly ℚ c).SplittingField)) = Nat.totient (2 * n) / 2 := by
      rw [IntermediateField.adjoin.finrank h_int_r, h_mp_r, h_deg]
    -- ℚ(r) ≤ SplittingField, so finrank SplittingField ≥ natDegree
    set SF := (minpoly ℚ c).SplittingField
    have h_adj_le : Module.finrank ℚ ↥(IntermediateField.adjoin ℚ ({r} : Set SF)) ≤
        Module.finrank ℚ SF := by
      have h_sub : Module.finrank ℚ ↥(IntermediateField.adjoin ℚ ({r} : Set SF)) ≤
          Module.finrank ℚ ↥(⊤ : IntermediateField ℚ SF) :=
        Submodule.finrank_mono
          (IntermediateField.toSubmodule_le.mpr le_top)
      rw [IntermediateField.finrank_top'] at h_sub
      exact h_sub
    linarith [h_fr_adj, h_adj_le]
  omega

-- ============================================================================
-- § 5. The Galois Group Order Theorem
-- ============================================================================

/-- **Galois Group Theorem**: For n ≥ 3, the Galois group of the minimal polynomial
    of cos(π/n) over ℚ has order φ(2n)/2.

    This is the non-tautological replacement for the placeholder in
    AngleTrisectionCos20GalOQ01OQ02.gal_order_eq_totient_div2_general.

    The degree part (natDegree = φ(2n)/2) is fully proved above.
    The Galois order part reduces to the splitting field degree (one sorry). -/
theorem cos_pi_gal_card (n : ℕ) (hn : 3 ≤ n) :
    Fintype.card (minpoly ℚ (Real.cos (Real.pi / ↑n))).Gal =
    Nat.totient (2 * n) / 2 := by
  set c := Real.cos (Real.pi / ↑n) with hc_def
  haveI : NeZero (2 * n) := ⟨by omega⟩
  -- Establish integrality via algebraicity from cyclotomic field
  have h_alg : IsAlgebraic ℚ c := by
    rw [hc_def, cos_pi_eq_cos_2pi_div_2n n (by omega)]
    exact AngleTrisectionOQ02OQ03OQ01.cos_algebraic_from_cyclotomic (2 * n) (by omega)
  have h_int : IsIntegral ℚ c := h_alg.isIntegral
  -- minpoly ℚ c is irreducible (it's a minimal polynomial), hence separable (char 0)
  have h_sep : (minpoly ℚ c).Separable :=
    (minpoly.irreducible h_int).separable
  -- |Gal(p)| = finrank ℚ SplittingField p  (for separable p)
  have hcard := Polynomial.Gal.card_of_separable h_sep
  rw [Nat.card_eq_fintype_card] at hcard
  rw [hcard]
  -- finrank SplittingField = φ(2n)/2
  exact cos_pi_splitting_finrank n hn

/-- **General formula** (non-tautological): For n ≥ 3, |Gal(minpoly ℚ (cos(π/n)))| = φ(2n)/2.

    This replaces the tautological placeholder `Nat.totient (2*n)/2 = Nat.totient (2*n)/2`
    in AngleTrisectionCos20GalOQ01OQ02, answering the open question affirmatively:
    IsCyclotomicExtension infrastructure is sufficient to prove the formula.

    The degree half is fully proved; the Galois order half has one documented sorry. -/
theorem gal_order_eq_totient_div2_general (n : ℕ) (hn : 3 ≤ n) :
    Fintype.card (minpoly ℚ (Real.cos (Real.pi / ↑n))).Gal =
    Nat.totient (2 * n) / 2 :=
  cos_pi_gal_card n hn

-- ============================================================================
-- § 6. Gallery Consistency Checks
-- ============================================================================

-- Verify φ(2n)/2 matches the known cases (n=5,7,9)

theorem totient_formula_n5 : Nat.totient (2 * 5) / 2 = 2 := by decide
theorem totient_formula_n7 : Nat.totient (2 * 7) / 2 = 3 := by decide
theorem totient_formula_n9 : Nat.totient (2 * 9) / 2 = 3 := by decide

/-- natDegree(minpoly ℚ (cos(π/5))) = 2, consistent with |Gal| = 2 for n=5. -/
theorem cos_pi5_minpoly_degree : (minpoly ℚ (Real.cos (Real.pi / 5))).natDegree = 2 := by
  have h := cos_pi_minpoly_natDegree 5 (by norm_num)
  simp only [Nat.cast_ofNat, show Nat.totient (2 * 5) / 2 = 2 from by decide] at h
  exact h

/-- natDegree(minpoly ℚ (cos(π/7))) = 3, consistent with |Gal| = 3 for n=7. -/
theorem cos_pi7_minpoly_degree : (minpoly ℚ (Real.cos (Real.pi / 7))).natDegree = 3 := by
  have h := cos_pi_minpoly_natDegree 7 (by norm_num)
  simp only [Nat.cast_ofNat, show Nat.totient (2 * 7) / 2 = 3 from by decide] at h
  exact h

/-- natDegree(minpoly ℚ (cos(π/9))) = 3, consistent with |Gal| = 3 for n=9. -/
theorem cos_pi9_minpoly_degree : (minpoly ℚ (Real.cos (Real.pi / 9))).natDegree = 3 := by
  have h := cos_pi_minpoly_natDegree 9 (by norm_num)
  simp only [Nat.cast_ofNat, show Nat.totient (2 * 9) / 2 = 3 from by decide] at h
  exact h

-- ============================================================================
-- § 7. Summary
-- ============================================================================

/-!
## Answer to the Open Question

**Q**: Can `gal_order_eq_totient_div2_general` be proved using `IsCyclotomicExtension`?

**A**: Yes. The proof proceeds in three steps:

1. **Reduction**: cos(π/n) = cos(2π/(2n)). This identifies the cos(π/n) family with
   the cos(2π/m) family (with m = 2n), for which AngleTrisectionOQ02OQ03OQ01 provides
   complete IsCyclotomicExtension machinery.

2. **Degree**: natDegree(minpoly ℚ (cos(π/n))) = φ(2n)/2.
   This is FULLY PROVED here: apply AngleTrisectionOQ02OQ03OQ01.minpoly_alphaCos_natDegree
   with m = 2n, using NeZero (2n) and the cosine identity.

3. **Galois order**: |Gal(minpoly)| = φ(2n)/2.
   Reduces to: finrank ℚ (SplittingField p) = φ(2n)/2.
   This follows from: ℚ(cos(π/n)) = maxRealSubfield(2n) is Galois over ℚ
   (conjSubgroup abelian → normal), hence minpoly splits over it, hence
   SplittingField ≅ ℚ(cos(π/n)). One sorry remains on the normality step.

## Techniques Used
- **IsCyclotomicExtension**: via AngleTrisectionOQ02OQ03OQ01's `alphaCos`, `maxRealSubfield`
- **Substitution n → 2n**: cos(π/n) = cos(2π/(2n)) is the key reduction
- **Chebyshev polynomials**: underlying the root containment argument (via OQ02OQ03OQ01)
- **Galois fixed field theory**: maxRealSubfield = fixed field of conjAut
-/

end AngleTrisectionCos20GalOQ01OQ02OQ02
