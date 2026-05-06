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
  3. `cos_pi_gal_card`: |Gal(minpoly ℚ (cos(π/n)))| = φ(2n)/2 — PROVED

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
-- § 4. Splitting Field Degree
-- ============================================================================

/-- The splitting field of minpoly ℚ (cos(π/n)) has degree φ(2n)/2 over ℚ.

    **Proof**:
    Let p = minpoly ℚ (cos(π/n)), with natDegree p = φ(2n)/2 (proved above).
    Let F = maxRealSubfield(2n) = fixed field of ⟨conjAut(2n)⟩ in CyclotomicField(2n,ℚ).
    Let α = alphaCos(2n) ∈ F with minpoly ℚ α = p.

    **Upper bound**: finrank SplittingField ≤ φ(2n)/2
    1. conjSubgroup(2n) is normal in Gal(CyclotomicField(2n,ℚ)/ℚ) (abelian group → every
       subgroup is normal, via autEquivPow isomorphism to (ℤ/2nℤ)×)
    2. Therefore F = fixedField(conjSubgroup) is Galois over ℚ (inferInstance)
    3. Since IsGalois ℚ ↥F and α_F ∈ F, by Normal.splits:
       p = minpoly ℚ α_F splits over F
    4. IsSplittingField.lift: p.SplittingField →ₐ[ℚ] F (injective algebra map)
    5. finrank SplittingField ≤ finrank F = φ(2n)/2

    **Lower bound**: natDegree p ≤ finrank SplittingField
    6. p splits over SplittingField (by definition), with natDegree p = φ(2n)/2 ≥ 1
       roots counted with multiplicity (separable)
    7. Obtain root r ∈ p.rootSet(SplittingField) via card_rootSet = natDegree p > 0
    8. AdjoinRoot.liftHom: AdjoinRoot p →ₐ[ℚ] p.SplittingField (injective, r is a root)
    9. finrank(AdjoinRoot p) = natDegree p ≤ finrank SplittingField -/
private theorem cos_pi_splitting_finrank (n : ℕ) (hn : 3 ≤ n) :
    Module.finrank ℚ (minpoly ℚ (Real.cos (Real.pi / ↑n))).SplittingField =
    Nat.totient (2 * n) / 2 := by
  haveI hne2n : NeZero (2 * n) := ⟨by omega⟩
  have hn' : 3 ≤ 2 * n := by omega
  set c := Real.cos (Real.pi / ↑n) with hc_def
  set p := minpoly ℚ c with hp_def
  set α := AngleTrisectionOQ02OQ03OQ01.alphaCos (2 * n) with hα_def
  set F := AngleTrisectionOQ02OQ03OQ01.maxRealSubfield (2 * n) with hF_def
  -- (A) Integrality of c
  have h_int_c : IsIntegral ℚ c := by
    rw [hc_def, cos_pi_eq_cos_2pi_div_2n n (by omega)]
    exact (AngleTrisectionOQ02OQ03OQ01.cos_algebraic_from_cyclotomic
      (2 * n) hn').isIntegral
  -- (B) p = minpoly ℚ α (same polynomial, via minpoly_alphaCos_eq_minpoly_cos)
  have h_p_eq : p = minpoly ℚ α := by
    rw [hp_def, hc_def, cos_pi_eq_cos_2pi_div_2n n (by omega)]
    rw [← AngleTrisectionOQ02OQ03OQ01.minpoly_alphaCos_eq_minpoly_cos (2 * n) hn']
  -- (C) α ∈ F: alphaCos = alpha/2 and alpha ∈ F
  have h_alpha_mem : AngleTrisectionOQ02OQ03OQ01.alpha (2 * n) ∈ F :=
    AngleTrisectionOQ02OQ03OQ01.alpha_in_fixedField (2 * n) hn'
  have h_α_mem : α ∈ F := by
    simp only [hα_def, AngleTrisectionOQ02OQ03OQ01.alphaCos, hF_def]
    exact IntermediateField.div_mem h_alpha_mem (IntermediateField.algebraMap_mem _ 2)
  -- (D) conjSubgroup(2n) is Normal (Galois group is abelian)
  haveI hNorm : (AngleTrisectionOQ02OQ03OQ01.conjSubgroup (2 * n)).Normal := by
    have hirr := Polynomial.cyclotomic.irreducible_rat (NeZero.pos (2 * n))
    set aep := IsCyclotomicExtension.autEquivPow (CyclotomicField (2 * n) ℚ) hirr
    refine ⟨fun x hx g => ?_⟩
    suffices h : g * x * g⁻¹ = x by rw [h]; exact hx
    have hab : g * x = x * g :=
      aep.injective (by rw [map_mul, map_mul, mul_comm])
    rw [hab]; group
  -- (E) F is Galois over ℚ (fixed field of Normal subgroup of Galois extension)
  haveI h_galois : IsGalois ℚ ↥F := inferInstance
  -- (F) Lift α to an element of ↥F
  let α_F : ↥F := ⟨α, h_α_mem⟩
  -- (G) minpoly ℚ α_F = p
  have h_minpoly_F : minpoly ℚ α_F = p := by
    conv_rhs => rw [h_p_eq]
    exact (minpoly.algHom_eq (IntermediateField.val F)
      (IntermediateField.val F).injective α_F).symm
  -- (H) p splits over F (Normal extension, α_F ∈ F, minpoly splits)
  have h_splits_F : p.Splits (algebraMap ℚ ↥F) := by
    rw [← h_minpoly_F]; exact Normal.splits α_F
  -- (I) SplittingField embeds into F via IsSplittingField.lift
  have h_lift : p.SplittingField →ₐ[ℚ] ↥F :=
    IsSplittingField.lift p.SplittingField p h_splits_F
  -- (J) finrank F = φ(2n)/2
  have h_finrank_F : Module.finrank ℚ ↥F = Nat.totient (2 * n) / 2 :=
    AngleTrisectionOQ02OQ03OQ01.maximal_real_subfield_degree (2 * n) hn'
  -- (K) Upper bound: finrank SplittingField ≤ finrank F = φ(2n)/2
  have h_ub : Module.finrank ℚ p.SplittingField ≤ Nat.totient (2 * n) / 2 :=
    (LinearMap.finrank_le_finrank_of_injective h_lift.toLinearMap
      h_lift.injective).trans h_finrank_F.le
  -- (L) natDegree p = φ(2n)/2
  have h_deg : p.natDegree = Nat.totient (2 * n) / 2 := cos_pi_minpoly_natDegree n hn
  -- (M) p is irreducible and nontrivial
  have h_irred : Irreducible p := minpoly.irreducible h_int_c
  have h_ne : p ≠ 0 := h_irred.ne_zero
  -- (N) Lower bound: natDegree p ≤ finrank SplittingField via AdjoinRoot
  -- Get a root of p in SplittingField using rootSet (separable poly, splits)
  have h_card_roots : 0 < Fintype.card (p.rootSet p.SplittingField) := by
    rw [Polynomial.card_rootSet_eq_natDegree h_irred.separable
      (Polynomial.SplittingField.splits p), h_deg]
    exact Nat.div_pos (Nat.totient_pos.mpr (by omega)) (by omega)
  obtain ⟨⟨root, hroot_mem⟩⟩ := Fintype.card_pos_iff.mp h_card_roots
  have h_aeval_root : Polynomial.aeval root p = 0 :=
    (Polynomial.mem_rootSet.mp hroot_mem).2
  -- Construct injective AlgHom: AdjoinRoot p →ₐ[ℚ] p.SplittingField
  haveI : Fact (Irreducible p) := ⟨h_irred⟩
  set ψ := AdjoinRoot.liftHom p root h_aeval_root
  -- finrank(AdjoinRoot p) = natDegree p (from PowerBasis)
  have h_adj_finrank : Module.finrank ℚ (AdjoinRoot p) = p.natDegree := by
    rw [(AdjoinRoot.powerBasis h_ne).finrank, AdjoinRoot.powerBasis_dim]
  -- finrank SplittingField ≥ finrank AdjoinRoot p = natDegree p = φ(2n)/2
  have h_lb : Nat.totient (2 * n) / 2 ≤ Module.finrank ℚ p.SplittingField := by
    rw [← h_deg, ← h_adj_finrank]
    exact LinearMap.finrank_le_finrank_of_injective ψ.toLinearMap
      (RingHom.injective ψ.toRingHom)
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
   (conjSubgroup abelian → normal via autEquivPow), hence minpoly splits over it
   (Normal.splits), hence SplittingField embeds into F (IsSplittingField.lift).
   Lower bound via AdjoinRoot: get root r ∈ rootSet, AdjoinRoot p →ₐ[ℚ] SplittingField
   gives finrank SplittingField ≥ finrank AdjoinRoot = natDegree p = φ(2n)/2.
   Zero sorries remaining.

## Techniques Used
- **IsCyclotomicExtension**: via AngleTrisectionOQ02OQ03OQ01's `alphaCos`, `maxRealSubfield`
- **Substitution n → 2n**: cos(π/n) = cos(2π/(2n)) is the key reduction
- **Chebyshev polynomials**: underlying the root containment argument (via OQ02OQ03OQ01)
- **Galois fixed field theory**: maxRealSubfield = fixed field of conjAut
-/

end AngleTrisectionCos20GalOQ01OQ02OQ02
