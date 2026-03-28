/-
  Cyclic Vectors Have Full Lebesgue Measure

  For a nonderogatory matrix M ∈ M_n(ℝ) over the reals, the set of cyclic
  vectors has full Lebesgue measure. Equivalently, the set of non-cyclic vectors
  has measure zero.

  The proof strategy:
  1. Non-cyclic vectors lie in a finite union of proper linear subspaces
     (kernels of cofactor polynomial evaluations μ/qᵢ)
  2. Each proper subspace of ℝⁿ has Lebesgue measure zero
     (via Mathlib's addHaar_submodule)
  3. A finite union of measure-zero sets has measure zero

  This extends the existential result from CayleyHamiltonMinpolyOQ05OQ01.lean
  (nonderogatory ⟹ ∃ cyclic vector) to a measure-theoretic statement:
  "almost every vector is cyclic."
-/
import Mathlib

noncomputable section

namespace CyclicVectorMeasure

open Matrix Polynomial MeasureTheory Measure

attribute [local instance] Classical.propDecidable

variable {n : ℕ}

-- ============================================================
-- SECTION I: Definitions (consistent with OQ05OQ01)
-- ============================================================

def IsCyclicVector (M : Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℝ) : Prop :=
  ∀ p : ℝ[X], p.natDegree < n → (aeval M p).mulVec v = 0 → p = 0

def IsNonderogatory (M : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  minpoly ℝ M = M.charpoly

-- ============================================================
-- SECTION II: Non-Cyclic Vectors Form a Measurable Null Set
-- ============================================================

/-- The kernel of a matrix as a linear map, viewed as a submodule. -/
def cofactorKernel (M : Matrix (Fin n) (Fin n) ℝ) (q : ℝ[X]) :
    Submodule ℝ (Fin n → ℝ) :=
  LinearMap.ker ((aeval M (minpoly ℝ M / q) : Matrix (Fin n) (Fin n) ℝ).mulVecLin)

/-- A nonzero polynomial of degree less than minpoly degree evaluates to a
    nonzero matrix. -/
theorem aeval_ne_zero_of_ne_zero {M : Matrix (Fin n) (Fin n) ℝ}
    {p : ℝ[X]} (hp : p ≠ 0) (hd : p.natDegree < (minpoly ℝ M).natDegree) :
    aeval M p ≠ 0 := by
  intro h
  have hdvd : minpoly ℝ M ∣ p := minpoly.dvd ℝ M h
  have hle := Polynomial.natDegree_le_of_dvd hdvd hp
  omega

/-- The kernel of a nonzero matrix is a proper submodule. -/
theorem ker_mulVecLin_ne_top
    {A : Matrix (Fin n) (Fin n) ℝ} (hA : A ≠ 0) :
    LinearMap.ker A.mulVecLin ≠ ⊤ := by
  intro h
  apply hA
  funext i j
  have h2 : A.mulVecLin (Pi.single j 1) = 0 := by
    rw [← LinearMap.mem_ker]; rw [h]; trivial
  have := congr_fun h2 i
  simp only [mulVecLin_apply, mulVec, dotProduct, Pi.single_apply] at this
  simpa using this

/-- Each cofactor kernel for an irreducible factor is a proper submodule. -/
theorem cofactorKernel_ne_top (M : Matrix (Fin n) (Fin n) ℝ) (hn : 0 < n)
    (hM : IsNonderogatory M)
    (q : ℝ[X]) (hq_dvd : q ∣ minpoly ℝ M) (hq_ne : q ≠ 0) (hq_irr : Irreducible q) :
    cofactorKernel M q ≠ ⊤ := by
  set μ := minpoly ℝ M with hμ_def
  have hμ_monic : μ.Monic := minpoly.monic (isIntegral M)
  have hμ_ne : μ ≠ 0 := hμ_monic.ne_zero
  have h_deg : μ.natDegree = n := by
    rw [hμ_def, hM, Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
  obtain ⟨cf, hcf_eq⟩ := hq_dvd
  have hcf_ne : cf ≠ 0 := right_ne_zero_of_mul (hcf_eq ▸ hμ_ne)
  have hdeg_sum : μ.natDegree = q.natDegree + cf.natDegree :=
    hcf_eq ▸ natDegree_mul hq_ne hcf_ne
  have hq_deg_pos : 0 < q.natDegree := by
    rcases Nat.eq_zero_or_pos q.natDegree with h0 | hpos
    · exfalso; apply hq_irr.1
      have h_coeff_ne : q.coeff 0 ≠ 0 := by
        intro h_eq; exact hq_ne
          (by rw [Polynomial.eq_C_of_natDegree_eq_zero h0, h_eq, map_zero])
      exact Polynomial.eq_C_of_natDegree_eq_zero h0 ▸
        isUnit_C.mpr (IsUnit.mk0 _ h_coeff_ne)
    · exact hpos
  have hcf_deg : cf.natDegree < n := by omega
  have hdiv_eq : μ / q = cf := by
    have hmod : μ % q = 0 := EuclideanDomain.mod_eq_zero.mpr ⟨cf, hcf_eq⟩
    have h1 := EuclideanDomain.div_add_mod μ q
    rw [hmod, add_zero] at h1
    exact mul_left_cancel₀ hq_ne (h1.trans hcf_eq)
  have heval_ne : (aeval M cf : Matrix (Fin n) (Fin n) ℝ) ≠ 0 :=
    aeval_ne_zero_of_ne_zero hcf_ne (by rw [h_deg]; exact hcf_deg)
  show cofactorKernel M q ≠ ⊤
  unfold cofactorKernel
  rw [hdiv_eq]
  exact ker_mulVecLin_ne_top heval_ne

-- ============================================================
-- SECTION III: GCD Annihilation (Bezout identity)
-- ============================================================

/-- If p(M)v = 0, then gcd(p, minpoly)(M)v = 0. -/
theorem gcd_aeval_mulVec_eq_zero {M : Matrix (Fin n) (Fin n) ℝ}
    {p : ℝ[X]} {v : Fin n → ℝ}
    (hp_ann : (aeval M p).mulVec v = 0) :
    (aeval M (EuclideanDomain.gcd p (minpoly ℝ M))).mulVec v = 0 := by
  set μ := minpoly ℝ M
  set d := EuclideanDomain.gcd p μ
  have bezout := EuclideanDomain.gcd_eq_gcd_ab p μ
  have hμ_ann : (aeval M μ : Matrix (Fin n) (Fin n) ℝ) = 0 := minpoly.aeval ℝ M
  calc (aeval M d).mulVec v
      = (aeval M (EuclideanDomain.gcdA p μ * p +
          EuclideanDomain.gcdB p μ * μ)).mulVec v := by
        congr 1; congr 1; rw [show d = _ from bezout]; ring
    _ = (aeval M (EuclideanDomain.gcdA p μ * p)).mulVec v +
        (aeval M (EuclideanDomain.gcdB p μ * μ)).mulVec v := by
        rw [map_add, Matrix.add_mulVec]
    _ = (aeval M (EuclideanDomain.gcdA p μ) * aeval M p).mulVec v +
        (aeval M (EuclideanDomain.gcdB p μ) * aeval M μ).mulVec v := by
        rw [map_mul, map_mul]
    _ = (aeval M (EuclideanDomain.gcdA p μ)).mulVec ((aeval M p).mulVec v) +
        (aeval M (EuclideanDomain.gcdB p μ)).mulVec ((aeval M μ).mulVec v) := by
        rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
    _ = 0 := by rw [hp_ann, hμ_ann, Matrix.zero_mulVec,
                     Matrix.mulVec_zero, Matrix.mulVec_zero, add_zero]

-- ============================================================
-- SECTION IV: Non-Cyclic Containment
-- ============================================================

/-- A non-cyclic vector lies in some cofactor kernel. This is the structural
    heart: if v is not cyclic, there exists an irreducible factor q of the
    minimal polynomial such that (μ/q)(M)v = 0. -/
theorem non_cyclic_mem_cofactorKernel (M : Matrix (Fin n) (Fin n) ℝ) (hn : 0 < n)
    (hM : IsNonderogatory M) (v : Fin n → ℝ) (hv : ¬IsCyclicVector M v) :
    ∃ q ∈ (UniqueFactorizationMonoid.normalizedFactors (minpoly ℝ M)).toFinset,
      v ∈ cofactorKernel M q := by
  set μ := minpoly ℝ M with hμ_def
  have hμ_monic : μ.Monic := minpoly.monic (isIntegral M)
  have hμ_ne : μ ≠ 0 := hμ_monic.ne_zero
  have h_deg : μ.natDegree = n := by
    rw [hμ_def, hM, Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
  have hμ_not_unit : ¬IsUnit μ := by
    intro hu; exact absurd (natDegree_eq_zero_of_isUnit hu) (by omega)
  -- v is not cyclic: ∃ nonzero p with deg < n, p(M)v = 0
  unfold IsCyclicVector at hv
  push_neg at hv
  obtain ⟨p, hp_deg, hp_ann, hp_ne⟩ := hv
  -- d = gcd(p, μ) annihilates v and properly divides μ
  set d := EuclideanDomain.gcd p μ with hd_def
  have hd_ann : (aeval M d).mulVec v = 0 := gcd_aeval_mulVec_eq_zero hp_ann
  have hd_dvd_μ : d ∣ μ := EuclideanDomain.gcd_dvd_right p μ
  have hd_dvd_p : d ∣ p := EuclideanDomain.gcd_dvd_left p μ
  have hd_ne : d ≠ 0 := by
    intro h0; rw [h0] at hd_dvd_μ; exact hμ_ne (eq_zero_of_zero_dvd hd_dvd_μ)
  have hd_deg : d.natDegree < n :=
    lt_of_le_of_lt (Polynomial.natDegree_le_of_dvd hd_dvd_p hp_ne) hp_deg
  -- μ = d * s where s has positive degree
  obtain ⟨s, hs_eq⟩ := hd_dvd_μ
  have hs_ne : s ≠ 0 := right_ne_zero_of_mul (hs_eq ▸ hμ_ne)
  have hs_deg_pos : 0 < s.natDegree := by
    have := (hs_eq ▸ natDegree_mul hd_ne hs_ne : μ.natDegree = d.natDegree + s.natDegree)
    omega
  have hs_not_unit : ¬IsUnit s := by
    intro hu; exact absurd (natDegree_eq_zero_of_isUnit hu) (by omega)
  -- s has a normalized irreducible factor q₀
  obtain ⟨q₀, hq₀_mem_s⟩ :=
    UniqueFactorizationMonoid.exists_mem_normalizedFactors hs_ne hs_not_unit
  have hq₀_dvd_s : q₀ ∣ s := dvd_of_mem_normalizedFactors hq₀_mem_s
  have hq₀_irr : Irreducible q₀ :=
    (UniqueFactorizationMonoid.prime_of_normalized_factor q₀ hq₀_mem_s).irreducible
  have hq₀_dvd_μ : q₀ ∣ μ := dvd_trans hq₀_dvd_s ⟨d, by rw [hs_eq]; ring⟩
  -- Find q' ∈ normalizedFactors μ associated to q₀
  obtain ⟨q', hq'_mem, hq'_assoc⟩ :=
    UniqueFactorizationMonoid.exists_mem_normalizedFactors_of_dvd hμ_ne hq₀_irr hq₀_dvd_μ
  have hq'_in_nf : q' ∈ (UniqueFactorizationMonoid.normalizedFactors μ).toFinset :=
    Multiset.mem_toFinset.mpr hq'_mem
  have hq'_ne : q' ≠ 0 := ne_zero_of_mem_normalizedFactors hq'_mem
  have hq'_dvd_q₀ : q' ∣ q₀ := hq'_assoc.symm.dvd
  have hq'_dvd_s : q' ∣ s := dvd_trans hq'_dvd_q₀ hq₀_dvd_s
  -- Show v ∈ cofactorKernel M q'
  refine ⟨q', hq'_in_nf, ?_⟩
  show v ∈ cofactorKernel M q'
  unfold cofactorKernel
  rw [LinearMap.mem_ker, mulVecLin_apply]
  obtain ⟨t, ht_eq⟩ := hq'_dvd_s
  have hμ_eq : μ = q' * (d * t) := by rw [hs_eq, ht_eq]; ring
  have hdiv_eq : μ / q' = d * t := by
    have hmod : μ % q' = 0 := EuclideanDomain.mod_eq_zero.mpr ⟨d * t, hμ_eq⟩
    have h1 := EuclideanDomain.div_add_mod μ q'
    rw [hmod, add_zero] at h1
    exact mul_left_cancel₀ hq'_ne (h1.trans hμ_eq)
  rw [hdiv_eq]
  calc (aeval M (d * t) : Matrix (Fin n) (Fin n) ℝ).mulVec v
      = (aeval M (t * d) : Matrix (Fin n) (Fin n) ℝ).mulVec v := by
        rw [mul_comm]
    _ = (aeval M t * aeval M d).mulVec v := by rw [map_mul]
    _ = (aeval M t).mulVec ((aeval M d).mulVec v) :=
        (Matrix.mulVec_mulVec _ _ _).symm
    _ = 0 := by rw [hd_ann, Matrix.mulVec_zero]

-- ============================================================
-- SECTION V: Measure Theory — Proper Subspaces Have Measure Zero
-- ============================================================

/-- A proper submodule of ℝⁿ (viewed as Fin n → ℝ) has Lebesgue measure zero.
    This follows from Mathlib's result that additive Haar measures assign zero
    measure to proper submodules of finite-dimensional spaces. -/
theorem volume_submodule_eq_zero
    (S : Submodule ℝ (Fin n → ℝ)) (hS : S ≠ ⊤) :
    volume (S : Set (Fin n → ℝ)) = 0 :=
  Measure.addHaar_submodule volume S hS

-- ============================================================
-- SECTION VI: Main Theorem
-- ============================================================

/-- The set of non-cyclic vectors for a nonderogatory real matrix has
    Lebesgue measure zero. -/
theorem non_cyclic_measure_zero (hn : 0 < n)
    (M : Matrix (Fin n) (Fin n) ℝ) (hM : IsNonderogatory M) :
    volume {v : Fin n → ℝ | ¬IsCyclicVector M v} = 0 := by
  set μ := minpoly ℝ M
  set nf := (UniqueFactorizationMonoid.normalizedFactors μ).toFinset
  -- Non-cyclic vectors ⊆ ⋃ q ∈ nf, cofactorKernel M q
  have h_subset : {v : Fin n → ℝ | ¬IsCyclicVector M v} ⊆
      ⋃ q ∈ nf, (cofactorKernel M q : Set (Fin n → ℝ)) := by
    intro v hv
    obtain ⟨q, hq_mem, hv_in⟩ := non_cyclic_mem_cofactorKernel M hn hM v hv
    exact Set.mem_biUnion hq_mem hv_in
  -- Each cofactor kernel has measure zero
  have h_zero : ∀ q ∈ nf, volume (cofactorKernel M q : Set (Fin n → ℝ)) = 0 := by
    intro q hq
    have hq_mem : q ∈ UniqueFactorizationMonoid.normalizedFactors μ :=
      Multiset.mem_toFinset.mp hq
    have hq_dvd : q ∣ μ := dvd_of_mem_normalizedFactors hq_mem
    have hq_ne : q ≠ 0 := ne_zero_of_mem_normalizedFactors hq_mem
    have hq_irr : Irreducible q :=
      (UniqueFactorizationMonoid.prime_of_normalized_factor q hq_mem).irreducible
    exact volume_submodule_eq_zero _ (cofactorKernel_ne_top M hn hM q hq_dvd hq_ne hq_irr)
  -- Finite union of null sets is null
  calc volume {v : Fin n → ℝ | ¬IsCyclicVector M v}
      ≤ volume (⋃ q ∈ nf, (cofactorKernel M q : Set (Fin n → ℝ))) :=
        measure_mono h_subset
    _ ≤ ∑ q ∈ nf, volume (cofactorKernel M q : Set (Fin n → ℝ)) :=
        measure_biUnion_finset_le nf _
    _ = 0 := by simp [h_zero]

/-- Cyclic vectors for a nonderogatory real matrix have full Lebesgue measure.
    This is the positive formulation: the complement of cyclic vectors is null. -/
theorem cyclic_vectors_ae (hn : 0 < n)
    (M : Matrix (Fin n) (Fin n) ℝ) (hM : IsNonderogatory M) :
    ∀ᵐ v ∂(volume : Measure (Fin n → ℝ)), IsCyclicVector M v := by
  rw [ae_iff]
  exact non_cyclic_measure_zero hn M hM

end CyclicVectorMeasure

end
