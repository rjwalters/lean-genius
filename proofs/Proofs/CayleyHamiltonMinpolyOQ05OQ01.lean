/-
  Nonderogatory → Cyclic Vector: Complete Proof (Infinite Fields)

  Resolves the sorry in CayleyHamiltonMinpolyOQ04Backward.lean by completing
  the main theorem using the UniqueFactorizationMonoid API (normalizedFactors).

  THEOREM: Over an infinite field K, if M ∈ M_n(K) is nonderogatory
  (minpoly = charpoly), then M has a cyclic vector.
-/
import Mathlib

noncomputable section

namespace NonderogatoryComplete

open Matrix Polynomial

attribute [local instance] Classical.propDecidable

variable {K : Type*} [Field K] {n : ℕ}

-- ============================================================
-- Definitions
-- ============================================================

def IsCyclicVector (M : Matrix (Fin n) (Fin n) K) (v : Fin n → K) : Prop :=
  ∀ p : K[X], p.natDegree < n → (aeval M p).mulVec v = 0 → p = 0

def IsNonderogatory (M : Matrix (Fin n) (Fin n) K) : Prop :=
  minpoly K M = M.charpoly

-- ============================================================
-- SECTION I: Helper Lemmas (from CayleyHamiltonMinpolyOQ04Backward)
-- ============================================================

theorem aeval_ne_zero_of_ne_zero {M : Matrix (Fin n) (Fin n) K}
    {p : K[X]} (hp : p ≠ 0) (hd : p.natDegree < (minpoly K M).natDegree) :
    aeval M p ≠ 0 := by
  intro h
  have hdvd : minpoly K M ∣ p := minpoly.dvd K M h
  have hle := Polynomial.natDegree_le_of_dvd hdvd hp
  omega

theorem not_union_proper_subspaces {V : Type*} [AddCommGroup V] [Module K V]
    [Nontrivial V] [Infinite K]
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (S : ι → Submodule K V)
    (hS : ∀ i ∈ s, S i ≠ ⊤) :
    ∃ v : V, ∀ i ∈ s, v ∉ S i := by
  induction s using Finset.induction_on with
  | empty =>
    obtain ⟨v, _⟩ := exists_pair_ne V
    exact ⟨v, fun _ h => absurd h (Finset.notMem_empty _)⟩
  | @insert k s' hk ih =>
    have hS' : ∀ i ∈ s', S i ≠ ⊤ := fun i hi =>
      hS i (Finset.mem_insert_of_mem hi)
    obtain ⟨w, hw⟩ := ih hS'
    have hk_proper := hS k (Finset.mem_insert_self k s')
    have ⟨v, hv⟩ : ∃ v : V, v ∉ S k := by
      by_contra h; push_neg at h
      apply hk_proper
      rw [eq_top_iff]
      intro x _; exact h x
    by_cases hw_k : w ∉ S k
    · exact ⟨w, fun i hi => by
        rw [Finset.mem_insert] at hi
        rcases hi with rfl | hi
        · exact hw_k
        · exact hw i hi⟩
    · push_neg at hw_k
      have h_no_k : ∀ t : K, v + t • w ∉ S k := by
        intro t ht
        have htw : t • w ∈ S k := (S k).smul_mem t hw_k
        have : v ∈ S k := by
          have : v = (v + t • w) - t • w := by abel
          rw [this]; exact (S k).sub_mem ht htw
        exact hv this
      have h_bad_finite : Set.Finite (⋃ i ∈ s', {t : K | v + t • w ∈ S i}) := by
        apply Set.Finite.biUnion s'.finite_toSet
        intro i hi
        have hwi : w ∉ S i := hw i hi
        apply Set.Subsingleton.finite
        intro t₁ ht₁ t₂ ht₂
        simp only [Set.mem_setOf_eq] at ht₁ ht₂
        by_contra hne
        have : (t₁ - t₂) • w ∈ S i := by
          have h1 : (v + t₁ • w) - (v + t₂ • w) ∈ S i := (S i).sub_mem ht₁ ht₂
          rwa [show (v + t₁ • w) - (v + t₂ • w) = (t₁ - t₂) • w by module] at h1
        have ht_ne : t₁ - t₂ ≠ 0 := sub_ne_zero.mpr hne
        have : w ∈ S i := by
          have := (S i).smul_mem (t₁ - t₂)⁻¹ this
          simp [ht_ne] at this
          exact this
        exact hwi this
      have h_bad_ne_univ : (⋃ i ∈ s', {t : K | v + t • w ∈ S i}) ≠ Set.univ := by
        intro h_eq
        exact Set.infinite_univ (h_eq ▸ h_bad_finite)
      obtain ⟨t, ht⟩ := Set.nonempty_compl.mpr h_bad_ne_univ
      rw [Set.mem_compl_iff, Set.mem_iUnion₂] at ht
      push_neg at ht
      exact ⟨v + t • w, fun i hi => by
        rw [Finset.mem_insert] at hi
        rcases hi with rfl | hi
        · exact h_no_k t
        · exact ht i hi⟩

/-- GCD annihilation via Bezout identity. -/
theorem gcd_aeval_mulVec_eq_zero {M : Matrix (Fin n) (Fin n) K}
    {p : K[X]} {v : Fin n → K}
    (hp_ann : (aeval M p).mulVec v = 0) :
    (aeval M (EuclideanDomain.gcd p (minpoly K M))).mulVec v = 0 := by
  set μ := minpoly K M
  set d := EuclideanDomain.gcd p μ
  have bezout := EuclideanDomain.gcd_eq_gcd_ab p μ
  have hμ_ann : (aeval M μ : Matrix (Fin n) (Fin n) K) = 0 := minpoly.aeval K M
  -- d = p * gcdA + μ * gcdB (Bezout). Commute to gcdA * p + gcdB * μ
  -- so that p(M) and μ(M) are applied to v first.
  calc (aeval M d).mulVec v
      = (aeval M (EuclideanDomain.gcdA p μ * p +
          EuclideanDomain.gcdB p μ * μ)).mulVec v := by
        show (aeval M d).mulVec v = _
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

theorem ker_mulVecLin_ne_top
    {A : Matrix (Fin n) (Fin n) K} (hA : A ≠ 0) :
    LinearMap.ker A.mulVecLin ≠ ⊤ := by
  intro h
  apply hA
  funext i j
  have h2 : A.mulVecLin (Pi.single j 1) = 0 := by
    rw [← LinearMap.mem_ker]; rw [h]; trivial
  have := congr_fun h2 i
  simp only [mulVecLin_apply, mulVec, dotProduct, Pi.single_apply] at this
  simpa using this

-- ============================================================
-- SECTION II: Main Theorem
-- ============================================================

open UniqueFactorizationMonoid in
theorem nonderogatory_has_cyclic_vector [Infinite K]
    (M : Matrix (Fin n) (Fin n) K) (h : IsNonderogatory M) :
    ∃ v, IsCyclicVector M v := by
  -- Base case
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact ⟨Fin.elim0, fun p hp _ => by omega⟩
  -- Setup
  set μ := minpoly K M with hμ_def
  have h_deg : μ.natDegree = n := by
    rw [hμ_def, h, Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
  have hμ_monic : μ.Monic := minpoly.monic (isIntegral M)
  have hμ_ne : μ ≠ 0 := hμ_monic.ne_zero
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  haveI : Nontrivial (Fin n → K) := Function.nontrivial
  have hμ_not_unit : ¬IsUnit μ := by
    intro hu; exact absurd (natDegree_eq_zero_of_isUnit hu) (by omega)
  -- Phase 1: Irreducible factors of μ as a Finset
  set nf := (normalizedFactors μ).toFinset with nf_def
  -- Phase 2: For each factor q, the cofactor's kernel is a proper subspace
  let S : K[X] → Submodule K (Fin n → K) := fun q =>
    LinearMap.ker ((aeval M (μ / q) : Matrix (Fin n) (Fin n) K).mulVecLin)
  have hS_proper : ∀ q ∈ nf, S q ≠ ⊤ := by
    intro q hq
    have hq_mem : q ∈ normalizedFactors μ := Multiset.mem_toFinset.mp hq
    have hq_dvd : q ∣ μ := dvd_of_mem_normalizedFactors hq_mem
    have hq_ne : q ≠ 0 := ne_zero_of_mem_normalizedFactors hq_mem
    have hq_irr : Irreducible q := (prime_of_normalized_factor q hq_mem).irreducible
    -- Get cofactor
    obtain ⟨cf, hcf_eq⟩ := hq_dvd  -- μ = q * cf
    have hcf_ne : cf ≠ 0 := right_ne_zero_of_mul (hcf_eq ▸ hμ_ne)
    have hdeg_sum : μ.natDegree = q.natDegree + cf.natDegree :=
      hcf_eq ▸ natDegree_mul hq_ne hcf_ne
    -- q is irreducible → degree ≥ 1
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
    -- μ / q = cf (exact division)
    have hdiv_eq : μ / q = cf := by
      have hmod : μ % q = 0 := EuclideanDomain.mod_eq_zero.mpr ⟨cf, hcf_eq⟩
      have h1 := EuclideanDomain.div_add_mod μ q
      rw [hmod, add_zero] at h1
      -- h1 : q * (μ / q) = μ, hcf_eq : μ = q * cf
      exact mul_left_cancel₀ hq_ne (h1.trans hcf_eq)
    -- kernel is proper (since aeval M cf ≠ 0)
    have heval_ne : (aeval M cf : Matrix (Fin n) (Fin n) K) ≠ 0 :=
      aeval_ne_zero_of_ne_zero hcf_ne (by rw [h_deg]; exact hcf_deg)
    show S q ≠ ⊤
    change LinearMap.ker ((aeval M (μ / q) : Matrix (Fin n) (Fin n) K).mulVecLin) ≠ ⊤
    rw [hdiv_eq]
    exact ker_mulVecLin_ne_top heval_ne
  -- Phase 3: Union avoidance — find v outside all kernels
  obtain ⟨v, hv⟩ := not_union_proper_subspaces nf S hS_proper
  -- Phase 4: Prove v is cyclic
  refine ⟨v, fun p hp hann => ?_⟩
  by_contra hp_ne
  -- d = gcd(p, μ) annihilates v and properly divides μ
  set d := EuclideanDomain.gcd p μ with hd_def
  have hd_ann : (aeval M d).mulVec v = 0 := gcd_aeval_mulVec_eq_zero hann
  have hd_dvd_μ : d ∣ μ := EuclideanDomain.gcd_dvd_right p μ
  have hd_dvd_p : d ∣ p := EuclideanDomain.gcd_dvd_left p μ
  have hd_ne : d ≠ 0 := by
    intro h0; rw [h0] at hd_dvd_μ; exact hμ_ne (eq_zero_of_zero_dvd hd_dvd_μ)
  have hd_deg : d.natDegree < n :=
    lt_of_le_of_lt (Polynomial.natDegree_le_of_dvd hd_dvd_p hp_ne) hp
  -- μ = d * s where s has positive degree
  obtain ⟨s, hs_eq⟩ := hd_dvd_μ
  have hs_ne : s ≠ 0 := right_ne_zero_of_mul (hs_eq ▸ hμ_ne)
  have hs_deg_pos : 0 < s.natDegree := by
    have := (hs_eq ▸ natDegree_mul hd_ne hs_ne : μ.natDegree = d.natDegree + s.natDegree)
    omega
  have hs_not_unit : ¬IsUnit s := by
    intro hu; exact absurd (natDegree_eq_zero_of_isUnit hu) (by omega)
  -- s has a normalized irreducible factor q₀
  obtain ⟨q₀, hq₀_mem_s⟩ := exists_mem_normalizedFactors hs_ne hs_not_unit
  have hq₀_irr : Irreducible q₀ := (prime_of_normalized_factor q₀ hq₀_mem_s).irreducible
  have hq₀_dvd_s : q₀ ∣ s := dvd_of_mem_normalizedFactors hq₀_mem_s
  have hq₀_dvd_μ : q₀ ∣ μ := dvd_trans hq₀_dvd_s ⟨d, by rw [hs_eq]; ring⟩
  -- Find q' ∈ normalizedFactors μ associated to q₀
  obtain ⟨q', hq'_mem, hq'_assoc⟩ :=
    exists_mem_normalizedFactors_of_dvd hμ_ne hq₀_irr hq₀_dvd_μ
  -- q' is in our finset nf
  have hq'_in_nf : q' ∈ nf := Multiset.mem_toFinset.mpr hq'_mem
  -- q' ~ q₀ implies q' | s (since q₀ | s and q' ~ q₀ means q' | q₀ | s)
  have hq'_dvd_q₀ : q' ∣ q₀ := hq'_assoc.symm.dvd
  have hq'_dvd_s : q' ∣ s := dvd_trans hq'_dvd_q₀ hq₀_dvd_s
  -- Show v ∈ S q' (contradicts hv)
  have hv_in : v ∈ S q' := by
    change v ∈ LinearMap.ker ((aeval M (μ / q') : Matrix (Fin n) (Fin n) K).mulVecLin)
    rw [LinearMap.mem_ker, mulVecLin_apply]
    -- μ = d * s, q' | s, so s = q' * t, hence μ = q' * (d * t)
    obtain ⟨t, ht_eq⟩ := hq'_dvd_s
    have hq'_ne : q' ≠ 0 := ne_zero_of_mem_normalizedFactors hq'_mem
    have hμ_eq : μ = q' * (d * t) := by rw [hs_eq, ht_eq]; ring
    -- μ / q' = d * t
    have hdiv_eq : μ / q' = d * t := by
      have hmod : μ % q' = 0 := EuclideanDomain.mod_eq_zero.mpr ⟨d * t, hμ_eq⟩
      have h1 := EuclideanDomain.div_add_mod μ q'
      rw [hmod, add_zero] at h1
      exact mul_left_cancel₀ hq'_ne (h1.trans hμ_eq)
    -- (μ / q')(M) v = (d * t)(M) v = t(M)(d(M) v) = t(M) 0 = 0
    rw [hdiv_eq]
    calc (aeval M (d * t) : Matrix (Fin n) (Fin n) K).mulVec v
        = (aeval M (t * d) : Matrix (Fin n) (Fin n) K).mulVec v := by
          rw [mul_comm]
      _ = (aeval M t * aeval M d).mulVec v := by rw [map_mul]
      _ = (aeval M t).mulVec ((aeval M d).mulVec v) :=
          (Matrix.mulVec_mulVec _ _ _).symm
      _ = 0 := by rw [hd_ann, Matrix.mulVec_zero]
  exact absurd hv_in (hv q' hq'_in_nf)

end NonderogatoryComplete

end
