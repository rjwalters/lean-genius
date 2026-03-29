/-
  Nonderogatory → Cyclic Vector: Finite Field Version

  Weakens the infinite field hypothesis in CayleyHamiltonMinpolyOQ05OQ01.lean
  to fields with |K| > n. The key insight: the union avoidance lemma only
  needs |K| > k, where k is the number of proper subspaces (at most n for
  the normalized factors of a degree-n polynomial).

  THEOREM: Over a field K with |K| > n, if M ∈ M_n(K) is nonderogatory
  (minpoly = charpoly), then M has a cyclic vector.

  This strictly generalizes the infinite field version, which requires
  [Infinite K] — a stronger hypothesis.

  Mathematical background:
  The union avoidance lemma states that a vector space V over a field K
  cannot be covered by k proper subspaces if |K| > k. The standard proof
  uses induction on k: given w outside the first (k-1) subspaces and v
  outside the k-th, the line {v + tw : t ∈ K} can hit at most one
  "bad" value per subspace, so if |K| > k-1, a good t exists.
-/
import Mathlib

noncomputable section

namespace NonderogatoryFinite

open Matrix Polynomial

attribute [local instance] Classical.propDecidable

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K] {n : ℕ}

-- ============================================================
-- Definitions (same as NonderogatoryComplete)
-- ============================================================

def IsCyclicVector (M : Matrix (Fin n) (Fin n) K) (v : Fin n → K) : Prop :=
  ∀ p : K[X], p.natDegree < n → (aeval M p).mulVec v = 0 → p = 0

def IsNonderogatory (M : Matrix (Fin n) (Fin n) K) : Prop :=
  minpoly K M = M.charpoly

-- ============================================================
-- SECTION I: Finite Union Avoidance Lemma
-- ============================================================

/--
**Union Avoidance (Finite Version):**
A vector space V over a finite field K cannot be covered by k proper
subspaces, provided |K| > k. This weakens the standard [Infinite K]
hypothesis.

The proof follows the same induction as the infinite case, but replaces
the "infinite field has infinitely many elements" argument with the
counting argument: there are at most k-1 bad values of t, and |K| > k-1.
-/
theorem not_union_proper_subspaces_fin {V : Type*} [AddCommGroup V] [Module K V]
    [Nontrivial V]
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (S : ι → Submodule K V)
    (hS : ∀ i ∈ s, S i ≠ ⊤) (hcard : s.card < Fintype.card K) :
    ∃ v : V, ∀ i ∈ s, v ∉ S i := by
  induction s using Finset.induction_on with
  | empty =>
    obtain ⟨v, _⟩ := exists_pair_ne V
    exact ⟨v, fun _ h => absurd h (Finset.notMem_empty _)⟩
  | @insert k s' hk ih =>
    have hS' : ∀ i ∈ s', S i ≠ ⊤ := fun i hi =>
      hS i (Finset.mem_insert_of_mem hi)
    have hcard' : s'.card < Fintype.card K := by
      have := Finset.card_insert_of_not_mem hk
      omega
    obtain ⟨w, hw⟩ := ih hS' hcard'
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
      -- v ∉ S k, w ∈ S k
      -- For any t : K, v + t • w ∉ S k (since v ∉ S k and t • w ∈ S k)
      have h_no_k : ∀ t : K, v + t • w ∉ S k := by
        intro t ht
        have htw : t • w ∈ S k := (S k).smul_mem t hw_k
        have : v ∈ S k := by
          have : v = (v + t • w) - t • w := by abel
          rw [this]; exact (S k).sub_mem ht htw
        exact hv this
      -- For each subspace S i (i ∈ s'), at most one t makes v + tw ∈ S i
      have h_bad_subsingleton : ∀ i ∈ s', Set.Subsingleton {t : K | v + t • w ∈ S i} := by
        intro i hi
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
        exact (hw i hi) this
      -- The bad set ⋃ i ∈ s', {t | v + tw ∈ S i} is finite with ≤ s'.card elements
      -- Since |K| > s.card = s'.card + 1 > s'.card, there exists t not in the bad set
      have h_bad_finite : (⋃ i ∈ s', {t : K | v + t • w ∈ S i}).Finite := by
        apply Set.Finite.biUnion s'.finite_toSet
        intro i hi
        exact (h_bad_subsingleton i hi).finite
      -- The bad set is not all of K (since |K| > |s'|)
      have h_bad_ne_univ : (⋃ i ∈ s', {t : K | v + t • w ∈ S i}) ≠ Set.univ := by
        intro h_eq
        -- If the bad set = K, build an injection K → s' via Choice,
        -- contradicting |K| > s'.card
        suffices h : Fintype.card K ≤ s'.card from absurd hcard' (not_lt.mpr h)
        -- Every t ∈ K is bad for some i ∈ s'
        have h_all_bad : ∀ t : K, ∃ i ∈ s', v + t • w ∈ S i := by
          intro t
          have := h_eq ▸ Set.mem_univ t
          rwa [Set.mem_iUnion₂] at this
        choose f hf_mem hf_in using h_all_bad
        -- f is injective: if f t₁ = f t₂, then t₁ and t₂ are both in
        -- the subsingleton {t | v + tw ∈ S (f t₁)}, so t₁ = t₂
        have hf_inj : Function.Injective f := by
          intro t₁ t₂ hfeq
          exact h_bad_subsingleton (f t₁) (hf_mem t₁) (hf_in t₁) (hfeq ▸ hf_in t₂)
        -- Injection from K to ↑s' gives |K| ≤ |s'|
        calc Fintype.card K
          ≤ Fintype.card ↑s' :=
            Fintype.card_le_of_injective (fun t => ⟨f t, hf_mem t⟩)
              (fun t₁ t₂ h => hf_inj (Subtype.mk.inj h))
          _ = s'.card := Fintype.card_coe s'
      obtain ⟨t, ht⟩ := Set.nonempty_compl.mpr h_bad_ne_univ
      rw [Set.mem_compl_iff, Set.mem_iUnion₂] at ht
      push_neg at ht
      exact ⟨v + t • w, fun i hi => by
        rw [Finset.mem_insert] at hi
        rcases hi with rfl | hi
        · exact h_no_k t
        · exact ht i hi⟩

-- ============================================================
-- SECTION II: Helper Lemmas (reused from NonderogatoryComplete)
-- ============================================================

theorem aeval_ne_zero_of_ne_zero {M : Matrix (Fin n) (Fin n) K}
    {p : K[X]} (hp : p ≠ 0) (hd : p.natDegree < (minpoly K M).natDegree) :
    aeval M p ≠ 0 := by
  intro h
  have hdvd : minpoly K M ∣ p := minpoly.dvd K M h
  have hle := Polynomial.natDegree_le_of_dvd hdvd hp
  omega

theorem gcd_aeval_mulVec_eq_zero {M : Matrix (Fin n) (Fin n) K}
    {p : K[X]} {v : Fin n → K}
    (hp_ann : (aeval M p).mulVec v = 0) :
    (aeval M (EuclideanDomain.gcd p (minpoly K M))).mulVec v = 0 := by
  set μ := minpoly K M
  set d := EuclideanDomain.gcd p μ
  have hμ_ann : (aeval M μ : Matrix (Fin n) (Fin n) K) = 0 := minpoly.aeval K M
  calc (aeval M d).mulVec v
      = (aeval M (EuclideanDomain.gcdA p μ * p +
          EuclideanDomain.gcdB p μ * μ)).mulVec v := by
        show (aeval M d).mulVec v = _
        congr 1; congr 1; rw [show d = _ from EuclideanDomain.gcd_eq_gcd_ab p μ]; ring
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
-- SECTION III: Main Theorem (Finite Field Version)
-- ============================================================

open UniqueFactorizationMonoid in
/--
**Main Theorem (Finite Field Version):**
Over a field K with |K| > n, if M ∈ M_n(K) is nonderogatory,
then M has a cyclic vector.

This generalizes the infinite field version. The bound |K| > n is
sharp: we use at most n proper subspaces (one per irreducible factor
of the degree-n minimal polynomial).
-/
theorem nonderogatory_has_cyclic_vector_fin
    (hcard : n < Fintype.card K)
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
  -- Phase 1.5: Bound the number of factors by degree (≤ n)
  have h_nf_card : nf.card ≤ n := by
    calc nf.card ≤ (normalizedFactors μ).card :=
          Multiset.toFinset_card_le_card _
      _ ≤ μ.natDegree := by
          -- Each irreducible factor has degree ≥ 1; card ≤ sum of degrees = natDegree
          suffices hsuff : ∀ (m : Multiset K[X]), (∀ q ∈ m, Irreducible q) →
              (∀ q ∈ m, q ≠ 0) → m.card ≤ m.prod.natDegree by
            have h_bound := hsuff (normalizedFactors μ)
              (fun q hq => (prime_of_normalized_factor q hq).irreducible)
              (fun q hq => ne_zero_of_mem_normalizedFactors hq)
            calc (normalizedFactors μ).card
              ≤ (normalizedFactors μ).prod.natDegree := h_bound
              _ = μ.natDegree := by
                  obtain ⟨u, hu⟩ := normalizedFactors_prod hμ_ne
                  rw [hu, natDegree_mul hμ_ne (IsUnit.ne_zero u.isUnit),
                      natDegree_eq_zero_of_isUnit u.isUnit, add_zero]
          intro m hm_irr hm_ne
          induction m using Multiset.induction_on with
          | empty => simp
          | cons a s ih =>
            simp only [Multiset.prod_cons, Multiset.card_cons]
            have ha_irr := hm_irr a (Multiset.mem_cons_self a s)
            have ha_ne := hm_ne a (Multiset.mem_cons_self a s)
            have hs_irr := fun q hq => hm_irr q (Multiset.mem_cons_of_mem hq)
            have hs_ne := fun q hq => hm_ne q (Multiset.mem_cons_of_mem hq)
            have hs_prod_ne : s.prod ≠ 0 :=
              Multiset.prod_induction s (· ≠ 0)
                (fun a b ha hb => mul_ne_zero ha hb) one_ne_zero hs_ne
            have ha_deg : 1 ≤ a.natDegree := by
              rcases Nat.eq_zero_or_pos a.natDegree with h0 | hpos
              · exfalso; exact ha_irr.1 (by
                  rw [Polynomial.eq_C_of_natDegree_eq_zero h0]
                  exact isUnit_C.mpr (IsUnit.mk0 _ (fun hc =>
                    ha_ne (by rw [Polynomial.eq_C_of_natDegree_eq_zero h0, hc, map_zero]))))
              · exact hpos
            rw [natDegree_mul ha_ne hs_prod_ne]
            linarith [ih hs_irr hs_ne]
      _ = n := h_deg
  have h_nf_lt_K : nf.card < Fintype.card K := by omega
  -- Phase 2: For each factor q, the cofactor's kernel is a proper subspace
  let S : K[X] → Submodule K (Fin n → K) := fun q =>
    LinearMap.ker ((aeval M (μ / q) : Matrix (Fin n) (Fin n) K).mulVecLin)
  have hS_proper : ∀ q ∈ nf, S q ≠ ⊤ := by
    intro q hq
    have hq_mem : q ∈ normalizedFactors μ := Multiset.mem_toFinset.mp hq
    have hq_dvd : q ∣ μ := dvd_of_mem_normalizedFactors hq_mem
    have hq_ne : q ≠ 0 := ne_zero_of_mem_normalizedFactors hq_mem
    have hq_irr : Irreducible q := (prime_of_normalized_factor q hq_mem).irreducible
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
    have heval_ne : (aeval M cf : Matrix (Fin n) (Fin n) K) ≠ 0 :=
      aeval_ne_zero_of_ne_zero hcf_ne (by rw [h_deg]; exact hcf_deg)
    show S q ≠ ⊤
    change LinearMap.ker ((aeval M (μ / q) : Matrix (Fin n) (Fin n) K).mulVecLin) ≠ ⊤
    rw [hdiv_eq]
    exact ker_mulVecLin_ne_top heval_ne
  -- Phase 3: Union avoidance with finite field bound
  obtain ⟨v, hv⟩ := not_union_proper_subspaces_fin nf S hS_proper h_nf_lt_K
  -- Phase 4: Prove v is cyclic (identical to infinite case)
  refine ⟨v, fun p hp hann => ?_⟩
  by_contra hp_ne
  set d := EuclideanDomain.gcd p μ with hd_def
  have hd_ann : (aeval M d).mulVec v = 0 := gcd_aeval_mulVec_eq_zero hann
  have hd_dvd_μ : d ∣ μ := EuclideanDomain.gcd_dvd_right p μ
  have hd_dvd_p : d ∣ p := EuclideanDomain.gcd_dvd_left p μ
  have hd_ne : d ≠ 0 := by
    intro h0; rw [h0] at hd_dvd_μ; exact hμ_ne (eq_zero_of_zero_dvd hd_dvd_μ)
  have hd_deg : d.natDegree < n :=
    lt_of_le_of_lt (Polynomial.natDegree_le_of_dvd hd_dvd_p hp_ne) hp
  obtain ⟨s, hs_eq⟩ := hd_dvd_μ
  have hs_ne : s ≠ 0 := right_ne_zero_of_mul (hs_eq ▸ hμ_ne)
  have hs_deg_pos : 0 < s.natDegree := by
    have := (hs_eq ▸ natDegree_mul hd_ne hs_ne : μ.natDegree = d.natDegree + s.natDegree)
    omega
  have hs_not_unit : ¬IsUnit s := by
    intro hu; exact absurd (natDegree_eq_zero_of_isUnit hu) (by omega)
  obtain ⟨q₀, hq₀_mem_s⟩ := exists_mem_normalizedFactors hs_ne hs_not_unit
  have hq₀_irr : Irreducible q₀ := (prime_of_normalized_factor q₀ hq₀_mem_s).irreducible
  have hq₀_dvd_s : q₀ ∣ s := dvd_of_mem_normalizedFactors hq₀_mem_s
  have hq₀_dvd_μ : q₀ ∣ μ := dvd_trans hq₀_dvd_s ⟨d, by rw [hs_eq]; ring⟩
  obtain ⟨q', hq'_mem, hq'_assoc⟩ :=
    exists_mem_normalizedFactors_of_dvd hμ_ne hq₀_irr hq₀_dvd_μ
  have hq'_in_nf : q' ∈ nf := Multiset.mem_toFinset.mpr hq'_mem
  have hq'_dvd_q₀ : q' ∣ q₀ := hq'_assoc.symm.dvd
  have hq'_dvd_s : q' ∣ s := dvd_trans hq'_dvd_q₀ hq₀_dvd_s
  have hv_in : v ∈ S q' := by
    change v ∈ LinearMap.ker ((aeval M (μ / q') : Matrix (Fin n) (Fin n) K).mulVecLin)
    rw [LinearMap.mem_ker, mulVecLin_apply]
    obtain ⟨t, ht_eq⟩ := hq'_dvd_s
    have hq'_ne : q' ≠ 0 := ne_zero_of_mem_normalizedFactors hq'_mem
    have hμ_eq : μ = q' * (d * t) := by rw [hs_eq, ht_eq]; ring
    have hdiv_eq : μ / q' = d * t := by
      have hmod : μ % q' = 0 := EuclideanDomain.mod_eq_zero.mpr ⟨d * t, hμ_eq⟩
      have h1 := EuclideanDomain.div_add_mod μ q'
      rw [hmod, add_zero] at h1
      exact mul_left_cancel₀ hq'_ne (h1.trans hμ_eq)
    rw [hdiv_eq]
    calc (aeval M (d * t) : Matrix (Fin n) (Fin n) K).mulVec v
        = (aeval M (t * d) : Matrix (Fin n) (Fin n) K).mulVec v := by
          rw [mul_comm]
      _ = (aeval M t * aeval M d).mulVec v := by rw [map_mul]
      _ = (aeval M t).mulVec ((aeval M d).mulVec v) :=
          (Matrix.mulVec_mulVec _ _ _).symm
      _ = 0 := by rw [hd_ann, Matrix.mulVec_zero]
  exact absurd hv_in (hv q' hq'_in_nf)

end NonderogatoryFinite

end
