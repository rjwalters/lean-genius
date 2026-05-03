/-
  Backward Direction: Nonderogatory → Cyclic Vector (Infinite Fields)
  (cayley-hamilton-minpoly-oq-04, continuation)

  Theorem: Over an infinite field K, if M ∈ M_n(K) is nonderogatory
  (minpoly = charpoly), then M has a cyclic vector.

  This eliminates the axiom from CayleyHamiltonMinpolyOQ04.lean for all
  infinite fields, which includes all algebraically closed fields.

  Proof strategy:
  1. Non-cyclic vectors lie in ker(p(M)) for nonzero p with deg(p) < n
  2. Each such ker(p(M)) is a proper subspace (since p(M) ≠ 0 by minimality)
  3. Over infinite fields, a vector space cannot be a finite union of
     proper subspaces (proved via a line argument)
  4. Therefore cyclic vectors exist

  References:
  - Hoffman & Kunze, "Linear Algebra" §7.2
  - Roman, "Advanced Linear Algebra" §10.4
  - CayleyHamiltonMinpolyOQ04.lean (forward direction and definitions)
-/
import Mathlib

noncomputable section

namespace Nonderogatory.Backward

open Matrix Polynomial

attribute [local instance] Classical.propDecidable

variable {K : Type*} [Field K] {n : ℕ}

-- ============================================================
-- Definitions (duplicated from OQ04 to avoid importing axiom)
-- ============================================================

/-- A vector v is a cyclic vector for M if no nonzero polynomial
    of degree < n annihilates v under M. -/
def IsCyclicVector (M : Matrix (Fin n) (Fin n) K) (v : Fin n → K) : Prop :=
  ∀ p : K[X], p.natDegree < n → (aeval M p).mulVec v = 0 → p = 0

/-- A matrix is nonderogatory if minpoly = charpoly. -/
def IsNonderogatory (M : Matrix (Fin n) (Fin n) K) : Prop :=
  minpoly K M = M.charpoly

-- ============================================================
-- PART I: Polynomial Evaluation Lemmas
-- ============================================================

/-- If p is a nonzero polynomial with degree < degree of minpoly,
    then p(M) ≠ 0 (as a matrix). This is because minpoly is the
    minimal-degree monic polynomial annihilating M. -/
theorem aeval_ne_zero_of_ne_zero {M : Matrix (Fin n) (Fin n) K}
    {p : K[X]} (hp : p ≠ 0) (hd : p.natDegree < (minpoly K M).natDegree) :
    aeval M p ≠ 0 := by
  intro h
  have hdvd : minpoly K M ∣ p := minpoly.dvd K M h
  have hle := Polynomial.natDegree_le_of_dvd hdvd hp
  omega

/-- Nonzero matrices have vectors outside their kernel. -/
theorem exists_mulVec_ne_zero {n : ℕ}
    {A : Matrix (Fin n) (Fin n) K} (hA : A ≠ 0) :
    ∃ v : Fin n → K, A.mulVec v ≠ 0 := by
  by_contra hall
  push_neg at hall
  -- If A.mulVec v = 0 for all v, then A = 0
  apply hA
  funext i j
  specialize hall (Pi.single j 1)
  have : (A.mulVec (Pi.single j 1)) i = 0 := congr_fun hall i
  simp only [mulVec, dotProduct, Pi.single_apply] at this
  simpa using this

-- ============================================================
-- PART II: Union Avoidance for Vector Spaces
-- ============================================================

/-- Over an infinite field, a nontrivial vector space is not a finite
    union of proper subspaces.

    Proof by induction on the number of subspaces, using a line argument:
    given v ∉ S_k and w ∉ S₁ ∪ ... ∪ S_{k-1}, the line {v + tw}
    meets each S_i in at most one point. Since K is infinite, some
    point on the line avoids all subspaces. -/
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
    -- By induction, find w avoiding all subspaces in s'
    have hS' : ∀ i ∈ s', S i ≠ ⊤ := fun i hi =>
      hS i (Finset.mem_insert_of_mem hi)
    obtain ⟨w, hw⟩ := ih hS'
    -- Find v not in S k
    have hk_proper := hS k (Finset.mem_insert_self k s')
    have ⟨v, hv⟩ : ∃ v : V, v ∉ S k := by
      by_contra h; push_neg at h
      apply hk_proper
      rw [eq_top_iff]
      intro x _; exact h x
    -- If w also avoids S k, we're done
    by_cases hw_k : w ∉ S k
    · exact ⟨w, fun i hi => by
        rw [Finset.mem_insert] at hi
        rcases hi with rfl | hi
        · exact hw_k
        · exact hw i hi⟩
    · push_neg at hw_k
      -- w ∈ S k but w ∉ S i for i ∈ s'.
      -- Use line argument: consider v + t • w for t ∈ K.
      -- For i = k: tw ∈ S k (since w ∈ S k), so v + tw ∈ S k iff v ∈ S k.
      --           Since v ∉ S k, NO t is bad for S k.
      -- For i ∈ s': at most ONE t is bad (if two t values work, w ∈ S i, contradiction).
      -- Total bad t values ≤ |s'|. Since K infinite, good t exists.
      have h_no_k : ∀ t : K, v + t • w ∉ S k := by
        intro t ht
        have htw : t • w ∈ S k := (S k).smul_mem t hw_k
        have : v ∈ S k := by
          have : v = (v + t • w) - t • w := by abel
          rw [this]; exact (S k).sub_mem ht htw
        exact hv this
      -- For each i ∈ s': the set {t : v + tw ∈ S i} has at most 1 element.
      -- Proof: if t₁ ≠ t₂ both work, then (t₁ - t₂) • w ∈ S i, so w ∈ S i,
      -- contradicting hw.
      -- The set of all bad t values across s' is finite (at most |s'| elements).
      -- Since K is infinite, there exists a t that avoids all.
      -- We formalize this using the fact that a finite set of elements of K
      -- cannot exhaust K (since K is infinite).
      -- Collect bad t values into a finite set
      have h_bad_finite : Set.Finite (⋃ i ∈ s', {t : K | v + t • w ∈ S i}) := by
        apply Set.Finite.biUnion s'.finite_toSet
        intro i hi
        -- Show {t : v + tw ∈ S i} is finite (has at most 1 element)
        have hwi : w ∉ S i := hw i hi
        -- If t₁, t₂ both bad and t₁ ≠ t₂, then w ∈ S i, contradiction
        -- So the set is a subsingleton, hence finite
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
      -- Since K is infinite and the bad set is finite, there exists a good t
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

-- ============================================================
-- PART III: Linear Independence of Matrix Powers
-- ============================================================

/-- If minpoly(M) has degree n, then {I, M, M², ..., M^{n-1}} are
    K-linearly independent in the matrix algebra.

    This means the algebra K[M] has dimension n over K. -/
theorem powers_linearIndependent
    (M : Matrix (Fin n) (Fin n) K)
    (h_deg : (minpoly K M).natDegree = n) :
    LinearIndependent K (fun k : Fin n => M ^ (k : ℕ)) := by
  rw [linearIndependent_iff']
  intro s c hc i hi
  by_contra h_ne
  -- Construct the polynomial p = ∑_{k ∈ s} c_k X^k
  -- p(M) = ∑ c_k M^k = 0 (from hc)
  -- p ≠ 0 (c_i ≠ 0) and deg(p) < n (all k < n)
  -- This contradicts minimality of minpoly
  let p := ∑ k ∈ s, C (c k) * X ^ (k : ℕ)
  -- p(M) = ∑ c_k M^k = 0 (from hc), p ≠ 0 (c_i ≠ 0), deg(p) < n
  -- This contradicts minimality of minpoly (degree n)
  have hp_eval : aeval M p = 0 := by
    simp only [p, map_sum, map_mul, map_pow, aeval_C, aeval_X]
    simp only [Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]
    exact hc
  have hp_ne : p ≠ 0 := by
    intro hp0; apply h_ne
    have h1 : p.coeff ↑i = 0 := by rw [hp0, coeff_zero]
    -- Extract coefficient: p.coeff ↑i = c i
    simp only [p, C_mul_X_pow_eq_monomial, finset_sum_coeff, coeff_monomial] at h1
    -- h1 : ∑ k ∈ s, if ↑k = ↑i then c k else 0 = 0
    simp only [Fin.val_injective.eq_iff, Finset.sum_ite_eq', hi, ite_true] at h1
    exact h1
  have hp_deg : p.natDegree < n := by
    apply lt_of_le_of_lt (natDegree_sum_le s _)
    apply Finset.sup_lt_iff (Nat.pos_of_ne_zero (by intro h0; subst h0; exact Fin.elim0 i))
      |>.mpr
    intro k _
    exact lt_of_le_of_lt (natDegree_C_mul_X_pow_le (c k) ↑k) k.isLt
  exact absurd hp_eval (aeval_ne_zero_of_ne_zero hp_ne (by omega))

-- ============================================================
-- PART IV: Cyclic Vector from Linear Independence
-- ============================================================

/-- If {I, M, ..., M^{n-1}} are linearly independent in M_n(K), and
    v is a vector such that {v, Mv, ..., M^{n-1}v} are linearly
    independent, then v is a cyclic vector (annihilator formulation). -/
theorem isCyclicVector_of_linearIndependent
    (M : Matrix (Fin n) (Fin n) K) (v : Fin n → K)
    (hli : LinearIndependent K (fun k : Fin n => (M ^ (k : ℕ)).mulVec v)) :
    IsCyclicVector M v := by
  intro p hp hann
  -- All coefficients of p must be 0
  suffices h : ∀ k : Fin n, p.coeff ↑k = 0 by
    ext m; simp only [Polynomial.coeff_zero]
    by_cases hm : m < n
    · exact h ⟨m, hm⟩
    · exact Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
  -- Linear independence: ∑ c_k • v_k = 0 → all c_k = 0
  apply Fintype.linearIndependent_iff.mp hli
  -- Goal: ∑ k : Fin n, p.coeff ↑k • (M ^ ↑k).mulVec v = 0
  -- Step 1: aeval M p = ∑_{i < n} p.coeff i • M^i
  have heval : aeval M p = ∑ i ∈ Finset.range n, p.coeff i • M ^ i := by
    rw [aeval_def, eval₂_eq_sum_range' hp]
    simp only [Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]
  -- Step 2: mulVec distributes over finite sums
  have hdist : ∀ (s : Finset ℕ),
      (∑ i in s, p.coeff i • M ^ i).mulVec v =
      ∑ i in s, p.coeff i • (M ^ i).mulVec v := by
    intro s
    induction s using Finset.induction with
    | empty => simp [Matrix.zero_mulVec]
    | insert ha ih =>
      rw [Finset.sum_insert ha, Matrix.add_mulVec, ih,
          Finset.sum_insert ha, Matrix.smul_mulVec_assoc]
  -- Step 3: Convert Fin n sum to range n sum, factor out mulVec, use hann
  rw [Fin.sum_univ_eq_sum_range, ← hdist, ← heval]
  exact hann

-- ============================================================
-- PART IV-B: Helper Lemmas for Main Theorem
-- ============================================================

/-- **Reverse direction**: IsCyclicVector implies linear independence of
    Krylov vectors. This is the converse of `isCyclicVector_of_linearIndependent`. -/
theorem linearIndependent_of_isCyclicVector
    (M : Matrix (Fin n) (Fin n) K) (v : Fin n → K)
    (hv : IsCyclicVector M v) (hn : 0 < n) :
    LinearIndependent K (fun k : Fin n => (M ^ (k : ℕ)).mulVec v) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc i
  -- Construct the polynomial p = ∑ c_k X^k
  set p := ∑ k : Fin n, C (c k) * X ^ (k : ℕ) with hp_def
  -- p(M) = ∑ c_k • M^k
  have hp_aeval : aeval M p = ∑ k : Fin n, c k • M ^ (k : ℕ) := by
    simp only [p, map_sum, map_mul, map_pow, aeval_C, aeval_X,
               Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]
  -- (aeval M p).mulVec v = 0 (from hc, distributing mulVec)
  have hp_ann : (aeval M p).mulVec v = 0 := by
    rw [hp_aeval]
    have : (∑ k : Fin n, c k • M ^ (k : ℕ)).mulVec v =
           ∑ k : Fin n, c k • (M ^ (k : ℕ)).mulVec v := by
      simp only [← Matrix.mulVecLin_apply]
      rw [map_sum]; congr 1; ext k; rw [map_smul, Matrix.mulVecLin_apply]
    rw [this, hc]
  -- deg(p) < n
  have hp_deg : p.natDegree < n := by
    apply lt_of_le_of_lt (natDegree_sum_le _ _)
    apply (Finset.sup_lt_iff (by omega : (0 : ℕ) < n)).mpr
    intro k _; exact lt_of_le_of_lt (natDegree_C_mul_X_pow_le (c k) ↑k) k.isLt
  -- By IsCyclicVector: p = 0, so all coefficients vanish
  have hp_zero : p = 0 := hv p hp_deg hp_ann
  -- Extract coefficient c i = 0
  have h_coeff := congr_arg (Polynomial.coeff · ↑i) hp_zero
  simp only [Polynomial.coeff_zero, p, C_mul_X_pow_eq_monomial,
             finset_sum_coeff, coeff_monomial] at h_coeff
  simpa [Fin.val_injective.eq_iff] using h_coeff

/-- **GCD annihilation**: if p(M)v = 0, then gcd(p, minpoly)(M)v = 0.
    Follows from Bezout's identity: gcd = a*p + b*minpoly, and
    both p(M)v = 0 and minpoly(M) = 0. -/
theorem gcd_aeval_mulVec_eq_zero {M : Matrix (Fin n) (Fin n) K}
    {p : K[X]} {v : Fin n → K}
    (hp_ann : (aeval M p).mulVec v = 0) :
    (aeval M (EuclideanDomain.gcd p (minpoly K M))).mulVec v = 0 := by
  set μ := minpoly K M with hμ_set
  set d := EuclideanDomain.gcd p μ with hd_def
  have bezout := EuclideanDomain.gcd_eq_gcd_ab p μ
  have hμ_ann : (aeval M μ : Matrix (Fin n) (Fin n) K) = 0 := minpoly.aeval K M
  calc (aeval M d).mulVec v
      = (aeval M (EuclideanDomain.gcdA p μ * p +
          EuclideanDomain.gcdB p μ * μ)).mulVec v := by
        congr 2
        change EuclideanDomain.gcd p μ = _
        rw [bezout]; ring
    _ = (aeval M (EuclideanDomain.gcdA p μ * p)).mulVec v +
        (aeval M (EuclideanDomain.gcdB p μ * μ)).mulVec v := by
        rw [map_add, Matrix.add_mulVec]
    _ = (aeval M (EuclideanDomain.gcdA p μ) * aeval M p).mulVec v +
        (aeval M (EuclideanDomain.gcdB p μ) * aeval M μ).mulVec v := by
        rw [map_mul, map_mul]
    _ = (aeval M (EuclideanDomain.gcdA p μ)).mulVec ((aeval M p).mulVec v) +
        (aeval M (EuclideanDomain.gcdB p μ)).mulVec ((aeval M μ).mulVec v) := by
        rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
    _ = 0 := by rw [hp_ann, hμ_ann, Matrix.zero_mulVec, Matrix.mulVec_zero, add_zero]

-- ============================================================
-- PART IV-C: Kernel Properness Helper
-- ============================================================

/-- A nonzero matrix has a proper kernel (as a linear map). -/
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
-- PART V: Main Theorem
-- ============================================================

/-- Over an infinite field, a nonderogatory matrix has a cyclic vector.

    **Proof strategy**: For each irreducible factor q of the minimal polynomial μ,
    the quotient μ/q has degree < n, so (μ/q)(M) ≠ 0, giving ker((μ/q)(M)) as
    a proper subspace. By union avoidance (infinite K), there exists v outside
    all these kernels. If p(M)v = 0 for nonzero p with deg(p) < n, then
    d = gcd(p, μ) properly divides μ and d(M)v = 0 (Bezout). The quotient
    μ/d has an irreducible factor q, and d | (μ/q), so by commutativity
    (μ/q)(M)v = 0, contradicting the choice of v. -/
open UniqueFactorizationMonoid in
theorem nonderogatory_has_cyclic_vector_infinite [Infinite K]
    (M : Matrix (Fin n) (Fin n) K) (h : IsNonderogatory M) :
    ∃ v, IsCyclicVector M v := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact ⟨Fin.elim0, fun p hp _ => by omega⟩
  have h_deg : (minpoly K M).natDegree = n := by
    unfold IsNonderogatory at h; rw [h, charpoly_natDegree_eq_dim, Fintype.card_fin]
  set μ := minpoly K M with hμ_def
  have hμ_monic : μ.Monic := minpoly.monic (isIntegral M)
  have hμ_ne : μ ≠ 0 := hμ_monic.ne_zero
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  haveI : Nontrivial (Fin n → K) := Function.nontrivial
  have hμ_not_unit : ¬IsUnit μ := by
    intro hu; exact absurd (natDegree_eq_zero_of_isUnit hu) (by omega)
  set nf := (normalizedFactors μ).toFinset with nf_def
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
  obtain ⟨v, hv⟩ := not_union_proper_subspaces nf S hS_proper
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
        = (aeval M (t * d) : Matrix (Fin n) (Fin n) K).mulVec v := by rw [mul_comm]
      _ = (aeval M t * aeval M d).mulVec v := by rw [map_mul]
      _ = (aeval M t).mulVec ((aeval M d).mulVec v) :=
          (Matrix.mulVec_mulVec _ _ _).symm
      _ = 0 := by rw [hd_ann, Matrix.mulVec_zero]
  exact absurd hv_in (hv q' hq'_in_nf)

-- ============================================================
-- PART VI: Single Eigenvalue Case (Nilpotent)
-- ============================================================

/-- For a nilpotent matrix N with N^{n-1} ≠ 0, any vector v with
    N^{n-1} v ≠ 0 generates linearly independent Krylov vectors.

    Proof: apply N^{n-1-i} to a linear relation ∑ cₖ N^k v = 0.
    For k > n-1-i: N^k N^{n-1-i} = N^{k+n-1-i} = 0 (nilpotent).
    For k = n-1-i: get c_{n-1-i} N^{n-1} v = 0, so c_{n-1-i} = 0.
    Descending induction gives all coefficients zero. -/
theorem nilpotent_krylov_independent
    (N : Matrix (Fin n) (Fin n) K)
    (hnil : N ^ n = 0)
    (v : Fin n → K) (hv : (N ^ (n - 1)).mulVec v ≠ 0) :
    LinearIndependent K (fun k : Fin n => (N ^ (k : ℕ)).mulVec v) := by
  -- Ascending induction: apply N^{n-1-j} to ∑ c_k N^k v = 0.
  -- For k > j: N^{k+n-1-j} = 0 (nilpotency). For k < j: c_k = 0 (IH).
  -- For k = j: c_j N^{n-1} v = 0, so c_j = 0 (since N^{n-1}v ≠ 0).
  rw [Fintype.linearIndependent_iff]
  intro c hc
  -- Strong induction: prove c ⟨j, _⟩ = 0 for j = 0, 1, ..., n-1
  suffices main : ∀ j : ℕ, (hj : j < n) → c ⟨j, hj⟩ = 0 from
    fun i => main ↑i i.isLt
  intro j hj
  induction j using Nat.strongRecOn with
  | ind j ih =>
    -- Apply N^{n-1-j} to ∑ c_k N^k v = 0 and distribute
    have happ : ∑ k : Fin n, c k • (N ^ (n - 1 - j + ↑k)).mulVec v = 0 := by
      have h0 := congr_arg (fun w => (N ^ (n - 1 - j)).mulVec w) hc
      simp only [Matrix.mulVec_zero] at h0
      -- Distribute mulVec (as a linear map) over sum and smul
      -- Step 1: distribute mulVec over sum and smul
      have hdist : (N ^ (n - 1 - j)).mulVec (∑ k : Fin n, c k • (N ^ (↑k : ℕ)).mulVec v) =
          ∑ k : Fin n, c k • (N ^ (n - 1 - j)).mulVec ((N ^ (↑k : ℕ)).mulVec v) := by
        rw [← Matrix.mulVecLin_apply]; rw [map_sum]
        congr 1; ext k; rw [map_smul, Matrix.mulVecLin_apply]
      rw [hdist] at h0
      -- Step 2: combine matrix products and powers
      simp only [Matrix.mulVec_mulVec, ← pow_add] at h0
      exact h0
    -- The sum reduces to c ⟨j, hj⟩ • N^{n-1} v (other terms vanish)
    have hred : ∑ k : Fin n, c k • (N ^ (n - 1 - j + ↑k)).mulVec v =
                c ⟨j, hj⟩ • (N ^ (n - 1)).mulVec v := by
      rw [Finset.sum_eq_single_of_mem ⟨j, hj⟩ (Finset.mem_univ _)]
      · -- The j-th term: n-1-j+j = n-1
        congr 1; congr 1; congr 1
        exact Nat.sub_add_cancel (Nat.le_sub_one_of_lt hj)
      · -- All other terms vanish
        intro k _ hk
        have hk_val : (↑k : ℕ) ≠ j := fun h => hk (Fin.ext h)
        rcases lt_or_gt_of_ne hk_val with hlt | hgt
        · -- ↑k < j: c k = 0 by induction hypothesis
          have : c k = 0 := by
            have := ih ↑k hlt k.isLt
            rwa [show (⟨↑k, k.isLt⟩ : Fin n) = k from Fin.eta k k.isLt] at this
          simp [this]
        · -- ↑k > j: N^{n-1-j+↑k} ≥ N^n = 0 by nilpotency
          have hge : n ≤ n - 1 - j + ↑k := by
            have := Nat.le_sub_one_of_lt hj
            omega
          have hpow : N ^ (n - 1 - j + ↑k) = 0 := by
            obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hge
            rw [hd, pow_add, hnil, zero_mul]
          simp [hpow, Matrix.zero_mulVec]
    -- Extract: c ⟨j, hj⟩ • N^{n-1} v = 0, so c ⟨j, hj⟩ = 0
    rw [hred] at happ
    rcases smul_eq_zero.mp happ with h | h
    · exact h
    · exact absurd h hv

-- ============================================================
-- Summary
-- ============================================================

/-
  ## Summary: Backward Direction (Infinite Fields)

  **Fully proved** (0 sorries):
  - `aeval_ne_zero_of_ne_zero`: nonzero low-degree polynomials evaluate to nonzero matrices
  - `exists_mulVec_ne_zero`: nonzero matrices have vectors outside their kernel
  - `not_union_proper_subspaces`: union avoidance for finitely many proper subspaces
  - `powers_linearIndependent`: {I, M, ..., M^{n-1}} are linearly independent
  - `isCyclicVector_of_linearIndependent`: LI Krylov vectors → IsCyclicVector
  - `nilpotent_krylov_independent`: nilpotent N with N^{n-1}≠0 → Krylov LI
  - `linearIndependent_of_isCyclicVector`: IsCyclicVector → LI Krylov vectors
  - `gcd_aeval_mulVec_eq_zero`: if p(M)v=0, then gcd(p,μ)(M)v=0 via Bezout

  - `nonderogatory_has_cyclic_vector_infinite`: normalizedFactors union-avoidance
    + GCD/Bezout contradiction. Uses `open UniqueFactorizationMonoid` + explicit
    `DecidableEq K[X]` instance.

  **Proof Architecture for Main Theorem** (nonderogatory → cyclic vector):
  1. deg(minpoly) = n ⟹ {I, M, ..., M^{n-1}} linearly independent [✓]
  2. For each q ∈ normalizedFactors(μ), ker((μ/q)(M)) is proper [✓]
  3. Union avoidance gives v ∉ ⋃ ker((μ/q)(M)) [✓]
  4. GCD/Bezout: if p(M)v = 0, then gcd(p,μ)(M)v = 0 [✓]
  5. Factor extraction: μ/gcd has irreducible factor q, giving d | (μ/q) [✓]
  6. Commutativity: d|μ/q and d(M)v=0 ⟹ (μ/q)(M)v=0 → contradiction [✓]
-/

end Nonderogatory.Backward

end -- noncomputable section
