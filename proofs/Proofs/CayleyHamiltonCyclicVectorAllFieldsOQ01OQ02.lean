/-
  OQ-01-OQ-02: Nonderogatory Matrices are Similar to Their Companion Matrix
  (cayley-hamilton-cyclic-vector-all-fields-oq-01-oq-02)

  Every nonderogatory n×n matrix M over K is similar to the companion matrix C(minpoly K M).
  This is the nonderogatory case of the rational canonical form.

  ## Status: 0 sorries, 0 axioms

  The previous `hMn_axiom` (M^n v expressed via lower powers using minpoly coefficients)
  is now derived from Mathlib: minpoly is monic of degree n, so its `aeval`-expansion at M
  gives M^n + Σ_{k<n} c_k • M^k = 0; applying `mulVec v` yields the identity directly.

  ## Session 3: Companion-similarity biconditional

  This session establishes the *converse* of `nonderogatory_similar_to_companion`:
  if M is similar to `companionMx (minpoly K M)`, then M is nonderogatory. Combined
  with the existing forward direction, this yields the full biconditional
  `nonderogatory_iff_similar_to_companion`. The argument:

    1. The standard basis vector e₀ is a cyclic vector for `companionMx p` for any p
       (since C^k e₀ = e_k for k < n by the subdiagonal structure).
    2. Similarity transports cyclic vectors: if P⁻¹ M P = N and w is cyclic for N,
       then P · w is cyclic for M (because q(M)(P w) = P (q(N) w) and P is invertible).
    3. The biconditional `IsNonderogatory M ↔ ∃ v, IsCyclicVector M v` from OQ-01-OQ-01
       then closes the converse: M has a cyclic vector ⇒ M is nonderogatory.
-/
import Mathlib
import Proofs.CayleyHamiltonMinpolyOQ05OQ01OQ04WIP04
import Proofs.CayleyHamiltonCyclicVectorAllFields
import Proofs.CayleyHamiltonCyclicVectorAllFieldsOQ01OQ01

set_option linter.unusedSimpArgs false

noncomputable section

namespace CayleyHamiltonCyclicVectorAllFieldsOQ01OQ02

open Matrix Polynomial GeneralCyclicVector CyclicVectorBiconditional

variable {K : Type*} [Field K] {n : ℕ}

/-- Companion matrix: C[i,j] = -(coeff i) if j=n-1, 1 if i=j+1, 0 otherwise. -/
def companionMx (p : K[X]) : Matrix (Fin n) (Fin n) K :=
  fun i j =>
    if j.val + 1 = n then -(p.coeff i.val)
    else if i.val = j.val + 1 then 1
    else 0

/-- Cyclic orbit matrix: P[i,j] = (Mʲv)ᵢ. -/
def cyclicMatrix (M : Matrix (Fin n) (Fin n) K) (v : Fin n → K) :
    Matrix (Fin n) (Fin n) K :=
  fun i j => (M ^ j.val).mulVec v i

private lemma cyclicMatrix_ker (M : Matrix (Fin n) (Fin n) K)
    (v : Fin n → K) (hcyc : IsCyclicVector M v)
    (c : Fin n → K) (hzero : cyclicMatrix M v *ᵥ c = 0) : c = 0 := by
  set q := ∑ j : Fin n, Polynomial.C (c j) * X ^ j.val with hq_def
  -- q(M)v = 0: since P*c = (q(M))v entrywise
  have hqv : (aeval M q).mulVec v = 0 := by
    funext i
    have key : (aeval M q).mulVec v i = (cyclicMatrix M v *ᵥ c) i := by
      simp only [cyclicMatrix, Matrix.mulVec, dotProduct, hq_def,
                 map_sum, map_mul, aeval_C, aeval_X_pow,
                 Matrix.sum_mulVec, Matrix.smul_mulVec,
                 Finset.sum_apply, Pi.smul_apply, ← Algebra.smul_def, smul_eq_mul]
      congr 1; ext j; ring
    rw [key, congr_fun hzero i, Pi.zero_apply]
  -- deg(q) < n
  have hdeg : q.natDegree < n := by
    apply (natDegree_sum_le _ _).trans_lt
    rw [Finset.sup_lt_iff (b := n)]
    intro ⟨j, hj⟩ _
    simp only [Function.comp]
    calc (Polynomial.C (c ⟨j, hj⟩) * X ^ j).natDegree
        ≤ (Polynomial.C (c ⟨j, hj⟩)).natDegree + (X ^ j : K[X]).natDegree := natDegree_mul_le
      _ ≤ 0 + j := add_le_add natDegree_C_le (by simp [natDegree_pow])
      _ = j := zero_add j
      _ < n := hj
  -- IsCyclicVector: q = 0
  have hq0 : q = 0 := hcyc q hdeg hqv
  -- Extract c j = 0 from coefficient extraction
  funext j
  show c j = 0
  have hcoeff := congr_arg (fun p => p.coeff j.val) hq0
  simp only [hq_def, Polynomial.finset_sum_coeff, coeff_C_mul, coeff_X_pow, mul_ite,
             mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true,
             coeff_zero] at hcoeff
  exact hcoeff

theorem cyclicMatrix_injective (M : Matrix (Fin n) (Fin n) K) (v : Fin n → K)
    (hcyc : IsCyclicVector M v) : Function.Injective (cyclicMatrix M v).mulVec := fun c₁ c₂ heq =>
  sub_eq_zero.mp (cyclicMatrix_ker M v hcyc (c₁ - c₂) (by rw [mulVec_sub, heq, sub_self]))

/-- cyclicMatrix is invertible: injective mulVec → IsUnit. -/
theorem cyclicMatrix_isUnit (M : Matrix (Fin n) (Fin n) K) (v : Fin n → K)
    (hcyc : IsCyclicVector M v) : IsUnit (cyclicMatrix M v) :=
  mulVec_injective_iff_isUnit.mp (cyclicMatrix_injective M v hcyc)

/-- mulVec distributes over finite sums of matrices (local helper). -/
private lemma sum_mulVec_local {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (f : ι → Matrix (Fin n) (Fin n) K) (v : Fin n → K) :
    (∑ i ∈ s, f i).mulVec v = ∑ i ∈ s, (f i).mulVec v := by
  induction s using Finset.induction_on with
  | empty => simp [Matrix.zero_mulVec]
  | @insert a s' has ih =>
      rw [Finset.sum_insert has, Matrix.add_mulVec, ih, Finset.sum_insert has]

/-- aeval expansion: aeval M p = ∑ k ∈ range (n+1), p.coeff k • M^k for natDegree p = n.

    `Polynomial.eval₂_eq_sum` produces `algebraMap _ _ (coeff k) * M^k`; we convert with
    `← Algebra.smul_def` to `coeff k • M^k`, then extend the support sum to `range (n+1)`
    using monotonicity of natDegree. -/
private lemma aeval_eq_sum_pow_local (p : K[X]) (hdeg : p.natDegree = n)
    (M : Matrix (Fin n) (Fin n) K) :
    aeval M p = ∑ k ∈ Finset.range (n + 1), p.coeff k • M ^ k := by
  simp only [aeval_def, Polynomial.eval₂_eq_sum, Polynomial.sum_def, ← Algebra.smul_def]
  apply Finset.sum_subset
  · intro i hi
    exact Finset.mem_range.mpr
      (Nat.lt_succ_of_le (hdeg ▸ Polynomial.le_natDegree_of_mem_supp i hi))
  · intro i _ hi
    simp [Polynomial.notMem_support_iff.mp hi]

/-- **M^n v = -Σ_{k<n} c_k • M^k v** where c_k are the coefficients of minpoly K M.

    Proof: minpoly K M is monic of degree n, so
    aeval M (minpoly K M) = ∑_{k ≤ n} (coeff k) • M^k = (∑_{k<n} c_k • M^k) + M^n.
    Since `aeval M (minpoly K M) = 0`, we get M^n = -∑_{k<n} c_k • M^k.
    Apply mulVec v to both sides. -/
private theorem hMn_axiom (M : Matrix (Fin n) (Fin n) K) (v : Fin n → K)
    [NeZero n] (hdeg : (minpoly K M).natDegree = n) :
    (M ^ n).mulVec v =
      -(∑ k ∈ Finset.range n, (minpoly K M).coeff k • (M ^ k).mulVec v) := by
  set p := minpoly K M with hp_def
  -- p is monic and aeval M p = 0
  have hmon : p.Monic := minpoly.monic (Matrix.isIntegral M)
  have hcoeff_n : p.coeff n = 1 := by
    have := hmon.leadingCoeff
    rwa [Polynomial.leadingCoeff, hdeg] at this
  -- aeval expansion: aeval M p = ∑_{k<n} c_k • M^k + 1 • M^n = 0
  have hsum : aeval M p = ∑ k ∈ Finset.range (n + 1), p.coeff k • M ^ k :=
    aeval_eq_sum_pow_local p hdeg M
  have haeval : aeval M p = 0 := minpoly.aeval K M
  rw [Finset.sum_range_succ, hcoeff_n, one_smul, haeval] at hsum
  -- hsum: 0 = (∑ k<n, c_k • M^k) + M^n  → solve for M^n
  have hMn : M ^ n = -∑ k ∈ Finset.range n, p.coeff k • M ^ k :=
    eq_neg_of_add_eq_zero_right hsum.symm
  -- Apply mulVec v to both sides
  have key := congr_arg (Matrix.mulVec · v) hMn
  simp only [Matrix.neg_mulVec, sum_mulVec_local] at key
  -- key: (M^n).mulVec v = -∑ k<n, ((c_k • M^k).mulVec v)
  -- Convert (c_k • M^k).mulVec v = c_k • (M^k).mulVec v
  rw [key]
  congr 1
  refine Finset.sum_congr rfl ?_
  intro k _
  exact Matrix.smul_mulVec _ _ _

theorem M_mul_cyclicMatrix (M : Matrix (Fin n) (Fin n) K) (v : Fin n → K)
    (hcyc : IsCyclicVector M v) [NeZero n] :
    M * cyclicMatrix M v = cyclicMatrix M v * companionMx (minpoly K M) := by
  have hdeg : (minpoly K M).natDegree = n := minpoly_natDegree_of_cyclic M v hcyc
  have hMn := hMn_axiom M v hdeg
  ext i j
  simp only [mul_apply, cyclicMatrix, companionMx]
  by_cases hjlast : j.val + 1 = n
  · -- Last column: both sides equal (M^n v)_i
    simp only [hjlast, ite_true, neg_mul]
    -- LHS: ∑ k, M i k * (M^j v)_k = (M · (M^j v))_i = (M^n v)_i
    have hLHS : ∑ k : Fin n, M i k * (M ^ j.val).mulVec v k = (M ^ n).mulVec v i := by
      have heq : M.mulVec ((M ^ j.val).mulVec v) = (M ^ n).mulVec v := by
        rw [Matrix.mulVec_mulVec, ← pow_succ', hjlast]
      exact congr_fun heq i
    -- RHS: ∑ k, (M^k v)_i * -coeff k = -∑ k<n, coeff k • (M^k v)_i = (M^n v)_i (by hMn)
    have hRHS : ∑ k : Fin n, (M ^ k.val).mulVec v i * -(minpoly K M).coeff k.val =
        (M ^ n).mulVec v i := by
      rw [hMn]
      simp only [Pi.neg_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      rw [← Fin.sum_univ_eq_sum_range]
      simp only [mul_neg, ← Finset.sum_neg_distrib]
      congr 1; ext k; ring
    rw [hLHS, hRHS]
  · -- Non-last column: both sides equal (M^{j+1} v)_i
    push_neg at hjlast
    have hj1 : j.val + 1 < n := Nat.lt_of_le_of_ne j.isLt hjlast
    simp only [if_neg hjlast]
    -- LHS: ∑ k, M i k * (M^j v)_k = (M · (M^j v))_i = (M^{j+1} v)_i
    have hLHS : ∑ k : Fin n, M i k * (M ^ j.val).mulVec v k =
        (M ^ (j.val + 1)).mulVec v i := by
      have h0 : M.mulVec ((M ^ j.val).mulVec v) = (M ^ (j.val + 1)).mulVec v := by
        rw [Matrix.mulVec_mulVec, ← pow_succ']
      exact congr_fun h0 i
    -- RHS: ∑ k, (M^k v)_i * (if k=j+1 then 1 else 0) = (M^{j+1} v)_i
    have hRHS : ∑ k : Fin n, (M ^ k.val).mulVec v i *
        (if k.val = j.val + 1 then (1 : K) else 0) = (M ^ (j.val + 1)).mulVec v i := by
      rw [Finset.sum_eq_single ⟨j.val + 1, hj1⟩]
      · simp
      · intro k _ hk; simp [show ¬k.val = j.val + 1 from fun h => hk (Fin.ext h)]
      · intro h; exact absurd (Finset.mem_univ _) h
    rw [hLHS, hRHS]

/-- Every nonderogatory matrix is similar to its companion matrix. -/
theorem nonderogatory_similar_to_companion
    (M : Matrix (Fin n) (Fin n) K)
    (h : GeneralCyclicVector.IsNonderogatory M) (hn : 0 < n) :
    ∃ P : Matrix (Fin n) (Fin n) K, IsUnit P ∧
      P⁻¹ * M * P = companionMx (minpoly K M) := by
  haveI : NeZero n := ⟨hn.ne'⟩
  obtain ⟨v, hcyc⟩ := CayleyHamiltonCyclicVectorAllFields.nonderogatory_has_cyclic_vector M h
  have hPunit : IsUnit (cyclicMatrix M v) := cyclicMatrix_isUnit M v hcyc
  have hconj : M * cyclicMatrix M v = cyclicMatrix M v * companionMx (minpoly K M) :=
    M_mul_cyclicMatrix M v hcyc
  have hPI : (cyclicMatrix M v)⁻¹ * cyclicMatrix M v = 1 := by
    apply nonsing_inv_mul
    exact (isUnit_iff_isUnit_det (A := cyclicMatrix M v)).mp hPunit
  exact ⟨cyclicMatrix M v, hPunit, by
    calc (cyclicMatrix M v)⁻¹ * M * cyclicMatrix M v
        = (cyclicMatrix M v)⁻¹ * (M * cyclicMatrix M v) := mul_assoc _ _ _
      _ = (cyclicMatrix M v)⁻¹ * (cyclicMatrix M v * companionMx (minpoly K M)) := by rw [hconj]
      _ = ((cyclicMatrix M v)⁻¹ * cyclicMatrix M v) * companionMx (minpoly K M) :=
          (mul_assoc _ _ _).symm
      _ = 1 * companionMx (minpoly K M) := by rw [hPI]
      _ = companionMx (minpoly K M) := one_mul _⟩

/-! ## Session 3: Converse direction — companion-similarity biconditional -/

/-- aeval expansion to a finite sum (general polynomial, no degree assumption). -/
private lemma aeval_eq_sum_range_natDegree (q : K[X])
    (M : Matrix (Fin n) (Fin n) K) :
    aeval M q = ∑ k ∈ Finset.range (q.natDegree + 1), q.coeff k • M ^ k := by
  simp only [aeval_def, Polynomial.eval₂_eq_sum, Polynomial.sum_def, ← Algebra.smul_def]
  apply Finset.sum_subset
  · intro i hi
    exact Finset.mem_range.mpr
      (Nat.lt_succ_of_le (Polynomial.le_natDegree_of_mem_supp i hi))
  · intro i _ hi
    simp [Polynomial.notMem_support_iff.mp hi]

/-- For C = companionMx p (any p), C^k applied to the standard basis vector e₀
    equals e_k, for k < n. Reflects the subdiagonal structure of C. -/
private lemma companionMx_pow_e0 (p : K[X]) (hn : 0 < n) :
    ∀ (k : ℕ) (hk : k < n),
      ((companionMx (n := n) p) ^ k).mulVec (Pi.single (⟨0, hn⟩ : Fin n) (1 : K)) =
        Pi.single (⟨k, hk⟩ : Fin n) 1 := by
  intro k
  induction k with
  | zero =>
    intro _
    simp [pow_zero, Matrix.one_mulVec]
  | succ k ih =>
    intro hk
    have hk' : k < n := Nat.lt_of_succ_lt hk
    -- A^(k+1) = A * A^k via pow_succ', so (A^(k+1)).mulVec v = A.mulVec (A^k.mulVec v).
    rw [pow_succ', Matrix.mul_mulVec, ih hk']
    funext i
    simp only [Matrix.mulVec, dotProduct]
    rw [Finset.sum_eq_single (⟨k, hk'⟩ : Fin n)]
    · -- Main term: companionMx p i ⟨k, hk'⟩ * (Pi.single ⟨k, hk'⟩ 1) ⟨k, hk'⟩
      simp only [Pi.single_eq_same, mul_one, companionMx]
      have hk1ne : k + 1 ≠ n := Nat.ne_of_lt hk
      rw [if_neg hk1ne]
      -- Goal: (if i.val = k + 1 then (1:K) else 0) = Pi.single ⟨k+1, hk⟩ 1 i
      simp only [Pi.single_apply]
      by_cases hi : i.val = k + 1
      · have hieq : (i : Fin n) = ⟨k + 1, hk⟩ := Fin.ext hi
        rw [if_pos hi, if_pos hieq]
      · have hineq : (i : Fin n) ≠ ⟨k + 1, hk⟩ := fun h => hi (by rw [h])
        rw [if_neg hi, if_neg hineq]
    · -- Off-diagonal term vanishes via Pi.single
      intro j _ hjne
      have hpi : (Pi.single (⟨k, hk'⟩ : Fin n) (1 : K)) j = 0 := by
        simp only [Pi.single_apply, if_neg hjne]
      rw [hpi, mul_zero]
    · intro h; exact absurd (Finset.mem_univ _) h

/-- For any polynomial p, the standard basis vector e₀ is a cyclic vector
    for `companionMx p`. -/
private theorem companionMx_isCyclic_e0 (p : K[X]) (hn : 0 < n) :
    IsCyclicVector (companionMx (n := n) p) (Pi.single (⟨0, hn⟩ : Fin n) (1 : K)) := by
  intro q hq_deg hann
  -- Show q.coeff k = 0 for all k by examining hann at position k.
  ext k
  rw [Polynomial.coeff_zero]
  rcases lt_or_ge k n with hk | hk
  · -- Case k < n: extract from hann at position ⟨k, hk⟩.
    have h_at_k := congr_fun hann ⟨k, hk⟩
    simp only [Pi.zero_apply] at h_at_k
    rw [aeval_eq_sum_range_natDegree q (companionMx p), sum_mulVec_local,
        Finset.sum_apply] at h_at_k
    -- h_at_k : ∑ j ∈ range (deg q + 1), (q.coeff j • C^j).mulVec e0 ⟨k, hk⟩ = 0
    rcases le_or_lt k q.natDegree with hkd | hkd
    · -- Case k ≤ deg q: isolate j = k in the sum.
      have hk_in : k ∈ Finset.range (q.natDegree + 1) :=
        Finset.mem_range.mpr (Nat.lt_succ_of_le hkd)
      have term_at_k :
          (q.coeff k • (companionMx (n := n) p) ^ k).mulVec
            (Pi.single (⟨0, hn⟩ : Fin n) 1) ⟨k, hk⟩ = q.coeff k := by
        rw [Matrix.smul_mulVec, companionMx_pow_e0 p hn k hk]
        simp [Pi.single_eq_same]
      have other_terms_zero : ∀ j ∈ Finset.range (q.natDegree + 1), j ≠ k →
          (q.coeff j • (companionMx (n := n) p) ^ j).mulVec
            (Pi.single (⟨0, hn⟩ : Fin n) 1) ⟨k, hk⟩ = 0 := by
        intro j hj_mem hj_ne
        have hj_lt_n : j < n := by
          have h1 : j < q.natDegree + 1 := Finset.mem_range.mp hj_mem
          omega
        rw [Matrix.smul_mulVec, companionMx_pow_e0 p hn j hj_lt_n]
        simp only [Pi.smul_apply, Pi.single_apply, smul_eq_mul]
        rw [if_neg]
        · exact mul_zero _
        · intro h
          -- h : (⟨k, hk⟩ : Fin n) = ⟨j, hj_lt_n⟩; extract k = j and contradict hj_ne.
          exact hj_ne (congrArg Fin.val h.symm)
      rw [Finset.sum_eq_single k other_terms_zero (fun h => absurd hk_in h)] at h_at_k
      rw [term_at_k] at h_at_k
      exact h_at_k
    · -- Case k > deg q: q.coeff k = 0 by definition of natDegree.
      exact Polynomial.coeff_eq_zero_of_natDegree_lt hkd
  · -- Case k ≥ n: q.coeff k = 0 since deg q < n ≤ k.
    exact Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_lt_of_le hq_deg hk)

/-- **Similarity transports cyclic vectors**: if P⁻¹ M P = N with P invertible
    and w is cyclic for N, then P · w is cyclic for M. -/
private theorem cyclicVector_similar_transport
    (M N : Matrix (Fin n) (Fin n) K) (P : Matrix (Fin n) (Fin n) K) (hP : IsUnit P)
    (hsim : P⁻¹ * M * P = N) (w : Fin n → K) (hw : IsCyclicVector N w) :
    IsCyclicVector M (P.mulVec w) := by
  intro q hq_deg hann
  -- Apply hw at q with the goal (aeval N q).mulVec w = 0.
  apply hw q hq_deg
  -- M * P = P * N (multiply hsim by P on the left and use P * P⁻¹ = 1).
  have hPunit_det : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).mp hP
  have hPP_inv : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P hPunit_det
  have hMP : M * P = P * N := by
    have h1 : P * (P⁻¹ * M * P) = P * N := by rw [hsim]
    have h2 : P * (P⁻¹ * M * P) = M * P := by
      -- P * ((P⁻¹ * M) * P) → (P * (P⁻¹ * M)) * P → ((P * P⁻¹) * M) * P → (1 * M) * P → M * P
      rw [← mul_assoc P (P⁻¹ * M) P, ← mul_assoc P P⁻¹ M, hPP_inv, one_mul]
    exact h2.symm.trans h1
  -- Show M^j * P = P * N^j by induction on j.
  have hsemi : ∀ j : ℕ, M ^ j * P = P * N ^ j := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      calc M ^ (j + 1) * P
          = M * (M ^ j * P) := by rw [pow_succ', mul_assoc]
        _ = M * (P * N ^ j) := by rw [ih]
        _ = (M * P) * N ^ j := by rw [mul_assoc]
        _ = (P * N) * N ^ j := by rw [hMP]
        _ = P * N ^ (j + 1) := by rw [mul_assoc, ← pow_succ']
  -- Lift to aeval: aeval M q * P = P * aeval N q.
  have hac : aeval M q * P = P * aeval N q := by
    rw [aeval_eq_sum_range_natDegree q M, aeval_eq_sum_range_natDegree q N,
        Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    -- (q.coeff j • M^j) * P → q.coeff j • (M^j * P) → q.coeff j • (P * N^j)
    -- mul_smul_comm: rewrites a * (c • b) to c • (a * b), giving P * (q.coeff j • N^j) on RHS.
    rw [smul_mul_assoc, hsemi, mul_smul_comm]
  -- Convert to mulVec form and apply injectivity of P.mulVec.
  have hmv : (aeval M q * P).mulVec w = (P * aeval N q).mulVec w := by rw [hac]
  -- (A * B).mulVec v = A.mulVec (B.mulVec v) via ← Matrix.mulVec_mulVec.
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hann] at hmv
  -- hmv : 0 = P.mulVec ((aeval N q).mulVec w)
  have hPmv : P.mulVec ((aeval N q).mulVec w) = 0 := hmv.symm
  have hPinj : Function.Injective P.mulVec :=
    Matrix.mulVec_injective_iff_isUnit.mpr hP
  exact hPinj (by rw [hPmv, Matrix.mulVec_zero])

/-- **Converse direction**: if M is similar to `companionMx (minpoly K M)`, then
    M is nonderogatory. -/
theorem similar_to_companion_implies_nonderogatory
    (M : Matrix (Fin n) (Fin n) K)
    {P : Matrix (Fin n) (Fin n) K} (hP : IsUnit P)
    (hsim : P⁻¹ * M * P = companionMx (minpoly K M)) (hn : 0 < n) :
    GeneralCyclicVector.IsNonderogatory M := by
  have h_e0_cyc :
      IsCyclicVector (companionMx (n := n) (minpoly K M))
        (Pi.single (⟨0, hn⟩ : Fin n) (1 : K)) :=
    companionMx_isCyclic_e0 _ hn
  have h_Pe0_cyc : IsCyclicVector M (P.mulVec (Pi.single (⟨0, hn⟩ : Fin n) 1)) :=
    cyclicVector_similar_transport M (companionMx (minpoly K M)) P hP hsim _ h_e0_cyc
  exact (CyclicVectorBiconditional.nonderogatory_iff_has_cyclic_vector M).mpr
    ⟨_, h_Pe0_cyc⟩

/-- **Companion-similarity biconditional**: M is nonderogatory iff M is similar
    to the companion matrix of its minimal polynomial.

    The forward direction is `nonderogatory_similar_to_companion` (Session 1+2).
    The backward direction is `similar_to_companion_implies_nonderogatory`
    (Session 3), proved via cyclic-vector transport: e₀ is cyclic for the
    companion matrix, so P · e₀ is cyclic for M, so M is nonderogatory by
    the cyclic-vector biconditional from OQ-01-OQ-01. -/
theorem nonderogatory_iff_similar_to_companion
    (M : Matrix (Fin n) (Fin n) K) (hn : 0 < n) :
    GeneralCyclicVector.IsNonderogatory M ↔
      ∃ P : Matrix (Fin n) (Fin n) K, IsUnit P ∧
        P⁻¹ * M * P = companionMx (minpoly K M) := by
  refine ⟨fun h => nonderogatory_similar_to_companion M h hn, ?_⟩
  rintro ⟨P, hP, hsim⟩
  exact similar_to_companion_implies_nonderogatory M hP hsim hn

/-! ## Session 4: companionMx satisfies its polynomial — vector form at e₀

  Stepping stone toward `aeval (companionMx p) p = 0` for monic `p` of degree `n`,
  which would give `minpoly K (companionMx p) = p` (Q2 of the openQuestions list).

  Strategy:
    - `companionMx_mulVec_eNm1`: action of `companionMx p` on e_{n-1} returns the
      last column = `(-(p.coeff i))_{i<n}` (by the def of companionMx).
    - `companionMx_pow_n_eq_lastCol_e0`: combining `companionMx_pow_e0` (k = n-1)
      with the last-column action, `(companionMx p)^n e₀ = -∑ p.coeff i • e_i`.
    - `aeval_companionMx_p_mulVec_e0_zero`: monicity (`p.coeff n = 1`) cancels the
      `1 • C^n e₀` term against `∑_{k<n} p.coeff k • C^k e₀ = ∑_{k<n} p.coeff k • e_k`.

  The matrix-level identity `aeval (companionMx p) p = 0` follows from cyclicity of
  e₀ (Session 3's `companionMx_isCyclic_e0` extended just past `natDegree < n`)
  but needs a small additional step and is deferred to Session 5.
-/

/-- Action of `companionMx p` on `e_{n-1}`: it returns the last column of the matrix,
    which by the definition of `companionMx` is the vector `(-(p.coeff i))_{i<n}`. -/
private lemma companionMx_mulVec_eNm1 (p : K[X]) (hn : 0 < n) :
    (companionMx (n := n) p).mulVec
        (Pi.single (⟨n - 1, Nat.sub_lt hn one_pos⟩ : Fin n) (1 : K)) =
      fun i : Fin n => -(p.coeff i.val) := by
  funext i
  simp only [Matrix.mulVec, dotProduct]
  rw [Finset.sum_eq_single (⟨n - 1, Nat.sub_lt hn one_pos⟩ : Fin n)]
  · -- Main term: companionMx p i ⟨n-1, _⟩ * 1 = -(p.coeff i.val).
    -- The first if-condition `j.val + 1 = n` triggers for j = ⟨n-1, _⟩.
    simp only [Pi.single_eq_same, mul_one, companionMx]
    have hnstep : (n - 1 : ℕ) + 1 = n := Nat.sub_add_cancel hn
    rw [if_pos hnstep]
  · -- Off-diagonal: Pi.single is zero away from ⟨n-1, _⟩.
    intro j _ hjne
    have hpsi : (Pi.single (⟨n - 1, Nat.sub_lt hn one_pos⟩ : Fin n) (1 : K)) j = 0 := by
      simp only [Pi.single_apply, if_neg hjne]
    rw [hpsi, mul_zero]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- For `n ≥ 1`, `(companionMx p)^n` applied to `e₀` returns the last-column
    vector `(-(p.coeff i))_{i<n}`. Combines `companionMx_pow_e0` (k = n-1) with
    `companionMx_mulVec_eNm1`. -/
private lemma companionMx_pow_n_eq_lastCol_e0 (p : K[X]) (hn : 0 < n) :
    ((companionMx (n := n) p) ^ n).mulVec (Pi.single (⟨0, hn⟩ : Fin n) (1 : K)) =
      fun i : Fin n => -(p.coeff i.val) := by
  have hnn1 : n - 1 < n := Nat.sub_lt hn one_pos
  -- Rewrite the exponent n as (n-1) + 1 (via congr 1 + omega), then apply pow_succ'.
  have hpow_eq : (companionMx (n := n) p) ^ n =
      (companionMx (n := n) p) ^ (n - 1 + 1) := by
    congr 1; omega
  rw [hpow_eq, pow_succ', Matrix.mul_mulVec,
      companionMx_pow_e0 p hn (n - 1) hnn1]
  exact companionMx_mulVec_eNm1 p hn

/-- For monic `p` of degree `n` (with `n ≥ 1`), the polynomial `p` annihilates
    `companionMx p` *applied to* the standard basis vector `e₀`. This is the
    main computational step toward the matrix-level identity
    `aeval (companionMx p) p = 0` (which together with cyclicity of `e₀` would
    yield `minpoly K (companionMx p) = p`). -/
private lemma aeval_companionMx_p_mulVec_e0_zero
    (p : K[X]) (hp_monic : p.Monic) (hp_deg : p.natDegree = n) (hn : 0 < n) :
    (aeval (companionMx (n := n) p) p).mulVec
        (Pi.single (⟨0, hn⟩ : Fin n) (1 : K)) = 0 := by
  -- Expand aeval as a finite sum and apply mulVec termwise.
  rw [aeval_eq_sum_range_natDegree p (companionMx (n := n) p), sum_mulVec_local, hp_deg]
  -- Peel off the k = n top term.
  rw [Finset.sum_range_succ]
  -- Monic + natDegree = n: p.coeff n = 1.
  have hcn : p.coeff n = 1 := by
    have hlc := hp_monic.leadingCoeff
    rwa [Polynomial.leadingCoeff, hp_deg] at hlc
  rw [hcn, one_smul]
  -- Apply C^n e₀ = (-(p.coeff i))_{i<n}.
  rw [companionMx_pow_n_eq_lastCol_e0 p hn]
  funext i
  simp only [Pi.add_apply, Finset.sum_apply, Pi.zero_apply]
  -- The sum over k < n of (p.coeff k • C^k.mulVec e₀) at i picks out k = i.val,
  -- giving p.coeff i.val. The C^n term contributes -(p.coeff i.val); they cancel.
  have hsum_at_i :
      ∑ k ∈ Finset.range n,
          (p.coeff k • (companionMx (n := n) p) ^ k).mulVec
            (Pi.single (⟨0, hn⟩ : Fin n) 1) i = p.coeff i.val := by
    rw [Finset.sum_eq_single i.val]
    · -- Main term: k = i.val.
      rw [Matrix.smul_mulVec, companionMx_pow_e0 p hn i.val i.isLt]
      simp only [Pi.smul_apply, smul_eq_mul]
      have hieq : (⟨i.val, i.isLt⟩ : Fin n) = i := Fin.ext rfl
      rw [hieq, Pi.single_eq_same, mul_one]
    · -- Off-diagonal: k ∈ range n, k ≠ i.val.
      intro k hk hkne
      have hk_lt_n : k < n := Finset.mem_range.mp hk
      rw [Matrix.smul_mulVec, companionMx_pow_e0 p hn k hk_lt_n]
      simp only [Pi.smul_apply, smul_eq_mul]
      have hne : i ≠ (⟨k, hk_lt_n⟩ : Fin n) := by
        intro heq; exact hkne (congrArg Fin.val heq).symm
      have hpsi : (Pi.single (⟨k, hk_lt_n⟩ : Fin n) (1 : K)) i = 0 := by
        rw [Pi.single_apply, if_neg hne]
      rw [hpsi, mul_zero]
    · -- Vacuous: i.val ∈ range n always.
      intro h; exact absurd (Finset.mem_range.mpr i.isLt) h
  rw [hsum_at_i]
  ring

end CayleyHamiltonCyclicVectorAllFieldsOQ01OQ02

end
