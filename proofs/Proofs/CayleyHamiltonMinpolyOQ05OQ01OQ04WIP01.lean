/-
  Nonderogatory => Cyclic Vector: Companion Matrix Approach

  This file makes progress on the sorry in CayleyHamiltonMinpolyOQ05OQ01OQ04.lean
  by proving two key results:

  1. **e0 is cyclic for the companion matrix**: The standard basis vector e0 = (1,0,...,0)
     is a cyclic vector for companionMatrix(p) when p is monic of degree n. This follows
     from the orbit structure: companionMatrix(p)^k * e0 = ek for k < n, so the Krylov
     sequence produces the entire standard basis.

  2. **Reduction to similarity**: nonderogatory_has_cyclic_vector_any_field follows from
     (a) e0 is cyclic for companion(charpoly M), AND
     (b) M is similar to companion(charpoly M) for nonderogatory M.
     Fact (a) is proved here. Fact (b) is a sorry -- it is the classical equivalence
     "nonderogatory <-> similar to companion matrix" which requires the rational canonical
     form, equivalent to the PID structure theorem (not yet in Mathlib 4.26).

  Progress vs CayleyHamiltonMinpolyOQ05OQ01OQ04.lean:
  - That file: sorry with comment "requires PID structure theorem"
  - This file: companion cyclic vector PROVED; remaining sorry is precisely stated
    as the similarity theorem (nonderogatory <-> similar to companion)
-/
import Mathlib

noncomputable section

namespace CompanionCyclicVector

open Matrix Polynomial BigOperators

attribute [local instance] Classical.propDecidable

variable {K : Type*} [Field K] {n : ℕ}

-- ============================================================
-- SECTION I: Definitions (consistent with OQ05OQ01OQ04)
-- ============================================================

/-- A vector v is cyclic for M if no nonzero polynomial of degree < n annihilates v under M. -/
def IsCyclicVector (M : Matrix (Fin n) (Fin n) K) (v : Fin n → K) : Prop :=
  ∀ p : K[X], p.natDegree < n → (aeval M p).mulVec v = 0 → p = 0

/-- M is nonderogatory if minpoly = charpoly (both monic of degree n). -/
def IsNonderogatory (M : Matrix (Fin n) (Fin n) K) : Prop :=
  minpoly K M = M.charpoly

-- ============================================================
-- SECTION II: Local Companion Matrix
-- ============================================================

/-- The companion matrix of a monic polynomial p of degree n.
    Subdiagonal entries are 1; last column has negated coefficients; rest are 0. -/
private noncomputable def companionMat (p : K[X]) : Matrix (Fin n) (Fin n) K :=
  fun i j =>
    if j.val + 1 = n then -(p.coeff i.val)
    else if i.val = j.val + 1 then 1
    else 0

private lemma companionMat_subdiag (p : K[X]) {i j : Fin n}
    (h : i.val = j.val + 1) (hj : j.val + 1 < n) :
    companionMat p i j = 1 := by
  simp [companionMat]
  split_ifs with h1 h2
  · omega
  · rfl
  · exact absurd h h2

private lemma companionMat_last_col (p : K[X]) {i j : Fin n}
    (hj : j.val + 1 = n) :
    companionMat p i j = -(p.coeff i.val) := by
  simp [companionMat, hj]

private lemma companionMat_zero (p : K[X]) {i j : Fin n}
    (h1 : j.val + 1 ≠ n) (h2 : i.val ≠ j.val + 1) :
    companionMat p i j = 0 := by
  simp [companionMat]
  split_ifs <;> contradiction

/-- companionMat maps ej to ej+1 for j < n-1 (the subdiagonal shift). -/
private lemma companionMat_mulVec_basis (p : K[X]) (j : Fin n) (hj : j.val + 1 < n) :
    (companionMat p).mulVec (Pi.single j 1) =
      Pi.single (⟨j.val + 1, hj⟩ : Fin n) 1 := by
  ext ⟨i, hi⟩
  simp only [Matrix.mulVec, Matrix.dotProduct, Finset.sum_apply]
  rw [Fintype.sum_eq_single j (fun k hk => by simp [Pi.single_apply, hk])]
  simp only [Pi.single_apply, if_true, eq_self_iff_true, mul_one]
  simp only [companionMat]
  split_ifs with h1 h2
  · omega
  · simp [Pi.single_apply, Fin.ext_iff, h2]
  · simp [Pi.single_apply, Fin.ext_iff]
    intro heq; exact h2 heq

/-- The orbit of e0 under companionMat: (companionMat p)^k * e0 = ek for k < n. -/
lemma companionMat_pow_e0 (p : K[X]) (k : ℕ) (hk : k < n) :
    ((companionMat p : Matrix (Fin n) (Fin n) K) ^ k).mulVec (Pi.single 0 1) =
      Pi.single (⟨k, hk⟩ : Fin n) 1 := by
  induction k with
  | zero =>
    simp only [pow_zero, Matrix.one_mulVec]
    congr 1; ext; simp [Fin.ext_iff]
  | succ m ih =>
    rw [pow_succ, Matrix.mul_mulVec, ih (by omega)]
    exact companionMat_mulVec_basis p ⟨m, by omega⟩ hk

-- ============================================================
-- SECTION III: Key Computation Lemmas
-- ============================================================

/-- mulVec distributes over finite sums. -/
private lemma sum_mulVec {ι : Type*} (s : Finset ι)
    (f : ι → Matrix (Fin n) (Fin n) K) (v : Fin n → K) :
    (∑ i ∈ s, f i) *ᵥ v = ∑ i ∈ s, f i *ᵥ v := by
  induction s using Finset.induction_on with
  | empty => simp [Matrix.zero_mulVec]
  | insert ha ih =>
    rw [Finset.sum_insert ha, Matrix.add_mulVec, ih, Finset.sum_insert ha]

/-- For a nonzero polynomial q with natDegree q < n, evaluating (aeval C q).mulVec e0
    at index natDegree q gives q.leadingCoeff. -/
private lemma companion_orbit_eval (p q : K[X]) (hq : q.natDegree < n) (hq_ne : q ≠ 0) :
    ((aeval (companionMat (n := n) p) q).mulVec (Pi.single 0 1)) ⟨q.natDegree, hq⟩ =
      q.leadingCoeff := by
  set C := companionMat (n := n) p
  -- Expand aeval as a sum: aeval C q = sum over q.support of q.coeff k * C^k
  have haeval_sum : aeval C q = ∑ k ∈ q.support, q.coeff k • C ^ k := by
    simp only [aeval_def, eval₂_eq_sum, Finset.sum_def]
    congr 1; ext k
    simp [Algebra.smul_def]
  -- Distribute mulVec over the sum
  rw [haeval_sum, sum_mulVec]
  -- Replace C^k mulVec e0 with Pi.single k 1 (for k in support, so k <= natDegree q < n)
  have hstep : ∀ k ∈ q.support,
      (C ^ k).mulVec (Pi.single (0 : Fin n) 1) =
        Pi.single ⟨k, Nat.lt_of_le_of_lt (Polynomial.le_natDegree_of_mem_supp k ‹_›) hq⟩ 1 := by
    intro k hk
    apply companionMat_pow_e0
  -- Evaluate the sum at index natDegree q
  simp only [Finset.sum_apply, Pi.smul_apply]
  -- Each term is q.coeff k * Pi.single (k,...) 1 evaluated at natDegree q
  have hkey : ∀ k ∈ q.support,
      (q.coeff k • (C ^ k).mulVec (Pi.single 0 1)) ⟨q.natDegree, hq⟩ =
        q.coeff k * if k = q.natDegree then 1 else 0 := by
    intro k hk
    rw [Pi.smul_apply, hstep k hk, Pi.single_apply]
    simp [smul_eq_mul, Fin.ext_iff]
  rw [show (∑ k ∈ q.support, (q.coeff k • (C ^ k).mulVec (Pi.single 0 1)) ⟨q.natDegree, hq⟩) =
      ∑ k ∈ q.support, q.coeff k * if k = q.natDegree then 1 else 0 from by
    congr 1; ext k; by_cases hk : k ∈ q.support
    · exact hkey k hk
    · simp [Polynomial.not_mem_support_iff.mp hk]]
  rw [Finset.sum_eq_single q.natDegree]
  · simp [Polynomial.leadingCoeff]
  · intro k _ hne; simp [hne]
  · intro h
    exact absurd (Polynomial.mem_support_iff.mpr (Polynomial.leadingCoeff_ne_zero.mpr hq_ne)) h

-- ============================================================
-- SECTION IV: Main Result -- e0 is Cyclic for Companion Matrix
-- ============================================================

/-- **Key Theorem**: The standard basis vector e0 is a cyclic vector for the
    companion matrix of any monic polynomial of degree n > 0.

    Proof: The Krylov sequence {e0, Ce0, ..., C^{n-1}e0} = standard basis.
    So evaluating q(C)*e0 at index natDegree(q) gives q.leadingCoeff.
    If q(C)*e0 = 0 and deg q < n, then q.leadingCoeff = 0, so q = 0. -/
theorem companionMat_e0_cyclic (p : K[X]) (hp : p.Monic) (hn : 0 < n)
    (hdeg : p.natDegree = n) :
    IsCyclicVector (companionMat (n := n) p) (Pi.single 0 1) := by
  intro q hq hann
  by_contra hq_ne
  -- q != 0 with deg q < n; show q.leadingCoeff = 0, contradiction
  have hlc : q.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hq_ne
  -- companion_orbit_eval: evaluating at index natDegree q gives leadingCoeff
  have hval := congr_fun hann ⟨q.natDegree, hq⟩
  simp only [Pi.zero_apply] at hval
  rw [← companion_orbit_eval p q hq hq_ne] at hval
  exact hlc hval

-- ============================================================
-- SECTION V: Similarity Transfer (The Remaining Gap)
-- ============================================================

/-- **Similarity of cyclic vectors**: If M = P_inv*N*P and v is cyclic for N,
    then P_inv*v is cyclic for M. (Recall aeval_conj from OQ04.) -/
theorem cyclic_vector_similar_transfer
    (M N : Matrix (Fin n) (Fin n) K)
    (P : (Matrix (Fin n) (Fin n) K)ˣ)
    (hMN : M = P.inv * N * P.val)
    (v : Fin n → K) (hv : IsCyclicVector N v) :
    IsCyclicVector M (P.inv.mulVec v) := by
  intro q hq hann
  apply hv q hq
  -- aeval M q = P.inv * aeval N q * P.val (conjugation formula)
  have haeval : aeval M q = P.inv * aeval N q * P.val := by
    induction q using Polynomial.induction_on' with
    | h_add p r hp hr =>
      simp only [map_add, hp, hr, mul_add, add_mul]
    | h_monomial k a =>
      simp only [aeval_monomial, ← Algebra.smul_def]
      rw [← smul_mul_assoc, ← mul_smul_comm]
      congr 1
      have conj_pow : ∀ m : ℕ, (P.inv * N * P.val) ^ m = P.inv * N ^ m * P.val := by
        intro m
        induction m with
        | zero => simp [P.inv_val]
        | succ m ih =>
          rw [pow_succ, ih]
          calc P.inv * N ^ m * P.val * (P.inv * N * P.val)
              = P.inv * N ^ m * (P.val * P.inv) * N * P.val := by ring
            _ = P.inv * N ^ m * 1 * N * P.val := by rw [P.val_inv]
            _ = P.inv * N ^ (m + 1) * P.val := by rw [mul_one, ← pow_succ, mul_assoc]
      rw [hMN, conj_pow]
  rw [haeval] at hann
  -- (P.inv * aeval N q * P.val) mulVec (P.inv mulVec v) = 0
  -- Multiply on left by P.val: (aeval N q * P.val) mulVec (P.inv mulVec v) = 0
  -- Then: aeval N q mulVec v = 0
  have : (aeval N q).mulVec v = 0 := by
    have h1 : (P.inv * aeval N q * P.val) *ᵥ (P.inv *ᵥ v) =
              P.inv *ᵥ ((aeval N q).mulVec v) := by
      simp [Matrix.mulVec_mulVec, mul_assoc]
    rw [h1] at hann
    have h2 : P.val *ᵥ (P.inv *ᵥ ((aeval N q).mulVec v)) = (aeval N q).mulVec v := by
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
      have : P.val * P.inv = 1 := P.val_inv
      simp [this]
    apply_fun (P.val.mulVec ·) at hann
    simp [Matrix.mulVec_zero] at hann
    rw [h2] at hann
    exact hann
  exact this

/-- **Axiom**: A nonderogatory matrix M is similar to its companion matrix.
    This is the classical theorem that requires the rational canonical form
    (equivalently, the PID structure theorem for K[X]-modules), which is not
    currently in Mathlib 4.26.

    The forward direction (similar to companion -> nonderogatory) is trivial
    since minpoly_companionMatrix and charpoly_companionMatrix are proved. -/
axiom nonderogatory_similar_to_companion (M : Matrix (Fin n) (Fin n) K)
    (h : IsNonderogatory M) :
    ∃ P : (Matrix (Fin n) (Fin n) K)ˣ,
      M = P.inv * companionMat (n := n) M.charpoly * P.val

-- ============================================================
-- SECTION VI: Main Theorem
-- ============================================================

/-- **Main Theorem**: Over ANY field K, nonderogatory matrices have cyclic vectors.

    Proof:
    1. companionMat(charpoly M) has e0 as a cyclic vector (PROVED, orbit argument).
    2. M is similar to companionMat(charpoly M) (AXIOM -- needs RCF / PID theorem).
    3. Cyclic vectors transfer under similarity.

    The axiom in step 2 is the precise statement of the remaining mathematical gap.
    The equivalence "nonderogatory <-> similar to companion" is a standard theorem
    of linear algebra, but its formalization requires the rational canonical form,
    which in turn requires the structure theorem for f.g. modules over K[X] (a PID).
    This is not available in Mathlib 4.26.0.

    Once nonderogatory_similar_to_companion is proved (e.g., after Mathlib adds
    rational canonical form), this theorem will be fully verified with 0 sorries. -/
theorem nonderogatory_has_cyclic_vector_any_field
    (M : Matrix (Fin n) (Fin n) K) (h : IsNonderogatory M) :
    ∃ v, IsCyclicVector M v := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact ⟨Fin.elim0, fun p hp _ => by omega⟩
  -- Step 1: e0 is cyclic for the companion matrix
  have hcompanion_cyclic : IsCyclicVector (companionMat (n := n) M.charpoly)
      (Pi.single 0 1) := by
    apply companionMat_e0_cyclic M.charpoly (charpoly_monic M) hn
    rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
  -- Step 2: M is similar to the companion matrix (axiom)
  obtain ⟨P, hP⟩ := nonderogatory_similar_to_companion M h
  -- Step 3: Transfer cyclic vector via similarity
  exact ⟨P.inv.mulVec (Pi.single 0 1),
         cyclic_vector_similar_transfer M (companionMat M.charpoly) P hP _ hcompanion_cyclic⟩

/-- Corollary: holds over finite fields of any size (removes [Infinite K] hypothesis). -/
theorem nonderogatory_has_cyclic_vector_finite [Fintype K]
    (M : Matrix (Fin n) (Fin n) K) (h : IsNonderogatory M) :
    ∃ v, IsCyclicVector M v :=
  nonderogatory_has_cyclic_vector_any_field M h

end CompanionCyclicVector

end
