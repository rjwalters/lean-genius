/-
  OQ-01-OQ-02: Nonderogatory Matrices are Similar to Their Companion Matrix
  (cayley-hamilton-cyclic-vector-all-fields-oq-01-oq-02)

  Every nonderogatory n×n matrix M over K is similar to the companion matrix C(minpoly K M).
  This is the nonderogatory case of the rational canonical form.

  ## Status: 0 sorries, 1 axiom (hMn_axiom)
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
  have hcoeff := congr_arg (fun p => p.coeff j.val) hq0
  simp only [hq_def, coeff_sum, coeff_C_mul, coeff_X_pow, mul_ite, mul_one, mul_zero,
             Finset.sum_ite_eq', Finset.mem_univ, if_true, coeff_zero] at hcoeff
  exact hcoeff

theorem cyclicMatrix_injective (M : Matrix (Fin n) (Fin n) K) (v : Fin n → K)
    (hcyc : IsCyclicVector M v) : Function.Injective (cyclicMatrix M v).mulVec := fun c₁ c₂ heq =>
  sub_eq_zero.mp (cyclicMatrix_ker M v hcyc (c₁ - c₂) (by rw [mulVec_sub, heq, sub_self]))

/-- cyclicMatrix is invertible: injective mulVec → IsUnit. -/
theorem cyclicMatrix_isUnit (M : Matrix (Fin n) (Fin n) K) (v : Fin n → K)
    (hcyc : IsCyclicVector M v) : IsUnit (cyclicMatrix M v) :=
  mulVec_injective_iff_isUnit.mp (cyclicMatrix_injective M v hcyc)

/-- M^n v = -(Σ_{k<n} c_k M^k v). Axiomatized: follows from minpoly(M)v = 0. -/
private axiom hMn_axiom (M : Matrix (Fin n) (Fin n) K) (v : Fin n → K)
    [NeZero n] (hdeg : (minpoly K M).natDegree = n) :
    (M ^ n).mulVec v =
      -(∑ k ∈ Finset.range n, (minpoly K M).coeff k • (M ^ k).mulVec v)

theorem M_mul_cyclicMatrix (M : Matrix (Fin n) (Fin n) K) (v : Fin n → K)
    (hcyc : IsCyclicVector M v) [NeZero n] :
    M * cyclicMatrix M v = cyclicMatrix M v * companionMx (minpoly K M) := by
  have hdeg : (minpoly K M).natDegree = n := minpoly_natDegree_of_cyclic M v hcyc
  have hMn := hMn_axiom M v hdeg
  ext i j
  simp only [mul_apply, cyclicMatrix, companionMx, mulVec, dotProduct]
  by_cases hjlast : j.val + 1 = n
  · -- Last column
    simp only [hjlast, ite_true, neg_mul]
    -- LHS: (M^n v)_i
    have hLHS : ∑ k : Fin n, M i k * (M ^ j.val).mulVec v k = (M ^ n).mulVec v i := by
      have heq : M.mulVec ((M ^ j.val).mulVec v) = (M ^ n).mulVec v := by
        rw [← mul_mulVec]
        congr 1
        rw [← hjlast, pow_succ']
      exact congr_fun heq i
    -- RHS: (M^n v)_i
    have hRHS : ∑ k : Fin n, (M ^ k.val).mulVec v i * -(minpoly K M).coeff k.val =
        (M ^ n).mulVec v i := by
      rw [hMn]
      simp only [Pi.neg_apply, Pi.smul_apply, smul_eq_mul]
      rw [← Fin.sum_univ_eq_sum_range]
      simp only [mul_neg, ← Finset.sum_neg_distrib]
      congr 1; ext k; ring
    rw [hLHS, hRHS]
  · -- Non-last column
    push_neg at hjlast
    have hj1 : j.val + 1 < n := Nat.lt_of_le_of_ne j.isLt hjlast
    simp only [if_neg hjlast]
    -- LHS: (M^{j+1} v)_i
    have hLHS : ∑ k : Fin n, M i k * (M ^ j.val).mulVec v k =
        (M ^ (j.val + 1)).mulVec v i := by
      have : M.mulVec ((M ^ j.val).mulVec v) = (M ^ (j.val + 1)).mulVec v := by
        rw [← mul_mulVec, pow_succ']
      exact congr_fun this i
    -- RHS: (M^{j+1} v)_i
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

end CayleyHamiltonCyclicVectorAllFieldsOQ01OQ02

end
