/-
  Aristotle targets for Cayley-Hamilton Minpoly OQ-03
  (Computational Complexity of Finding the Minimal Polynomial)

  All theorems now proved — proofs transferred from
  CayleyHamiltonMinpolyOQ03.lean main formalization.
  See that file for the full development and documentation.
-/
import Mathlib.LinearAlgebra.Matrix.Charpoly.Minpoly
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.LinearIndependent.Basic
import Mathlib.Tactic

namespace MinpolyComplexityAristotle

open Matrix Polynomial Finset

variable {K : Type*} [Field K] {n : ℕ}

/-- The k-th Krylov vector: M^k applied to v. -/
def krylovVec (M : Matrix (Fin n) (Fin n) K) (v : Fin n → K) (k : ℕ) : Fin n → K :=
  (M ^ k).mulVec v

-- Helper: mulVec distributes over finite sums of matrices
private theorem sum_mulVec {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (f : ι → Matrix (Fin n) (Fin n) K) (v : Fin n → K) :
    (∑ i ∈ s, f i).mulVec v = ∑ i ∈ s, (f i).mulVec v := by
  induction s using Finset.induction_on with
  | empty => simp [Matrix.zero_mulVec]
  | @insert a s' has ih =>
    rw [Finset.sum_insert has, Matrix.add_mulVec, ih, Finset.sum_insert has]

/-- Polynomial evaluation at a matrix distributes through mulVec as a
    linear combination of Krylov vectors with the polynomial's coefficients. -/
theorem aeval_mulVec_eq_krylov_sum (M : Matrix (Fin n) (Fin n) K)
    (v : Fin n → K) (p : K[X]) :
    (aeval M p).mulVec v =
      ∑ i ∈ range (p.natDegree + 1), p.coeff i • krylovVec M v i := by
  have haeval_expand : aeval M p =
      ∑ i ∈ range (p.natDegree + 1), p.coeff i • M ^ i := by
    simp only [aeval_def, Polynomial.eval₂_eq_sum, Polynomial.sum_def]
    have hsub : p.support ⊆ range (p.natDegree + 1) := by
      intro i hi
      exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Polynomial.le_natDegree_of_mem_supp _ hi))
    rw [Finset.sum_subset hsub]
    · congr 1; ext i
      rw [Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]
    · intro i _ hi
      rw [Polynomial.notMem_support_iff.mp hi, map_zero, zero_mul]
  rw [haeval_expand, sum_mulVec]
  simp only [Matrix.smul_mulVec, krylovVec]

/-- The minimal polynomial annihilates every vector. -/
theorem minpoly_annihilates_vec (M : Matrix (Fin n) (Fin n) K)
    (v : Fin n → K) :
    (aeval M (minpoly K M)).mulVec v = 0 := by
  simp [minpoly.aeval K M]

/-- The Krylov vectors {v, Mv, ..., M^d·v} are linearly dependent where
    d = deg(minpoly). The minimal polynomial provides the nontrivial
    dependence relation via its monic leading coefficient. -/
theorem krylov_dependent_at_minpoly_degree [hn : NeZero n]
    (M : Matrix (Fin n) (Fin n) K) (v : Fin n → K) :
    ¬ LinearIndependent K
      (fun i : Fin ((minpoly K M).natDegree + 1) => krylovVec M v i) := by
  intro hli
  have hmonic := minpoly.monic (isIntegral M)
  have hann := minpoly_annihilates_vec M v
  rw [aeval_mulVec_eq_krylov_sum] at hann
  rw [← Fin.sum_univ_eq_sum_range] at hann
  have hzero := (Fintype.linearIndependent_iff.mp hli)
    (fun i => (minpoly K M).coeff ↑i) hann
  have h0 : (minpoly K M).leadingCoeff = 0 :=
    hzero ⟨(minpoly K M).natDegree, Nat.lt_succ_of_le le_rfl⟩
  exact one_ne_zero (hmonic.leadingCoeff.symm.trans h0)

/-- For a nonderogatory matrix (minpoly = charpoly), a cyclic vector
    produces exactly n linearly independent Krylov vectors. -/
theorem nonderogatory_krylov_optimal
    (M : Matrix (Fin n) (Fin n) K)
    (v : Fin n → K)
    (hcyclic : ∀ p : K[X], p.natDegree < n → (aeval M p).mulVec v = 0 → p = 0)
    (hnond : minpoly K M = M.charpoly) :
    LinearIndependent K (fun i : Fin n => krylovVec M v i) := by
  by_cases hn : n = 0
  · subst hn; exact linearIndependent_empty_type
  · rw [Fintype.linearIndependent_iff]
    intro g hg
    set p := ∑ i : Fin n, Polynomial.C (g i) * Polynomial.X ^ (i : ℕ) with hp_def
    have hpv : (aeval M p).mulVec v = 0 := by
      rw [hp_def, map_sum, sum_mulVec]
      simp only [map_mul, map_pow, aeval_C, aeval_X,
        Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul, Matrix.smul_mulVec]
      exact hg
    have hpd : p.natDegree < n := by
      calc p.natDegree
          ≤ Finset.univ.sup (fun i : Fin n =>
              (Polynomial.C (g i) * Polynomial.X ^ (i : ℕ)).natDegree) :=
            Polynomial.natDegree_sum_le _ _
        _ < n := by
            rw [Finset.sup_lt_iff (Nat.pos_of_ne_zero hn)]
            intro i _
            exact (Polynomial.natDegree_C_mul_X_pow_le (g i) i).trans_lt i.isLt
    have hp0 := hcyclic p hpd hpv
    intro i
    have hpc : p.coeff ↑i = 0 := by simp [hp0]
    rw [hp_def, Polynomial.finset_sum_coeff] at hpc
    simp only [Polynomial.coeff_C_mul_X_pow] at hpc
    rw [Finset.sum_eq_single i] at hpc
    · simpa using hpc
    · intro j _ hji; exact if_neg (Ne.symm (Fin.val_ne_of_ne hji))
    · intro h; exact absurd (Finset.mem_univ i) h

end MinpolyComplexityAristotle
