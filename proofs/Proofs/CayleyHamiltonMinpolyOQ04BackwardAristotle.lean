/-
  Aristotle targets for cayley-hamilton-minpoly-oq-04 (backward direction)
  Routine supporting lemmas for automated proof search.
  See CayleyHamiltonMinpolyOQ04Backward.lean for the main formalization.

  Criteria for inclusion:
  - NOT the main open conjecture (backward direction of nonderogatory characterization)
  - Known results likely provable from Mathlib
  - Clean theorem statements with no definition sorries
  - No axioms
-/
import Mathlib.LinearAlgebra.Matrix.Charpoly.Minpoly
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.LinearIndependent.Basic
import Mathlib.Tactic

namespace Nonderogatory.Backward.Aristotle

open Matrix Polynomial

variable {K : Type*} [Field K] {n : ℕ}

-- ============================================================
-- Lemma 1: Nonzero low-degree polynomial evaluates to nonzero matrix
-- ============================================================

/-- If p is nonzero with deg < deg(minpoly), then p(M) ≠ 0. -/
theorem aeval_ne_zero_of_ne_zero {M : Matrix (Fin n) (Fin n) K}
    {p : K[X]} (hp : p ≠ 0) (hd : p.natDegree < (minpoly K M).natDegree) :
    aeval M p ≠ 0 := by
  intro h_eq
  -- If aeval M p = 0, the minpoly divides p (after making it monic)
  -- But deg(minpoly) > deg(p), so minpoly can't divide a nonzero p of lower degree
  have h_minpoly_dvd := minpoly.dvd K M h_eq
  have h_deg := Polynomial.natDegree_le_of_dvd h_minpoly_dvd hp
  omega

-- ============================================================
-- Lemma 2: Nonzero matrix has a vector outside its kernel
-- ============================================================

/-- A nonzero matrix has a vector not in its kernel. -/
theorem exists_mulVec_ne_zero' {n : ℕ}
    {A : Matrix (Fin n) (Fin n) K} (hA : A ≠ 0) :
    ∃ v : Fin n → K, A.mulVec v ≠ 0 := by
  -- If ∀ v, A.mulVec v = 0, then A = 0 (contradiction)
  by_contra h
  push_neg at h
  apply hA
  ext i j
  have hv := congr_fun (h (Pi.single j 1)) i
  simp only [Pi.zero_apply] at hv
  -- Show (A *ᵥ Pi.single j 1) i = A i j
  simp only [mulVec, dotProduct, Pi.single_apply, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true, mul_one] at hv
  simpa using hv

-- ============================================================
-- Lemma 3: Polynomial coefficient extraction
-- ============================================================

/-- If ∑ cₖ Xᵏ = 0 as a polynomial, then cₖ = 0 for all k. -/
theorem coeff_sum_eq_zero_of_sum_eq_zero
    {s : Finset (Fin n)} {c : Fin n → K}
    (h : ∑ k ∈ s, C (c k) * X ^ (k : ℕ) = (0 : K[X]))
    (i : Fin n) (hi : i ∈ s) : c i = 0 := by
  have h_coeff : (∑ k ∈ s, C (c k) * X ^ (k : ℕ)).coeff (i : ℕ) = 0 := by
    rw [h]; simp
  simp only [Polynomial.finset_sum_coeff, Polynomial.coeff_C_mul_X_pow] at h_coeff
  -- h_coeff : ∑ x ∈ s, if ↑i = ↑x then c x else 0 = 0
  -- Flip equality direction so sum_eq_single_of_mem can match
  simp only [eq_comm (a := (i : ℕ))] at h_coeff
  rwa [Finset.sum_eq_single_of_mem i hi (fun k _ hki => if_neg (Fin.val_ne_of_ne hki)),
    if_pos rfl] at h_coeff

-- ============================================================
-- Lemma 4: Degree bound for polynomial sum
-- ============================================================

/-- A polynomial ∑ cₖ Xᵏ for k : Fin n has degree < n. -/
theorem natDegree_sum_lt {s : Finset (Fin n)} {c : Fin n → K}
    (hn : 0 < n) :
    (∑ k ∈ s, C (c k) * X ^ (k : ℕ)).natDegree < n := by
  calc (∑ k ∈ s, C (c k) * X ^ (k : ℕ)).natDegree
      ≤ s.sup (fun k => (C (c k) * X ^ (k : ℕ)).natDegree) :=
        Polynomial.natDegree_sum_le s _
    _ ≤ n - 1 := by
        apply Finset.sup_le; intro k _
        exact (Polynomial.natDegree_C_mul_X_pow_le (c k) k).trans
          (Nat.lt_iff_le_pred hn |>.mp k.isLt)
    _ < n := Nat.sub_lt hn Nat.one_pos

-- ============================================================
-- Lemma 5: Linear independence from annihilation
-- ============================================================

/-- If {v, Mv, ..., M^{n-1}v} are linearly independent and p(M)v = 0
    with deg(p) < n, then p = 0. -/
theorem eq_zero_of_aeval_mulVec_eq_zero
    {M : Matrix (Fin n) (Fin n) K} {v : Fin n → K}
    (hli : LinearIndependent K (fun k : Fin n => (M ^ (k : ℕ)).mulVec v))
    {p : K[X]} (hp_deg : p.natDegree < n) (hp_ann : (aeval M p).mulVec v = 0) :
    p = 0 := by
  -- Extract coefficient data from linear independence
  rw [Fintype.linearIndependent_iff] at hli
  -- Express aeval M p as sum over Fin n, using natDegree < n
  have hp_expand : (aeval M p).mulVec v =
      ∑ i : Fin n, p.coeff (i : ℕ) • (M ^ (i : ℕ)).mulVec v := by
    simp only [aeval_def,
      eval₂_eq_sum_range' (algebraMap K _) M (show p.natDegree < n from hp_deg)]
    simp only [Matrix.sum_mulVec, Pi.smul_apply, Matrix.mulVec_smul]
    congr 1; ext i
    simp [Algebra.algebraMap_eq_smul_one, Matrix.smul_mulVec_assoc]
  -- From hp_ann: the sum of coeff(i) • M^i v = 0
  have hsum : ∑ i : Fin n, p.coeff (i : ℕ) • (M ^ (i : ℕ)).mulVec v = 0 := by
    rw [← hp_expand]; exact hp_ann
  -- Linear independence gives all coefficients zero
  have hcoeff : ∀ i : Fin n, p.coeff (i : ℕ) = 0 := hli _ hsum
  -- Polynomial with all coefficients zero (below and at degree) is zero
  ext m
  by_cases hm : m < n
  · exact hcoeff ⟨m, hm⟩
  · exact Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)

end Nonderogatory.Backward.Aristotle
