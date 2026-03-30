/-
  Aristotle targets for Skolem-Noether Matrix Automorphism proof
  (cayley-hamilton-minpoly-oq-02-oq-01-oq-01)

  Routine supporting lemmas for automated proof search.
  See SkolemNoetherMatrixAut.lean for the main formalization.

  Criteria for inclusion:
  - NOT the main open conjecture
  - Known results likely provable from Mathlib
  - Clean theorem statements with no definition sorries
  - No axioms (use theorem ... := by sorry instead)

  Remaining sorries in the main file:
  1. p_linearIndependent: linearly independent vectors from intertwining
  2. IsUnit Pmat: invertibility from linear independence
  3. hintertwine: phi(A)*P = P*A by linearity from generators
-/
import Mathlib

set_option linter.deprecated false

namespace SkolemNoetherAristotle

variable {K : Type*} [Field K]
variable {n : Type*} [DecidableEq n] [Fintype n]

/-
  Lemma 1: Linear independence from intertwining property

  Given vectors p_j = φ(E_{j,i₀}).mulVec(v₀) satisfying:
    φ(E_{ij}).mulVec(p_k) = δ_{jk} · p_i

  The p_j are linearly independent. Proof:
  Suppose ∑ c_j p_j = 0. Apply φ(E_{kk}).mulVec:
    ∑ c_j · φ(E_{kk}).mulVec(p_j) = 0
    ∑ c_j · δ_{kj} · p_k = 0
    c_k · p_k = 0
  Since p_k ≠ 0 (from hv₀), c_k = 0.
-/
theorem linearIndependent_of_intertwine
    (p : n → (n → K))
    (hp_ne : ∀ j, p j ≠ 0)
    (hfp : ∀ i j k, (fun a => ∑ m, (if i = a ∧ j = m then (1 : K) else 0) *
      p k m) = if j = k then p i else 0) :
    LinearIndependent K p := by
  -- From hfp at (k,k,j) evaluated at k: p j k = if k = j then p k k else 0
  have hpjk : ∀ k j, p j k = if k = j then p k k else 0 := by
    intro k j
    have h := congr_fun (hfp k k j) k
    simp only [eq_self_iff_true, true_and, ite_mul, one_mul, zero_mul] at h
    rw [show ∀ f : n → K, (if k = j then f else 0) k =
        if k = j then f k else 0 from fun f => by split_ifs <;> rfl] at h
    rwa [show (∑ m : n, if k = m then p j m else 0) = p j k from by
      rw [Finset.sum_ite_eq' Finset.univ k]; simp] at h
  -- p k k ≠ 0 (otherwise p k = 0 since p k a = if a = k then p k k else 0)
  have hpkk : ∀ k, p k k ≠ 0 := by
    intro k h0; apply hp_ne k; ext a
    rw [show p k a = if a = k then p k k else 0 from by rw [hpjk a k]; split_ifs <;> simp [*]]
    simp [h0]
  -- Linear independence via Fintype.linearIndependent_iff
  rw [Fintype.linearIndependent_iff]
  intro c hsum k
  -- Evaluate ∑ c j • p j at point k
  have heval : ∑ j : n, c j * p j k = 0 := by
    have := congr_fun hsum k; simpa [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using this
  -- Substitute hpjk: c k * p k k = 0
  simp_rw [hpjk k] at heval
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true] at heval
  exact (mul_eq_zero.mp heval).resolve_right (hpkk k)

/-
  Lemma 2: Square matrix with linearly independent columns is invertible

  If the columns of an n×n matrix over a field are linearly independent,
  the matrix is a unit (invertible). This is standard linear algebra.
-/
theorem isUnit_of_linearIndependent_cols
    (P : Matrix n n K)
    (hli : LinearIndependent K (fun j : n => fun i : n => P i j)) :
    IsUnit P := by
  -- P.mulVec w = ∑ j, w j • (column j of P)
  have hmulvec : ∀ w : n → K, P.mulVec w = ∑ j : n, w j • (fun i => P i j) := by
    intro w; ext i
    simp [Matrix.mulVec, Matrix.dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
          mul_comm]
  -- mulVecLin is injective from linear independence of columns
  have hinj : Function.Injective (Matrix.mulVecLin P) := by
    intro u v huv
    have h0 : P.mulVec (u - v) = 0 := by
      show (Matrix.mulVecLin P) (u - v) = 0
      rw [map_sub, sub_eq_zero]; exact huv
    rw [hmulvec] at h0
    have hcoeff := (Fintype.linearIndependent_iff.mp hli) (u - v) h0
    ext j; exact sub_eq_zero.mpr (by simpa using (hcoeff j).symm)
  -- Injective endomorphism of fin-dim space → surjective → IsUnit
  have hbij : Function.Bijective (Matrix.mulVecLin P) :=
    ⟨hinj, LinearMap.injective_iff_surjective.mp hinj⟩
  rw [Matrix.isUnit_iff_isUnit_det]
  rwa [Matrix.isUnit_det_iff_isUnit_mulVecLin, LinearMap.isUnit_iff_bijective]

/-
  Lemma 3: Matrix decomposition into standard basis

  Every matrix A can be written as A = ∑ᵢ ∑ⱼ A(i,j) • E_ij.
  This is the standard basis decomposition for matrices.
-/
theorem matrix_eq_sum_stdBasisMatrix (A : Matrix n n K) :
    A = ∑ i : n, ∑ j : n, A i j • Matrix.stdBasisMatrix i j 1 := by
  ext a b
  simp [Matrix.stdBasisMatrix, Finset.sum_apply, smul_apply, smul_eq_mul]
  rw [Finset.sum_eq_single a (fun i _ hi => by simp [hi]) (by simp)]
  rw [Finset.sum_eq_single b (fun j _ hj => by simp [hj]) (by simp)]
  simp

/-
  Lemma 4: mulVec distributes over Finset.sum with smul

  M.mulVec (∑ j, c j • v j) = ∑ j, c j • M.mulVec (v j)
-/
theorem mulVec_finset_sum_smul (M : Matrix n n K) (c : n → K)
    (v : n → (n → K)) :
    M.mulVec (∑ j : n, c j • v j) = ∑ j : n, c j • M.mulVec (v j) := by
  simp [Matrix.mulVec_sum, Matrix.mulVec_smul]

end SkolemNoetherAristotle
