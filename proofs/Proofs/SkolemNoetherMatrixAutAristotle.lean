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
  rw [Fintype.linearIndependent_iff]
  intro c hc k
  -- Step 1: p j a = 0 when j ≠ a (E_{aa} · p_j = δ_{aj} · p_a)
  have hp_offdiag : ∀ j a, j ≠ a → p j a = 0 := by
    intro j a hja
    have h := congr_fun (hfp a a j) a
    simp only [eq_self_iff_true, true_and, ite_mul, one_mul, zero_mul,
               Finset.sum_ite_eq, Finset.mem_univ, ite_true,
               if_neg (Ne.symm hja), Pi.zero_apply] at h
    exact h
  -- Step 2: p k k ≠ 0 (since p k ≠ 0 and off-diagonal entries vanish)
  have hpkk : p k k ≠ 0 := by
    intro hpkk_eq
    apply hp_ne k; funext a
    by_cases hka : k = a
    · subst hka; simpa using hpkk_eq
    · exact hp_offdiag k a hka
  -- Step 3: Evaluate ∑ c_j · p_j = 0 at index k; only the k-th term survives
  have hk := congr_fun hc k
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hk
  rw [Finset.sum_eq_single k] at hk
  · exact (mul_eq_zero.mp hk).resolve_right hpkk
  · intro j _ hjk; rw [hp_offdiag j k hjk, mul_zero]
  · intro habs; exact absurd (Finset.mem_univ _) habs

/-
  Lemma 2: Square matrix with linearly independent columns is invertible

  If the columns of an n×n matrix over a field are linearly independent,
  the matrix is a unit (invertible). This is standard linear algebra.
-/
theorem isUnit_of_linearIndependent_cols
    (P : Matrix n n K)
    (hli : LinearIndependent K (fun j : n => fun i : n => P i j)) :
    IsUnit P := by
  -- mulVec w = ∑ j, w j • (column j), so injectivity follows from lin. independence
  have hinj : Function.Injective (Matrix.mulVecLin P) := by
    intro u v huv
    have h0 : P.mulVec (u - v) = 0 := by
      show (Matrix.mulVecLin P) (u - v) = 0
      rw [map_sub, sub_eq_zero]; exact huv
    -- P.mulVec (u - v) = ∑ j, (u - v) j • (column j of P)
    have hmulvec : P.mulVec (u - v) = ∑ j : n, (u - v) j • (fun i => P i j) := by
      ext i; simp [Matrix.mulVec, Matrix.dotProduct, Finset.sum_apply, smul_eq_mul]
    rw [hmulvec] at h0
    have hcoeff := (Fintype.linearIndependent_iff.mp hli) (u - v) h0
    ext j; exact sub_eq_zero.mpr (by simpa using (hcoeff j).symm)
  -- Injective endomorphism of finite-dim space → bijective → IsUnit
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
