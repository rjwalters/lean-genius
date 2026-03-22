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
    LinearIndependent K p := by sorry

/-
  Lemma 2: Square matrix with linearly independent columns is invertible

  If the columns of an n×n matrix over a field are linearly independent,
  the matrix is a unit (invertible). This is standard linear algebra.
-/
theorem isUnit_of_linearIndependent_cols
    (P : Matrix n n K)
    (hli : LinearIndependent K (fun j : n => fun i : n => P i j)) :
    IsUnit P := by sorry

/-
  Lemma 3: Matrix decomposition into standard basis

  Every matrix A can be written as A = ∑ᵢ ∑ⱼ A(i,j) • E_ij.
  This is the standard basis decomposition for matrices.
-/
theorem matrix_eq_sum_stdBasisMatrix (A : Matrix n n K) :
    A = ∑ i : n, ∑ j : n, A i j • Matrix.stdBasisMatrix i j 1 := by sorry

/-
  Lemma 4: mulVec distributes over Finset.sum with smul

  M.mulVec (∑ j, c j • v j) = ∑ j, c j • M.mulVec (v j)
-/
theorem mulVec_finset_sum_smul (M : Matrix n n K) (c : n → K)
    (v : n → (n → K)) :
    M.mulVec (∑ j : n, c j • v j) = ∑ j : n, c j • M.mulVec (v j) := by sorry

end SkolemNoetherAristotle
