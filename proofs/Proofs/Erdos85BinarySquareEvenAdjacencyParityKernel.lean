import Proofs.Erdos85AlternatingParity
import Proofs.Erdos85EvenExcessOneDefectKernel

/-!
# The uniform even-square adjacency parity kernel

At every even regular square-order core, the mod-two adjacency matrix is
alternating on an even-dimensional space and kills the all-ones vector.  Its
kernel therefore contains a nonconstant vector.  The binary square identity
transports the same vector to the kernel of `I + J + D`.

The final orthogonality clause is the form needed by a binary cut atom: every
adjacency-image support is perpendicular to this mandatory extra kernel
direction.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- A kernel vector of a symmetric matrix is orthogonal to its entire image. -/
theorem dotProduct_mulVec_eq_zero_of_symm_of_mem_kernel_zmodTwo
    {V : Type*} [Fintype V] [DecidableEq V]
    (A : Matrix V V (ZMod 2))
    (hsymm : ∀ x y, A x y = A y x)
    {w : V → ZMod 2} (hw : A.mulVec w = 0) (u : V → ZMod 2) :
    w ⬝ᵥ A.mulVec u = 0 := by
  calc
    w ⬝ᵥ A.mulVec u = Matrix.vecMul w A ⬝ᵥ u :=
      Matrix.dotProduct_mulVec w A u
    _ = A.mulVec w ⬝ᵥ u := by
      congr 1
      funext x
      simp only [Matrix.vecMul, Matrix.mulVec, dotProduct]
      apply Finset.sum_congr rfl
      intro y _hy
      rw [hsymm y x, mul_comm]
    _ = 0 := by rw [hw]; simp

/-- Every even-degree regular C4-free graph of square order has a mod-two
adjacency-kernel vector distinct from both constants.  The same vector lies in
the kernel of the defect square `I + J + D` and is orthogonal to every
adjacency-image vector. -/
theorem binarySquare_even_exists_nontrivial_adjacency_defect_kernel_vector
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 1 ≤ q)
    (heven : Even q) (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q) :
    ∃ w : V → ZMod 2,
      w ≠ 0 ∧ w ≠ (fun _ => 1) ∧
      (G.adjMatrix (ZMod 2)).mulVec w = 0 ∧
      ((1 : Matrix V V (ZMod 2)) +
          Matrix.of (fun _ _ => (1 : ZMod 2)) +
          (secondOrderDefectGraph G).adjMatrix (ZMod 2)).mulVec w = 0 ∧
      ∀ u : V → ZMod 2,
        w ⬝ᵥ (G.adjMatrix (ZMod 2)).mulVec u = 0 := by
  haveI : Nonempty V := by
    rw [← Fintype.card_pos_iff, hcard]
    positivity
  have hcardEven : Even (Fintype.card V) := by
    obtain ⟨k, hk⟩ := heven
    refine ⟨k * q, ?_⟩
    rw [hcard, hk]
    ring
  have hsymm : ∀ x y : V,
      G.adjMatrix (ZMod 2) x y = G.adjMatrix (ZMod 2) y x := by
    intro x y
    simp only [SimpleGraph.adjMatrix_apply]
    by_cases hxy : G.Adj x y
    · rw [if_pos hxy, if_pos hxy.symm]
    · rw [if_neg hxy, if_neg (fun hyx => hxy hyx.symm)]
  have hdiag : ∀ x : V, G.adjMatrix (ZMod 2) x x = 0 := by
    intro x
    rw [SimpleGraph.adjMatrix_apply, if_neg (G.loopless.irrefl x)]
  have hones := adjMatrix_zmodTwo_mulVec_ones_eq_zero G heven hreg
  obtain ⟨w, hw, hw0, hw1⟩ := exists_kernel_vector_ne_zero_ne_ones
    hcardEven (G.adjMatrix (ZMod 2)) hsymm hdiag hones
  refine ⟨w, hw0, hw1, hw, ?_, ?_⟩
  · rw [← adjMatrix_sq_eq_defect_mod_two_of_even_regular
      G hfree heven hreg, ← Matrix.mulVec_mulVec, hw, Matrix.mulVec_zero]
  · exact dotProduct_mulVec_eq_zero_of_symm_of_mem_kernel_zmodTwo
      (G.adjMatrix (ZMod 2)) hsymm hw

end

end Erdos85

#print axioms Erdos85.dotProduct_mulVec_eq_zero_of_symm_of_mem_kernel_zmodTwo
#print axioms
  Erdos85.binarySquare_even_exists_nontrivial_adjacency_defect_kernel_vector
