import Mathlib

/-!
# The bottom-root equation of a strongly regular graph

This isolates the spectral scalar equation needed by the proper-owner
strongly-regular obstruction.  A nonzero adjacency eigenvector with negative
eigenvalue is orthogonal to the constant vector by regularity.  Evaluating
the strongly-regular matrix identity on it then gives the root equation.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- A negative adjacency eigenvector of a regular graph has coordinate sum
zero. -/
theorem sum_eq_zero_of_regular_negative_eigenvector
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    {k m : ℕ} (hreg : H.IsRegularOfDegree k) (hm : 1 ≤ m)
    (v : V → ℝ)
    (heig : (H.adjMatrix ℝ).mulVec v = fun x => -(m : ℝ) * v x) :
    ∑ x, v x = 0 := by
  let one : V → ℝ := fun _ => 1
  have hAone : (H.adjMatrix ℝ).mulVec one = fun _ => (k : ℝ) := by
    funext x
    simpa [one] using
      (H.adjMatrix_mulVec_const_apply_of_regular (α := ℝ) hreg
        (a := (1 : ℝ)) (v := x))
  have hsymm : (H.adjMatrix ℝ).transpose = H.adjMatrix ℝ := by
    exact H.isSymm_adjMatrix.eq
  have hdot : dotProduct one ((H.adjMatrix ℝ).mulVec v) =
      dotProduct ((H.adjMatrix ℝ).mulVec one) v := by
    rw [Matrix.dotProduct_mulVec, ← Matrix.vecMul_transpose, hsymm]
  rw [heig, hAone] at hdot
  simp only [dotProduct, one, one_mul] at hdot
  have hdot' : -(m : ℝ) * (∑ x, v x) = (k : ℝ) * (∑ x, v x) := by
    simpa only [← Finset.mul_sum] using hdot
  have : ((k + m : ℕ) : ℝ) * (∑ x, v x) = 0 := by
    push_cast
    nlinarith [hdot']
  exact (mul_eq_zero.mp this).resolve_left (by positivity)

/-- If `-m` occurs as a nonzero adjacency eigenvalue of a strongly regular
graph, then it is a root of the nonprincipal SRG quadratic. -/
theorem srg_bottom_root_equation
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    {n k lambda mu m : ℕ}
    (hSRG : H.IsSRGWith n k lambda mu) (hm : 1 ≤ m)
    (v : V → ℝ) (hv : v ≠ 0)
    (heig : (H.adjMatrix ℝ).mulVec v = fun x => -(m : ℝ) * v x) :
    (m : ℝ) ^ 2 = (k : ℝ) - (lambda : ℝ) * m +
      (mu : ℝ) * (m - 1) := by
  have hsum := sum_eq_zero_of_regular_negative_eigenvector
    H hSRG.regular hm v heig
  have hcomp : (Hᶜ.adjMatrix ℝ).mulVec v = fun x => ((m : ℝ) - 1) * v x := by
    have hall := H.one_add_adjMatrix_add_compl_adjMatrix_eq_of_one (α := ℝ)
    rw [H.compl_adjMatrix_eq_adjMatrix_compl (α := ℝ)] at hall
    have happ := congrArg (fun M : Matrix V V ℝ => M.mulVec v) hall
    simp only [Matrix.add_mulVec, Matrix.one_mulVec] at happ
    rw [heig] at happ
    funext x
    have hx := congrFun happ x
    simp only [Pi.add_apply] at hx
    have hright : (Matrix.of (1 : V → V → ℝ)).mulVec v x = 0 := by
      simp [Matrix.mulVec, dotProduct, hsum]
    rw [hright] at hx
    nlinarith
  have hmatrix := hSRG.matrix_eq (α := ℝ)
  have happ := congrArg (fun M : Matrix V V ℝ => M.mulVec v) hmatrix
  have heig' : (H.adjMatrix ℝ).mulVec v = (-(m : ℝ)) • v := by
    funext x
    simpa [Pi.smul_apply] using congrFun heig x
  rw [pow_two, ← Matrix.mulVec_mulVec, heig', Matrix.mulVec_smul, heig'] at happ
  simp only [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec] at happ
  rw [heig', hcomp] at happ
  obtain ⟨x, hx⟩ : ∃ x, v x ≠ 0 := by
    simpa [Function.ne_iff] using hv
  have hcoord := congrFun happ x
  simp only [Pi.add_apply, Pi.mul_apply, Pi.smul_apply, Pi.natCast_apply,
    smul_eq_mul, nsmul_eq_mul] at hcoord
  have hfactor :
      ((m : ℝ) ^ 2 - ((k : ℝ) - (lambda : ℝ) * m +
        (mu : ℝ) * (m - 1))) * v x = 0 := by
    nlinarith [hcoord]
  rcases mul_eq_zero.mp hfactor with h | h
  · nlinarith
  · exact (hx h).elim

#print axioms sum_eq_zero_of_regular_negative_eigenvector

#print axioms srg_bottom_root_equation

end

end Erdos85
