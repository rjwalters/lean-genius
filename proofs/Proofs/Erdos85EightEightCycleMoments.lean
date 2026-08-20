import Proofs.Erdos85MuThreeAllTfEightEightCoordinates
import Proofs.Erdos85CenteredShoreMoments

/-! # Trace moments of a labeled disjoint union of two eight-cycles -/

open Finset SimpleGraph Matrix

namespace Erdos85

noncomputable section

/-- Matrix powers, hence their traces, are unchanged by a simultaneous
equivalence of row and column labels. -/
theorem trace_pow_eq_of_equiv_entries
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    {R : Type*} [CommRing R]
    (e : X ≃ Y) (A : Matrix X X R) (B : Matrix Y Y R)
    (h : ∀ i j, A i j = B (e i) (e j)) (n : ℕ) :
    Matrix.trace (A ^ n) = Matrix.trace (B ^ n) := by
  classical
  have hp : ∀ k i j, (A ^ k) i j = (B ^ k) (e i) (e j) := by
    intro k
    induction k with
    | zero =>
        intro i j
        simp [Matrix.one_apply, e.injective.eq_iff]
    | succ k ih =>
        intro i j
        rw [pow_succ, pow_succ, Matrix.mul_apply, Matrix.mul_apply]
        simp_rw [ih, h]
        exact Fintype.sum_equiv e
          (fun x ↦ (B ^ k) (e i) (e x) * B (e x) (e j))
          (fun y ↦ (B ^ k) (e i) y * B y (e j)) (fun _ ↦ rfl)
  simp only [Matrix.trace, Matrix.diag, hp]
  exact Fintype.sum_equiv e
    (fun x ↦ (B ^ n) (e x) (e x))
    (fun y ↦ (B ^ n) y y) (fun _ ↦ rfl)

theorem eightEightCycleGraph_integer_moments :
    Matrix.trace ((eightEightCycleGraph.adjMatrix ℤ) ^ 3) = 0 ∧
      Matrix.trace ((eightEightCycleGraph.adjMatrix ℤ) ^ 4) = 96 := by
  native_decide

/-- Any graph labeled as `C8 ⊔ C8` has the third and fourth adjacency
moments used by the centered-shore quotient calculation. -/
theorem eightEightCycleLabeling_trace_moments
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (label : EightEightCycleLabeling H) :
    Matrix.trace ((H.adjMatrix ℂ) ^ 3) = 0 ∧
      Matrix.trace ((H.adjMatrix ℂ) ^ 4) = 96 := by
  classical
  have hentries : ∀ i j,
      H.adjMatrix ℂ i j =
        eightEightCycleGraph.adjMatrix ℂ (label.toEquiv i) (label.toEquiv j) := by
    intro i j
    simp [SimpleGraph.adjMatrix_apply, label.map_adj_iff]
  have h3transfer := trace_pow_eq_of_equiv_entries label.toEquiv
    (H.adjMatrix ℂ) (eightEightCycleGraph.adjMatrix ℂ) hentries 3
  have h4transfer := trace_pow_eq_of_equiv_entries label.toEquiv
    (H.adjMatrix ℂ) (eightEightCycleGraph.adjMatrix ℂ) hentries 4
  have h3cast := trace_complex_adjMatrix_pow_eq_intCast eightEightCycleGraph 3
  have h4cast := trace_complex_adjMatrix_pow_eq_intCast eightEightCycleGraph 4
  rw [eightEightCycleGraph_integer_moments.1] at h3cast
  rw [eightEightCycleGraph_integer_moments.2] at h4cast
  norm_num at h3cast h4cast
  exact ⟨h3transfer.trans h3cast, h4transfer.trans h4cast⟩

end

end Erdos85

#print axioms Erdos85.trace_pow_eq_of_equiv_entries
#print axioms Erdos85.eightEightCycleGraph_integer_moments
#print axioms Erdos85.eightEightCycleLabeling_trace_moments
