import Proofs.Erdos85RegularCubicExcessEquality

/-! # Equality in the arbitrary-center global cubic bound

Node: F.3 GENERALIZATION.  Global sharpness is localized exactly to
two-level support in every nonneighbor cubic row.
-/

open Finset SimpleGraph Matrix

namespace Erdos85

noncomputable section

/-- The general global sixth-moment lower bound is sharp iff every
nonneighbor cubic entry in every row belongs to `{c,c+1}`. -/
theorem regular_c4Free_global_baseline_eq_trace_pow_six_iff
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) (d : ℕ)
    (hreg : ∀ x, G.degree x = d) (c : ℤ) :
    let A3 := G.adjMatrix ℤ * G.adjMatrix ℤ * G.adjMatrix ℤ
    ((∑ a,
      ((d : ℤ) * (2 * (d : ℤ) - 1) ^ 2 + (A3 a a) ^ 2 +
        (2 * c + 1) *
          ((d : ℤ) ^ 3 - (d : ℤ) * (2 * (d : ℤ) - 1) - A3 a a) -
        c * (c + 1) * ((cubicNonneighborFinset G a).card : ℤ))) =
      Matrix.trace ((G.adjMatrix ℤ) ^ 6)) ↔
      ∀ a, ∀ b ∈ cubicNonneighborFinset G a,
        A3 a b = c ∨ A3 a b = c + 1 := by
  classical
  dsimp only
  let A3 := G.adjMatrix ℤ * G.adjMatrix ℤ * G.adjMatrix ℤ
  let Base : V → ℤ := fun a =>
    (d : ℤ) * (2 * (d : ℤ) - 1) ^ 2 + (A3 a a) ^ 2 +
      (2 * c + 1) *
        ((d : ℤ) ^ 3 - (d : ℤ) * (2 * (d : ℤ) - 1) - A3 a a) -
      c * (c + 1) * ((cubicNonneighborFinset G a).card : ℤ)
  have hle (a : V) : Base a ≤ ∑ b, (A3 a b) ^ 2 := by
    simpa only [Base, A3] using
      regular_c4Free_cube_row_square_baseline_le
        G hfree d hreg c a
  have hsharp (a : V) :
      (Base a = ∑ b, (A3 a b) ^ 2) ↔
        ∀ b ∈ cubicNonneighborFinset G a,
          A3 a b = c ∨ A3 a b = c + 1 := by
    simpa only [Base, A3] using
      regular_c4Free_cube_row_square_baseline_eq_iff
        G hfree d hreg c a
  let A := G.adjMatrix ℤ
  have hA : A.IsSymm := by
    simpa [A] using (SimpleGraph.isSymm_adjMatrix G ℤ)
  have htrace : (∑ a, ∑ b, (A3 a b) ^ 2) =
      Matrix.trace ((G.adjMatrix ℤ) ^ 6) := by
    have hcube : A ^ 3 = A * A * A := by
      simp [pow_succ, Matrix.mul_assoc]
    symm
    rw [trace_pow_six_eq_sum_cube_apply_sq A hA, hcube]
  constructor
  · intro heq
    have heq' : (∑ a, Base a) =
        Matrix.trace ((G.adjMatrix ℤ) ^ 6) := by
      simpa only [Base, A3] using heq
    have hsums : (∑ a, Base a) = ∑ a, ∑ b, (A3 a b) ^ 2 :=
      heq'.trans htrace.symm
    have hpoint := (Finset.sum_eq_sum_iff_of_le
      (fun a _ => hle a)).mp hsums
    intro a
    exact (hsharp a).mp (hpoint a (Finset.mem_univ a))
  · intro hlevels
    have hpoint : ∀ a : V, Base a = ∑ b, (A3 a b) ^ 2 := by
      intro a
      apply (hsharp a).mpr
      exact hlevels a
    have hsums : (∑ a, Base a) = ∑ a, ∑ b, (A3 a b) ^ 2 := by
      apply Finset.sum_congr rfl
      intro a _
      exact hpoint a
    have heq' : (∑ a, Base a) =
        Matrix.trace ((G.adjMatrix ℤ) ^ 6) := hsums.trans htrace
    simpa only [Base, A3] using heq'

end


end Erdos85

#print axioms Erdos85.regular_c4Free_global_baseline_eq_trace_pow_six_iff
