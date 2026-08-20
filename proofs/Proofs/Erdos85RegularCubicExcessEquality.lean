import Proofs.Erdos85RegularCubicExcessLowerBound

/-! # Equality in the arbitrary-center cubic row bound

Node: F.3 GENERALIZATION.  Sharpness of the row moment bound is equivalent
to two-level support on the nonneighbor cubic entries.
-/

open Finset SimpleGraph Matrix

namespace Erdos85

noncomputable section

/-- A sum of consecutive-integer excess terms vanishes exactly when every
entry lies at one of the two centers. -/
theorem sum_consecutive_integer_excess_eq_zero_iff
    {X : Type*} (s : Finset X) (f : X → ℤ) (c : ℤ) :
    (∑ x ∈ s, (f x - c) * (f x - (c + 1))) = 0 ↔
      ∀ x ∈ s, f x = c ∨ f x = c + 1 := by
  classical
  constructor
  · intro hsum x hx
    have hterm := (Finset.sum_eq_zero_iff_of_nonneg
      (fun y _ => consecutive_integer_excess_nonneg (f y) c)).mp hsum x hx
    rcases mul_eq_zero.mp hterm with hleft | hright
    · exact Or.inl (sub_eq_zero.mp hleft)
    · exact Or.inr (sub_eq_zero.mp hright)
  · intro hlevels
    apply Finset.sum_eq_zero
    intro x hx
    rcases hlevels x hx with hxc | hxc
    · simp [hxc]
    · simp [hxc]

/-- The arbitrary-center cubic row lower bound is sharp iff every
nonneighbor cubic entry equals `c` or `c+1`. -/
theorem regular_c4Free_cube_row_square_baseline_eq_iff
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) (d : ℕ)
    (hreg : ∀ x, G.degree x = d) (c : ℤ) (a : V) :
    let A3 := G.adjMatrix ℤ * G.adjMatrix ℤ * G.adjMatrix ℤ
    let Q := cubicNonneighborFinset G a
    ((d : ℤ) * (2 * (d : ℤ) - 1) ^ 2 + (A3 a a) ^ 2 +
        (2 * c + 1) *
          ((d : ℤ) ^ 3 - (d : ℤ) * (2 * (d : ℤ) - 1) - A3 a a) -
        c * (c + 1) * (Q.card : ℤ) =
      ∑ b, (A3 a b) ^ 2) ↔
      ∀ b ∈ Q, A3 a b = c ∨ A3 a b = c + 1 := by
  classical
  dsimp only
  let A3 := G.adjMatrix ℤ * G.adjMatrix ℤ * G.adjMatrix ℤ
  let Q := cubicNonneighborFinset G a
  have hledger := regular_c4Free_cube_row_square_eq_baseline_add_excess
    G hfree d hreg c a
  change (∑ b, (A3 a b) ^ 2) =
    (d : ℤ) * (2 * (d : ℤ) - 1) ^ 2 + (A3 a a) ^ 2 +
      (2 * c + 1) *
        ((d : ℤ) ^ 3 - (d : ℤ) * (2 * (d : ℤ) - 1) - A3 a a) -
      c * (c + 1) * (Q.card : ℤ) +
      ∑ b ∈ Q, (A3 a b - c) * (A3 a b - (c + 1)) at hledger
  have hzero := sum_consecutive_integer_excess_eq_zero_iff
    Q (fun b => A3 a b) c
  constructor
  · intro heq
    have heq' :
        (d : ℤ) * (2 * (d : ℤ) - 1) ^ 2 + (A3 a a) ^ 2 +
            (2 * c + 1) *
              ((d : ℤ) ^ 3 - (d : ℤ) * (2 * (d : ℤ) - 1) - A3 a a) -
            c * (c + 1) * (Q.card : ℤ) =
          ∑ b, (A3 a b) ^ 2 := by
      simpa only [A3, Q] using heq
    have hexcess : (∑ b ∈ Q,
        (A3 a b - c) * (A3 a b - (c + 1))) = 0 := by
      omega
    have hlevels := hzero.mp hexcess
    simpa only [A3, Q] using hlevels
  · intro hlevels
    have hlevels' : ∀ b ∈ Q,
        A3 a b = c ∨ A3 a b = c + 1 := by
      simpa only [A3, Q] using hlevels
    have hexcess := hzero.mpr hlevels'
    have heq' :
        (d : ℤ) * (2 * (d : ℤ) - 1) ^ 2 + (A3 a a) ^ 2 +
            (2 * c + 1) *
              ((d : ℤ) ^ 3 - (d : ℤ) * (2 * (d : ℤ) - 1) - A3 a a) -
            c * (c + 1) * (Q.card : ℤ) =
          ∑ b, (A3 a b) ^ 2 := by
      omega
    simpa only [A3, Q] using heq'

end


end Erdos85

#print axioms Erdos85.sum_consecutive_integer_excess_eq_zero_iff
#print axioms Erdos85.regular_c4Free_cube_row_square_baseline_eq_iff
