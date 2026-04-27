/-
  Aristotle targets for Erdős Problem #339 (Additive Bases and Distinct Element Sums)
  Routine supporting lemma for automated proof search.
  See Erdos339Problem.lean for the main formalization.

  Key target:
  1. squares_basis_of_order_4_aristotle: Lagrange's four-squares theorem recast as
     IsBasisOfOrder {n | ∃ m, n = m^2} 4.
     Proof route: Nat.sum_four_squares n gives a b c d with a^2+b^2+c^2+d^2=n.
     Take N=0; witness f = ![a^2, b^2, c^2, d^2] : Fin 4 → ℕ,
     membership via ⟨a, rfl⟩ etc., sum via Fin.sum_univ_four.

  Note: hegyvari_hennecart_plagne_1 and _2 are deep theorems from combinatorics
  (HHP 2003); Aristotle cannot prove them.
-/
import Mathlib
import Proofs.Erdos339Problem

namespace Erdos339

/-- Lagrange's four-squares theorem gives IsBasisOfOrder for squares.
    Proof: Nat.sum_four_squares gives a b c d with a^2+b^2+c^2+d^2=n;
    use f = ![a^2, b^2, c^2, d^2], N = 0. -/
theorem squares_basis_of_order_4_aristotle :
    IsBasisOfOrder { n | ∃ m, n = m^2 } 4 := by
  use 0
  intro n _
  obtain ⟨a, b, c, d, h⟩ := Nat.sum_four_squares n
  refine ⟨![a^2, b^2, c^2, d^2], ?_, ?_⟩
  · intro i
    fin_cases i <;> simp [Set.mem_setOf_eq] <;> exact ⟨_, rfl⟩
  · simp [Fin.sum_univ_four, ← h]

end Erdos339
