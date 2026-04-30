/-
  Aristotle targets for Erdős Problem #338 (Restricted Order of Additive Bases)
  Routine supporting lemmas and known mathematical results for automated proof search.
  See Erdos338Problem.lean for the main formalization.

  Key targets:
  1. mul_self_mem_squares: k*k ∈ squares (trivial by definition)
  2. sq_mem_squares: k^2 ∈ squares (ring from definition)
  3. squares_order_four_aristotle: Lagrange four-squares → IsBasisOfOrder squares 4
     Proof route: Nat.sum_four_squares n gives a b c d with a^2+b^2+c^2+d^2=n.
     Take N=0; witness s = {a^2, b^2, c^2, d^2} (Multiset), membership via sq_mem_squares,
     card = 4 ≤ 4, Multiset.sum = a^2+b^2+c^2+d^2 = n.
-/
import Mathlib
import Proofs.Erdos338Problem

namespace Erdos338

/-- k*k belongs to the squares set, directly by definition. -/
theorem mul_self_mem_squares (k : ℕ) : k * k ∈ squares := ⟨k, rfl⟩

/-- k^2 belongs to the squares set (since k^2 = k*k). -/
theorem sq_mem_squares (k : ℕ) : k ^ 2 ∈ squares := ⟨k, by ring⟩

/-- Lagrange's four-squares theorem recast as IsBasisOfOrder.
    Every natural number n is a sum of four perfect squares (Nat.sum_four_squares).
    Proof: take N = 0; for any n ≥ 0, Nat.sum_four_squares n gives a b c d with
    a^2 + b^2 + c^2 + d^2 = n. Use multiset {a^2, b^2, c^2, d^2}:
    each element is in squares, card = 4 ≤ 4, Multiset.sum = n. -/
theorem squares_order_four_aristotle : IsBasisOfOrder squares 4 := by
  refine ⟨0, fun n _ => ?_⟩
  obtain ⟨a, b, c, d, h⟩ := Nat.sum_four_squares n
  refine ⟨↑([a ^ 2, b ^ 2, c ^ 2, d ^ 2] : List ℕ), ?_, ?_, ?_⟩
  · intro x hx
    simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    all_goals exact ⟨_, by ring⟩
  · simp [Multiset.card_coe]
  · simp only [Multiset.coe_sum, List.sum_cons, List.sum_nil, add_zero]
    linarith

end Erdos338
