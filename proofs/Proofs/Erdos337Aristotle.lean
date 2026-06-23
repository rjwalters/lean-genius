/-
  Aristotle targets for Erdős Problem #337 (Additive Bases and Sumset Growth)
  Routine supporting lemmas for automated proof search.
  See Erdos337Problem.lean for the main formalization.

  Key target:
  squares_basis_of_order_4_erdos337: The perfect squares are an additive basis
  of order 4 in the sense of Erdos337.isAdditiveBasis.

  Proof route: Nat.sum_four_squares n gives a b c d with a^2+b^2+c^2+d^2=n.
  The squares set squares337 = {m | ∃ k, m = k^2} satisfies:
  - n ∈ hFoldSumset 4 squares337 for every n (use N₀ = 0)
  - Build bottom-up: d^2 ∈ squares337, c^2 + d^2 ∈ hFoldSumset 2,
    b^2 + c^2 + d^2 ∈ hFoldSumset 3, a^2 + b^2 + c^2 + d^2 = n ∈ hFoldSumset 4

  Note: turjanyi_counterexample, ruzsa_turjanyi_generalization, and
  scaled_conjecture_open are deep results; Aristotle cannot prove them.
-/
import Mathlib
import Proofs.Erdos337Problem

namespace Erdos337

/-- The set of perfect squares (including 0 = 0^2). -/
def squares337 : Set ℕ := {m | ∃ k : ℕ, m = k ^ 2}

/-- k^2 belongs to squares337, directly from definition. -/
theorem sq_mem_squares337 (k : ℕ) : k ^ 2 ∈ squares337 := ⟨k, rfl⟩

/-- Lagrange's four-squares theorem: squares337 is an additive basis of order 4
    in the sense of isAdditiveBasis.
    Proof:
    1. 4 ≥ 1 by norm_num.
    2. Use N₀ = 0 (every n works, not just large n).
    3. For any n, Nat.sum_four_squares gives a b c d with a^2+b^2+c^2+d^2 = n.
    4. Unfold hFoldSumset 4: need ∃ x ∈ squares337, ∃ t ∈ hFoldSumset 3, n = x + t.
       Take x = a^2 (∈ squares337), t = b^2 + (c^2 + d^2).
    5. t ∈ hFoldSumset 3: need ∃ y ∈ squares337, ∃ u ∈ hFoldSumset 2, t = y + u.
       Take y = b^2 (∈ squares337), u = c^2 + d^2.
    6. u ∈ hFoldSumset 2: need ∃ z ∈ squares337, ∃ v ∈ hFoldSumset 1 = squares337, u = z + v.
       Take z = c^2, v = d^2 (both ∈ squares337), u = c^2 + d^2 = z + v by rfl.
    7. n = a^2 + (b^2 + (c^2 + d^2)) follows from h by ring/omega. -/
theorem squares_basis_of_order_4_erdos337 : isAdditiveBasis 4 squares337 := by
  sorry

end Erdos337
