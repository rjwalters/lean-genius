/-
  Aristotle targets for Erdős Problem #589 (Points in General Position)
  Routine supporting lemmas for automated proof search.
  See Erdos589Problem.lean for the main formalization.

  Target:
  - erdos_belief_false: ¬ErdosBelief — follows from furedi_upper_bound.
    Strategy: assume ∃ c > 0, ∀ n ≥ 1, g(n) ≥ c*n; apply furedi_upper_bound
    with ε = c/2 to get N where ∀ n ≥ N, g(n) < (c/2)*n; pick n = max N 1;
    both bounds hold, giving c*n ≤ g(n) < (c/2)*n, so c < c/2, contradiction.
-/
import Mathlib
import Proofs.Erdos589Problem

namespace Erdos589Aristotle

open Erdos589

/-- Erdős's linear belief was wrong: g(n) ≠ Ω(n).
    Proof: furedi_upper_bound gives g(n) = o(n); this contradicts any linear lower bound. -/
theorem erdos_belief_false : ¬ErdosBelief := by
  intro ⟨c, hc, hBound⟩
  obtain ⟨N, hN⟩ := furedi_upper_bound (c / 2) (by linarith)
  let n := max N 1
  have hn_ge1 : n ≥ 1 := le_max_right N 1
  have hn_geN : n ≥ N := le_max_left N 1
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (by omega)
  have hlb : c * (n : ℝ) ≤ (g n : ℝ) := hBound n hn_ge1
  have hub : (g n : ℝ) < c / 2 * (n : ℝ) := hN n hn_geN
  nlinarith

end Erdos589Aristotle
