/-
  Derangements: D(n) = round(n!/e)
  Open Question: derangements-convergence-oq-03

  The number of derangements of n elements equals the nearest integer to n!/e.

  ## Main Result

  `derangements_eq_round` (PROVED): For n ≥ 2,
    (numDerangements n : ℤ) = round(n! · rexp(-1))

  ## Proof Strategy

  From `DerangementsConvergence.derangements_convergence_rate`:
    |D(n)/n! - rexp(-1)| ≤ 1/(n+1)!

  Multiplying by n! (using abs_div + div_le_iff):
    |D(n) - n!·rexp(-1)| ≤ n!/(n+1)! = 1/(n+1)

  For n ≥ 2: n+1 ≥ 3 > 2, so 1/(n+1) < 1/2.

  Therefore |D(n) - n!/e| < 1/2. Since D(n) is an integer, it equals
  the nearest integer to n!/e, i.e., round(n!/e).

  The nearest integer characterization uses:
    round x = ⌊x + 1/2⌋             (Mathlib: round_eq)
    ⌊r⌋ = z ↔ ↑z ≤ r ∧ r < z + 1  (Mathlib: floor_eq_iff)
-/

import Mathlib
import Proofs.DerangementsConvergence

open Nat Real Filter Topology

namespace DerangementsConvergenceOQ03

private lemma factorial_mul_one_div_factorial_succ (n : ℕ) :
    (n.factorial : ℝ) * (1 / ((n + 1).factorial : ℝ)) = 1 / (n + 1 : ℝ) := by
  rw [Nat.factorial_succ]
  push_cast
  field_simp
  ring

/-- For n ≥ 2, the number of derangements equals the nearest integer to n!/e.

  Proof: The alternating series bound gives |D(n)/n! - e⁻¹| ≤ 1/(n+1)!.
  Multiplying by n! yields |D(n) - n!/e| ≤ 1/(n+1) ≤ 1/3 < 1/2.
  So D(n) is the unique integer nearest to n!/e. -/
theorem derangements_eq_round (n : ℕ) (hn : 2 ≤ n) :
    (numDerangements n : ℤ) = round ((n.factorial : ℝ) * rexp (-1)) := by
  have hfact_pos : (0 : ℝ) < n.factorial := Nat.cast_pos.mpr n.factorial_pos
  set x : ℝ := (n.factorial : ℝ) * rexp (-1) with hx_def
  -- Step 1: show |D(n) - x| < 1/2
  have hlt : |(numDerangements n : ℝ) - x| < 1 / 2 := by
    have hrate := derangements_convergence_rate n
    -- Rewrite: |D/n! - rexp(-1)| = |D - x|/n!
    have hmul : |(numDerangements n : ℝ) / (n.factorial : ℝ) - rexp (-1)| =
        |(numDerangements n : ℝ) - x| / (n.factorial : ℝ) := by
      rw [show (numDerangements n : ℝ) / (n.factorial : ℝ) - rexp (-1) =
          ((numDerangements n : ℝ) - x) / (n.factorial : ℝ) from by
        simp only [hx_def]; field_simp]
      rw [abs_div, abs_of_pos hfact_pos]
    -- So |D - x|/n! ≤ 1/(n+1)!, multiply both sides by n!
    rw [hmul, div_le_iff hfact_pos] at hrate
    -- Now hrate : |D - x| ≤ n! * (1/(n+1)!) = 1/(n+1)
    -- For n ≥ 2: 1/(n+1) < 1/2 since n+1 ≥ 3 > 2
    have hn3 : (2 : ℝ) < n + 1 := by exact_mod_cast (show 2 < n + 1 by omega)
    have hlt3 : 1 / (n + 1 : ℝ) < 1 / 2 := one_div_lt_one_div_of_lt (by norm_num) hn3
    calc |(numDerangements n : ℝ) - x|
        ≤ (n.factorial : ℝ) * (1 / ((n + 1).factorial : ℝ)) := hrate
      _ = 1 / (n + 1 : ℝ) := factorial_mul_one_div_factorial_succ n
      _ < 1 / 2 := hlt3
  -- Step 2: D(n) = ⌊x + 1/2⌋ = round x
  rw [round_eq]
  symm
  apply floor_eq_iff.mpr
  have habs := abs_lt.mp hlt
  -- habs.1 : -(1/2) < D - x, i.e., x - 1/2 < D, i.e., x + 1/2 < D + 1
  -- habs.2 : D - x < 1/2, i.e., D < x + 1/2, i.e., D ≤ x + 1/2
  constructor
  · -- ↑(numDerangements n : ℤ) ≤ x + 1/2
    push_cast
    linarith [habs.2]
  · -- x + 1/2 < ↑(numDerangements n : ℤ) + 1
    push_cast
    linarith [habs.1]

end DerangementsConvergenceOQ03
