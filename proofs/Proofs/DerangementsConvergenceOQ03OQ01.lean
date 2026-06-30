/-
  Derangements: round, floor, and ceiling forms of the rounding formula
  Open Question: derangements-convergence-oq-03-oq-01

  The parent open question (`derangements-convergence-oq-03`) established the
  nearest-integer identity D(n) = round(n!/e) for n ≥ 2.  This entry repackages
  that result in the three equivalent integer-rounding forms that appear in the
  literature, all derived from a single strict two-sided bound.

  ## Main Results

  `abs_derangements_sub_lt_half` : For n ≥ 2,  |D(n) - n!·e⁻¹| < 1/2.

  `derangements_eq_round` : For n ≥ 2,  (numDerangements n : ℤ) = round(n!·e⁻¹).
  `derangements_eq_floor` : For n ≥ 2,  (numDerangements n : ℤ) = ⌊n!·e⁻¹ + 1/2⌋.
  `derangements_eq_ceil`  : For n ≥ 2,  (numDerangements n : ℤ) = ⌈n!·e⁻¹ - 1/2⌉.

  ## Proof Strategy

  The whole file rests on the strict bound `|D(n) - n!/e| < 1/2`, extracted from
  `DerangementsConvergence.derangements_convergence_rate` (multiply the rate
  `|D/n! - e⁻¹| ≤ 1/(n+1)!` by `n!`, then `1/(n+1) < 1/2` for `n ≥ 2`).

  Writing x = n!/e and D = D(n), the bound `|D - x| < 1/2` gives, by elementary
  rearrangement, the hypotheses of three Mathlib characterisations:

    * `Int.floor_eq_iff`  ⟹  ⌊x + 1/2⌋ = D    (needs D ≤ x+1/2 < D+1)
    * `Int.ceil_eq_iff`   ⟹  ⌈x - 1/2⌉ = D    (needs D-1 < x-1/2 ≤ D)
    * `round_eq`          ⟹  round x = ⌊x+1/2⌋ = D

  Because e is irrational, x = n!/e is never a half-integer, so rounding up from
  x-1/2 and down to x+1/2 land on the same integer D.

  This is a routine packaging corollary: completeness / citability, not novelty.
  (Note: the file is intentionally self-contained — it depends only on the base
  `DerangementsConvergence` entry, re-deriving the round form rather than
  importing the parent `DerangementsConvergenceOQ03`.)
-/

import Mathlib
import Proofs.DerangementsConvergence

open Nat Real Filter Topology

namespace DerangementsConvergenceOQ03OQ01

/-- The strict two-sided bound `|D(n) - n!/e| < 1/2` for `n ≥ 2`.

  This is the engine behind the round / floor / ceiling forms.  It is extracted
  from `DerangementsConvergence.derangements_convergence_rate`. -/
theorem abs_derangements_sub_lt_half (n : ℕ) (hn : 2 ≤ n) :
    |(numDerangements n : ℝ) - (n.factorial : ℝ) * rexp (-1)| < 1 / 2 := by
  have hfact_pos : (0 : ℝ) < n.factorial := Nat.cast_pos.mpr n.factorial_pos
  set x : ℝ := (n.factorial : ℝ) * rexp (-1) with hx_def
  have hrate := derangements_convergence_rate n
  have hmul : |(numDerangements n : ℝ) / (n.factorial : ℝ) - rexp (-1)| =
      |(numDerangements n : ℝ) - x| / (n.factorial : ℝ) := by
    rw [show (numDerangements n : ℝ) / (n.factorial : ℝ) - rexp (-1) =
        ((numDerangements n : ℝ) - x) / (n.factorial : ℝ) from by
      simp only [hx_def]; field_simp]
    rw [abs_div, abs_of_pos hfact_pos]
  rw [hmul, div_le_iff₀ hfact_pos] at hrate
  -- hrate : |D - x| ≤ 1/(n+1)! * n!
  have hn3 : (2 : ℝ) < n + 1 := by exact_mod_cast (show 2 < n + 1 by omega)
  have hlt3 : 1 / (n + 1 : ℝ) < 1 / 2 := one_div_lt_one_div_of_lt (by norm_num) hn3
  have hfe : 1 / ((n + 1).factorial : ℝ) * (n.factorial : ℝ) = 1 / (n + 1 : ℝ) := by
    rw [Nat.factorial_succ]; push_cast; field_simp
  calc |(numDerangements n : ℝ) - x|
      ≤ 1 / ((n + 1).factorial : ℝ) * (n.factorial : ℝ) := hrate
    _ = 1 / (n + 1 : ℝ) := hfe
    _ < 1 / 2 := hlt3

/-- **Floor form.** For `n ≥ 2`, the number of derangements equals `⌊n!/e + 1/2⌋`.

  Directly from the strict bound via `Int.floor_eq_iff`. -/
theorem derangements_eq_floor (n : ℕ) (hn : 2 ≤ n) :
    (numDerangements n : ℤ) = ⌊(n.factorial : ℝ) * rexp (-1) + 1 / 2⌋ := by
  have habs := abs_lt.mp (abs_derangements_sub_lt_half n hn)
  -- habs.1 : -(1/2) < D - x ;  habs.2 : D - x < 1/2
  symm
  apply Int.floor_eq_iff.mpr
  refine ⟨?_, ?_⟩
  · -- (D : ℝ) ≤ x + 1/2
    push_cast; linarith [habs.2]
  · -- x + 1/2 < D + 1
    push_cast; linarith [habs.1]

/-- **Ceiling form.** For `n ≥ 2`, the number of derangements equals `⌈n!/e - 1/2⌉`.

  Directly from the strict bound via `Int.ceil_eq_iff`. -/
theorem derangements_eq_ceil (n : ℕ) (hn : 2 ≤ n) :
    (numDerangements n : ℤ) = ⌈(n.factorial : ℝ) * rexp (-1) - 1 / 2⌉ := by
  have habs := abs_lt.mp (abs_derangements_sub_lt_half n hn)
  symm
  apply Int.ceil_eq_iff.mpr
  refine ⟨?_, ?_⟩
  · -- (D : ℝ) - 1 < x - 1/2  ⟺  D - x < 1/2
    push_cast; linarith [habs.2]
  · -- x - 1/2 ≤ D
    push_cast; linarith [habs.1]

/-- **Round form** (parent identity, re-derived self-containedly). For `n ≥ 2`,
    the number of derangements equals the nearest integer `round(n!/e)`.

  `round x = ⌊x + 1/2⌋` by `round_eq`, then apply the floor form. -/
theorem derangements_eq_round (n : ℕ) (hn : 2 ≤ n) :
    (numDerangements n : ℤ) = round ((n.factorial : ℝ) * rexp (-1)) := by
  rw [round_eq]; exact derangements_eq_floor n hn

/-- The floor and ceiling forms agree (both equal `D(n)`): `n!/e` is never a
    half-integer in the relevant range. -/
theorem floor_eq_ceil_forms (n : ℕ) (hn : 2 ≤ n) :
    ⌊(n.factorial : ℝ) * rexp (-1) + 1 / 2⌋
      = ⌈(n.factorial : ℝ) * rexp (-1) - 1 / 2⌉ := by
  rw [← derangements_eq_floor n hn, ← derangements_eq_ceil n hn]

end DerangementsConvergenceOQ03OQ01
