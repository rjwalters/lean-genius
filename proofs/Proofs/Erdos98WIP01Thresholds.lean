/-
  Erdős Problem #98 — Distinct distances in general position:
  monotonicity-sharpened small-`n` lower bounds (0-axiom).

  Companion to `Erdos98WIP01.lean`, which pins the exact values `h 2 = h 3 = 1`,
  `h 4 = 2`, `h 5 = 3`, proves `h` is monotone (`h_mono`), and gives the general
  elementary ladder `le_h_of_three_mul_sub_one_le : 3 * k - 1 ≤ n → k ≤ h n`.

  The ladder is the sharpest *uniform* elementary lower bound, but for a fixed
  small `n` an exact base value combined with monotonicity beats it.  In
  particular the ladder yields `3 ≤ h n` only from `n ≥ 8` (`k = 3` needs
  `n ≥ 3·3 - 1 = 8`), whereas `h 5 = 3` together with `h_mono` gives `3 ≤ h n`
  for *every* `n ≥ 5`.  This file records those sharpened thresholds, filling the
  `n ∈ {5, 6, 7}` gap the ladder leaves open — the current best-known lower bounds
  for `h 6` and `h 7`.

  * `two_le_h_of_four_le`   : `4 ≤ n → 2 ≤ h n`   (from `h 4 = 2`, monotone).
  * `three_le_h_of_five_le` : `5 ≤ n → 3 ≤ h n`   (from `h 5 = 3`, monotone).
  * `three_le_h_six` / `three_le_h_seven` : the `n = 6, 7` instances the ladder
    cannot reach.

  These are honest corollaries, not new mechanisms: pinning `h 6 = 3` (or proving
  `h 6 ≥ 4`) is a genuinely open direction — it needs either an explicit
  general-position 6-point 3-distance configuration (whose existence is itself
  open; the regular hexagon and pentagon-plus-centre are disqualified by the
  no-four-concyclic condition) or incidence-geometry machinery beyond Mathlib.

  0 axioms, 0 sorries — `#print axioms` = propext / Classical.choice / Quot.sound.
-/

import Mathlib
import Proofs.Erdos98WIP01

namespace Erdos98WIP01

/-- **`2 ≤ h n` for every `n ≥ 4.`**  Immediate from the exact value `h 4 = 2` and
    monotonicity of `h`: adding points (in general position) can only increase the
    minimum number of distinct distances. -/
theorem two_le_h_of_four_le {n : ℕ} (hn : 4 ≤ n) : 2 ≤ h n := by
  have := h_mono hn
  rwa [h_four] at this

/-- **`3 ≤ h n` for every `n ≥ 5.`**  From the exact value `h 5 = 3` and
    monotonicity.  This sharpens the general ladder bound
    `le_h_of_three_mul_sub_one_le`, which only reaches `3 ≤ h n` from `n ≥ 8`;
    monotonicity closes the `n ∈ {5, 6, 7}` gap. -/
theorem three_le_h_of_five_le {n : ℕ} (hn : 5 ≤ n) : 3 ≤ h n := by
  have := h_mono hn
  rwa [h_five_eq_three] at this

/-- **`3 ≤ h 6.`**  The current best-known lower bound for six points in general
    position, obtained purely from `h 5 = 3` and monotonicity — the ladder bound
    does not reach `3` until `n ≥ 8`.  Whether `h 6 = 3` (equivalently, whether a
    general-position 6-point set with only 3 distinct distances exists) is open. -/
theorem three_le_h_six : 3 ≤ h 6 := three_le_h_of_five_le (by norm_num)

/-- **`3 ≤ h 7.`**  Likewise from `h 5 = 3` and monotonicity; still below the
    ladder's `n ≥ 8` threshold. -/
theorem three_le_h_seven : 3 ≤ h 7 := three_le_h_of_five_le (by norm_num)

end Erdos98WIP01
