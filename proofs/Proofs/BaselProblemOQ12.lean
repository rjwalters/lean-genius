/-
Basel Problem OQ-12: The sixth-power zeta value ζ(6) = π⁶/945

  ∑_{n=1}^∞ 1/n⁶ = π⁶/945.

This is the next Euler zeta value after ζ(2) = π²/6 and ζ(4) = π⁴/90.
Euler's general formula is

  ζ(2k) = (-1)^{k+1} · 2^{2k-1} · π^{2k} · B_{2k} / (2k)!,

which Mathlib packages as `hasSum_zeta_nat`. Specialising at k = 3 reduces the
problem to the single Bernoulli number B₆ = 1/42, which Mathlib does NOT provide
(it stops at `bernoulli'_four`). The genuine new content of this entry is the
evaluation `bernoulli'_six : bernoulli' 6 = 1/42`, computed from the defining
recurrence `bernoulli'_def`; everything else is bookkeeping on top of
`hasSum_zeta_nat`.

  ζ(6) = (-1)⁴ · 2⁵ · π⁶ · B₆ / 6!
       = 32 · π⁶ · (1/42) / 720
       = 32 π⁶ / 30240
       = π⁶ / 945.

References:
- Mathlib: Mathlib.NumberTheory.ZetaValues (`hasSum_zeta_nat`, `hasSum_zeta_four`)
- Mathlib: Mathlib.NumberTheory.Bernoulli (`bernoulli'_def`, `bernoulli'_four`,
  `bernoulli'_eq_zero_of_odd`, `bernoulli_eq_bernoulli'_of_ne_one`)
-/

import Mathlib.NumberTheory.ZetaValues
import Mathlib.NumberTheory.Bernoulli
import Mathlib.Tactic

open Real

namespace BaselProblemOQ12

/-- The sixth Bernoulli number `B₆ = 1/42`, computed directly from the defining
    recurrence `bernoulli'_def`. Mathlib only provides `bernoulli'_two`,
    `bernoulli'_three`, `bernoulli'_four`, so this fills the gap needed for ζ(6).

    The recurrence gives
    `bernoulli' 6 = 1 - ∑_{k<6} C(6,k)/(6-k+1) · bernoulli' k`, and the inner sum
    evaluates to `1/7 + 1/2 + 1/2 + 0 - 1/6 + 0 = 41/42`, so `bernoulli' 6 = 1/42`. -/
theorem bernoulli'_six : bernoulli' 6 = 1 / 42 := by
  have h5 : bernoulli' 5 = 0 := bernoulli'_eq_zero_of_odd (by decide) (by norm_num)
  have c2 : Nat.choose 6 2 = 15 := by decide
  have c3 : Nat.choose 6 3 = 20 := by decide
  have c4 : Nat.choose 6 4 = 15 := by decide
  have c5 : Nat.choose 6 5 = 6 := by decide
  rw [bernoulli'_def]
  norm_num [Finset.sum_range_succ, Finset.sum_range_zero, c2, c3, c4, c5, h5,
    bernoulli'_zero, bernoulli'_one, bernoulli'_two, bernoulli'_three, bernoulli'_four]

/-- The signed Bernoulli number `bernoulli 6 = 1/42` (equal to `bernoulli' 6`
    since `6 ≠ 1`). -/
theorem bernoulli_six : bernoulli 6 = 1 / 42 := by
  rw [bernoulli_eq_bernoulli'_of_ne_one (by decide), bernoulli'_six]

/-- **ζ(6) = π⁶/945.** The sixth-power zeta value, as a `HasSum`.

    Specialises Euler's general formula `hasSum_zeta_nat` at `k = 3` and plugs in
    `bernoulli 6 = 1/42`. -/
theorem hasSum_zeta_six :
    HasSum (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 6) (π ^ 6 / 945) := by
  convert hasSum_zeta_nat (k := 3) (by norm_num) using 1
  norm_num [Nat.factorial, bernoulli_six]
  ring

/-- Summability of `∑ 1/n⁶` over `ℝ`. -/
theorem summable_zeta_six : Summable (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 6) :=
  hasSum_zeta_six.summable

/-- The `tsum` form: `∑' n, 1/n⁶ = π⁶/945`. -/
theorem tsum_zeta_six : ∑' n : ℕ, (1 : ℝ) / (n : ℝ) ^ 6 = π ^ 6 / 945 :=
  hasSum_zeta_six.tsum_eq

end BaselProblemOQ12
