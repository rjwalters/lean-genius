import Mathlib

/-
# Birthday Problem — OQ-03-OQ-01-OQ-01-OQ-03-OQ-01: The Sharp k = 3 Threshold Constant

## Research Problem: birthday-problem-oq-03-oq-01-oq-01-oq-03-oq-01

The parent (`birthday-problem-oq-03-oq-01-oq-01-oq-03`) proves the leading-order *triple*
coincidence threshold: the `n ≥ 2` solving the expected-triple balance

      n(n-1)(n-2) = 6 d² ln 2

satisfies `(6 d² ln 2)^{1/3} ≤ n ≤ (6 d² ln 2)^{1/3} + 2`, i.e. `n = (6 d² ln 2)^{1/3} + O(1)`
with the additive error only bounded by the constant `2`.  The sibling general-`k` file
recovers the same loose `± (k-1) = ± 2` window for `k = 3`.

**This file sharpens the `k = 3` case: it pins the lower-order term to *exactly* `1`, with a
remainder that *provably vanishes* as `d → ∞`.**  Writing `c := (6 d² ln 2)^{1/3}`,

      c + 1  ≤  n  ≤  c + 1 + 1/(3 c).

Hence `n = (6 d² ln 2)^{1/3} + 1 + θ` with `0 ≤ θ ≤ 1/(3 c) = O(d^{-2/3}) → 0`.  So the true
threshold is `(6 d² ln 2)^{1/3} + 1 + o(1)`, a strict refinement of the parent's `± 2` band.

## The sharpening idea — a *centered* cube instead of a corner cube

The parent sandwiches the falling factorial between the corner cubes `(n-2)³` and `n³`, which
are a distance `2` apart, so the cube-root sandwich can only pin `n` to within `2`.  The key
new observation is the exact *centered* factorisation

      n(n-1)(n-2) = (n-1)³ - (n-1).

Setting `m := n - 1`, the balance equation becomes the depressed cubic `m³ - m = c³` (where
`c³ = 6 d² ln 2`).  Then:

* **Lower bound.**  `m³ = c³ + m ≥ c³` (as `m ≥ 0`), so `m ≥ c`, i.e. `n ≥ c + 1`.
* **Upper bound.**  With `a := c + 1/(3c)` one computes the clean identity
  `a³ - a = c³ + 1/(27 c³) ≥ c³ = m³ - m`.  Equivalently, multiplying the target
  `3 c (m - c) ≤ 1` by `m² + mc + c² > 0` and using `m³ - c³ = m` collapses it to
  `(m - c)² ≥ 0`.  Hence `m ≤ c + 1/(3c)`, i.e. `n ≤ c + 1 + 1/(3c)`.

The whole improvement is bought by replacing the corner cube `n³` with the centered cube
`(n-1)³`: the centered cube touches the falling factorial to within the bounded correction
`(n-1)`, which is exactly what upgrades the `O(1)` error to `1 + o(1)`.  (This trick is special
to `k = 3`; for general `k` the centered monomial `(n - (k-1)/2)^k` no longer divides the
falling factorial exactly, which is why the general-`k` file keeps the loose `± (k-1)` band.)

## What is proved

* `cubeRoot_cube` — `(x³)^{1/3} = x` for `x ≥ 0` (same helper as the parent).
* `birthday_triple_threshold_sharp` — the two-sided bound `c + 1 ≤ n ≤ c + 1 + 1/(3c)`.
* `birthday_triple_threshold_const_one` — packaged as `|n - (c + 1)| ≤ 1/(3c)`, exhibiting the
  exact constant term `1` and the `d`-dependent (vanishing) remainder.

Tags: probability, birthday-problem, asymptotics, sharp-threshold, depressed-cubic, cube-root
-/

namespace BirthdayProblemOQ03OQ01OQ01OQ03OQ01

open Real

/-- **Cube-root identity.**  `(x³)^{1/3} = x` for `x ≥ 0`. -/
theorem cubeRoot_cube {x : ℝ} (hx : 0 ≤ x) : (x ^ 3) ^ ((1 : ℝ) / 3) = x := by
  rw [show (1 : ℝ) / 3 = ((3 : ℕ) : ℝ)⁻¹ by norm_num]
  exact Real.pow_rpow_inv_natCast hx (by norm_num)

/-- **The sharp k = 3 coincidence threshold.**

    If `n ≥ 2` solves the expected-triple balance `n(n-1)(n-2) = 6 d² ln 2`, then, writing
    `c := (6 d² ln 2)^{1/3}`,

        c + 1 ≤ n ≤ c + 1 + 1/(3 c).

    So the lower-order term is *exactly* `1` up to a remainder `≤ 1/(3c) = O(d^{-2/3})` that
    vanishes as `d → ∞` — a strict refinement of the parent's `c ≤ n ≤ c + 2` band. -/
theorem birthday_triple_threshold_sharp (d n : ℝ) (hd : 0 < d) (hn : 2 ≤ n)
    (hbal : n * (n - 1) * (n - 2) = 6 * d ^ 2 * Real.log 2) :
    (6 * d ^ 2 * Real.log 2) ^ ((1 : ℝ) / 3) + 1 ≤ n ∧
    n ≤ (6 * d ^ 2 * Real.log 2) ^ ((1 : ℝ) / 3) + 1
        + 1 / (3 * (6 * d ^ 2 * Real.log 2) ^ ((1 : ℝ) / 3)) := by
  set L := 6 * d ^ 2 * Real.log 2 with hLdef
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hL : 0 < L := by rw [hLdef]; positivity
  set c := L ^ ((1 : ℝ) / 3) with hc
  have hcpos : 0 < c := by rw [hc]; exact Real.rpow_pos_of_pos hL _
  have hcnn : 0 ≤ c := le_of_lt hcpos
  set m := n - 1 with hm_def
  have hm1 : 1 ≤ m := by rw [hm_def]; linarith
  have hmnn : 0 ≤ m := by linarith
  -- Centered form of the balance equation: m³ - m = L (= c³).
  have hrel0 : m ^ 3 - m = L := by rw [← hbal, hm_def]; ring
  -- c³ = L.
  have hc3 : c ^ 3 = L := by
    rw [hc, ← Real.rpow_natCast (L ^ ((1 : ℝ) / 3)) 3, ← Real.rpow_mul (le_of_lt hL),
        show (1 : ℝ) / 3 * ((3 : ℕ) : ℝ) = 1 by norm_num, Real.rpow_one]
  have hrel : m ^ 3 - m = c ^ 3 := by rw [hc3]; exact hrel0
  have hpos : 0 < m ^ 2 + m * c + c ^ 2 := by positivity
  refine ⟨?_, ?_⟩
  · -- Lower bound: c ≤ m, hence c + 1 ≤ n.
    have hLm : L ≤ m ^ 3 := by linarith [hrel0, hmnn]
    have hcm : c ≤ m := by
      have h := Real.rpow_le_rpow (le_of_lt hL) hLm (by norm_num : (0 : ℝ) ≤ (1 : ℝ) / 3)
      rwa [← hc, cubeRoot_cube hmnn] at h
    rw [hm_def] at hcm; linarith
  · -- Upper bound: 3 c (m - c) ≤ 1, hence m ≤ c + 1/(3c), hence n ≤ c + 1 + 1/(3c).
    have hident : (m ^ 2 + m * c + c ^ 2) * (1 - 3 * c * (m - c)) = (m - c) ^ 2 := by
      linear_combination (-3 * c) * hrel
    have hub : 3 * c * (m - c) ≤ 1 := by
      nlinarith [hident, hpos, sq_nonneg (m - c)]
    have h3c : (0 : ℝ) < 3 * c := by positivity
    rw [← sub_nonneg]
    have expand : c + 1 + 1 / (3 * c) - n = (1 - 3 * c * (m - c)) / (3 * c) := by
      rw [hm_def]; field_simp [hcpos.ne']; ring
    rw [expand]
    exact div_nonneg (by linarith [hub]) (le_of_lt h3c)

/-- **The exact lower-order constant.**  The balance-equation solution `n` sits a distance
    *exactly* `1` above the leading term `(6 d² ln 2)^{1/3}`, up to a one-sided remainder that
    is at most `1/(3 c) = O(d^{-2/3})` and therefore vanishes as `d → ∞`:

        |n - ((6 d² ln 2)^{1/3} + 1)| ≤ 1 / (3 (6 d² ln 2)^{1/3}).

    This is the precise asymptotic `n = (6 d² ln 2)^{1/3} + 1 + o(1)`. -/
theorem birthday_triple_threshold_const_one (d n : ℝ) (hd : 0 < d) (hn : 2 ≤ n)
    (hbal : n * (n - 1) * (n - 2) = 6 * d ^ 2 * Real.log 2) :
    |n - ((6 * d ^ 2 * Real.log 2) ^ ((1 : ℝ) / 3) + 1)| ≤
      1 / (3 * (6 * d ^ 2 * Real.log 2) ^ ((1 : ℝ) / 3)) := by
  obtain ⟨hlo, hhi⟩ := birthday_triple_threshold_sharp d n hd hn hbal
  have hL : 0 < 6 * d ^ 2 * Real.log 2 := by
    have : 0 < Real.log 2 := Real.log_pos (by norm_num)
    positivity
  have hcpos : 0 < (6 * d ^ 2 * Real.log 2) ^ ((1 : ℝ) / 3) := Real.rpow_pos_of_pos hL _
  have hinv : 0 ≤ 1 / (3 * (6 * d ^ 2 * Real.log 2) ^ ((1 : ℝ) / 3)) := by positivity
  rw [abs_le]
  constructor <;> linarith

#check @cubeRoot_cube
#check @birthday_triple_threshold_sharp
#check @birthday_triple_threshold_const_one

/-
## Summary

Proved (0 sorries, 0 axioms — self-contained, imports only Mathlib):

* `cubeRoot_cube` — `(x³)^{1/3} = x` for `x ≥ 0`.
* `birthday_triple_threshold_sharp` — for `n ≥ 2` solving `n(n-1)(n-2) = 6 d² ln 2`, with
  `c := (6 d² ln 2)^{1/3}`,  `c + 1 ≤ n ≤ c + 1 + 1/(3 c)`.
* `birthday_triple_threshold_const_one` — equivalently `|n - (c + 1)| ≤ 1/(3 c)`.

This sharpens the parent's `c ≤ n ≤ c + 2` (additive error `2`) to the asymptotically exact
`n = (6 d² ln 2)^{1/3} + 1 + o(1)`: the lower-order term is the explicit constant `1`, with a
remainder bounded by `1/(3 c) = O(d^{-2/3})`.  The improvement comes from the centered cube
identity `n(n-1)(n-2) = (n-1)³ - (n-1)`, which turns the balance into the depressed cubic
`m³ - m = c³` (`m = n - 1`); the lower bound is `m³ ≥ c³` and the upper bound collapses to
`(m - c)² ≥ 0` after multiplying `3c(m-c) ≤ 1` by `m² + mc + c² > 0`.
-/

end BirthdayProblemOQ03OQ01OQ01OQ03OQ01

#print axioms BirthdayProblemOQ03OQ01OQ01OQ03OQ01.birthday_triple_threshold_sharp
#print axioms BirthdayProblemOQ03OQ01OQ01OQ03OQ01.birthday_triple_threshold_const_one
