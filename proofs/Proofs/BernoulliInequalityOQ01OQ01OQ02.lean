import Mathlib

/-
# The line-escapes-a-bounded-power lemma

**Open question (bernoulli-inequality-oq-01-oq-01-oq-02).** The parent entry
`bernoulli-inequality-oq-01-oq-01` proved strict Bernoulli
`1 + n·a < (1 + a)ⁿ` on Mathlib's full weak domain `-2 ≤ a`.  Over the hard range
`-2 ≤ a ≤ -1` the positive-factor induction collapses (the factor `1 + a` is
`≤ 0`), and the proof fell back to an *ad hoc* size argument: since `|1 + a| ≤ 1`
the power `(1 + a)ⁿ` is trapped `≥ -1`, while the line `1 + n·a` drops below `-1`.

This file **extracts that mechanism as a reusable lemma** and develops it into a
small standalone theory, independent of Bernoulli:

> **Escape principle.** Every power of a magnitude-`≤ 1` base is trapped in the
> band `[-1, 1]`.  Consequently *any* line of nonzero slope eventually escapes
> that band — below it (negative slope) or above it (positive slope) — and so
> eventually crosses every such power.

## The trap

* `abs_pow_le_one`  : `|x| ≤ 1 → |xⁿ| ≤ 1`.
* `neg_one_le_pow`  : `|x| ≤ 1 → -1 ≤ xⁿ`.
* `pow_le_one`      : `|x| ≤ 1 → xⁿ ≤ 1`.

## The escape engine

* `lt_pow_of_lt_neg_one` : `|x| ≤ 1 → c < -1 → c < xⁿ`  (anything below the band is
  beaten by every power — this is exactly the parent's size argument).
* `pow_lt_of_one_lt`     : `|x| ≤ 1 → 1 < c → xⁿ < c`  (the mirror image).

## Asymptotic band escape (genuinely new)

* `eventually_line_lt_pow` : a negative-slope line is eventually `< xⁿ`, with an
  explicit threshold `N`.
* `eventually_pow_lt_line` : a positive-slope line is eventually `> xⁿ`.

Unlike the parent's positive-factor induction, the engine works verbatim for a
**negative (oscillating) base** such as `x = -1/2`, whose powers change sign yet
remain trapped; `example_oscillating_base` exhibits this.

## Application: Bernoulli's negative range as a one-liner

* `one_add_mul_lt_pow_neg` : for `-2 ≤ a ≤ -1` and `n ≥ 3`,
  `1 + n·a < (1 + a)ⁿ`, obtained from `lt_pow_of_lt_neg_one` in two lines — the
  parent's hand-rolled lines `83–90` collapse to a single engine call.

Fully machine-checked: `0` sorries, `0` axioms.
-/

namespace BernoulliInequalityOQ01OQ01OQ02

variable {x c b s : ℝ} {n : ℕ}

/-! ## The trap: powers of a magnitude-`≤ 1` base stay in `[-1, 1]`. -/

/-- If `|x| ≤ 1` then `|xⁿ| ≤ 1`: the magnitude bound is preserved by powers. -/
theorem abs_pow_le_one (hx : |x| ≤ 1) (n : ℕ) : |x ^ n| ≤ 1 := by
  rw [abs_pow]; exact pow_le_one₀ (abs_nonneg x) hx

/-- Lower wall of the trap: `|x| ≤ 1 → -1 ≤ xⁿ`. -/
theorem neg_one_le_pow (hx : |x| ≤ 1) (n : ℕ) : -1 ≤ x ^ n :=
  (abs_le.mp (abs_pow_le_one hx n)).1

/-- Upper wall of the trap: `|x| ≤ 1 → xⁿ ≤ 1`. -/
theorem pow_le_one (hx : |x| ≤ 1) (n : ℕ) : x ^ n ≤ 1 :=
  (abs_le.mp (abs_pow_le_one hx n)).2

/-! ## The escape engine. -/

/-- **Escape from below.**  If `|x| ≤ 1`, then any value `c < -1` lies strictly
below *every* power `xⁿ`.  This is precisely the size argument the parent entry
used by hand for the negative Bernoulli range, now isolated as a lemma. -/
theorem lt_pow_of_lt_neg_one (hx : |x| ≤ 1) (hc : c < -1) (n : ℕ) : c < x ^ n :=
  lt_of_lt_of_le (by linarith) (neg_one_le_pow hx n)

/-- **Escape from above.**  The mirror image: if `|x| ≤ 1`, then any value `1 < c`
strictly exceeds every power `xⁿ`. -/
theorem pow_lt_of_one_lt (hx : |x| ≤ 1) (hc : 1 < c) (n : ℕ) : x ^ n < c :=
  lt_of_le_of_lt (pow_le_one hx n) hc

/-! ## Asymptotic band escape. -/

/-- **A negative-slope line eventually drops below the band.**  If `|x| ≤ 1` and
the slope `s < 0`, then beyond an explicit threshold `N` the line `b + n·s` is
strictly below every power `xⁿ`.  The threshold is any natural number exceeding
`(b + 1)/(-s)`. -/
theorem eventually_line_lt_pow (hx : |x| ≤ 1) (hs : s < 0) :
    ∃ N : ℕ, ∀ n ≥ N, b + n * s < x ^ n := by
  have hns : (0 : ℝ) < -s := by linarith
  obtain ⟨N, hN⟩ := exists_nat_gt ((b + 1) / (-s))
  refine ⟨N, fun n hn => ?_⟩
  have hnN : ((N : ℝ)) ≤ (n : ℝ) := by exact_mod_cast hn
  have h1 : (b + 1) / (-s) < (n : ℝ) := lt_of_lt_of_le hN hnN
  rw [div_lt_iff₀ hns] at h1
  -- `b + 1 < n · (-s)`, hence `b + n·s < -1`
  have hline : b + (n : ℝ) * s < -1 := by nlinarith [h1]
  exact lt_pow_of_lt_neg_one hx hline n

/-- **A positive-slope line eventually rises above the band.**  If `|x| ≤ 1` and
the slope `s > 0`, then beyond an explicit threshold `N` the line `b + n·s`
strictly exceeds every power `xⁿ`. -/
theorem eventually_pow_lt_line (hx : |x| ≤ 1) (hs : 0 < s) :
    ∃ N : ℕ, ∀ n ≥ N, x ^ n < b + n * s := by
  obtain ⟨N, hN⟩ := exists_nat_gt ((1 - b) / s)
  refine ⟨N, fun n hn => ?_⟩
  have hnN : ((N : ℝ)) ≤ (n : ℝ) := by exact_mod_cast hn
  have h1 : (1 - b) / s < (n : ℝ) := lt_of_lt_of_le hN hnN
  rw [div_lt_iff₀ hs] at h1
  -- `1 - b < n · s`, hence `1 < b + n·s`
  have hline : (1 : ℝ) < b + (n : ℝ) * s := by nlinarith [h1]
  exact pow_lt_of_one_lt hx hline n

/-! ## A negative base: the engine handles oscillating powers. -/

/-- The base may be **negative**: for `x = -1/2` the powers `(-1/2)ⁿ` oscillate in
sign yet stay in `[-1, 1]`, so the descending line `10 - n` still escapes below
them past `n = 11`.  The parent's positive-factor induction cannot see this. -/
theorem example_oscillating_base :
    ∃ N : ℕ, ∀ n ≥ N, (10 : ℝ) - n < (-1 / 2) ^ n := by
  have hx : |(-1 / 2 : ℝ)| ≤ 1 := by rw [abs_le]; constructor <;> norm_num
  obtain ⟨N, hN⟩ := eventually_line_lt_pow (x := (-1 / 2 : ℝ)) (b := 10) (s := -1) hx
    (by norm_num)
  exact ⟨N, fun n hn => by have h := hN n hn; linarith⟩

/-! ## Application: Bernoulli's hard negative range, from the engine. -/

/-- **Strict Bernoulli on `-2 ≤ a ≤ -1`, via the escape engine.**  For `n ≥ 3`,
`1 + n·a < (1 + a)ⁿ`.  Setting `x = 1 + a` (so `|x| ≤ 1` on this range) and
observing the line `1 + n·a ≤ 1 - n < -1` for `n ≥ 3`, the result is one call to
`lt_pow_of_lt_neg_one`.  This reproduces the parent's bespoke negative-range
argument as a corollary of the general lemma. -/
theorem one_add_mul_lt_pow_neg {a : ℝ} (ha2 : -2 ≤ a) (ha1 : a ≤ -1)
    (hn : 3 ≤ n) : 1 + n * a < (1 + a) ^ n := by
  have hx : |1 + a| ≤ 1 := by rw [abs_le]; constructor <;> linarith
  have hn3 : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  -- the line `1 + n·a` is below `-1`: `n·a ≤ 3a ≤ -3`
  have hna : (n : ℝ) * a ≤ 3 * a :=
    mul_le_mul_of_nonpos_right hn3 (by linarith)
  have hline : 1 + (n : ℝ) * a < -1 := by linarith
  exact lt_pow_of_lt_neg_one hx hline n

/-- Concrete instance outside the parent's positive range:
`1 + 4·(−3/2) = −5 < 1/16 = (1 − 3/2)⁴`. -/
example : (1 : ℝ) + 4 * (-3 / 2) < (1 + (-3 / 2)) ^ 4 :=
  one_add_mul_lt_pow_neg (by norm_num) (by norm_num) (by norm_num)

/-- Boundary base `a = -2`, where `1 + a = -1` oscillates:
`1 + 5·(−2) = −9 < −1 = (1 − 2)⁵`. -/
example : (1 : ℝ) + 5 * (-2) < (1 + (-2)) ^ 5 :=
  one_add_mul_lt_pow_neg (by norm_num) (by norm_num) (by norm_num)

end BernoulliInequalityOQ01OQ01OQ02
