import Mathlib

/-
# The magnitude-bounded power band and the escape/capture dichotomy

**Open question (bernoulli-inequality-oq-01-oq-01-oq-02-oq-01).** The parent entry
`bernoulli-inequality-oq-01-oq-01-oq-02` (*the line-escapes-a-bounded-power lemma*)
trapped every power of a magnitude-`≤ 1` base inside the **fixed** band `[-1, 1]`,
and concluded that any line of nonzero slope eventually escapes it.

This file generalizes the bound to a magnitude-`≤ B` base, whose powers live in the
**`n`-dependent** band `[-Bⁿ, Bⁿ]`, and asks the natural follow-up:

> *Which lines escape the `n`-dependent band?*

The answer is a sharp dichotomy governed by the critical value `B = 1`.

## The generalized trap

* `abs_pow_le`     : `|x| ≤ B → |xⁿ| ≤ Bⁿ`.
* `neg_pow_le_pow` : `|x| ≤ B → -Bⁿ ≤ xⁿ`.
* `pow_le_pow_band`: `|x| ≤ B → xⁿ ≤ Bⁿ`.

## The escape engine (any `B`)

* `lt_pow_of_lt_neg_pow` : `|x| ≤ B → c < -Bⁿ → c < xⁿ`.
* `pow_lt_of_pow_lt`     : `|x| ≤ B → Bⁿ < c → xⁿ < c`.

## The dichotomy

* **Shrinking / critical band `0 ≤ B ≤ 1`** (`Bⁿ ≤ 1`): the band is contained in
  `[-1, 1]`, so the parent's mechanism survives verbatim — a negative-slope line
  eventually drops below *every* power (`eventually_line_lt_pow_band`) and a
  positive-slope line eventually rises above every power (`eventually_pow_lt_line_band`).
  The parent (`B = 1`) is the boundary case.

* **Growing band `B > 1`** (`Bⁿ → ∞`): the band swallows every line.  *No* line of
  *any* slope can escape: beyond an explicit threshold the line lies strictly inside
  `(-Bⁿ, Bⁿ)` (`eventually_line_mem_band`).  The driver is that the exponential `Bⁿ`
  dominates the linear `|b| + n·|s|` — `Mathlib`'s
  `tendsto_pow_const_div_const_pow_of_one_lt`.

The contrast `eventually_line_lt_pow_band` (escape, `B ≤ 1`) versus
`eventually_line_mem_band` (capture, `B > 1`) is the crystallized boundary
phenomenon: the parent sits exactly on the knife-edge `B = 1`.

Fully machine-checked: `0` sorries, `0` axioms.
-/

namespace BernoulliInequalityOQ01OQ01OQ02OQ01

open Filter Topology

variable {x c b s B : ℝ} {n : ℕ}

/-! ## The generalized trap: powers of a magnitude-`≤ B` base stay in `[-Bⁿ, Bⁿ]`. -/

/-- A magnitude bound is preserved by powers: `|x| ≤ B → |xⁿ| ≤ Bⁿ`.  (Note `0 ≤ B`
is automatic from `|x| ≤ B`.) -/
theorem abs_pow_le (hx : |x| ≤ B) (n : ℕ) : |x ^ n| ≤ B ^ n := by
  rw [abs_pow]
  exact pow_le_pow_left₀ (abs_nonneg x) hx n

/-- Lower wall of the band: `|x| ≤ B → -Bⁿ ≤ xⁿ`. -/
theorem neg_pow_le_pow (hx : |x| ≤ B) (n : ℕ) : -B ^ n ≤ x ^ n :=
  (abs_le.mp (abs_pow_le hx n)).1

/-- Upper wall of the band: `|x| ≤ B → xⁿ ≤ Bⁿ`. -/
theorem pow_le_pow_band (hx : |x| ≤ B) (n : ℕ) : x ^ n ≤ B ^ n :=
  (abs_le.mp (abs_pow_le hx n)).2

/-! ## The escape engine (works for every `B`). -/

/-- **Escape from below.**  Anything strictly under the lower wall `-Bⁿ` is beaten
by the power `xⁿ`. -/
theorem lt_pow_of_lt_neg_pow (hx : |x| ≤ B) (hc : c < -B ^ n) : c < x ^ n :=
  lt_of_lt_of_le hc (neg_pow_le_pow hx n)

/-- **Escape from above.**  Anything strictly over the upper wall `Bⁿ` exceeds the
power `xⁿ`. -/
theorem pow_lt_of_pow_lt (hx : |x| ≤ B) (hc : B ^ n < c) : x ^ n < c :=
  lt_of_le_of_lt (pow_le_pow_band hx n) hc

/-! ## Shrinking / critical band `0 ≤ B ≤ 1`: lines still escape.

When `B ≤ 1` the band `[-Bⁿ, Bⁿ] ⊆ [-1, 1]`, so the parent's threshold argument
generalizes unchanged: any line of nonzero slope eventually leaves `[-1, 1]`, and
a fortiori the smaller band. -/

/-- For `0 ≤ B ≤ 1` the upper wall never exceeds `1`. -/
theorem pow_le_one_of_le_one (hB0 : 0 ≤ B) (hB1 : B ≤ 1) (n : ℕ) : B ^ n ≤ 1 :=
  pow_le_one₀ hB0 hB1

/-- **A negative-slope line eventually drops below the whole band (`B ≤ 1`).**  If
`|x| ≤ B ≤ 1` and `s < 0`, then beyond an explicit threshold the line `b + n·s` is
strictly below *every* power `xⁿ`.  Generalizes the parent's `eventually_line_lt_pow`
from the fixed band `B = 1` to every `B ≤ 1`. -/
theorem eventually_line_lt_pow_band (hx : |x| ≤ B) (hB1 : B ≤ 1) (hs : s < 0) :
    ∃ N : ℕ, ∀ n ≥ N, b + n * s < x ^ n := by
  have hB0 : 0 ≤ B := le_trans (abs_nonneg x) hx
  have hns : (0 : ℝ) < -s := by linarith
  obtain ⟨N, hN⟩ := exists_nat_gt ((b + 1) / (-s))
  refine ⟨N, fun n hn => ?_⟩
  have hnN : ((N : ℝ)) ≤ (n : ℝ) := by exact_mod_cast hn
  have h1 : (b + 1) / (-s) < (n : ℝ) := lt_of_lt_of_le hN hnN
  rw [div_lt_iff₀ hns] at h1
  have hline : b + (n : ℝ) * s < -1 := by nlinarith [h1]
  -- the line is below `-1 ≤ -Bⁿ`, hence below the band, hence below `xⁿ`.
  have hwall : -(1 : ℝ) ≤ -B ^ n := by
    have := pow_le_one_of_le_one hB0 hB1 n; linarith
  exact lt_pow_of_lt_neg_pow hx (lt_of_lt_of_le hline hwall)

/-- **A positive-slope line eventually rises above the whole band (`B ≤ 1`).**  The
mirror image: if `|x| ≤ B ≤ 1` and `s > 0`, the line `b + n·s` eventually exceeds
every power `xⁿ`. -/
theorem eventually_pow_lt_line_band (hx : |x| ≤ B) (hB1 : B ≤ 1) (hs : 0 < s) :
    ∃ N : ℕ, ∀ n ≥ N, x ^ n < b + n * s := by
  have hB0 : 0 ≤ B := le_trans (abs_nonneg x) hx
  obtain ⟨N, hN⟩ := exists_nat_gt ((1 - b) / s)
  refine ⟨N, fun n hn => ?_⟩
  have hnN : ((N : ℝ)) ≤ (n : ℝ) := by exact_mod_cast hn
  have h1 : (1 - b) / s < (n : ℝ) := lt_of_lt_of_le hN hnN
  rw [div_lt_iff₀ hs] at h1
  have hline : (1 : ℝ) < b + (n : ℝ) * s := by nlinarith [h1]
  have hwall : B ^ n ≤ (1 : ℝ) := pow_le_one_of_le_one hB0 hB1 n
  exact pow_lt_of_pow_lt hx (lt_of_le_of_lt hwall hline)

/-! ## Growing band `B > 1`: the band captures every line.

The new phenomenon.  When `B > 1` the walls `±Bⁿ` grow exponentially and dominate
any line `b + n·s`.  Hence *no* line escapes: it is eventually trapped strictly
inside the open band `(-Bⁿ, Bⁿ)`.  This is the exact opposite of the `B ≤ 1` case. -/

/-- The exponential wall dominates the linear envelope `|b| + n·|s|`: for `B > 1` the
quotient `(|b| + |s|·n) / Bⁿ` tends to `0`. -/
theorem tendsto_linear_div_pow (hB : 1 < B) (b s : ℝ) :
    Tendsto (fun n : ℕ => (|b| + |s| * (n : ℝ)) / B ^ n) atTop (𝓝 0) := by
  have h0 : Tendsto (fun n : ℕ => (1 : ℝ) / B ^ n) atTop (𝓝 0) := by
    have := tendsto_pow_const_div_const_pow_of_one_lt 0 hB
    simpa using this
  have h1 : Tendsto (fun n : ℕ => (n : ℝ) / B ^ n) atTop (𝓝 0) := by
    have := tendsto_pow_const_div_const_pow_of_one_lt 1 hB
    simpa using this
  have hcomb :
      Tendsto (fun n : ℕ => |b| * ((1 : ℝ) / B ^ n) + |s| * ((n : ℝ) / B ^ n))
        atTop (𝓝 (|b| * 0 + |s| * 0)) :=
    (h0.const_mul |b|).add (h1.const_mul |s|)
  have hcong :
      (fun n : ℕ => (|b| + |s| * (n : ℝ)) / B ^ n)
        = fun n : ℕ => |b| * ((1 : ℝ) / B ^ n) + |s| * ((n : ℝ) / B ^ n) := by
    funext n; ring
  rw [hcong]
  simpa using hcomb

/-- **Capture (`B > 1`): every line is eventually trapped strictly inside the band.**
For `B > 1` and *any* intercept `b` and slope `s`, there is an explicit threshold
beyond which `-Bⁿ < b + n·s < Bⁿ`.  No line of any slope escapes the growing band —
the sharp contrast with `eventually_line_lt_pow_band`. -/
theorem eventually_line_mem_band (hB : 1 < B) (b s : ℝ) :
    ∃ N : ℕ, ∀ n ≥ N, b + n * s ∈ Set.Ioo (-B ^ n) (B ^ n) := by
  have hBpos : (0 : ℝ) < B := lt_trans one_pos hB
  have hev : ∀ᶠ n : ℕ in atTop, (|b| + |s| * (n : ℝ)) / B ^ n < 1 :=
    (tendsto_linear_div_pow hB b s).eventually_lt_const (by norm_num)
  obtain ⟨N, hN⟩ := eventually_atTop.mp hev
  refine ⟨N, fun n hn => ?_⟩
  have hBn : (0 : ℝ) < B ^ n := pow_pos hBpos n
  have hlt : |b| + |s| * (n : ℝ) < B ^ n := (div_lt_one hBn).mp (hN n hn)
  -- bound the line by its linear envelope
  have henv : |b + (n : ℝ) * s| ≤ |b| + |s| * (n : ℝ) := by
    have hns : |(n : ℝ) * s| = |s| * (n : ℝ) := by
      rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg n), mul_comm]
    calc |b + (n : ℝ) * s| ≤ |b| + |(n : ℝ) * s| := abs_add_le b _
      _ = |b| + |s| * (n : ℝ) := by rw [hns]
  have : |b + (n : ℝ) * s| < B ^ n := lt_of_le_of_lt henv hlt
  rw [abs_lt] at this
  exact ⟨this.1, this.2⟩

/-- The capture statement unpacked: for `B > 1` the line eventually lies strictly
between the walls. -/
theorem eventually_neg_pow_lt_line_lt_pow (hB : 1 < B) (b s : ℝ) :
    ∃ N : ℕ, ∀ n ≥ N, -B ^ n < b + n * s ∧ b + n * s < B ^ n := by
  obtain ⟨N, hN⟩ := eventually_line_mem_band hB b s
  exact ⟨N, fun n hn => hN n hn⟩

/-! ## The dichotomy, side by side. -/

/-- **Boundary dichotomy.**  Fix any line `b + n·s` with negative slope `s < 0`.
* If `B > 1` the line is eventually captured inside the band `(-Bⁿ, Bⁿ)`.
* If `0 ≤ B ≤ 1` (and `|x| ≤ B`) the same line eventually escapes below the band,
  beaten by every power `xⁿ`.
The single hypothesis `B ≷ 1` flips capture into escape — the parent's fixed band
`B = 1` is exactly the knife-edge. -/
theorem escape_or_capture (hx : |x| ≤ B) (hs : s < 0) :
    (1 < B → ∃ N : ℕ, ∀ n ≥ N, b + n * s ∈ Set.Ioo (-B ^ n) (B ^ n)) ∧
    (B ≤ 1 → ∃ N : ℕ, ∀ n ≥ N, b + n * s < x ^ n) :=
  ⟨fun hB => eventually_line_mem_band hB b s,
   fun hB1 => eventually_line_lt_pow_band hx hB1 hs⟩

/-! ## Sanity checks. -/

/-- Shrinking band `B = 1/2`: the descending line `10 - n` escapes below the powers
of `x = -1/2` (whose band is `[-(1/2)ⁿ, (1/2)ⁿ]`). -/
example : ∃ N : ℕ, ∀ n ≥ N, (10 : ℝ) - n < (-1 / 2) ^ n := by
  have hx : |(-1 / 2 : ℝ)| ≤ (1 / 2 : ℝ) := by rw [abs_le]; constructor <;> norm_num
  obtain ⟨N, hN⟩ :=
    eventually_line_lt_pow_band (x := (-1 / 2 : ℝ)) (B := (1 / 2 : ℝ))
      (b := 10) (s := -1) hx (by norm_num) (by norm_num)
  exact ⟨N, fun n hn => by have h := hN n hn; linarith⟩

/-- Growing band `B = 2`: the steep line `5 + 100·n` cannot escape — it is eventually
trapped inside `(-2ⁿ, 2ⁿ)`. -/
example : ∃ N : ℕ, ∀ n ≥ N, (5 : ℝ) + n * 100 ∈ Set.Ioo (-(2 : ℝ) ^ n) ((2 : ℝ) ^ n) :=
  eventually_line_mem_band (B := (2 : ℝ)) (by norm_num) 5 100

end BernoulliInequalityOQ01OQ01OQ02OQ01
