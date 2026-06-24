import Mathlib

/-
# Shapiro's Cyclic Inequality for n = 4

Nesbitt's inequality (the parent entry) is the `n = 3` case of **Shapiro's cyclic
inequality**

`Σ_{i} a_i / (a_{i+1} + a_{i+2}) ≥ n / 2`   (indices mod `n`, all `a_i > 0`).

Shapiro's inequality is **true** for `n ≤ 12` even and `n ≤ 23` odd, and **false** in
general (it fails for `n = 14` even, `n = 25` odd). The parent's open question asks
whether the cyclic sums admit sum-of-squares certificates "for all `n` where the
inequality holds". Here we settle the next case beyond Nesbitt, `n = 4`:

`a/(b+c) + b/(c+d) + c/(d+a) + d/(a+b) ≥ 2`   for positive reals `a, b, c, d`.

## Method

The engine is the two-term **Titu (Engel-form Cauchy–Schwarz)** estimate
`p²/x + q²/y ≥ (p+q)²/(x+y)`, whose deficit is the explicit square
`(p y − q x)² / (x y (x+y)) ≥ 0`. Writing each term `a/(b+c) = a²/(a(b+c))` and pairing
the *opposite* terms `(1,3)` and `(2,4)` — the pairing that makes the cyclic structure
collapse — two applications fold the four fractions down to a single quotient
`(a+b+c+d)² / (X+Y)` with `X+Y = a(b+c)+c(d+a)+b(c+d)+d(a+b)`. The final polynomial step

`(a+b+c+d)² = 2(X+Y) + (a−c)² + (b−d)²`

exhibits the whole deficit, giving the sharp lower bound

`Σ ≥ 2 + ((a−c)² + (b−d)²) / (X+Y)`.

## What is new relative to Nesbitt (n = 3)

For `n = 3` Nesbitt equality forces `a = b = c` — a single ray. The `n = 4` deficit above
vanishes **iff `a = c` and `b = d`**, a genuine *two-parameter* family of equality points
(e.g. `(1,2,1,2)` gives `Σ = 2`). So the equality locus is positive-dimensional, in sharp
contrast to the `n = 3` case. We prove this characterisation as an `iff`.

All results are fully machine-checked with no `sorry` and no extra axioms.
-/

namespace NesbittInequalityOQ01OQ02

/-- **Two-term Titu / Engel-form Cauchy–Schwarz.** For positive `x, y` and arbitrary
`p, q`, `(p+q)²/(x+y) ≤ p²/x + q²/y`. The deficit is `(p y − q x)²/(x y (x+y))`. -/
theorem engel2 (p q x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    (p + q) ^ 2 / (x + y) ≤ p ^ 2 / x + q ^ 2 / y := by
  have hx0 : x ≠ 0 := ne_of_gt hx
  have hy0 : y ≠ 0 := ne_of_gt hy
  have hxy0 : x + y ≠ 0 := by positivity
  rw [← sub_nonneg]
  have hkey : p ^ 2 / x + q ^ 2 / y - (p + q) ^ 2 / (x + y)
      = (p * y - q * x) ^ 2 / (x * y * (x + y)) := by
    field_simp
    ring
  rw [hkey]
  positivity

/-- **Titu in fraction form.** For positive `p, q, u, v`,
`p/u + q/v ≥ (p+q)²/(p·u + q·v)`. (Substitute `x = p u`, `y = q v` into `engel2` and use
`p²/(p u) = p/u`.) -/
theorem titu2 (p q u v : ℝ) (hp : 0 < p) (hq : 0 < q) (hu : 0 < u) (hv : 0 < v) :
    (p + q) ^ 2 / (p * u + q * v) ≤ p / u + q / v := by
  have hrw : p / u + q / v = p ^ 2 / (p * u) + q ^ 2 / (q * v) := by
    rw [pow_two, pow_two, mul_div_mul_left _ _ (ne_of_gt hp),
      mul_div_mul_left _ _ (ne_of_gt hq)]
  rw [hrw]
  exact engel2 p q (p * u) (q * v) (by positivity) (by positivity)

/-- **Sharp lower bound for the 4-cycle (deficit form).** The full deficit of the
`n = 4` Shapiro sum above `2` is the explicit nonnegative quantity
`((a−c)² + (b−d)²) / (X+Y)`. -/
theorem shapiro_four_lower (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hd : 0 < d) :
    2 + ((a - c) ^ 2 + (b - d) ^ 2) / (a * (b + c) + c * (d + a) + (b * (c + d) + d * (a + b)))
      ≤ a / (b + c) + b / (c + d) + c / (d + a) + d / (a + b) := by
  set X := a * (b + c) + c * (d + a) with hX
  set Y := b * (c + d) + d * (a + b) with hY
  have hXpos : 0 < X := by rw [hX]; positivity
  have hYpos : 0 < Y := by rw [hY]; positivity
  -- Pair opposite terms (1,3) and (2,4).
  have H1 : (a + c) ^ 2 / X ≤ a / (b + c) + c / (d + a) := by
    rw [hX]; exact titu2 a c (b + c) (d + a) ha hc (by positivity) (by positivity)
  have H2 : (b + d) ^ 2 / Y ≤ b / (c + d) + d / (a + b) := by
    rw [hY]; exact titu2 b d (c + d) (a + b) hb hd (by positivity) (by positivity)
  -- Fold the two squared quotients into one.
  have H3 : ((a + c) + (b + d)) ^ 2 / (X + Y) ≤ (a + c) ^ 2 / X + (b + d) ^ 2 / Y :=
    engel2 (a + c) (b + d) X Y hXpos hYpos
  -- The single quotient equals 2 plus the explicit deficit.
  have hsum : (0 : ℝ) < X + Y := by linarith
  have hkey : ((a + c) + (b + d)) ^ 2 = 2 * (X + Y) + ((a - c) ^ 2 + (b - d) ^ 2) := by
    rw [hX, hY]; ring
  have hid : ((a + c) + (b + d)) ^ 2 / (X + Y)
      = 2 + ((a - c) ^ 2 + (b - d) ^ 2) / (X + Y) := by
    rw [hkey, add_div, mul_div_assoc, div_self (ne_of_gt hsum), mul_one]
  -- Chain everything.
  calc 2 + ((a - c) ^ 2 + (b - d) ^ 2) / (X + Y)
      = ((a + c) + (b + d)) ^ 2 / (X + Y) := hid.symm
    _ ≤ (a + c) ^ 2 / X + (b + d) ^ 2 / Y := H3
    _ ≤ (a / (b + c) + c / (d + a)) + (b / (c + d) + d / (a + b)) := by
        exact add_le_add H1 H2
    _ = a / (b + c) + b / (c + d) + c / (d + a) + d / (a + b) := by ring

/-- **Shapiro's cyclic inequality, `n = 4`.** For positive reals `a, b, c, d`,
`a/(b+c) + b/(c+d) + c/(d+a) + d/(a+b) ≥ 2`. The next case beyond Nesbitt (`n = 3`). -/
theorem shapiro_four (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
    2 ≤ a / (b + c) + b / (c + d) + c / (d + a) + d / (a + b) := by
  have h := shapiro_four_lower a b c d ha hb hc hd
  have hnn : 0 ≤ ((a - c) ^ 2 + (b - d) ^ 2)
      / (a * (b + c) + c * (d + a) + (b * (c + d) + d * (a + b))) := by positivity
  linarith

/-- **Equality locus is a two-parameter family.** Unlike Nesbitt (`n = 3`, equality only at
`a = b = c`), the `n = 4` Shapiro sum equals `2` **iff `a = c` and `b = d`** — a genuinely
positive-dimensional set (e.g. `(1,2,1,2)`). -/
theorem shapiro_four_eq_iff (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hd : 0 < d) :
    a / (b + c) + b / (c + d) + c / (d + a) + d / (a + b) = 2 ↔ a = c ∧ b = d := by
  constructor
  · intro h
    have hlow := shapiro_four_lower a b c d ha hb hc hd
    have hpos : 0 < a * (b + c) + c * (d + a) + (b * (c + d) + d * (a + b)) := by positivity
    -- From the deficit bound and `Σ = 2`, the deficit must be ≤ 0, hence = 0.
    have hle : ((a - c) ^ 2 + (b - d) ^ 2)
        / (a * (b + c) + c * (d + a) + (b * (c + d) + d * (a + b))) ≤ 0 := by linarith
    have hsq : (a - c) ^ 2 + (b - d) ^ 2 ≤ 0 := by
      by_contra hcon
      push_neg at hcon
      have : 0 < ((a - c) ^ 2 + (b - d) ^ 2)
          / (a * (b + c) + c * (d + a) + (b * (c + d) + d * (a + b))) :=
        div_pos hcon hpos
      linarith
    have hac : a = c := by
      have h1 : (a - c) ^ 2 ≤ 0 := by nlinarith [sq_nonneg (b - d)]
      have h2 : (a - c) ^ 2 = 0 := le_antisymm h1 (sq_nonneg _)
      have h3 : a - c = 0 := (pow_eq_zero_iff (by norm_num)).mp h2
      linarith
    have hbd : b = d := by
      have h1 : (b - d) ^ 2 ≤ 0 := by nlinarith [sq_nonneg (a - c)]
      have h2 : (b - d) ^ 2 = 0 := le_antisymm h1 (sq_nonneg _)
      have h3 : b - d = 0 := (pow_eq_zero_iff (by norm_num)).mp h2
      linarith
    exact ⟨hac, hbd⟩
  · rintro ⟨hac, hbd⟩
    rw [hac, hbd]
    have hcd : c + d ≠ 0 := by positivity
    have hdc : d + c ≠ 0 := by positivity
    field_simp
    ring

end NesbittInequalityOQ01OQ02
