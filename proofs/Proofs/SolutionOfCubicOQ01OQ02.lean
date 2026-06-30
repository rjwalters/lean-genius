import Proofs.SolutionOfCubicOQ01OQ01

/-!
# The Sign of the Real Cubic Discriminant Classifies the Root Structure (Solution of Cubic, OQ-01-OQ-02)

## What This Proves

The sibling file `SolutionOfCubicOQ01OQ01` defines the general cubic discriminant
`Δ(a,b,c,d) = 18abcd − 4b³d + b²c² − 4ac³ − 27a²d²` over `ℂ`, proves its invariance under the
Tschirnhaus shift, and gives the symmetric **root form** `Δ = a⁴·∏_{i<j}(xᵢ−xⱼ)²`. Over `ℂ` the
discriminant is just an algebraic invariant: it vanishes iff two roots collide.

Over `ℝ` the discriminant carries **strictly more** information — its **sign** classifies the
root structure of a real cubic. This is the classical *discriminant test*:

  * `Δ > 0`  ⟺  three **distinct real** roots;
  * `Δ < 0`  ⟺  one real root and a **non-real complex-conjugate pair**;
  * `Δ = 0`  ⟺  a **repeated** root (all roots then real).

This file proves the three forward sign implications (the directions used in practice), which —
because the three structural cases are exhaustive for a real cubic — give the full
classification. None of this is in the sibling: the sibling is a characteristic-free algebraic
identity over `ℂ`; here the content is the **order** structure of `ℝ`.

## The key idea

Both sign theorems come from the root form `Δ = a⁴·((x₁−x₂)(x₁−x₃)(x₂−x₃))²`:

* **All-real roots.** The bracket is a real number, so `Δ = a⁴·(real)²  ≥ 0`, and `> 0` exactly
  when the roots are distinct. (`realDiscriminant_pos_of_distinct_real_roots`.)

* **Conjugate pair.** If the roots are `r` (real) and `w, w̄` with `w = m + n·i`, the Vieta
  coefficients are real and a *single real polynomial identity* collapses the discriminant to

    `Δ = −4·a⁴·n²·((r−m)² + n²)²`,

  which is `< 0` precisely when `n ≠ 0` (a genuine non-real pair). The whole computation is a
  `ring` identity in `a, r, m, n` — the complex root `(w − w̄)² = −4n²` is what flips the sign.
  (`realDiscriminant_conj_pair`, `realDiscriminant_neg_of_conj_pair`.)

To certify that the conjugate-pair *parametrization* really is the Vieta data of the complex
roots `r, w, w̄`, `realDiscriminant_conj_pair_root_form` bridges back to the sibling's complex
`generalDiscriminant_eq_root_form` via the real-to-complex cast.

## Original Contributions
- `realDiscriminant` — the real-valued cubic discriminant (so its sign is meaningful).
- `realDiscriminant_eq_root_form` — real root form `Δ = a⁴·((x₁−x₂)(x₁−x₃)(x₂−x₃))²`.
- `realDiscriminant_nonneg_of_real_roots` / `realDiscriminant_pos_of_distinct_real_roots` —
  three real roots force `Δ ≥ 0`, strictly `> 0` when distinct.
- `realDiscriminant_eq_zero_iff_repeated_real` — among real roots, `Δ = 0` ⟺ two coincide.
- `realDiscriminant_conj_pair` — the headline real identity `Δ = −4a⁴n²((r−m)²+n²)²` for the
  conjugate-pair Vieta data.
- `realDiscriminant_neg_of_conj_pair` — `Δ < 0` for a real root plus a non-real conjugate pair.
- `realDiscriminant_conj_pair_root_form` — certifies the parametrization is the complex root
  form of `r, w, w̄` (`w = m + n·i`), bridging to the sibling's `generalDiscriminant`.

## Proof Techniques
Everything reduces to `ring` over `ℝ` plus `positivity`/`nlinarith` for the sign. The only
complex-number work is the bridge, which proves three Vieta equalities componentwise
(`Complex.ext`) — the algebraic core never leaves `ℝ`. `0`-axiom throughout.
-/

namespace SolutionOfCubicOQ01OQ02

open SolutionOfCubicOQ01OQ01

/-! ## Part 1: The real cubic discriminant -/

/-- The discriminant of the **real** cubic `a x³ + b x² + c x + d`. Same polynomial as the
sibling's complex `generalDiscriminant`, but valued in `ℝ` so that its **sign** is meaningful. -/
def realDiscriminant (a b c d : ℝ) : ℝ :=
  18 * a * b * c * d - 4 * b ^ 3 * d + b ^ 2 * c ^ 2 - 4 * a * c ^ 3 - 27 * a ^ 2 * d ^ 2

/-- The real discriminant is the cast of the complex one: it agrees with the sibling's
`generalDiscriminant` after `ℝ → ℂ`. -/
theorem realDiscriminant_cast (a b c d : ℝ) :
    (realDiscriminant a b c d : ℂ)
      = generalDiscriminant (a : ℂ) (b : ℂ) (c : ℂ) (d : ℂ) := by
  unfold realDiscriminant generalDiscriminant
  push_cast
  ring

/-- A leading coefficient of a genuine cubic gives `a⁴ > 0`. -/
private lemma pow4_pos {a : ℝ} (ha : a ≠ 0) : 0 < a ^ 4 := by positivity

/-! ## Part 2: The all-real-roots case — `Δ ≥ 0`

For three real roots the discriminant is `a⁴` times a real square, hence nonnegative, and
strictly positive exactly when the roots are distinct. -/

/-- **Real root form.** If `b, c, d` are the Vieta coefficients of three *real* roots
`x₁, x₂, x₃` (so `a x³ + b x² + c x + d = a(x−x₁)(x−x₂)(x−x₃)`), then
`Δ = a⁴·((x₁−x₂)(x₁−x₃)(x₂−x₃))²`. -/
theorem realDiscriminant_eq_root_form (a x₁ x₂ x₃ b c d : ℝ)
    (hb : b = -a * (x₁ + x₂ + x₃))
    (hc : c = a * (x₁ * x₂ + x₁ * x₃ + x₂ * x₃))
    (hd : d = -a * (x₁ * x₂ * x₃)) :
    realDiscriminant a b c d = a ^ 4 * ((x₁ - x₂) * (x₁ - x₃) * (x₂ - x₃)) ^ 2 := by
  subst hb hc hd
  unfold realDiscriminant
  ring

/-- **Three real roots force `Δ ≥ 0`.** -/
theorem realDiscriminant_nonneg_of_real_roots (a x₁ x₂ x₃ b c d : ℝ)
    (hb : b = -a * (x₁ + x₂ + x₃))
    (hc : c = a * (x₁ * x₂ + x₁ * x₃ + x₂ * x₃))
    (hd : d = -a * (x₁ * x₂ * x₃)) :
    0 ≤ realDiscriminant a b c d := by
  rw [realDiscriminant_eq_root_form a x₁ x₂ x₃ b c d hb hc hd]
  positivity

/-- **Three distinct real roots force `Δ > 0`** — the first leg of the discriminant test. -/
theorem realDiscriminant_pos_of_distinct_real_roots (a x₁ x₂ x₃ b c d : ℝ)
    (ha : a ≠ 0) (h12 : x₁ ≠ x₂) (h13 : x₁ ≠ x₃) (h23 : x₂ ≠ x₃)
    (hb : b = -a * (x₁ + x₂ + x₃))
    (hc : c = a * (x₁ * x₂ + x₁ * x₃ + x₂ * x₃))
    (hd : d = -a * (x₁ * x₂ * x₃)) :
    0 < realDiscriminant a b c d := by
  rw [realDiscriminant_eq_root_form a x₁ x₂ x₃ b c d hb hc hd]
  have hprod : (x₁ - x₂) * (x₁ - x₃) * (x₂ - x₃) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (sub_ne_zero.mpr h12) (sub_ne_zero.mpr h13)) (sub_ne_zero.mpr h23)
  positivity

/-- **Repeated-root criterion over `ℝ`.** For real roots, `Δ = 0` iff two of them coincide —
the boundary `Δ = 0` of the discriminant test. -/
theorem realDiscriminant_eq_zero_iff_repeated_real (a x₁ x₂ x₃ b c d : ℝ) (ha : a ≠ 0)
    (hb : b = -a * (x₁ + x₂ + x₃))
    (hc : c = a * (x₁ * x₂ + x₁ * x₃ + x₂ * x₃))
    (hd : d = -a * (x₁ * x₂ * x₃)) :
    realDiscriminant a b c d = 0 ↔ (x₁ = x₂ ∨ x₁ = x₃ ∨ x₂ = x₃) := by
  rw [realDiscriminant_eq_root_form a x₁ x₂ x₃ b c d hb hc hd, mul_eq_zero]
  constructor
  · rintro (h | h)
    · exact absurd h (pow_ne_zero 4 ha)
    · have hp : (x₁ - x₂) * (x₁ - x₃) * (x₂ - x₃) = 0 := pow_eq_zero_iff (by norm_num) |>.mp h
      rcases mul_eq_zero.mp hp with h2 | h2
      · rcases mul_eq_zero.mp h2 with h3 | h3
        · exact Or.inl (sub_eq_zero.mp h3)
        · exact Or.inr (Or.inl (sub_eq_zero.mp h3))
      · exact Or.inr (Or.inr (sub_eq_zero.mp h2))
  · intro h
    refine Or.inr ?_
    rcases h with h | h | h <;> subst h <;> ring

/-! ## Part 3: The conjugate-pair case — `Δ < 0`

If the roots are one real `r` and a non-real conjugate pair `m ± n·i`, the Vieta coefficients
are real and the discriminant collapses to a manifestly nonpositive real form. -/

/-- **The conjugate-pair discriminant identity.** A real cubic with roots `r` (real) and the
conjugate pair `m ± n·i` has Vieta coefficients `b = −a(r+2m)`, `c = a(2rm + m²+n²)`,
`d = −a·r(m²+n²)`, and its discriminant is the pure real expression

  `Δ = −4·a⁴·n²·((r−m)² + n²)²`.

The sign-flipping factor `−4n²` is exactly `(w − w̄)² = (2n·i)²`. -/
theorem realDiscriminant_conj_pair (a r m n : ℝ) :
    realDiscriminant a (-a * (r + 2 * m)) (a * (2 * r * m + (m ^ 2 + n ^ 2)))
        (-a * (r * (m ^ 2 + n ^ 2)))
      = -4 * a ^ 4 * n ^ 2 * ((r - m) ^ 2 + n ^ 2) ^ 2 := by
  unfold realDiscriminant
  ring

/-- **A real root plus a non-real conjugate pair force `Δ < 0`** — the second leg of the
discriminant test. The hypothesis `n ≠ 0` is exactly "the pair is genuinely non-real". -/
theorem realDiscriminant_neg_of_conj_pair (a r m n : ℝ) (ha : a ≠ 0) (hn : n ≠ 0) :
    realDiscriminant a (-a * (r + 2 * m)) (a * (2 * r * m + (m ^ 2 + n ^ 2)))
        (-a * (r * (m ^ 2 + n ^ 2))) < 0 := by
  rw [realDiscriminant_conj_pair]
  have h1 : 0 < a ^ 4 := pow4_pos ha
  have h2 : 0 < n ^ 2 := by positivity
  have h3 : 0 < ((r - m) ^ 2 + n ^ 2) ^ 2 := by positivity
  nlinarith [mul_pos (mul_pos h1 h2) h3]

/-! ## Part 4: The bridge — the parametrization is the complex root form

We certify that the conjugate-pair coefficients above are genuinely the Vieta data of the three
complex roots `r, w, w̄` with `w = m + n·i`, by casting to `ℂ` and invoking the sibling's
`generalDiscriminant_eq_root_form`. The three Vieta equalities are checked componentwise. -/

set_option linter.unusedSimpArgs false in
/-- **Bridge to complex conjugate roots.** With `w = m + n·i`, the real cubic of
`realDiscriminant_conj_pair` is exactly the cubic with roots `r, w, w̄`: casting to `ℂ`, its
discriminant equals the sibling's complex root form `a⁴·((r−w)(r−w̄)(w−w̄))²`. This shows the
negativity is caused by the genuine non-real pair `w, w̄`. -/
theorem realDiscriminant_conj_pair_root_form (a r m n : ℝ) :
    (realDiscriminant a (-a * (r + 2 * m)) (a * (2 * r * m + (m ^ 2 + n ^ 2)))
        (-a * (r * (m ^ 2 + n ^ 2))) : ℂ)
      = (a : ℂ) ^ 4 *
          (((r : ℂ) - ((m : ℂ) + (n : ℂ) * Complex.I)) *
            ((r : ℂ) - (starRingEnd ℂ) ((m : ℂ) + (n : ℂ) * Complex.I)) *
            (((m : ℂ) + (n : ℂ) * Complex.I) -
              (starRingEnd ℂ) ((m : ℂ) + (n : ℂ) * Complex.I))) ^ 2 := by
  rw [realDiscriminant_cast]
  -- `apply` unifies the roots as `r, w, w̄` (`w = m + n·i`) from the right-hand side, leaving the
  -- three Vieta equalities `b = -a·e₁`, `c = a·e₂`, `d = -a·e₃`. Each is checked componentwise
  -- (`re`/`im` — keeping the real coefficients under the `ℝ → ℂ` cast) and closed by `ring`.
  apply generalDiscriminant_eq_root_form <;>
    (apply Complex.ext <;>
      simp only [Complex.neg_re, Complex.neg_im, Complex.add_re, Complex.add_im, Complex.sub_re,
        Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
        Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im] <;>
      ring)

/-! ## Part 5: Sanity checks — the discriminant test on worked cubics -/

/-- `x³ − x = x(x−1)(x+1)`: three distinct real roots `0, 1, −1`, so `Δ = 4 > 0`. -/
example : realDiscriminant 1 0 (-1) 0 = 4 := by unfold realDiscriminant; norm_num

example : 0 < realDiscriminant 1 0 (-1) 0 := by unfold realDiscriminant; norm_num

/-- `x³ + x = x(x²+1)`: real root `0` and the conjugate pair `±i`, so `Δ = −4 < 0`. This is the
`r = 0, m = 0, n = 1` instance of `realDiscriminant_conj_pair`: `−4·1·1·(0+1)² = −4`. -/
example : realDiscriminant 1 0 1 0 = -4 := by unfold realDiscriminant; norm_num

example : realDiscriminant 1 0 1 0 < 0 := by unfold realDiscriminant; norm_num

/-- `x³ − 3x + 2 = (x−1)²(x+2)`: a repeated real root, so `Δ = 0` (the boundary of the test). -/
example : realDiscriminant 1 0 (-3) 2 = 0 := by unfold realDiscriminant; norm_num

end SolutionOfCubicOQ01OQ02

-- Summary of key results
#check SolutionOfCubicOQ01OQ02.realDiscriminant_pos_of_distinct_real_roots
#check SolutionOfCubicOQ01OQ02.realDiscriminant_neg_of_conj_pair
#check SolutionOfCubicOQ01OQ02.realDiscriminant_eq_zero_iff_repeated_real
#check SolutionOfCubicOQ01OQ02.realDiscriminant_conj_pair
#check SolutionOfCubicOQ01OQ02.realDiscriminant_conj_pair_root_form
