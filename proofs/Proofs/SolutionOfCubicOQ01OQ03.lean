import Mathlib.Tactic

/-!
# Tschirnhaus Depression over a General Field of Characteristic ≠ 3 (Solution of Cubic, OQ-01-OQ-03)

## What This Proves

The parent file `SolutionOfCubicOQ01` proved the **Tschirnhaus shift** `x = t − b/(3a)`,
which depresses a general cubic `a x³ + b x² + c x + d` to `a·(t³ + p t + q)`, but it did so
only over `ℂ`, where `field_simp` discharges the numeral side-conditions `9 ≠ 0`, `27 ≠ 0`
by computation. The parent listed, among its open questions, the request to

> state the reduction over a general field of characteristic ≠ 3, isolating exactly where
> invertibility of 3 is used.

This file answers that question. It ports the reduction to an arbitrary field `K` with
`(3 : K) ≠ 0`, isolating the single concrete obstacle — numeral nonzeroness must now be
*derived* from `3 ≠ 0` via `9 = 3²`, `27 = 3³`, and `pow_ne_zero`. It then proves the sharp
**characteristic-3 boundary**: the `t²`-coefficient changes by exactly `3s` under a shift by
`s`, so when `3 = 0` it is *shift-invariant* — a generic cubic cannot be depressed. This is
the "completing the cube" analogue of needing `2` invertible to complete the square.

## Original Contributions
- `cubic_depress` — the Tschirnhaus reduction over any field with `(3 : K) ≠ 0`.
- `general_root_of_depressed_root` / `depressed_root_of_general_root` — the shift
  `t ↦ t − b/(3a)` is a root bijection (inverse `x ↦ x + b/(3a)`) over the general field.
- `shift_quadratic_coeff` — the exact `t²`-coefficient after a shift `x = t + s` of a monic
  cubic is `3s + b`, over ANY commutative ring.
- `charThree_quadratic_coeff_invariant` — the boundary theorem: when `3 = 0`, every shift
  leaves the quadratic coefficient equal to `b`.
- `depress_iff_three_ne_zero` — a quadratic-killing shift exists iff `b = 0` or `(3 : K) ≠ 0`.

## Proof Techniques
Pure field arithmetic (`field_simp` + `ring`) with the numeral nonzeroness supplied from the
hypothesis; a single universal ring identity (`ring`) for the shift coefficient; elementary
case analysis for the dichotomy. Everything is `0`-axiom and `0`-sorry.
-/

namespace SolutionOfCubicOQ01OQ03

section GeneralField

variable {K : Type*} [Field K]

/-! ## Part 1: The depressed parameters over a general field

Given a general cubic `a x³ + b x² + c x + d` over a field `K`, these are the `p` and `q` of
the depressed cubic obtained from the shift `x = t − b/(3a)` — literally the parent's
ℂ-formulas with `ℂ` replaced by `K`. -/

/-- Linear coefficient of the depressed cubic: `p = (3ac − b²)/(3a²)`. -/
def depressedP (a b c : K) : K := (3 * a * c - b ^ 2) / (3 * a ^ 2)

/-- Constant coefficient of the depressed cubic: `q = (2b³ − 9abc + 27a²d)/(27a³)`. -/
def depressedQ (a b c d : K) : K :=
  (2 * b ^ 3 - 9 * a * b * c + 27 * a ^ 2 * d) / (27 * a ^ 3)

/-! ## Part 2: The core reduction identity over `K`

Substituting `x = t − b/(3a)` into the general cubic gives `a · (t³ + p t + q)`. The only
adaptation from the parent (over `ℂ`) is supplying `9 ≠ 0` and `27 ≠ 0` from `3 ≠ 0`. -/

/-- **The Tschirnhaus shift over a general field.** For a field with `(3 : K) ≠ 0` and
`a ≠ 0`, evaluating `a x³ + b x² + c x + d` at `x = t − b/(3a)` produces `a · (t³ + p t + q)`,
where `p` and `q` are the depressed parameters. The `t²` term has vanished. -/
theorem cubic_depress (a b c d t : K) (h3 : (3 : K) ≠ 0) (ha : a ≠ 0) :
    a * (t - b / (3 * a)) ^ 3 + b * (t - b / (3 * a)) ^ 2 + c * (t - b / (3 * a)) + d
      = a * (t ^ 3 + depressedP a b c * t + depressedQ a b c d) := by
  have h9 : (9 : K) ≠ 0 := by
    have : (9 : K) = 3 ^ 2 := by norm_num
    rw [this]; exact pow_ne_zero 2 h3
  have h27 : (27 : K) ≠ 0 := by
    have : (27 : K) = 3 ^ 3 := by norm_num
    rw [this]; exact pow_ne_zero 3 h3
  unfold depressedP depressedQ
  field_simp
  ring

/-! ## Part 3: Evaluation form and the root bijection

We package the general and depressed cubics as evaluation functions and relate their roots
under the shift. Because `a ≠ 0`, roots transfer in both directions. -/

/-- The general cubic `a x³ + b x² + c x + d` as an evaluation function. -/
def generalCubicEval (a b c d x : K) : K := a * x ^ 3 + b * x ^ 2 + c * x + d

/-- The depressed cubic `t³ + p t + q` as an evaluation function. -/
def depressedCubicEval (p q t : K) : K := t ^ 3 + p * t + q

/-- Evaluation form of the shift: the general cubic at `t − b/(3a)` equals `a` times the
depressed cubic evaluated at `t`. -/
theorem generalCubicEval_shift (a b c d t : K) (h3 : (3 : K) ≠ 0) (ha : a ≠ 0) :
    generalCubicEval a b c d (t - b / (3 * a))
      = a * depressedCubicEval (depressedP a b c) (depressedQ a b c d) t := by
  unfold generalCubicEval depressedCubicEval
  exact cubic_depress a b c d t h3 ha

/-- **Roots descend along the shift.** If `t` is a root of the depressed cubic, then
`t − b/(3a)` is a root of the general cubic. -/
theorem general_root_of_depressed_root (a b c d t : K) (h3 : (3 : K) ≠ 0) (ha : a ≠ 0)
    (ht : depressedCubicEval (depressedP a b c) (depressedQ a b c d) t = 0) :
    generalCubicEval a b c d (t - b / (3 * a)) = 0 := by
  rw [generalCubicEval_shift a b c d t h3 ha, ht, mul_zero]

/-- **Roots lift along the shift.** Conversely, if `x` is a root of the general cubic, then
`t = x + b/(3a)` is a root of the depressed cubic. Together with the previous theorem this
shows `t ↦ t − b/(3a)` is a bijection between the two root sets (inverse `x ↦ x + b/(3a)`). -/
theorem depressed_root_of_general_root (a b c d x : K) (h3 : (3 : K) ≠ 0) (ha : a ≠ 0)
    (hx : generalCubicEval a b c d x = 0) :
    depressedCubicEval (depressedP a b c) (depressedQ a b c d) (x + b / (3 * a)) = 0 := by
  have hshift := generalCubicEval_shift a b c d (x + b / (3 * a)) h3 ha
  rw [add_sub_cancel_right, hx] at hshift
  rcases mul_eq_zero.mp hshift.symm with h | h
  · exact absurd h ha
  · exact h

end GeneralField

/-! ## Part 4: The sharp boundary — characteristic 3

The obstruction to Tschirnhaus reduction is exactly the non-invertibility of `3`, and this is
a *theorem*, not a proof artifact. We work over an arbitrary commutative ring `R`: the
quadratic coefficient after a shift `x = t + s` is `3s + b`, so when `3 = 0` it is fixed. -/

section CommRingBoundary

variable {R : Type*} [CommRing R]

/-- **The universal shift identity.** Over any commutative ring, expanding a monic cubic
`x³ + b x² + c x + d` at `x = t + s` gives a cubic in `t` whose `t²`-coefficient is exactly
`3s + b`. No hypothesis on `3` is needed; this cleanly separates the universal algebra (the
expansion) from the characteristic-dependent conclusion (which shifts are solvable). -/
theorem shift_quadratic_coeff (b c d s t : R) :
    (t + s) ^ 3 + b * (t + s) ^ 2 + c * (t + s) + d
      = t ^ 3 + (3 * s + b) * t ^ 2 + (3 * s ^ 2 + 2 * b * s + c) * t
          + (s ^ 3 + b * s ^ 2 + c * s + d) := by
  ring

/-- **The characteristic-3 boundary.** When `(3 : R) = 0`, the quadratic coefficient `3s + b`
of the shifted cubic equals `b` for *every* shift `s`. Hence in characteristic 3 the
quadratic term is shift-invariant: a cubic with `b ≠ 0` can never be depressed. This is the
"completing the cube" analogue of needing `2` invertible to complete the square. -/
theorem charThree_quadratic_coeff_invariant (h3 : (3 : R) = 0) (b s : R) :
    3 * s + b = b := by
  have hs : (3 : R) * s = 0 := by rw [h3, zero_mul]
  linear_combination hs

end CommRingBoundary

/-! ## Part 5: Iff packaging — existence of a depressing shift

Crystallizing the result as a dichotomy: a quadratic-killing shift (`3s + b = 0`) exists iff
`b = 0` or `(3 : K) ≠ 0`. For a generic cubic (`b ≠ 0`) it exists iff `3` is a unit. -/

section FieldBoundary

variable {K : Type*} [Field K]

/-- When `(3 : K) ≠ 0`, the shift `s = -b/3` kills the quadratic coefficient: `3s + b = 0`. -/
theorem monic_shift_kills_quadratic (h3 : (3 : K) ≠ 0) (b : K) :
    3 * (-b / 3) + b = 0 := by
  have h : (3 : K) * (-b / 3) = -b := by field_simp
  linear_combination h

/-- **The dichotomy.** A quadratic-killing shift `s` (one with `3s + b = 0`) exists iff
`b = 0` or `(3 : K) ≠ 0`. In characteristic 3 only the already-depressed cubics (`b = 0`)
admit such a shift; whenever `3` is a unit, the shift `s = -b/3` always works. -/
theorem depress_iff_three_ne_zero (b : K) :
    (∃ s : K, 3 * s + b = 0) ↔ (b = 0 ∨ (3 : K) ≠ 0) := by
  constructor
  · rintro ⟨s, hs⟩
    by_cases h3 : (3 : K) = 0
    · left
      rw [h3, zero_mul, zero_add] at hs
      exact hs
    · right
      exact h3
  · rintro (hb | h3)
    · exact ⟨0, by rw [mul_zero, zero_add]; exact hb⟩
    · exact ⟨-b / 3, monic_shift_kills_quadratic h3 b⟩

end FieldBoundary

/-! ## Part 6: Sanity checks

Concrete confirmations across characteristic-0 fields (`ℚ`, `ℝ`) and the boundary case
`ZMod 3`. -/

/-- For a *monic* cubic (`a = 1`) over `ℚ`, the depressed `p` is `c − b²/3`. -/
example (b c : ℚ) : depressedP 1 b c = c - b ^ 2 / 3 := by
  unfold depressedP; ring

/-- For a *monic* cubic over `ℚ`, the depressed `q` is `2b³/27 − bc/3 + d`. -/
example (b c d : ℚ) : depressedQ 1 b c d = 2 * b ^ 3 / 27 - b * c / 3 + d := by
  unfold depressedQ; ring

/-- The parent's example `x³ − 6x − 40 = 0` (already depressed) has root `x = 4`, over `ℝ`. -/
example : generalCubicEval (1 : ℝ) 0 (-6) (-40) 4 = 0 := by
  unfold generalCubicEval; norm_num

/-- The full reduction identity instantiated over `ℚ` with `a = 1, b = -3` (shift `x = t+1`). -/
example (c d t : ℚ) :
    (1 : ℚ) * (t - (-3) / (3 * 1)) ^ 3 + (-3) * (t - (-3) / (3 * 1)) ^ 2
        + c * (t - (-3) / (3 * 1)) + d
      = 1 * (t ^ 3 + depressedP 1 (-3) c * t + depressedQ 1 (-3) c d) :=
  cubic_depress 1 (-3) c d t (by norm_num) (by norm_num)

/-- **Characteristic 3 is sharp.** Over `ZMod 3` with `b = 1 ≠ 0`, every shift leaves the
quadratic coefficient equal to `1`: the cubic cannot be depressed. -/
example (s : ZMod 3) : 3 * s + 1 = 1 :=
  charThree_quadratic_coeff_invariant (by decide) 1 s

end SolutionOfCubicOQ01OQ03

-- Summary of key results
#check @SolutionOfCubicOQ01OQ03.cubic_depress
#check @SolutionOfCubicOQ01OQ03.generalCubicEval_shift
#check @SolutionOfCubicOQ01OQ03.general_root_of_depressed_root
#check @SolutionOfCubicOQ01OQ03.depressed_root_of_general_root
#check @SolutionOfCubicOQ01OQ03.shift_quadratic_coeff
#check @SolutionOfCubicOQ01OQ03.charThree_quadratic_coeff_invariant
#check @SolutionOfCubicOQ01OQ03.depress_iff_three_ne_zero
