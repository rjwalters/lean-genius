/-
# The degree-8 annihilating polynomial of √2 + √3 + √5 and its sign-conjugates

(OQ-04 of `sqrt2-plus-sqrt3-plus-sqrt5-irrational`)

The parent entry proves `√2 + √3 + √5` is irrational.  Its open question OQ-04
asks about the multiquadratic field `ℚ(√2, √3, √5)`: it has degree `8` over `ℚ`
with Galois group `(ℤ/2ℤ)³`, and `α := √2 + √3 + √5` is a primitive element whose
minimal polynomial has degree `8`.

This file formalizes the **constructive, elementary backbone** of that statement:

* the explicit degree-8 monic integer polynomial
  `p(x) = x⁸ - 40·x⁶ + 352·x⁴ - 960·x² + 576`,
* the fact that **all eight sign-conjugates** `±√2 ± √3 ± √5` are roots of `p`,
  proved *simultaneously* by one general lemma `conjugate_root`, and
* structural consequences: `p` is even (so roots come in `± r` pairs) and the
  all-plus conjugate `α` is the strict maximum of the eight, hence a simple root
  distinct from the other seven.

## Why one lemma covers all eight conjugates

`p` involves only even powers of `x`, and each sign-conjugate
`u + v + w` with `u = ε₁√2, v = ε₂√3, w = ε₃√5` satisfies
`u² = 2, v² = 3, w² = 5` *regardless of the signs* `εᵢ ∈ {±1}`.  So a single
lemma quantified over reals `u, v, w` with those three square relations proves
`p(u + v + w) = 0` for every choice of signs at once.

## Proof of the core identity — successive squaring

Writing `α = u + v + w` and `A = α² - 6`:

1. `α² - 2αu - 6 = 2vw`            (linear in the square relations);
2. squaring and using `u² = 2`:  `A² + 8α² - 60 = 4αu·A`;
3. squaring again and using `u² = 2`:  `(A² + 8α² - 60)² = 32·α²·A²`,
   which expands (as a pure polynomial in `α`) to `p(α) = 0`.

Every step is discharged by `linear_combination` over the three square relations,
so the whole proof is a sequence of ring identities — no `native_decide`, no
axioms beyond Lean's logical core.

## Honest scope

This establishes that `[ℚ(α):ℚ] ≤ 8` constructively (an explicit degree-8
annihilator).  The complementary **open/hard** content — irreducibility of `p`
(hence degree *exactly* 8), `ℚ`-linear independence of `{√2, √3, √5}`, full
pairwise distinctness of the eight conjugates, and the Galois group `(ℤ/2ℤ)³`
— is **not** formalized here.
-/

import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic

open Real

namespace Sqrt2Sqrt3Sqrt5MultiquadraticOQ04

/-- The explicit degree-8 polynomial
`p(x) = x⁸ - 40·x⁶ + 352·x⁴ - 960·x² + 576`, the minimal polynomial of
`√2 + √3 + √5` over `ℚ`. -/
def minPoly8 (x : ℝ) : ℝ :=
  x ^ 8 - 40 * x ^ 6 + 352 * x ^ 4 - 960 * x ^ 2 + 576

/-- **Core lemma.** For *any* reals `u, v, w` with `u² = 2`, `v² = 3`, `w² = 5`,
the sum `u + v + w` is a root of `p`.  Taking `u = ±√2`, `v = ±√3`, `w = ±√5`
shows all eight sign-conjugates `±√2 ± √3 ± √5` are roots simultaneously. -/
theorem conjugate_root (u v w : ℝ) (hu : u ^ 2 = 2) (hv : v ^ 2 = 3)
    (hw : w ^ 2 = 5) : minPoly8 (u + v + w) = 0 := by
  unfold minPoly8
  -- Step 1: α² - 2αu - 6 = 2vw.
  have h1 : (u + v + w) ^ 2 - 2 * (u + v + w) * u - 6 = 2 * v * w := by
    linear_combination (-1 : ℝ) * hu + hv + hw
  -- Step 2: square step 1; (2vw)² = 4·v²·w² = 60.
  have h2 : ((u + v + w) ^ 2 - 2 * (u + v + w) * u - 6) ^ 2 = 60 := by
    rw [h1]; linear_combination (4 * w ^ 2) * hv + 12 * hw
  -- Step 3: expand the square and substitute u² = 2 to eliminate the odd-in-u term.
  -- With A = α² - 6 :  A² + 8α² - 60 = 4αu·A.
  have h3 : ((u + v + w) ^ 2 - 6) ^ 2 + 8 * (u + v + w) ^ 2 - 60
      = 4 * (u + v + w) * u * ((u + v + w) ^ 2 - 6) := by
    linear_combination h2 - 4 * (u + v + w) ^ 2 * hu
  -- Step 4: square step 3; (4αu·A)² = 16·α²·u²·A² = 32·α²·A².
  have h4 : (((u + v + w) ^ 2 - 6) ^ 2 + 8 * (u + v + w) ^ 2 - 60) ^ 2
      = 32 * (u + v + w) ^ 2 * ((u + v + w) ^ 2 - 6) ^ 2 := by
    linear_combination (((u + v + w) ^ 2 - 6) ^ 2 + 8 * (u + v + w) ^ 2 - 60
        + 4 * (u + v + w) * u * ((u + v + w) ^ 2 - 6)) * h3
        + 16 * (u + v + w) ^ 2 * ((u + v + w) ^ 2 - 6) ^ 2 * hu
  -- Step 5: step 4 expands, as a pure polynomial in α, to p(α) = 0.
  linear_combination h4

/-- `(√2)² = 2`. -/
private theorem sq_sqrt2 : sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
/-- `(√3)² = 3`. -/
private theorem sq_sqrt3 : sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
/-- `(√5)² = 5`. -/
private theorem sq_sqrt5 : sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)

/-- **`α = √2 + √3 + √5` is a root of `p`.**  Hence `α` is an algebraic integer
of degree at most `8` over `ℚ`. -/
theorem sqrt2_sqrt3_sqrt5_root : minPoly8 (sqrt 2 + sqrt 3 + sqrt 5) = 0 :=
  conjugate_root _ _ _ sq_sqrt2 sq_sqrt3 sq_sqrt5

/-- A concrete sign-conjugate: `√2 - √3 + √5` is also a root of `p`. -/
theorem conjugate_pmp_root : minPoly8 (sqrt 2 - sqrt 3 + sqrt 5) = 0 := by
  have h : sqrt 2 - sqrt 3 + sqrt 5 = sqrt 2 + (-sqrt 3) + sqrt 5 := by ring
  rw [h]
  refine conjugate_root _ _ _ sq_sqrt2 ?_ sq_sqrt5
  rw [neg_pow, sq_sqrt3]; norm_num

/-- The fully-negated conjugate `-√2 - √3 - √5 = -α` is a root of `p`. -/
theorem conjugate_neg_root : minPoly8 (-(sqrt 2 + sqrt 3 + sqrt 5)) = 0 := by
  have h : -(sqrt 2 + sqrt 3 + sqrt 5) = (-sqrt 2) + (-sqrt 3) + (-sqrt 5) := by ring
  rw [h]
  refine conjugate_root _ _ _ ?_ ?_ ?_
  · rw [neg_pow, sq_sqrt2]; norm_num
  · rw [neg_pow, sq_sqrt3]; norm_num
  · rw [neg_pow, sq_sqrt5]; norm_num

/-- `p` is an **even** polynomial: `p(-x) = p(x)`.  (It involves only even
powers of `x`.) -/
theorem minPoly8_even (x : ℝ) : minPoly8 (-x) = minPoly8 x := by
  unfold minPoly8; ring

/-- Roots of `p` come in `± r` pairs: if `r` is a root then so is `-r`.  This is
the analytic shadow of the sign-flip symmetry `√k ↦ -√k` of the conjugates. -/
theorem root_neg {r : ℝ} (hr : minPoly8 r = 0) : minPoly8 (-r) = 0 := by
  rw [minPoly8_even]; exact hr

/-- **Strict maximality of the all-plus conjugate.**  Any sign-conjugate
`s₂·√2 + s₃·√3 + s₅·√5` with coefficients `≤ 1` and at least one coefficient
`< 1` is strictly smaller than `α = √2 + √3 + √5`.  In particular each of the
seven proper sign-conjugates `ε₁√2 + ε₂√3 + ε₃√5 ≠ √2 + √3 + √5` is `< α`. -/
theorem conjugate_lt_alpha (s₂ s₃ s₅ : ℝ) (h₂ : s₂ ≤ 1) (h₃ : s₃ ≤ 1)
    (h₅ : s₅ ≤ 1) (hne : s₂ < 1 ∨ s₃ < 1 ∨ s₅ < 1) :
    s₂ * sqrt 2 + s₃ * sqrt 3 + s₅ * sqrt 5 < sqrt 2 + sqrt 3 + sqrt 5 := by
  have p2 : (0 : ℝ) < sqrt 2 := sqrt_pos.mpr (by norm_num)
  have p3 : (0 : ℝ) < sqrt 3 := sqrt_pos.mpr (by norm_num)
  have p5 : (0 : ℝ) < sqrt 5 := sqrt_pos.mpr (by norm_num)
  -- Each term is `≤` the all-plus term; a strict coefficient makes its term strict.
  have b2 : s₂ * sqrt 2 ≤ sqrt 2 := by nlinarith
  have b3 : s₃ * sqrt 3 ≤ sqrt 3 := by nlinarith
  have b5 : s₅ * sqrt 5 ≤ sqrt 5 := by nlinarith
  rcases hne with h | h | h
  · have : s₂ * sqrt 2 < sqrt 2 := by nlinarith
    linarith
  · have : s₃ * sqrt 3 < sqrt 3 := by nlinarith
    linarith
  · have : s₅ * sqrt 5 < sqrt 5 := by nlinarith
    linarith

/-- **Consequence: `α` is a simple root, distinct from its seven proper
conjugates.**  No sign-conjugate other than the all-plus one equals `α`, since
each is strictly smaller. -/
theorem alpha_ne_proper_conjugate (s₂ s₃ s₅ : ℝ) (h₂ : s₂ ≤ 1) (h₃ : s₃ ≤ 1)
    (h₅ : s₅ ≤ 1) (hne : s₂ < 1 ∨ s₃ < 1 ∨ s₅ < 1) :
    s₂ * sqrt 2 + s₃ * sqrt 3 + s₅ * sqrt 5 ≠ sqrt 2 + sqrt 3 + sqrt 5 :=
  ne_of_lt (conjugate_lt_alpha s₂ s₃ s₅ h₂ h₃ h₅ hne)

end Sqrt2Sqrt3Sqrt5MultiquadraticOQ04
