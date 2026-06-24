/-
  # Per-leg divisibility in primitive Pythagorean triples
  # (pythagorean-triples-oq-08-oq-01)

  ## The Open Question

  The parent entry `pythagorean-triples-oq-08` proves that for *every* Pythagorean
  triple `x² + y² = z²` the product `x · y` is divisible by `12 = 4 · 3` (one leg by
  `4`, one leg by `3`, established only at the level of the **product** `x · y`).

  Its first listed open question asks to *sharpen* this to a per-leg statement for
  **primitive** triples:

  > In a primitive triple, exactly one leg is divisible by `4` and exactly one leg is
  > divisible by `3` (not merely the product) — can the per-leg statement be
  > formalised?

  ## What is proved

  For a primitive triple (`Int.gcd x y = 1`):

  * **`exactly_one_leg_div_four`** — exactly one of the two legs `x, y` is divisible
    by `4`; the other is not. (The even leg is `2mn` with `m, n` of opposite parity,
    hence divisible by `4`; the odd leg `m² − n²` is odd, so not even divisible by `2`.)

  * **`exactly_one_leg_div_three`** — exactly one of the two legs is divisible by `3`;
    the other is not. (A finite `ZMod 3` check shows that, away from the excluded case
    `3 ∣ m ∧ 3 ∣ n` — impossible by coprimality — precisely one of `m² − n²`, `2mn`
    vanishes mod `3`.)

  * **`twelve_dvd_mul`** — the primitive consequence `12 ∣ x · y`, recovered from the
    two per-leg facts via coprimality of `4` and `3`.

  ## Why primitivity is essential

  Without it the per-leg statement is false: `(6, 8, 10) = 2·(3,4,5)` has *both* legs
  even, so the "exactly one leg divisible by 4" claim fails (`4 ∣ 8` and `4 ∤ 6` is
  still fine here, but `(9, 12, 15) = 3·(3,4,5)` has `3 ∣ 9` and `3 ∣ 12`, so "exactly
  one leg divisible by 3" fails). The parent's product-level `12 ∣ x·y` survives
  scaling; the per-leg refinement does not — it is genuinely a statement about
  *primitive* triples.

  ## Method

  Everything is read off Mathlib's Euclid parametrization
  `PythagoreanTriple.coprime_classification`: a primitive triple is, up to swapping the
  legs, `(m² − n², 2mn, ±(m² + n²))` with `Int.gcd m n = 1` and `m, n` of opposite
  parity. The `4`-divisibility is pure algebra on `2mn` and `m² − n²`; the
  `3`-divisibility is a single `decide` over `ZMod 3` transported by
  `ZMod.intCast_zmod_eq_zero_iff_dvd`.

  ## Axiom count: 0  (the `decide` is a kernel decision over `ZMod 3`, no `native_decide`)
-/

import Mathlib

namespace PythagoreanPerLeg

open PythagoreanTriple

variable {x y z : ℤ}

/-! ## Parametrized helpers

The Euclid form has legs `2mn` (even) and `m² − n²` (odd) when `m, n` have opposite
parity, and coprime `m, n`. -/

/-- The even leg `2mn` is divisible by `4`: opposite parity forces one of `m, n` even,
so `mn` is even and `2mn` is a multiple of `4`. -/
theorem four_dvd_two_mul_mul {m n : ℤ}
    (hpar : m % 2 = 0 ∧ n % 2 = 1 ∨ m % 2 = 1 ∧ n % 2 = 0) :
    (4 : ℤ) ∣ 2 * m * n := by
  rcases hpar with ⟨hm, _⟩ | ⟨_, hn⟩
  · obtain ⟨a, ha⟩ := Int.dvd_of_emod_eq_zero hm
    exact ⟨a * n, by rw [ha]; ring⟩
  · obtain ⟨b, hb⟩ := Int.dvd_of_emod_eq_zero hn
    exact ⟨m * b, by rw [hb]; ring⟩

/-- The odd leg `m² − n²` is odd, hence not even divisible by `2`, a fortiori not by
`4`. -/
theorem not_four_dvd_sq_sub {m n : ℤ}
    (hpar : m % 2 = 0 ∧ n % 2 = 1 ∨ m % 2 = 1 ∧ n % 2 = 0) :
    ¬ (4 : ℤ) ∣ (m ^ 2 - n ^ 2) := by
  have hodd : Odd (m ^ 2 - n ^ 2) := by
    rcases hpar with ⟨hm, hn⟩ | ⟨hm, hn⟩
    · have em : Even (m ^ 2) := by rw [pow_two]; exact (Int.even_iff.mpr hm).mul_right m
      have on : Odd (n ^ 2) := (Int.odd_iff.mpr hn).pow
      exact em.sub_odd on
    · have om : Odd (m ^ 2) := (Int.odd_iff.mpr hm).pow
      have en : Even (n ^ 2) := by rw [pow_two]; exact (Int.even_iff.mpr hn).mul_right n
      exact om.sub_even en
  rintro ⟨c, hc⟩
  have hpar2 := Int.odd_iff.mp hodd
  omega

/-- Exactly one of the parametrized legs is divisible by `3`. A finite `ZMod 3` check:
away from the (coprimality-excluded) case `3 ∣ m ∧ 3 ∣ n`, precisely one of
`m² − n²`, `2mn` vanishes mod `3`. -/
theorem three_dvd_exactly_one {m n : ℤ} (hco : Int.gcd m n = 1) :
    ((3 : ℤ) ∣ (m ^ 2 - n ^ 2) ∧ ¬ (3 : ℤ) ∣ (2 * m * n)) ∨
      (¬ (3 : ℤ) ∣ (m ^ 2 - n ^ 2) ∧ (3 : ℤ) ∣ (2 * m * n)) := by
  have dvd_iff : ∀ k : ℤ, (3 : ℤ) ∣ k ↔ ((k : ZMod 3) = 0) := by
    intro k; rw [ZMod.intCast_zmod_eq_zero_iff_dvd]; norm_num
  have cast1 : ((m ^ 2 - n ^ 2 : ℤ) : ZMod 3) = (m : ZMod 3) ^ 2 - (n : ZMod 3) ^ 2 := by
    push_cast; ring
  have cast2 : ((2 * m * n : ℤ) : ZMod 3) = 2 * (m : ZMod 3) * (n : ZMod 3) := by
    push_cast; ring
  have hnot : ¬ ((3 : ℤ) ∣ m ∧ (3 : ℤ) ∣ n) := by
    rintro ⟨h1, h2⟩
    have hu : IsUnit (3 : ℤ) := (Int.isCoprime_iff_gcd_eq_one.mpr hco).isUnit_of_dvd' h1 h2
    rw [Int.isUnit_iff] at hu
    rcases hu with h | h <;> norm_num at h
  have hab : ((m : ZMod 3) ≠ 0 ∨ (n : ZMod 3) ≠ 0) := by
    by_contra h; push_neg at h
    exact hnot ⟨(dvd_iff m).mpr h.1, (dvd_iff n).mpr h.2⟩
  have key : ∀ a b : ZMod 3, (a ≠ 0 ∨ b ≠ 0) →
      ((a ^ 2 - b ^ 2 = 0 ∧ 2 * a * b ≠ 0) ∨ (a ^ 2 - b ^ 2 ≠ 0 ∧ 2 * a * b = 0)) := by
    decide
  rcases key (m : ZMod 3) (n : ZMod 3) hab with ⟨hA, hB⟩ | ⟨hA, hB⟩
  · left
    refine ⟨(dvd_iff _).mpr (by rw [cast1]; exact hA), ?_⟩
    intro hd
    exact hB (by have := (dvd_iff _).mp hd; rwa [cast2] at this)
  · right
    refine ⟨?_, (dvd_iff _).mpr (by rw [cast2]; exact hB)⟩
    intro hd
    exact hA (by have := (dvd_iff _).mp hd; rwa [cast1] at this)

/-! ## Main per-leg theorems -/

/-- **Exactly one leg divisible by 4.** In a primitive Pythagorean triple, exactly one
of the two legs `x, y` is divisible by `4` (the even leg), and the other is not. -/
theorem exactly_one_leg_div_four (h : PythagoreanTriple x y z) (hc : Int.gcd x y = 1) :
    ((4 : ℤ) ∣ x ∧ ¬ (4 : ℤ) ∣ y) ∨ (¬ (4 : ℤ) ∣ x ∧ (4 : ℤ) ∣ y) := by
  obtain ⟨m, n, hxy, _, _, hpar⟩ := PythagoreanTriple.coprime_classification.mp ⟨h, hc⟩
  rcases hxy with ⟨hx, hy⟩ | ⟨hx, hy⟩
  · right
    rw [hx, hy]
    exact ⟨not_four_dvd_sq_sub hpar, four_dvd_two_mul_mul hpar⟩
  · left
    rw [hx, hy]
    exact ⟨four_dvd_two_mul_mul hpar, not_four_dvd_sq_sub hpar⟩

/-- **Exactly one leg divisible by 3.** In a primitive Pythagorean triple, exactly one
of the two legs `x, y` is divisible by `3`, and the other is not. -/
theorem exactly_one_leg_div_three (h : PythagoreanTriple x y z) (hc : Int.gcd x y = 1) :
    ((3 : ℤ) ∣ x ∧ ¬ (3 : ℤ) ∣ y) ∨ (¬ (3 : ℤ) ∣ x ∧ (3 : ℤ) ∣ y) := by
  obtain ⟨m, n, hxy, _, hco, _⟩ := PythagoreanTriple.coprime_classification.mp ⟨h, hc⟩
  rcases hxy with ⟨hx, hy⟩ | ⟨hx, hy⟩
  · rw [hx, hy]; exact three_dvd_exactly_one hco
  · rw [hx, hy]
    rcases three_dvd_exactly_one hco with ⟨hA, hB⟩ | ⟨hA, hB⟩
    · right; exact ⟨hB, hA⟩
    · left; exact ⟨hB, hA⟩

/-- **Primitive consequence `12 ∣ x · y`.** Combining the two per-leg facts (one leg
divisible by `4`, one by `3`) via coprimality of `4` and `3`. The parent proves this
for *all* triples; here it is recovered as a corollary of the sharper per-leg
statement. -/
theorem twelve_dvd_mul (h : PythagoreanTriple x y z) (hc : Int.gcd x y = 1) :
    (12 : ℤ) ∣ x * y := by
  have d4 : (4 : ℤ) ∣ x * y := by
    rcases exactly_one_leg_div_four h hc with ⟨a, _⟩ | ⟨_, a⟩
    · exact a.mul_right y
    · exact a.mul_left x
  have d3 : (3 : ℤ) ∣ x * y := by
    rcases exactly_one_leg_div_three h hc with ⟨a, _⟩ | ⟨_, a⟩
    · exact a.mul_right y
    · exact a.mul_left x
  have hcop : IsCoprime (4 : ℤ) 3 := Int.isCoprime_iff_gcd_eq_one.mpr (by decide)
  have h12 := hcop.mul_dvd d4 d3
  norm_num at h12
  exact h12

/-- Sanity check on the smallest primitive triple `(3, 4, 5)`: leg `4` is the unique
leg divisible by `4`, and leg `3` is the unique leg divisible by `3`. -/
example : (¬ (4 : ℤ) ∣ 3 ∧ (4 : ℤ) ∣ 4) ∧ ((3 : ℤ) ∣ 3 ∧ ¬ (3 : ℤ) ∣ 4) :=
  ⟨⟨by norm_num, by norm_num⟩, ⟨by norm_num, by norm_num⟩⟩

end PythagoreanPerLeg

/-
  ## Summary

  | Result | Statement |
  |--------|-----------|
  | `four_dvd_two_mul_mul`     | opposite parity ⟹ `4 ∣ 2mn` (the even leg) |
  | `not_four_dvd_sq_sub`      | opposite parity ⟹ `4 ∤ m² − n²` (the odd leg) |
  | `three_dvd_exactly_one`    | coprime `m, n` ⟹ exactly one of `m²−n²`, `2mn` is `3`-divisible |
  | `exactly_one_leg_div_four` | primitive triple ⟹ exactly one leg divisible by `4` |
  | `exactly_one_leg_div_three`| primitive triple ⟹ exactly one leg divisible by `3` |
  | `twelve_dvd_mul`           | primitive consequence `12 ∣ x·y` |

  Answers the first open question of `pythagorean-triples-oq-08`: the per-leg
  refinement of the product-level `12 ∣ x·y`, valid for primitive triples and false
  without primitivity.

  **Sorries**: 0
  **Axioms**: 0
-/
