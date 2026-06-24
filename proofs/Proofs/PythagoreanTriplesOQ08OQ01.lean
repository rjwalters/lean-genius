/-
  # Per-Leg Divisibility in a Primitive Pythagorean Triple
  # (pythagorean-triples-oq-08-oq-01)

  ## The Open Question

  The parent entry `pythagorean-triples-oq-08` proves the *product*-level
  divisibilities `3 ∣ x·y`, `4 ∣ x·y` and `60 ∣ x·y·z` for **every** Pythagorean
  triple. Its first listed open question asks to *sharpen* this:

  > In a primitive triple exactly one leg is divisible by `4` and exactly one leg
  > by `3` (not merely the product). Can the per-leg statement be formalised?

  This file answers it. Under the primitivity hypothesis `IsCoprime x y`:

  * **`exactly_one_leg_div_four`** — exactly one of the legs `x`, `y` is divisible
    by `4`. (The product result `4 ∣ x·y` only says the legs *together* carry four
    factors of two; it does not pin them onto one leg.)

  * **`exactly_one_leg_div_three`** — exactly one of the legs is divisible by `3`.

  ## Why primitivity is essential

  Both sharpenings *fail* without coprimality. For the scaled triple `(6, 8, 10)`
  (= `2·(3,4,5)`) both legs are even and `4 ∣ 6·8`, yet `4 ∣ 8` while `4 ∤ 6` — here
  it still happens to be one leg, but for `(9, 12, 15)` we have `3 ∣ 9` *and*
  `3 ∣ 12`, so the per-leg "exactly one" statement is genuinely false without
  primitivity. The coprimality hypothesis forbids a common factor and forces the
  obstruction onto a single leg.

  ## Proof idea

  Everything reduces to the parent's product divisibilities plus the key
  consequence of `IsCoprime x y`: a prime cannot divide both legs (else it would be
  a unit). Concretely, for the factor `4`:

  * `4 ∣ x·y` ⟹ `2 ∣ x·y` ⟹ (prime `2`) one leg is even;
  * coprimality ⟹ the other leg is odd, hence coprime to `4`;
  * cancelling the odd leg out of `4 ∣ x·y` lands all four factors of two on the
    even leg, giving `4 ∣` (even leg) and `4 ∤` (odd leg).

  For `3` the argument is the bare prime/coprime split of `3 ∣ x·y`.

  ## Axiom count: 0
-/

import Mathlib
import Proofs.PythagoreanTriplesOQ08

namespace PythagoreanTriplesPerLeg

open PythagoreanTriple PythagoreanTriplesSixty

variable {x y z : ℤ}

/-- In a primitive triple a prime cannot divide both legs: it would have to be a
unit, but `2` and `3` (and indeed every prime of `ℤ`) are non-units. -/
theorem not_dvd_both_of_coprime {p : ℤ} (hp : Prime p) (hcop : IsCoprime x y) :
    ¬ (p ∣ x ∧ p ∣ y) := by
  rintro ⟨hx, hy⟩
  exact hp.not_unit (hcop.isUnit_of_dvd' hx hy)

/-! ## Divisibility by three -/

/-- **Exactly one leg is divisible by `3`** in a primitive Pythagorean triple.
The parent gives `3 ∣ x·y`; primitivity forbids `3` from dividing both legs. -/
theorem exactly_one_leg_div_three
    (h : PythagoreanTriple x y z) (hcop : IsCoprime x y) :
    (3 ∣ x ∧ ¬ (3 ∣ y)) ∨ (¬ (3 ∣ x) ∧ 3 ∣ y) := by
  have h3 : (3 : ℤ) ∣ x * y := three_dvd_legs h
  have hnb : ¬ ((3 : ℤ) ∣ x ∧ (3 : ℤ) ∣ y) := not_dvd_both_of_coprime Int.prime_three hcop
  rcases Int.prime_three.dvd_or_dvd h3 with hx | hy
  · exact Or.inl ⟨hx, fun hy => hnb ⟨hx, hy⟩⟩
  · exact Or.inr ⟨fun hx => hnb ⟨hx, hy⟩, hy⟩

/-! ## Divisibility by four -/

/-- The even leg of a primitive triple is divisible by `4`, the odd one is not.
This is the heart of the `4`-sharpening: cancelling the odd (hence `4`-coprime) leg
out of `4 ∣ x·y` forces all four factors of two onto the even leg. -/
theorem four_dvd_even_leg
    (h4 : (4 : ℤ) ∣ x * y) (hodd : ¬ (2 : ℤ) ∣ y) :
    (4 : ℤ) ∣ x := by
  -- `2` is coprime to the odd leg `y`, hence so is `4 = 2·2`.
  have hc2 : IsCoprime (2 : ℤ) y := (Int.prime_two.coprime_iff_not_dvd).mpr hodd
  have hc4 : IsCoprime (4 : ℤ) y := by
    have : (4 : ℤ) = 2 * 2 := by norm_num
    rw [this]; exact hc2.mul_left hc2
  exact hc4.dvd_of_dvd_mul_right h4

/-- **Exactly one leg is divisible by `4`** in a primitive Pythagorean triple.
The parent gives `4 ∣ x·y`; primitivity forces the four factors of two onto the
single even leg. -/
theorem exactly_one_leg_div_four
    (h : PythagoreanTriple x y z) (hcop : IsCoprime x y) :
    (4 ∣ x ∧ ¬ (4 ∣ y)) ∨ (¬ (4 ∣ x) ∧ 4 ∣ y) := by
  have h4 : (4 : ℤ) ∣ x * y := four_dvd_legs h
  -- At least one leg is even.
  have h2 : (2 : ℤ) ∣ x * y := dvd_trans (by norm_num) h4
  have hnb : ¬ ((2 : ℤ) ∣ x ∧ (2 : ℤ) ∣ y) := not_dvd_both_of_coprime Int.prime_two hcop
  -- `4 ∣ a` forces `2 ∣ a`, so an odd leg is never divisible by `4`.
  have not_four : ∀ {a : ℤ}, ¬ (2 : ℤ) ∣ a → ¬ (4 : ℤ) ∣ a :=
    fun hodd hd => hodd (dvd_trans (by norm_num) hd)
  rcases Int.prime_two.dvd_or_dvd h2 with hx2 | hy2
  · -- `x` even ⟹ `y` odd ⟹ `4 ∣ x`, `4 ∤ y`.
    have hy_odd : ¬ (2 : ℤ) ∣ y := fun hy => hnb ⟨hx2, hy⟩
    exact Or.inl ⟨four_dvd_even_leg h4 hy_odd, not_four hy_odd⟩
  · -- `y` even ⟹ `x` odd ⟹ `4 ∣ y`, `4 ∤ x`.
    have hx_odd : ¬ (2 : ℤ) ∣ x := fun hx => hnb ⟨hx, hy2⟩
    have h4y : (4 : ℤ) ∣ y := four_dvd_even_leg (by rwa [mul_comm] at h4) hx_odd
    exact Or.inr ⟨not_four hx_odd, h4y⟩

/-! ## Capstone -/

/-- **Per-leg sharpening of the parent product divisibilities.** In a primitive
Pythagorean triple exactly one leg is divisible by `4` and exactly one by `3`. -/
theorem per_leg_div_four_and_three
    (h : PythagoreanTriple x y z) (hcop : IsCoprime x y) :
    ((4 ∣ x ∧ ¬ (4 ∣ y)) ∨ (¬ (4 ∣ x) ∧ 4 ∣ y)) ∧
    ((3 ∣ x ∧ ¬ (3 ∣ y)) ∨ (¬ (3 ∣ x) ∧ 3 ∣ y)) :=
  ⟨exactly_one_leg_div_four h hcop, exactly_one_leg_div_three h hcop⟩

/-! ## A concrete instance

For the primitive triple `(3, 4, 5)`: the leg `4` carries the factor of four and
the leg `3` carries the factor of three — the two obstructions sit on *different*
legs here, but the theorem allows them to coincide as well. -/

/-- `(3, 4, 5)` is a primitive Pythagorean triple. -/
theorem coprime_345 : IsCoprime (3 : ℤ) 4 := by
  rw [Int.isCoprime_iff_gcd_eq_one]; decide

example :
    ((4 ∣ (3 : ℤ) ∧ ¬ (4 ∣ (4 : ℤ))) ∨ (¬ (4 ∣ (3 : ℤ)) ∧ 4 ∣ (4 : ℤ))) ∧
    ((3 ∣ (3 : ℤ) ∧ ¬ (3 ∣ (4 : ℤ))) ∨ (¬ (3 ∣ (3 : ℤ)) ∧ 3 ∣ (4 : ℤ))) :=
  per_leg_div_four_and_three triple_345 coprime_345

end PythagoreanTriplesPerLeg
