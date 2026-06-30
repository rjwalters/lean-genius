/-
  # Sixty Divides the Product of a Pythagorean Triple's Sides
  # (pythagorean-triples-oq-08)

  ## The Open Question

  For every Pythagorean triple `x² + y² = z²` in integers, the product `x · y · z`
  of the three sides is divisible by `60 = 4 · 3 · 5`. No primitivity (coprimality)
  hypothesis is required: the divisibility holds for *all* triples, scaled or not.

  ## What is proved

  The result splits into three independent residue obstructions, each verified by a
  finite `decide` over `ZMod n` and then transported to `ℤ` through
  `ZMod.intCast_zmod_eq_zero_iff_dvd`:

  * **`3 ∣ x · y`** — modulo 3 every square is `0` or `1`, so `x² + y² = z²` forces a
    leg to vanish mod 3 (otherwise `z² ≡ 2`, impossible). One *leg* is divisible by 3.

  * **`4 ∣ x · y`** — modulo 4 alone this *fails* (e.g. `(2,1,1)` satisfies the equation
    yet `x·y ≡ 2`); the genuine obstruction lives mod 8. Over `ZMod 8` every solution
    has `x · y ∈ {0, 4}`, which gives `4 ∣ x · y`. One *leg* is divisible by 4.

  * **`5 ∣ x · y · z`** — modulo 5 squares are `0, 1, 4`, and the only way to solve
    `x² + y² = z²` is for some *side* (leg or hypotenuse) to vanish mod 5.

  Combining the coprime factors `3`, `4`, `5` yields the headline `12 ∣ x · y` and
  `60 ∣ x · y · z`.

  ## Why this is new

  The sibling files cover the parametrization (`oq-06`), the parity dichotomy
  (`oq-07`, exactly one even leg), and lattice density (`oq-01`). The 3-, 4- and
  5-divisibility of the product — and especially the mod-8 sharpening that the naive
  mod-4 argument cannot reach — appear nowhere else in the gallery.

  ## Axiom count: 0  (all `decide`, no `native_decide`)
-/

import Mathlib

namespace PythagoreanTriplesSixty

open PythagoreanTriple

variable {x y z : ℤ}

/-! ## Part I: Finite residue obstructions

Each of the following is a complete finite check over the residues `ZMod n`. The
equation `a * a + b * b = c * c` is the image of the integer Pythagorean equation
under the ring map `ℤ → ZMod n`. -/

/-- Mod 3, a leg vanishes: every solution of `a² + b² = c²` has `a · b = 0`.
Squares are `0, 1` mod 3, so two nonzero legs give `c² ≡ 2`, impossible. -/
theorem ab_zero_mod3 : ∀ a b c : ZMod 3, a * a + b * b = c * c → a * b = 0 := by
  decide

/-- Mod 8, a leg is divisible by 4: every solution has `a · b ∈ {0, 4}`.
Modulo 4 alone is insufficient — `(2,1,1)` is a spurious solution with `a·b ≡ 2` —
so the sharp obstruction must be read off mod 8. -/
theorem ab_quarter_mod8 :
    ∀ a b c : ZMod 8, a * a + b * b = c * c → a * b = 0 ∨ a * b = 4 := by
  decide

/-- Mod 5, a side vanishes: every solution of `a² + b² = c²` has `a · b · c = 0`.
Squares are `0, 1, 4` mod 5, and no sum of two nonzero squares is a nonzero square. -/
theorem abc_zero_mod5 : ∀ a b c : ZMod 5, a * a + b * b = c * c → a * b * c = 0 := by
  decide

/-! ## Part II: Casting the equation into `ZMod n`

The Pythagorean equation in `ℤ` maps to the corresponding equation in any `ZMod n`. -/

/-- The Pythagorean equation reduced mod `n`. -/
theorem cast_eq (h : PythagoreanTriple x y z) (n : ℕ) :
    (x : ZMod n) * x + y * y = z * z := by
  have he : x * x + y * y = z * z := h
  have h' : ((x * x + y * y : ℤ) : ZMod n) = ((z * z : ℤ) : ZMod n) := by rw [he]
  push_cast at h'
  exact h'

/-! ## Part III: Integer divisibility of the product -/

/-- A leg of any Pythagorean triple is divisible by 3: `3 ∣ x · y`. -/
theorem three_dvd_legs (h : PythagoreanTriple x y z) : (3 : ℤ) ∣ x * y := by
  have hz : ((x * y : ℤ) : ZMod 3) = 0 := by
    push_cast
    exact ab_zero_mod3 _ _ _ (cast_eq h 3)
  exact_mod_cast (ZMod.intCast_zmod_eq_zero_iff_dvd (x * y) 3).mp hz

/-- A leg of any Pythagorean triple is divisible by 4: `4 ∣ x · y`.
The proof goes through `ZMod 8`, since mod 4 alone does not force this. -/
theorem four_dvd_legs (h : PythagoreanTriple x y z) : (4 : ℤ) ∣ x * y := by
  rcases ab_quarter_mod8 _ _ _ (cast_eq h 8) with h0 | h4
  · -- x·y ≡ 0 (mod 8) ⟹ 8 ∣ x·y ⟹ 4 ∣ x·y
    have hz : ((x * y : ℤ) : ZMod 8) = 0 := by push_cast; exact h0
    have h8 : (8 : ℤ) ∣ x * y := by
      exact_mod_cast (ZMod.intCast_zmod_eq_zero_iff_dvd (x * y) 8).mp hz
    omega
  · -- x·y ≡ 4 (mod 8) ⟹ 8 ∣ (x·y − 4) ⟹ 4 ∣ x·y
    have hz : ((x * y - 4 : ℤ) : ZMod 8) = 0 := by push_cast; rw [h4]; ring
    have h8 : (8 : ℤ) ∣ (x * y - 4) := by
      exact_mod_cast (ZMod.intCast_zmod_eq_zero_iff_dvd (x * y - 4) 8).mp hz
    omega

/-- A side of any Pythagorean triple is divisible by 5: `5 ∣ x · y · z`. -/
theorem five_dvd_sides (h : PythagoreanTriple x y z) : (5 : ℤ) ∣ x * y * z := by
  have hz : ((x * y * z : ℤ) : ZMod 5) = 0 := by
    push_cast
    exact abc_zero_mod5 _ _ _ (cast_eq h 5)
  exact_mod_cast (ZMod.intCast_zmod_eq_zero_iff_dvd (x * y * z) 5).mp hz

/-! ## Part IV: The headline divisibilities

`12 ∣ x · y` from the coprime factors `3` and `4`; then `60 ∣ x · y · z`. -/

/-- **Twelve divides the product of the legs**: `12 ∣ x · y`. -/
theorem twelve_dvd_legs (h : PythagoreanTriple x y z) : (12 : ℤ) ∣ x * y := by
  have cop : IsCoprime (3 : ℤ) 4 := by
    rw [Int.isCoprime_iff_gcd_eq_one]; decide
  have h12 := cop.mul_dvd (three_dvd_legs h) (four_dvd_legs h)
  norm_num at h12
  exact h12

/-- **Sixty divides the product of the three sides**: `60 ∣ x · y · z`,
for every Pythagorean triple, with no coprimality hypothesis. -/
theorem sixty_dvd_product (h : PythagoreanTriple x y z) : (60 : ℤ) ∣ x * y * z := by
  -- 12 ∣ x·y ⟹ 12 ∣ x·y·z
  have h12 : (12 : ℤ) ∣ x * y * z := (twelve_dvd_legs h).mul_right z
  have cop : IsCoprime (12 : ℤ) 5 := by
    rw [Int.isCoprime_iff_gcd_eq_one]; decide
  have h60 := cop.mul_dvd h12 (five_dvd_sides h)
  norm_num at h60
  exact h60

/-! ## Part V: A concrete instance

The smallest triple `(3, 4, 5)` has product `60`, exactly divisible by `60`. -/

/-- `(3, 4, 5)` is a Pythagorean triple. -/
theorem triple_345 : PythagoreanTriple 3 4 5 := by
  unfold PythagoreanTriple; norm_num

/-- The witness: `60 ∣ 3 · 4 · 5`. -/
example : (60 : ℤ) ∣ 3 * 4 * 5 := sixty_dvd_product triple_345

end PythagoreanTriplesSixty
