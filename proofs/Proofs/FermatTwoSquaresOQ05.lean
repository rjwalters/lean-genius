/-
  Sum-of-Two-Squares Obstruction: n ≡ 3 (mod 4) Is Never x² + y²
  Open Question: fermat-two-squares-oq-05

  Fermat's two-squares theorem (Mathlib's `Nat.Prime.sq_add_sq`) supplies the
  SUFFICIENT direction: every prime p with p % 4 ≠ 3 is a sum of two squares.
  This file supplies the matching NECESSARY direction — the elementary
  congruence obstruction.

  The mechanism is a "local obstruction": a single modulus (4) kills the
  global Diophantine equation n = x² + y². Every square is ≡ 0 or 1 (mod 4),
  so a sum of two squares is ≡ 0, 1, or 2 (mod 4) and can NEVER be ≡ 3 (mod 4).

  Combining the two directions sharpens Fermat's classification to a
  biconditional for primes:

        (∃ a b, a² + b² = p)  ↔  p % 4 ≠ 3.

  References:
  - Fermat (1640): two-squares characterization for primes
  - FermatTwoSquares.lean: parent two-squares characterization
  - FermatTwoSquaresOQ01.lean: Lagrange four-squares extension
-/

import Mathlib.NumberTheory.SumTwoSquares
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

namespace FermatTwoSquaresOQ05

-- ============================================================================
-- Part I: The Core Local Obstruction over ZMod 4
-- ============================================================================

/-- **Squares mod 4.** Every element of `ZMod 4` squares to `0` or `1`.
This is the arithmetic heart of the obstruction. -/
theorem sq_mem_zero_one (a : ZMod 4) : a ^ 2 = 0 ∨ a ^ 2 = 1 := by
  revert a; decide

/-- **The core obstruction.** No sum of two squares equals `3` in `ZMod 4`.
Since each square is `0` or `1`, the possible values of `a² + b²` are
`{0, 1, 2}` — never `3`. Verified by exhaustive check over the 16 pairs. -/
theorem zmod_four_sq_add_sq_ne_three (a b : ZMod 4) : a ^ 2 + b ^ 2 ≠ 3 := by
  revert a b; decide

-- ============================================================================
-- Part II: The Obstruction over ℤ (Int.ModEq form)
-- ============================================================================

/-- **Integer obstruction.** For all integers `a, b`, the sum `a² + b²` is never
congruent to `3` modulo `4`. This is the cleanest statement of the local
obstruction: it is a property of the equation, independent of any target `n`. -/
theorem int_sq_add_sq_not_three_mod_four (a b : ℤ) :
    ¬ (a ^ 2 + b ^ 2 ≡ 3 [ZMOD 4]) := by
  intro h
  -- Transport the congruence into ZMod 4, where it becomes a finite check.
  have h2 : ((a ^ 2 + b ^ 2 : ℤ) : ZMod 4) = ((3 : ℤ) : ZMod 4) := by
    rw [ZMod.intCast_eq_intCast_iff]
    exact_mod_cast h
  push_cast at h2
  exact zmod_four_sq_add_sq_ne_three (a : ZMod 4) (b : ZMod 4) h2

/-- **No integer `≡ 3 (mod 4)` is a sum of two integer squares.** -/
theorem int_not_sq_add_sq_of_mod_four {n : ℤ} (hn : n ≡ 3 [ZMOD 4]) :
    ¬ ∃ x y : ℤ, n = x ^ 2 + y ^ 2 := by
  rintro ⟨x, y, rfl⟩
  exact int_sq_add_sq_not_three_mod_four x y hn

-- ============================================================================
-- Part III: The Obstruction over ℕ
-- ============================================================================

/-- **Natural-number obstruction.** If `n % 4 = 3`, then `n` is not a sum of two
natural-number squares. This is the form most directly comparable to Fermat's
two-squares theorem. -/
theorem not_sq_add_sq_of_mod_four_eq_three {n : ℕ} (hn : n % 4 = 3) :
    ¬ ∃ x y : ℕ, n = x ^ 2 + y ^ 2 := by
  rintro ⟨x, y, rfl⟩
  -- Push the hypothesis `(x²+y²) % 4 = 3` into `ZMod 4`.
  have hcast : ((x ^ 2 + y ^ 2 : ℕ) : ZMod 4) = 3 := by
    have h : ((x ^ 2 + y ^ 2 : ℕ) : ZMod 4) = ((3 : ℕ) : ZMod 4) :=
      (ZMod.natCast_eq_natCast_iff' _ _ _).mpr (by omega)
    simpa using h
  push_cast at hcast
  exact zmod_four_sq_add_sq_ne_three (x : ZMod 4) (y : ZMod 4) hcast

-- ============================================================================
-- Part IV: Prime Case and the Biconditional Sharpening
-- ============================================================================

/-- **No prime `≡ 3 (mod 4)` is a sum of two squares.** A direct specialization
of the natural-number obstruction; stated separately because it is the half of
Fermat's classification that Mathlib does not ship. -/
theorem prime_not_sq_add_sq_of_mod_four {p : ℕ} (hp : p % 4 = 3) :
    ¬ ∃ x y : ℕ, p = x ^ 2 + y ^ 2 :=
  not_sq_add_sq_of_mod_four_eq_three hp

/-- **Fermat's two-squares theorem as a biconditional (for primes).**

Mathlib's `Nat.Prime.sq_add_sq` gives `p % 4 ≠ 3 → ∃ a b, a² + b² = p` (the
sufficient direction). Combining it with the obstruction of Part III closes the
loop:

        a prime `p` is a sum of two squares  ↔  `p % 4 ≠ 3`.

For odd primes this is exactly Fermat's classical statement
`p = x² + y² ↔ p ≡ 1 (mod 4)`, since an odd prime has `p % 4 ∈ {1, 3}`. -/
theorem prime_sq_add_sq_iff_mod_four_ne_three (p : ℕ) [Fact p.Prime] :
    (∃ a b : ℕ, a ^ 2 + b ^ 2 = p) ↔ p % 4 ≠ 3 := by
  constructor
  · rintro ⟨a, b, hab⟩ hp3
    -- A representation contradicts the mod-4 obstruction.
    exact not_sq_add_sq_of_mod_four_eq_three hp3 ⟨a, b, hab.symm⟩
  · intro hp
    exact Nat.Prime.sq_add_sq hp

/-- **Fermat's classification for odd primes.** For an odd prime `p`, being a
sum of two squares is equivalent to `p ≡ 1 (mod 4)`. This is the canonical
"iff" form, obtained from the biconditional above by noting an odd prime has
residue `1` or `3` modulo `4`. -/
theorem odd_prime_sq_add_sq_iff_mod_four_eq_one (p : ℕ) [Fact p.Prime]
    (hodd : Odd p) : (∃ a b : ℕ, a ^ 2 + b ^ 2 = p) ↔ p % 4 = 1 := by
  rw [prime_sq_add_sq_iff_mod_four_ne_three]
  -- An odd number is `1` or `3` mod 4; rule out `3`.
  rcases hodd with ⟨k, hk⟩
  omega

-- ============================================================================
-- Part V: Concrete Witnesses
-- ============================================================================

/-- `3` is not a sum of two squares (smallest example of the obstruction). -/
theorem three_not_sq_add_sq : ¬ ∃ x y : ℕ, (3 : ℕ) = x ^ 2 + y ^ 2 :=
  not_sq_add_sq_of_mod_four_eq_three (by norm_num)

/-- `7` is not a sum of two squares. -/
theorem seven_not_sq_add_sq : ¬ ∃ x y : ℕ, (7 : ℕ) = x ^ 2 + y ^ 2 :=
  not_sq_add_sq_of_mod_four_eq_three (by norm_num)

/-- The prime `11 ≡ 3 (mod 4)` is not a sum of two squares. -/
theorem eleven_not_sq_add_sq : ¬ ∃ x y : ℕ, (11 : ℕ) = x ^ 2 + y ^ 2 :=
  prime_not_sq_add_sq_of_mod_four (by norm_num)

/-- By contrast, `5 ≡ 1 (mod 4)` IS a sum of two squares: `5 = 1² + 2²`. -/
theorem five_is_sq_add_sq : ∃ x y : ℕ, (5 : ℕ) = x ^ 2 + y ^ 2 :=
  ⟨1, 2, by norm_num⟩

/-- And `13 = 2² + 3²`, confirming the sufficient direction for `13 ≡ 1 (mod 4)`. -/
theorem thirteen_is_sq_add_sq : ∃ x y : ℕ, (13 : ℕ) = x ^ 2 + y ^ 2 :=
  ⟨2, 3, by norm_num⟩

end FermatTwoSquaresOQ05
