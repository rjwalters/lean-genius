/-
  The Composition Boundary: Sums of Three Squares are NOT Multiplicatively Closed
  Open Question: fermat-two-squares-oq-01-oq-01

  The parent entry `fermat-two-squares-oq-01` (Lagrange's Four Squares Theorem)
  records Euler's four-square identity — the multiplicativity that reduces Lagrange
  to the prime case — and asks (open question #4):

    "What is the formal relationship between the Cayley–Dickson construction
     (reals → complex → quaternions → octonions) and the existence of
     n-square identities?"

  The Cayley–Dickson ladder produces *normed composition algebras* — and hence
  multiplicative n-square identities — in exactly the dimensions n = 1, 2, 4, 8
  (Hurwitz's theorem). Concretely:

    * n = 1: x² · y² = (xy)²                         (perfect squares)
    * n = 2: Brahmagupta–Fibonacci  (Mathlib: `sq_add_sq_mul_sq_add_sq`)
    * n = 4: Euler's identity        (Mathlib: `sum_four_sq_mul_sum_four_sq`)
    * n = 8: Degen's identity        (Mathlib: `sum_eight_sq_mul_sum_eight_sq`)

  This file pins down the *sharp boundary*: the very first dimension NOT in the
  list, n = 3, genuinely fails. The set of naturals representable as a sum of
  three squares is **not** closed under multiplication — so there is no
  three-square composition identity. We exhibit the smallest obstruction:

    3 = 1² + 1² + 1²,   5 = 0² + 1² + 2²,   but   3 · 5 = 15 is NOT a sum of
    three squares.

  The obstruction is the classical mod-8 congruence (the easy direction of
  Legendre's three-square theorem): no sum of three squares is ≡ 7 (mod 8), and
  15 ≡ 7 (mod 8). We contrast this with the n = 2 case, where multiplicative
  closure DOES hold (Brahmagupta–Fibonacci), making the n = 2 vs n = 3 dichotomy
  explicit.

  ## Honest scope
  The positive direction for n = 2 is Mathlib's `Nat.sq_add_sq_mul`. The n = 3
  *failure* (non-closure, via the mod-8 obstruction and the explicit witness 15)
  is the original content here. The full Legendre three-square theorem
  (n is a sum of three squares ⟺ n ≠ 4^a(8b+7)) — the deep "iff" — is not proved;
  only the easy modular obstruction it relies on. Likewise Hurwitz's theorem
  (composition algebras exist *only* in dimensions 1,2,4,8) is the surrounding
  context, not formalized here.

  References:
  - Legendre (1798): three-square theorem
  - Hurwitz (1898): the 1,2,4,8 theorem on normed composition algebras
  - FermatTwoSquaresOQ01.lean: parent (Lagrange + Euler's four-square identity)
-/

import Mathlib

namespace FermatTwoSquaresOQ01OQ01

/-- `n` is a sum of two squares. -/
def IsSumOfTwoSquares (n : ℕ) : Prop := ∃ a b : ℕ, a ^ 2 + b ^ 2 = n

/-- `n` is a sum of three squares. -/
def IsSumOfThreeSquares (n : ℕ) : Prop := ∃ a b c : ℕ, a ^ 2 + b ^ 2 + c ^ 2 = n

-- ============================================================================
-- Part I: n = 2 — multiplicative closure (the composition that DOES exist)
-- ============================================================================

/-- **Sums of two squares are multiplicatively closed.**

This is the number-theoretic shadow of the Brahmagupta–Fibonacci identity
`(a²+b²)(c²+d²) = (ac−bd)² + (ad+bc)²` — equivalently, multiplicativity of the
complex norm `|z·w|² = |z|²·|w|²`. It is the n = 2 rung of the Cayley–Dickson
ladder. Delegated to Mathlib's `Nat.sq_add_sq_mul`. -/
theorem isSumOfTwoSquares_mul {m n : ℕ}
    (hm : IsSumOfTwoSquares m) (hn : IsSumOfTwoSquares n) :
    IsSumOfTwoSquares (m * n) := by
  obtain ⟨a, b, hab⟩ := hm
  obtain ⟨c, d, hcd⟩ := hn
  obtain ⟨r, s, h⟩ := Nat.sq_add_sq_mul hab.symm hcd.symm
  exact ⟨r, s, h.symm⟩

-- ============================================================================
-- Part II: The mod-8 obstruction for three squares
-- ============================================================================

/-- **No sum of three squares is ≡ 7 (mod 8).**

Squares modulo 8 lie in `{0, 1, 4}`, and no three of these sum to 7 modulo 8.
This is the easy (necessity) half of Legendre's three-square theorem, here
discharged by a finite `decide` over `ZMod 8`. -/
theorem three_sq_ne_seven_mod_eight :
    ∀ a b c : ZMod 8, a ^ 2 + b ^ 2 + c ^ 2 ≠ 7 := by decide

/-- A natural number `≡ 7 (mod 8)` is not a sum of three squares. -/
theorem not_isSumOfThreeSquares_of_mod_eight {n : ℕ} (h : n % 8 = 7) :
    ¬ IsSumOfThreeSquares n := by
  rintro ⟨a, b, c, habc⟩
  -- Push the equation into `ZMod 8`.
  have hcast : (a : ZMod 8) ^ 2 + (b : ZMod 8) ^ 2 + (c : ZMod 8) ^ 2 = (n : ZMod 8) := by
    have := congrArg (Nat.cast : ℕ → ZMod 8) habc
    push_cast at this
    exact this
  -- `(n : ZMod 8) = 7` because `n % 8 = 7`.
  have hn : (n : ZMod 8) = 7 := by
    conv_lhs => rw [← Nat.div_add_mod n 8, h]
    push_cast
    rw [show (8 : ZMod 8) = 0 from by decide]
    ring
  rw [hn] at hcast
  exact three_sq_ne_seven_mod_eight a b c hcast

-- ============================================================================
-- Part III: n = 3 — the composition that does NOT exist
-- ============================================================================

/-- `3 = 1² + 1² + 1²` is a sum of three squares. -/
theorem three_isSumOfThreeSquares : IsSumOfThreeSquares 3 := ⟨1, 1, 1, by norm_num⟩

/-- `5 = 0² + 1² + 2²` is a sum of three squares. -/
theorem five_isSumOfThreeSquares : IsSumOfThreeSquares 5 := ⟨0, 1, 2, by norm_num⟩

/-- `15` is **not** a sum of three squares (it is `≡ 7 mod 8`). -/
theorem fifteen_not_isSumOfThreeSquares : ¬ IsSumOfThreeSquares 15 :=
  not_isSumOfThreeSquares_of_mod_eight (by norm_num)

/-- **The composition boundary at n = 3.**

The set of naturals representable as a sum of three squares is *not* closed under
multiplication: `3` and `5` are each sums of three squares, but their product
`15` is not. Hence there is no "three-square identity" analogous to the
Brahmagupta (n=2), Euler (n=4), or Degen (n=8) identities — exactly as predicted
by Hurwitz's theorem, which permits multiplicative norm forms only in dimensions
1, 2, 4, 8. -/
theorem isSumOfThreeSquares_not_multiplicative :
    ∃ m n : ℕ, IsSumOfThreeSquares m ∧ IsSumOfThreeSquares n ∧
      ¬ IsSumOfThreeSquares (m * n) := by
  refine ⟨3, 5, three_isSumOfThreeSquares, five_isSumOfThreeSquares, ?_⟩
  have h : (3 : ℕ) * 5 = 15 := by norm_num
  rw [h]
  exact fifteen_not_isSumOfThreeSquares

-- ============================================================================
-- Part IV: The dichotomy, packaged
-- ============================================================================

/-- **The n = 2 vs n = 3 dichotomy.**

Sums of two squares form a multiplicatively closed set (the n = 2 composition),
while sums of three squares do not (no n = 3 composition). This is the sharp
boundary the Cayley–Dickson / Hurwitz picture predicts between the "good"
dimensions {1,2,4,8} and the rest. -/
theorem two_squares_closed_three_squares_not :
    (∀ m n : ℕ, IsSumOfTwoSquares m → IsSumOfTwoSquares n → IsSumOfTwoSquares (m * n)) ∧
    (∃ m n : ℕ, IsSumOfThreeSquares m ∧ IsSumOfThreeSquares n ∧
      ¬ IsSumOfThreeSquares (m * n)) :=
  ⟨fun _ _ => isSumOfTwoSquares_mul, isSumOfThreeSquares_not_multiplicative⟩

end FermatTwoSquaresOQ01OQ01

#print axioms FermatTwoSquaresOQ01OQ01.isSumOfThreeSquares_not_multiplicative
#print axioms FermatTwoSquaresOQ01OQ01.two_squares_closed_three_squares_not
#print axioms FermatTwoSquaresOQ01OQ01.isSumOfTwoSquares_mul
