/-
  Sum of Two Squares for All Naturals — the Prime-Factorization Criterion
  Open Question: fermat-two-squares-oq-08

  The parent entry `fermat-two-squares` and sibling `fermat-two-squares-oq-05`
  characterize which PRIMES are sums of two squares (p = x² + y² ⟺ p ≢ 3 mod 4).
  This file promotes that prime-only statement to the full multiplicative
  characterization for EVERY natural number:

        n = x² + y²  for some x, y ∈ ℕ
          ⟺  every prime q ≡ 3 (mod 4) divides n to an EVEN power.

  Examples: 45 = 3²·5 = 6² + 3² is representable (the 3-mod-4 prime 3 occurs to
  the even power 2), while 21 = 3·7 is not (both 3 and 7 are ≡ 3 mod 4 with the
  odd exponent 1).

  The headline biconditional is exactly Mathlib's `Nat.eq_sq_add_sq_iff`. The
  contribution of this file is (i) to present it as the composite/all-naturals
  characterization the parent left open, (ii) to DERIVE the prime case back out
  of the general criterion — showing the two statements are one theorem, not two
  — and (iii) to exercise the criterion on concrete composite witnesses.

  References:
  - Fermat (1640): two-squares characterization for primes
  - FermatTwoSquares.lean: parent prime characterization
  - FermatTwoSquaresOQ05.lean: sibling mod-4 obstruction (necessity)
  - FermatTwoSquaresOQ06.lean: sibling Brahmagupta multiplicativity identity
-/

import Mathlib.NumberTheory.SumTwoSquares
import Mathlib.Tactic

namespace FermatTwoSquaresOQ08

-- ============================================================================
-- Part I: The Headline Criterion (all naturals)
-- ============================================================================

/-- **Sum-of-two-squares criterion for every natural number.**

A natural number `n` is a sum of two squares if and only if, in its prime
factorization, every prime `q ≡ 3 (mod 4)` occurs to an even power
`padicValNat q n`. This is the composite/all-naturals characterization that the
parent entry states as its open question; the prime case (below) is the special
case `n = p`.

This is Mathlib's `Nat.eq_sq_add_sq_iff`; we restate it here as the headline of
the entry and build the prime-case bridge on top of it. -/
theorem sum_two_squares_iff_even_padicVal (n : ℕ) :
    (∃ x y : ℕ, n = x ^ 2 + y ^ 2) ↔
      ∀ q ∈ n.primeFactors, q % 4 = 3 → Even (padicValNat q n) :=
  Nat.eq_sq_add_sq_iff

-- ============================================================================
-- Part II: Recovering the Prime Case from the General Criterion
-- ============================================================================

/-- **The prime case is a corollary of the general criterion.**

For a prime `p`, the only prime factor is `p` itself, occurring to the power
`padicValNat p p = 1`, which is odd. So the criterion of Part I collapses: the
even-exponent condition can only be met by having NO prime factor `≡ 3 (mod 4)`,
i.e. `p % 4 ≠ 3`. This reproduces Fermat's prime classification without invoking
`Nat.Prime.sq_add_sq` — it falls straight out of the all-naturals theorem. -/
theorem prime_sum_two_squares_iff {p : ℕ} (hp : p.Prime) :
    (∃ x y : ℕ, p = x ^ 2 + y ^ 2) ↔ p % 4 ≠ 3 := by
  rw [sum_two_squares_iff_even_padicVal, hp.primeFactors]
  simp only [Finset.mem_singleton, forall_eq]
  constructor
  · -- If representable, the even-exponent condition forces `p % 4 ≠ 3`,
    -- because `padicValNat p p = 1` is odd.
    intro h hp3
    have hev : Even (padicValNat p p) := h hp3
    rw [padicValNat.self hp.one_lt] at hev
    exact Nat.not_even_one hev
  · -- Conversely, if `p % 4 ≠ 3` the hypothesis `p % 4 = 3` is vacuous.
    intro hp4 hp3
    exact absurd hp3 hp4

/-- **Fermat's classical form for odd primes.** For an odd prime `p`, being a sum
of two squares is equivalent to `p ≡ 1 (mod 4)`. Obtained from
`prime_sum_two_squares_iff` by noting an odd prime has residue `1` or `3` mod 4. -/
theorem odd_prime_sum_two_squares_iff {p : ℕ} (hp : p.Prime) (hodd : Odd p) :
    (∃ x y : ℕ, p = x ^ 2 + y ^ 2) ↔ p % 4 = 1 := by
  rw [prime_sum_two_squares_iff hp]
  rcases hodd with ⟨k, hk⟩
  omega

-- ============================================================================
-- Part III: A Divisibility Obstruction at the Prime 3
-- ============================================================================
-- The mod-4 obstruction (oq-05) only rules out `n ≡ 3 (mod 4)`. It says nothing
-- about composites like `21 ≡ 1 (mod 4)` that fail the criterion because a
-- 3-mod-4 prime divides them to an ODD power. We isolate the smallest such case
-- (`q = 3`) with a self-contained argument: since the only squares in ZMod 3 are
-- `{0, 1}`, a sum of two squares vanishes mod 3 only when BOTH summands do, so
-- `3 ∣ x² + y²` forces `3 ∣ x` and `3 ∣ y`, hence `9 ∣ x² + y²`.

/-- **Core fact mod 3.** In `ZMod 3`, a sum of two squares is `0` only when both
squares are `0`. Exhaustive kernel check over the 9 pairs. -/
theorem zmod_three_sq_add_sq_eq_zero (a b : ZMod 3) (h : a ^ 2 + b ^ 2 = 0) :
    a = 0 ∧ b = 0 := by
  revert a b; decide

/-- **The odd-power-of-3 obstruction.** If `3 ∣ n` but `9 ∤ n` (i.e. `3` divides
`n` to an odd power `1`), then `n` is not a sum of two squares. This is the
instance of the general criterion for the prime `q = 3`, proved directly: a
representation would push `3 ∣ x` and `3 ∣ y`, forcing `9 ∣ n`. -/
theorem not_sq_add_sq_of_three_dvd_not_nine_dvd {n : ℕ} (h3 : 3 ∣ n)
    (h9 : ¬ (9 ∣ n)) : ¬ ∃ x y : ℕ, n = x ^ 2 + y ^ 2 := by
  rintro ⟨x, y, rfl⟩
  apply h9
  -- `x² + y² ≡ 0 (mod 3)`, transported to `ZMod 3`.
  have hz : ((x ^ 2 + y ^ 2 : ℕ) : ZMod 3) = 0 :=
    (ZMod.natCast_eq_zero_iff _ 3).mpr h3
  push_cast at hz
  obtain ⟨hx, hy⟩ := zmod_three_sq_add_sq_eq_zero _ _ hz
  -- Both `x` and `y` are divisible by 3.
  rw [ZMod.natCast_eq_zero_iff] at hx hy
  obtain ⟨a, rfl⟩ := hx
  obtain ⟨b, rfl⟩ := hy
  -- Then `(3a)² + (3b)² = 9(a² + b²)`.
  exact ⟨a ^ 2 + b ^ 2, by ring⟩

-- ============================================================================
-- Part IV: Concrete Witnesses
-- ============================================================================

/-- `45 = 3²·5` is a sum of two squares: the 3-mod-4 prime `3` occurs to the even
power `2`. Explicit witness `45 = 6² + 3²`. -/
theorem fortyfive_is_sq_add_sq : ∃ x y : ℕ, (45 : ℕ) = x ^ 2 + y ^ 2 :=
  ⟨6, 3, by norm_num⟩

/-- `50 = 2·5²` is a sum of two squares (no prime `≡ 3 mod 4` divides it at all):
`50 = 5² + 5²`. -/
theorem fifty_is_sq_add_sq : ∃ x y : ℕ, (50 : ℕ) = x ^ 2 + y ^ 2 :=
  ⟨5, 5, by norm_num⟩

/-- `21 = 3·7` is NOT a sum of two squares — even though `21 ≡ 1 (mod 4)`, so the
mod-4 obstruction is silent. The prime `3` divides `21` to the odd power `1`. -/
theorem twentyone_not_sq_add_sq : ¬ ∃ x y : ℕ, (21 : ℕ) = x ^ 2 + y ^ 2 :=
  not_sq_add_sq_of_three_dvd_not_nine_dvd (by norm_num) (by norm_num)

/-- `33 = 3·11` is NOT a sum of two squares: the prime `3` occurs to the odd
power `1` (and `33 ≡ 1 (mod 4)`, so again the mod-4 test alone does not detect it). -/
theorem thirtythree_not_sq_add_sq : ¬ ∃ x y : ℕ, (33 : ℕ) = x ^ 2 + y ^ 2 :=
  not_sq_add_sq_of_three_dvd_not_nine_dvd (by norm_num) (by norm_num)

/-- The prime `7 ≡ 3 (mod 4)` is not a sum of two squares — the prime case,
now read off `prime_sum_two_squares_iff` rather than a bespoke obstruction. -/
theorem seven_not_sq_add_sq : ¬ ∃ x y : ℕ, (7 : ℕ) = x ^ 2 + y ^ 2 := by
  rw [prime_sum_two_squares_iff (by norm_num)]
  norm_num

end FermatTwoSquaresOQ08
