import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
import Mathlib.Tactic

/-
# The Jacobi Symbol on Composite Moduli: Extending the Legendre Algorithm

## Open Question

The parent entry `quadratic-reciprocity-algorithm-oq-01` implements a verified
recursive algorithm `jacobiAlgo` for the symbol J(a | b) with an odd modulus b.
OQ-02 asks: what changes when the modulus b is **composite** — how does the
Jacobi symbol genuinely extend the Legendre symbol, and what is the precise price
of that extension?

## What This File Establishes

The Legendre symbol (a | p) over a prime p is a faithful residuosity test:
(a | p) = 1 ⟺ a is a nonzero square mod p, and (a | p) = −1 ⟺ a is a nonsquare.
The Jacobi symbol J(a | n) over a composite odd n keeps **one** of these
directions and loses the other. Concretely:

* **Multiplicativity in the modulus** (`jacobi_mul_right`):
  J(a | m·n) = J(a | m)·J(a | n). This is the defining feature that turns the
  prime-modulus Legendre symbol into a function of composite moduli.

* **It extends Legendre** (`jacobi_eq_legendre_of_prime`):
  for prime p, J(a | p) = legendreSym p a.

* **The surviving direction** (`nonsquare_of_jacobi_eq_neg_one`):
  J(a | n) = −1 ⟹ a is a nonsquare mod n, for ANY n — a genuine
  nonresidue certificate that needs no primality hypothesis.

* **The lost direction, made precise** (`jacobi_one_not_isSquare`):
  J(a | n) = 1 does NOT imply a is a square mod n once n is composite. The
  canonical witness is a = 2, n = 15: J(2 | 15) = J(2 | 3)·J(2 | 5) =
  (−1)·(−1) = 1, yet 2 is not a square mod 15 (the squares mod 15 are
  {0,1,4,6,9,10}). Over a PRIME modulus this never happens
  (`isSquare_of_jacobi_eq_one_prime`).

* **Why the witness exists** (`jacobi_neg_one_factor`): with n = m·k, a value
  J(a | n) = 1 can arise from J(a | m) = J(a | k) = −1, so a is a nonsquare
  modulo each factor while the product symbol cancels to +1.

All numeric Legendre/Jacobi values are evaluated through the residuosity iff
lemmas (`legendreSym.eq_one_iff`, `legendreSym.eq_neg_one_iff`), which reduce to
kernel-decidable `IsSquare` statements over the small fields `ZMod p` — so there
is no `native_decide` anywhere.

## Status: 0 sorries, 0 `axiom`s, no `native_decide`.
-/

namespace QuadraticReciprocityAlgorithmOQ02

open scoped NumberTheorySymbols

-- ============================================================================
-- Part 1: The Jacobi symbol extends Legendre and is multiplicative in n
-- ============================================================================

/-- The Jacobi symbol agrees with the Legendre symbol on a prime modulus. -/
theorem jacobi_eq_legendre_of_prime (p : ℕ) [Fact p.Prime] (a : ℤ) :
    J(a | p) = legendreSym p a :=
  (jacobiSym.legendreSym.to_jacobiSym p a).symm

/-- **Multiplicativity in the modulus.**  J(a | m·n) = J(a | m)·J(a | n).
    This is what makes the symbol a function of composite moduli at all. -/
theorem jacobi_mul_right (a : ℤ) (m n : ℕ) [NeZero m] [NeZero n] :
    J(a | m * n) = J(a | m) * J(a | n) :=
  jacobiSym.mul_right a m n

/-- Iterated multiplicativity: the Jacobi symbol over a product of three odd
    moduli factors completely. -/
theorem jacobi_mul_right₃ (a : ℤ) (m n k : ℕ) [NeZero m] [NeZero n] [NeZero k] :
    J(a | m * n * k) = J(a | m) * J(a | n) * J(a | k) := by
  rw [jacobi_mul_right, jacobi_mul_right]

-- ============================================================================
-- Part 2: The surviving direction — a nonresidue certificate for composite n
-- ============================================================================

/-- **The certificate that survives compositeness.**  If J(a | n) = −1 then `a`
    is a nonsquare modulo `n`, with no primality hypothesis on `n`. -/
theorem nonsquare_of_jacobi_eq_neg_one {a : ℤ} {n : ℕ} (h : J(a | n) = -1) :
    ¬ IsSquare (a : ZMod n) :=
  ZMod.nonsquare_of_jacobiSym_eq_neg_one h

/-- Contrapositive form: if `a` is a square mod `n`, the Jacobi symbol is not −1. -/
theorem jacobi_ne_neg_one_of_isSquare {a : ℤ} {n : ℕ} (h : IsSquare (a : ZMod n)) :
    J(a | n) ≠ -1 :=
  fun hj => nonsquare_of_jacobi_eq_neg_one hj h

-- ============================================================================
-- Part 3: Prime-modulus values via the residuosity iff lemmas
-- ============================================================================

/-- `J(2 | 3) = −1`: 2 is a nonsquare mod the prime 3. -/
theorem jacobi_two_three : J(2 | 3) = -1 := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  rw [jacobi_eq_legendre_of_prime, legendreSym.eq_neg_one_iff 3 (a := 2)]
  decide +revert

/-- `J(2 | 5) = −1`: 2 is a nonsquare mod the prime 5. -/
theorem jacobi_two_five : J(2 | 5) = -1 := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  rw [jacobi_eq_legendre_of_prime, legendreSym.eq_neg_one_iff 5 (a := 2)]
  decide +revert

/-- `J(2 | 7) = 1`: 2 is a square mod 7 (3² = 9 ≡ 2). -/
theorem jacobi_two_seven : J(2 | 7) = 1 := by
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  rw [jacobi_eq_legendre_of_prime, legendreSym.eq_one_iff 7 (a := 2) (by decide +revert)]
  decide +revert

/-- `J(7 | 3) = 1`: 7 ≡ 1 mod 3 is a square. -/
theorem jacobi_seven_three : J(7 | 3) = 1 := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  rw [jacobi_eq_legendre_of_prime, legendreSym.eq_one_iff 3 (a := 7) (by decide +revert)]
  decide +revert

/-- `J(7 | 5) = −1`: 7 ≡ 2 mod 5 is a nonsquare. -/
theorem jacobi_seven_five : J(7 | 5) = -1 := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  rw [jacobi_eq_legendre_of_prime, legendreSym.eq_neg_one_iff 5 (a := 7)]
  decide +revert

-- ============================================================================
-- Part 4: The lost direction — J = 1 does not certify a square mod composite n
-- ============================================================================

/-- `J(2 | 15) = 1`, from multiplicativity J(2|15) = J(2|3)·J(2|5) = (−1)·(−1).
    Two nonresidue contributions cancel. -/
theorem jacobi_two_fifteen : J(2 | 15) = 1 := by
  rw [show (15 : ℕ) = 3 * 5 from by norm_num, jacobi_mul_right,
    jacobi_two_three, jacobi_two_five]
  norm_num

/-- `2` is not a square modulo `15` (the squares mod 15 are {0,1,4,6,9,10}). -/
theorem two_not_isSquare_mod_fifteen : ¬ IsSquare (2 : ZMod 15) := by decide

/-- **The asymmetry, witnessed.**  There exist `a` and a composite odd `n` with
    J(a | n) = 1 yet `a` not a square mod `n`.  The Legendre symbol over a prime
    never behaves this way (`isSquare_of_jacobi_eq_one_prime`). -/
theorem jacobi_one_not_isSquare :
    ∃ (a : ℤ) (n : ℕ), J(a | n) = 1 ∧ ¬ IsSquare (a : ZMod n) :=
  ⟨2, 15, jacobi_two_fifteen, two_not_isSquare_mod_fifteen⟩

/-- The contrast: over a PRIME modulus, `J(a | p) = 1` does imply `a` is a square.
    This is exactly the direction that fails for composite `n`. -/
theorem isSquare_of_jacobi_eq_one_prime {a : ℤ} {p : ℕ} [Fact p.Prime]
    (h : J(a | p) = 1) : IsSquare (a : ZMod p) :=
  ZMod.isSquare_of_jacobiSym_eq_one h

-- ============================================================================
-- Part 5: Why the witness exists — cancellation across the factorization
-- ============================================================================

/-- The mechanism behind the lost direction: with `n = 3·5`, `J(2 | 15) = 1`
    arises from `J(2 | 3) = J(2 | 5) = −1`, i.e. `2` is a nonsquare modulo each
    prime factor while the product symbol is `+1`. -/
theorem jacobi_neg_one_factor :
    J(2 | 15) = 1 ∧ ¬ IsSquare (2 : ZMod 3) ∧ ¬ IsSquare (2 : ZMod 5) := by
  refine ⟨jacobi_two_fifteen, ?_, ?_⟩
  · exact nonsquare_of_jacobi_eq_neg_one jacobi_two_three
  · exact nonsquare_of_jacobi_eq_neg_one jacobi_two_five

-- ============================================================================
-- Part 6: Worked composite-modulus computations and the surviving direction
-- ============================================================================

/-- `J(7 | 15) = −1` via J(7|3)·J(7|5) = (1)·(−1).  Here the surviving direction
    applies: `7` is a genuine nonsquare mod 15. -/
theorem jacobi_seven_fifteen : J(7 | 15) = -1 := by
  rw [show (15 : ℕ) = 3 * 5 from by norm_num, jacobi_mul_right,
    jacobi_seven_three, jacobi_seven_five]
  norm_num

example : ¬ IsSquare (7 : ZMod 15) :=
  nonsquare_of_jacobi_eq_neg_one jacobi_seven_fifteen

/-- `J(2 | 21) = −1` via J(2|3)·J(2|7) = (−1)·(1), so `2` is a nonsquare mod 21. -/
theorem jacobi_two_twentyone : J(2 | 21) = -1 := by
  rw [show (21 : ℕ) = 3 * 7 from by norm_num, jacobi_mul_right,
    jacobi_two_three, jacobi_two_seven]
  norm_num

example : ¬ IsSquare (2 : ZMod 21) :=
  nonsquare_of_jacobi_eq_neg_one jacobi_two_twentyone

#check @jacobi_mul_right
#check @nonsquare_of_jacobi_eq_neg_one
#check @jacobi_one_not_isSquare
#check @isSquare_of_jacobi_eq_one_prime

end QuadraticReciprocityAlgorithmOQ02
