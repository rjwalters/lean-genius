import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
import Mathlib.Tactic
import Proofs.QuadraticReciprocityAlgorithmOQ02

/-
# Euler's Criterion Breaks on Composites — and That Break Is a Primality Test

## Open Question

The parent entry `quadratic-reciprocity-algorithm-oq-02` showed that, going from
a prime modulus to a composite one, the Jacobi symbol keeps the nonresidue
certificate `J(a | n) = −1 ⟹ a` is a nonsquare, but *loses* the converse
`J(a | n) = 1 ⟹ a` is a square (witness a = 2, n = 15).

OQ-02-OQ-01 asks: there is a second, sharper identity that the Legendre symbol
satisfies — **Euler's criterion** `(a | p) ≡ a^((p−1)/2) (mod p)`. Does the
Jacobi symbol inherit it on composite moduli, and if not, is the failure
*usable*? The answer is the foundation of the **Solovay–Strassen primality
test**: Euler's criterion holds for the Jacobi symbol exactly when the modulus
is prime, so any `a` violating the congruence is a certificate of compositeness.

## What This File Establishes

* **Euler's criterion, Jacobi form, prime modulus** (`jacobi_eq_pow_of_prime`):
  for prime `p`, `(J(a | p) : ZMod p) = a^(p/2)`. This is the prime-only identity;
  it follows from `J(a | p) = legendreSym p a` (parent) and `legendreSym.eq_pow`.

* **The Solovay–Strassen compositeness test** (`not_prime_of_eulerWitness`):
  if some `a` is an *Euler witness* for `n` — i.e. `(J(a | n) : ZMod n) ≠ a^(n/2)`
  — then `n` is not prime. A single witness certifies compositeness with no
  factorization of `n`.

* **A concrete witness** (`two_eulerWitness_fifteen`, `fifteen_not_prime`):
  `a = 2` witnesses the compositeness of `n = 15`. Here `J(2 | 15) = 1`
  (the parent's lost-direction witness) while `2^7 ≡ 8 (mod 15)`, so the
  congruence fails: `1 ≠ 8`. The same `a = 2` that the parent showed the
  Jacobi symbol *fails* to certify as a nonsquare turns out to *succeed* at
  certifying 15 as composite.

* **The test is one-sided** (`negOne_eulerLiar_fifteen`): not every `a` exposes a
  composite `n`. For `n = 15`, `a = −1` is an *Euler liar*:
  `J(−1 | 15) = −1` and `(−1)^7 ≡ −1 (mod 15)`, so the congruence *holds*
  even though 15 is composite. Hence a single non-witness can never prove
  primality — Solovay–Strassen is inherently a one-sided (Monte Carlo) test.

All Jacobi/Legendre values are computed through the parent's residuosity route
and `ZMod` power evaluations are discharged by `decide`; there is no
`native_decide` anywhere.

## Status: 0 sorries, 0 `axiom`s, no `native_decide`.
-/

namespace QuadraticReciprocityAlgorithmOQ02OQ01

open scoped NumberTheorySymbols
open QuadraticReciprocityAlgorithmOQ02

-- ============================================================================
-- Part 1: Euler's criterion for the Jacobi symbol — the prime-only identity
-- ============================================================================

/-- **Euler's criterion, Jacobi form (prime modulus).**  For a prime `p`,
    `(J(a | p) : ZMod p) = a^(p/2)`.  Over a prime the Jacobi symbol equals the
    Legendre symbol, and the Legendre symbol satisfies Euler's criterion. -/
theorem jacobi_eq_pow_of_prime (p : ℕ) [Fact p.Prime] (a : ℤ) :
    (J(a | p) : ZMod p) = (a : ZMod p) ^ (p / 2) := by
  rw [jacobi_eq_legendre_of_prime]
  exact legendreSym.eq_pow p a

-- ============================================================================
-- Part 2: The Solovay–Strassen compositeness witness
-- ============================================================================

/-- `a` is an **Euler witness** for `n` when it violates Euler's criterion:
    `(J(a | n) : ZMod n) ≠ a^(n/2)`.  Such an `a` certifies that `n` is composite. -/
def IsEulerWitness (a : ℤ) (n : ℕ) : Prop :=
  (J(a | n) : ZMod n) ≠ (a : ZMod n) ^ (n / 2)

/-- **The Solovay–Strassen test.**  An Euler witness certifies compositeness:
    if `a` violates Euler's criterion modulo `n`, then `n` is not prime.  No
    factorization of `n` is required — the contrapositive of the prime-case
    identity `jacobi_eq_pow_of_prime`. -/
theorem not_prime_of_eulerWitness {a : ℤ} {n : ℕ} (h : IsEulerWitness a n) :
    ¬ n.Prime := by
  intro hp
  haveI : Fact n.Prime := ⟨hp⟩
  exact h (jacobi_eq_pow_of_prime n a)

/-- Contrapositive: a prime modulus admits no Euler witness — every `a` satisfies
    Euler's criterion. -/
theorem no_eulerWitness_of_prime {n : ℕ} (hp : n.Prime) (a : ℤ) :
    ¬ IsEulerWitness a n :=
  fun h => not_prime_of_eulerWitness h hp

-- ============================================================================
-- Part 3: A concrete witness — a = 2 certifies that 15 is composite
-- ============================================================================

/-- `2^7 ≡ 8 (mod 15)`: the right-hand side of Euler's criterion at `a = 2`,
    `n = 15` (note `15 / 2 = 7`). -/
theorem two_pow_seven_fifteen : (2 : ZMod 15) ^ (15 / 2) = 8 := by decide

/-- **A concrete Euler witness.**  `a = 2` violates Euler's criterion modulo `15`:
    `J(2 | 15) = 1` (the parent's lost-direction witness) but `2^7 ≡ 8`, and
    `1 ≠ 8` in `ZMod 15`. -/
theorem two_eulerWitness_fifteen : IsEulerWitness 2 15 := by
  unfold IsEulerWitness
  rw [jacobi_two_fifteen]
  decide

/-- **The test in action.**  The single witness `a = 2` proves that `15` is
    composite, with no appeal to its factorization `15 = 3·5`. -/
theorem fifteen_not_prime : ¬ Nat.Prime 15 :=
  not_prime_of_eulerWitness two_eulerWitness_fifteen

-- ============================================================================
-- Part 4: The test is one-sided — an Euler liar for 15
-- ============================================================================

/-- `J(−1 | 15) = −1`, from multiplicativity `J(−1|15) = J(−1|3)·J(−1|5) =
    (−1)·(1)`.  `−1 ≡ 2 (mod 3)` is a nonsquare while `−1 ≡ 4 = 2² (mod 5)` is a
    square, so exactly one factor contributes a `−1`. -/
theorem jacobi_negOne_fifteen : J(-1 | 15) = -1 := by
  rw [show (15 : ℕ) = 3 * 5 from by norm_num, jacobi_mul_right]
  have h3 : J(-1 | 3) = -1 := by
    haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
    rw [jacobi_eq_legendre_of_prime, legendreSym.eq_neg_one_iff 3 (a := -1)]
    decide +revert
  have h5 : J(-1 | 5) = 1 := by
    haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    rw [jacobi_eq_legendre_of_prime, legendreSym.eq_one_iff 5 (a := -1) (by decide +revert)]
    decide +revert
  rw [h3, h5]; norm_num

/-- `(−1)^7 ≡ −1 (mod 15)`: the right-hand side of Euler's criterion at `a = −1`. -/
theorem negOne_pow_seven_fifteen : ((-1 : ℤ) : ZMod 15) ^ (15 / 2) = -1 := by decide

/-- **An Euler liar.**  `a = −1` is *not* an Euler witness for `15`, even though
    `15` is composite: `J(−1 | 15) = −1` and `(−1)^7 ≡ −1 (mod 15)`, so Euler's
    criterion holds.  A single non-witness therefore cannot certify primality —
    Solovay–Strassen is inherently one-sided. -/
theorem negOne_eulerLiar_fifteen : ¬ IsEulerWitness (-1) 15 := by
  unfold IsEulerWitness
  rw [jacobi_negOne_fifteen]
  decide

/-- The two faces of `n = 15` together: `a = 2` is a witness (the criterion
    fails) and `a = −1` is a liar (the criterion holds).  The gap between them is
    exactly why the test is probabilistic, not deterministic. -/
theorem fifteen_witness_and_liar :
    IsEulerWitness 2 15 ∧ ¬ IsEulerWitness (-1) 15 :=
  ⟨two_eulerWitness_fifteen, negOne_eulerLiar_fifteen⟩

#check @jacobi_eq_pow_of_prime
#check @not_prime_of_eulerWitness
#check @two_eulerWitness_fifteen
#check @negOne_eulerLiar_fifteen

end QuadraticReciprocityAlgorithmOQ02OQ01
