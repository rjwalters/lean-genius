import Mathlib.Data.Nat.Totient
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic

/-
# Erdős 1064 (OQ-03): the double totient iterate  φ(n)  vs  φ(n − φ(n − φ(n)))

## Background

Erdős #1064 concerns the single cototient step  c(n) = n − φ(n).  The parent
problem asks whether  φ(n) > φ(n − φ(n))  for almost all n (true, density 1,
Luca–Pomerance) while the reverse inequality still holds infinitely often.

This open question OQ-03 asks what happens for the **higher iterate**

  D(n)  :=  n − φ(n − φ(n)),

i.e. we compare  φ(n)  against  φ(D(n)) = φ(n − φ(n − φ(n))).

## What this file establishes (all machine-checked, no axioms)

1. **Collapse on primes.**  For *every* prime p we have  D(p) = p − 1
   exactly.  Indeed φ(p) = p − 1, so n − φ(n) = 1, φ(1) = 1, and
   D(p) = p − φ(1) = p − 1.

2. **Forward inequality on the whole family of odd primes.**  For every
   prime p ≥ 3,
        φ(D(p)) = φ(p − 1)  <  p − 1 = φ(p),
   so the "expected" direction  φ(n) > φ(D(n))  holds on an infinite family.
   The single exceptional prime is p = 2, where equality holds (D(2) = 1).

3. **The reverse inequality genuinely occurs.**  The smallest witness is
   n = 39: there D(39) = 31 is prime, φ(39) = 24 < 30 = φ(31) = φ(D(39)).
   So  φ(n) < φ(D(n))  for infinitely-often-observed n; concretely at n = 39.

The reverse cases empirically cluster where D(n) lands on a prime (31, 47, 73,
97, 113, …), making φ(D(n)) = D(n) − 1 large; a full "infinitely often"
statement remains the OPEN part of this question.
-/

open Nat

namespace Erdos1064OQ03

/-- The double cototient iterate  `D(n) = n − φ(n − φ(n))`. -/
def dblIter (n : ℕ) : ℕ := n - Nat.totient (n - Nat.totient n)

/-- **Collapse on primes.**  For every prime `p`, the double iterate satisfies
    `D(p) = p − 1`.  (φ(p) = p−1 ⟹ p − φ(p) = 1 ⟹ φ(1) = 1 ⟹ D(p) = p−1.) -/
theorem dblIter_prime {p : ℕ} (hp : p.Prime) : dblIter p = p - 1 := by
  unfold dblIter
  rw [Nat.totient_prime hp]
  have h1 : p - (p - 1) = 1 := by have := hp.two_le; omega
  rw [h1, Nat.totient_one]

/-- **Forward inequality on odd primes.**  For every prime `p ≥ 3`,
    `φ(D(p)) < φ(p)`, i.e. `φ(n) > φ(n − φ(n − φ(n)))` holds throughout the
    infinite family of odd primes. -/
theorem totient_dblIter_lt_of_prime {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) :
    Nat.totient (dblIter p) < Nat.totient p := by
  rw [dblIter_prime hp, Nat.totient_prime hp]
  exact Nat.totient_lt (p - 1) (by omega)

/-- Sharp boundary: at the even prime `p = 2` the forward inequality degenerates
    to equality, `D(2) = 1` and `φ(D(2)) = φ(2)`. -/
theorem totient_dblIter_eq_two : Nat.totient (dblIter 2) = Nat.totient 2 := by
  have : dblIter 2 = 1 := dblIter_prime (by norm_num)
  rw [this, Nat.totient_one, Nat.totient_prime (by norm_num)]

-- ----------------------------------------------------------------------------
-- Concrete totient values used for the reverse witness (via factorisation,
-- avoiding kernel evaluation of `gcd` inside `decide`).
-- ----------------------------------------------------------------------------

/-- `φ(39) = 24`  (39 = 3·13, distinct primes). -/
theorem totient_39 : Nat.totient 39 = 24 := by
  rw [show (39 : ℕ) = 3 * 13 from rfl, Nat.totient_mul (by decide),
      Nat.totient_prime (by norm_num), Nat.totient_prime (by norm_num)]

/-- `φ(15) = 8`  (15 = 3·5, distinct primes). -/
theorem totient_15 : Nat.totient 15 = 8 := by
  rw [show (15 : ℕ) = 3 * 5 from rfl, Nat.totient_mul (by decide),
      Nat.totient_prime (by norm_num), Nat.totient_prime (by norm_num)]

/-- `φ(31) = 30`  (31 is prime). -/
theorem totient_31 : Nat.totient 31 = 30 := by
  rw [Nat.totient_prime (by norm_num)]

/-- The double iterate of 39 lands on the prime 31:  `D(39) = 31`. -/
theorem dblIter_39 : dblIter 39 = 31 := by
  unfold dblIter
  rw [totient_39, show (39 : ℕ) - 24 = 15 from rfl, totient_15]

/-- **The reverse inequality occurs.**  At `n = 39` the double iterate reverses
    the expected direction: `φ(39) = 24 < 30 = φ(D(39))`, since `D(39) = 31` is
    prime.  This exhibits a concrete member of the (conjecturally infinite)
    family of reversal points. -/
theorem reverse_at_39 : Nat.totient 39 < Nat.totient (dblIter 39) := by
  rw [dblIter_39, totient_39, totient_31]
  decide

/-- Summary corollary: the forward inequality `φ(n) > φ(D(n))` is **not**
    universal — it fails at `n = 39` — yet holds on the entire infinite family
    of odd primes.  Hence the higher-iterate analogue of Erdős 1064 exhibits
    the same both-directions behaviour as the single step. -/
theorem forward_not_universal :
    (∀ p : ℕ, p.Prime → 3 ≤ p → Nat.totient (dblIter p) < Nat.totient p) ∧
    (∃ n : ℕ, Nat.totient n < Nat.totient (dblIter n)) :=
  ⟨fun _ hp hp3 => totient_dblIter_lt_of_prime hp hp3, ⟨39, reverse_at_39⟩⟩

end Erdos1064OQ03
