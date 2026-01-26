/-!
# Erdős Problem #1065 — Primes of the Form 2^k · q + 1

Are there infinitely many primes p such that p = 2^k · q + 1 for some
prime q and k ≥ 0?

More generally: are there infinitely many primes p = 2^k · 3^l · q + 1
for some prime q and k, l ≥ 0?

The first question asks whether the set of primes whose predecessor
p − 1 is a product of a power of 2 and a prime is infinite. The
second relaxes this to allow powers of 3 as well.

Status: OPEN
Reference: https://erdosproblems.com/1065
Guy B46
-/

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic

/-! ## Definitions -/

/-- A prime p has the 2^k · q + 1 form if p − 1 = 2^k · q for some prime q. -/
def IsTwoTimePrimePlusOne (p : ℕ) : Prop :=
  p.Prime ∧ ∃ q k : ℕ, q.Prime ∧ p = 2 ^ k * q + 1

/-- A prime p has the 2^k · 3^l · q + 1 form if p − 1 = 2^k · 3^l · q. -/
def IsTwoThreeTimePrimePlusOne (p : ℕ) : Prop :=
  p.Prime ∧ ∃ q k l : ℕ, q.Prime ∧ p = 2 ^ k * 3 ^ l * q + 1

/-! ## Main Conjectures -/

/-- **Erdős Problem #1065a**: are there infinitely many primes p = 2^k · q + 1? -/
axiom erdos_1065a :
  Set.Infinite {p : ℕ | IsTwoTimePrimePlusOne p}

/-- **Erdős Problem #1065b**: are there infinitely many primes p = 2^k · 3^l · q + 1? -/
axiom erdos_1065b :
  Set.Infinite {p : ℕ | IsTwoThreeTimePrimePlusOne p}

/-! ## Small Examples -/

/-- p = 3: 3 = 2^0 · 2 + 1 = 1 · 2 + 1. Here q = 2, k = 0. -/
axiom example_3 : IsTwoTimePrimePlusOne 3

/-- p = 5: 5 = 2^1 · 2 + 1 = 4 + 1. Here q = 2, k = 1. -/
axiom example_5 : IsTwoTimePrimePlusOne 5

/-- p = 7: 7 = 2^1 · 3 + 1 = 6 + 1. Here q = 3, k = 1. -/
axiom example_7 : IsTwoTimePrimePlusOne 7

/-- p = 13: 13 = 2^2 · 3 + 1 = 12 + 1. Here q = 3, k = 2. -/
axiom example_13 : IsTwoTimePrimePlusOne 13

/-! ## Observations -/

/-- **Implication**: the 2^k · q + 1 form is a subset of the 2^k · 3^l · q + 1 form
    (take l = 0). So 1065b is weaker than 1065a. -/
axiom form_a_implies_b (p : ℕ) :
  IsTwoTimePrimePlusOne p → IsTwoThreeTimePrimePlusOne p

/-- **Sophie Germain Connection**: when k = 1 and q is prime, p = 2q + 1 is a
    safe prime. It is conjectured that there are infinitely many safe primes,
    which would settle the k = 1 case of 1065a. -/
axiom sophie_germain_case :
  Set.Infinite {p : ℕ | p.Prime ∧ ∃ q : ℕ, q.Prime ∧ p = 2 * q + 1} →
  Set.Infinite {p : ℕ | IsTwoTimePrimePlusOne p}

/-- **Smooth Numbers**: p − 1 being 2^k · q means p − 1 is "2-smooth times a prime".
    The question is about the distribution of primes whose predecessor has this
    restricted factorization. -/
axiom smooth_structure :
  ∀ p : ℕ, IsTwoTimePrimePlusOne p →
    ∃ q k : ℕ, q.Prime ∧ p - 1 = 2 ^ k * q
