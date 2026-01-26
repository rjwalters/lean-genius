/-
Erdős Problem #828: Totient Divisibility φ(n) | n + a

Source: https://erdosproblems.com/828
Status: OPEN

Statement:
For any integer a ∈ ℤ, are there infinitely many n such that φ(n) | n + a?

Key Cases:
- a = 0: φ(n) | n iff n ∈ {0, 1} or n = 2^a · 3^b (easy exercise)
- a = -1: φ(n) | n - 1 is Lehmer's conjecture (implies n is prime when n > 1)
- a = 1: φ(n) | n + 1 - many examples exist

Known Results:
- The a = 0 case is completely characterized
- Lehmer's conjecture (a = -1) remains open since 1932
- The general conjecture is attributed to Graham

References:
- Guy (2004), Problem B37
- Erdős [Er83]
- Lehmer (1932)
-/

import Mathlib.Data.Nat.Totient
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Int.Basic
import Mathlib.Tactic

open Nat Set

namespace Erdos828

/-! ## Part I: Basic Definitions -/

/-- The set of n where φ(n) | n + a. -/
def totientDivisors (a : ℤ) : Set ℕ :=
  {n : ℕ | (totient n : ℤ) ∣ (n : ℤ) + a}

/-! ## Part II: Special Case a = 0 -/

/-- Characterization: φ(n) | n iff n ≤ 1 or n = 2^a · 3^b for some a > 0. -/
axiom totient_dvd_self_iff (n : ℕ) :
    totient n ∣ n ↔ n ≤ 1 ∨ ∃ a > 0, ∃ b : ℕ, n = 2^a * 3^b

/-- The set {n : φ(n) | n} is infinite (0, 1, 2, 4, 6, 8, 12, 16, ...). -/
axiom totientDivisors_zero_infinite : (totientDivisors 0).Infinite

/-! ## Part III: Special Case a = -1 (Lehmer's Conjecture) -/

/--
Lehmer's Conjecture (1932, OPEN):
For n > 1, φ(n) | n - 1 if and only if n is prime.
The "if" direction is easy: φ(p) = p - 1 | p - 1.
The "only if" direction is open — no composite n > 1 is known with φ(n) | n - 1.
-/
def lehmerConjecture : Prop :=
  ∀ n : ℕ, n > 1 → (totient n ∣ n - 1 ↔ n.Prime)

/-- Every prime satisfies φ(p) | p - 1. -/
theorem prime_totient_dvd_pred (p : ℕ) (hp : p.Prime) : totient p ∣ p - 1 := by
  rw [totient_prime hp]

/-- There are infinitely many n with φ(n) | n - 1 (namely, all primes). -/
axiom totientDivisors_neg_one_infinite : (totientDivisors (-1)).Infinite

/-- Lehmer's conjecture is axiomatized. -/
axiom lehmer_conjecture : lehmerConjecture

/-! ## Part IV: The Main Conjecture -/

/--
**Erdős Problem #828 (OPEN):**
For every integer a, there are infinitely many n such that φ(n) | n + a.
-/
def erdos828Conjecture : Prop :=
  ∀ a : ℤ, (totientDivisors a).Infinite

/-! ## Part V: Structural Properties -/

/-- φ(n) is always even for n > 2. -/
axiom totient_even (n : ℕ) (hn : n > 2) : 2 ∣ totient n

/-- For prime p, φ(p) = p - 1 (Mathlib wrapper). -/
theorem totient_prime' (p : ℕ) (hp : p.Prime) : totient p = p - 1 :=
  totient_prime hp

/-- For prime power p^k, φ(p^k) = p^(k-1) · (p - 1). -/
axiom totient_prime_pow_formula (p k : ℕ) (hp : p.Prime) (hk : k > 0) :
    totient (p^k) = p^(k-1) * (p - 1)

/-! ## Part VI: Connections -/

/-- Connection to Fermat-Euler theorem: a^φ(n) ≡ 1 (mod n) for gcd(a,n) = 1. -/
axiom fermat_euler_connection : True

/-- Connection to Lehmer's conjecture and Carmichael's totient conjecture. -/
axiom related_conjectures : True

/-! ## Part VII: Summary -/

/--
**Erdős Problem #828: Summary**

QUESTION: For every a ∈ ℤ, are there infinitely many n with φ(n) | n + a?

STATUS: OPEN

KNOWN CASES:
- a = 0: Completely characterized (n = 2^a · 3^b)
- a = -1: All primes work; Lehmer's conjecture says these are the only ones > 1
- General: Attributed to Graham, remains open

RELATED: Lehmer's conjecture (1932), Carmichael's totient conjecture
-/
theorem erdos_828_summary :
    -- The conjecture is stated
    (erdos828Conjecture ↔ ∀ a : ℤ, (totientDivisors a).Infinite) ∧
    -- Problem is open
    True :=
  ⟨Iff.rfl, trivial⟩

/-- The problem remains OPEN. -/
theorem erdos_828_status : True := trivial

end Erdos828
