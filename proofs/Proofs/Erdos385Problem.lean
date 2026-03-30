/-
Erdős Problem #385: Composite Numbers and Least Prime Divisors

Source: https://erdosproblems.com/385
Status: OPEN
References: Erdős, Eggleton, Selfridge [Er79d, p.73]; Erdős, Graham [ErGr80, p.74]

Statement:
Let F(n) = max{m + p(m) : m < n, m composite}, where p(m) is the least prime
divisor of m.

Question 1: Is F(n) > n for all sufficiently large n?
Question 2: Does F(n) - n → ∞ as n → ∞?

Known Results:
- F(n) ≤ n + √n (trivial upper bound, since p(m) ≤ √m for composite m)
- Conjectured: F(n) ≥ n + (1 - o(1))√n
- Question 1 is equivalent to Problem #430 (Sarosh Adenwalla)
- Terry Tao (2024) connected this to Siegel zeros

Example:
  F(10): composites below 10 are {4,6,8,9}.
  4+2=6, 6+2=8, 8+2=10, 9+3=12. So F(10) = 12 > 10.

OEIS: A322292
-/

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open Nat Set Filter

namespace Erdos385

/-
# Erdős Problem 385: Composite Numbers and Least Prime Divisors

*Reference:* [erdosproblems.com/385](https://www.erdosproblems.com/385)

Define F(n) = max{m + p(m) : m < n, m composite} where p(m) is the least prime
divisor of m. The problem asks whether F(n) > n for all large n and whether
the excess F(n) - n tends to infinity.
-/

/- ## Definitions -/

/-- A natural number is composite if it is greater than 1 and not prime. -/
def IsComposite (n : ℕ) : Prop := n > 1 ∧ ¬n.Prime

instance : DecidablePred IsComposite := fun n =>
  if h1 : n > 1 then
    if h2 : n.Prime then isFalse (fun ⟨_, hn⟩ => hn h2)
    else isTrue ⟨h1, h2⟩
  else isFalse (fun ⟨h, _⟩ => absurd h (not_lt.mpr (by omega)))

/-- The least prime divisor of n, using Mathlib's minFac.
    Returns 0 for n ≤ 1. -/
noncomputable def leastPrimeDivisor (n : ℕ) : ℕ :=
  if h : n > 1 then n.minFac else 0

/-- The least prime divisor of a composite number is prime. -/
theorem leastPrimeDivisor_prime (n : ℕ) (hn : IsComposite n) :
    (leastPrimeDivisor n).Prime := by
  unfold leastPrimeDivisor
  simp only [hn.1, dite_true]
  exact Nat.minFac_prime (by have := hn.1; omega)

/-- The least prime divisor divides n. -/
theorem leastPrimeDivisor_dvd (n : ℕ) (hn : n > 1) :
    leastPrimeDivisor n ∣ n := by
  unfold leastPrimeDivisor
  simp only [hn, dite_true]
  exact Nat.minFac_dvd n

/-- For composite n, the least prime divisor is at most √n.
    (If p(n) > √n then n/p(n) < √n < p(n), contradicting minimality.) -/
theorem leastPrimeDivisor_le_sqrt (n : ℕ) (hn : IsComposite n) :
    leastPrimeDivisor n ≤ Nat.sqrt n := by
  have h1 := hn.1
  unfold leastPrimeDivisor
  simp only [show n > 1 from h1, ↓reduceDIte]
  rw [Nat.le_sqrt']
  exact Nat.minFac_sq_le_self (by omega) hn.2

/- ## The Function F(n) -/

/-- F(n) = max{m + p(m) : m < n, m composite}.
    This is the maximum value of m + p(m) over all composite m less than n.
    Returns 0 if there are no composites below n. -/
noncomputable def F (n : ℕ) : ℕ :=
  if h : ∃ m < n, IsComposite m then
    Finset.sup' (Finset.filter (fun m => m < n ∧ IsComposite m) (Finset.range n))
      (by
        obtain ⟨m, hm, hcomp⟩ := h
        use m
        simp [hm, hcomp])
      (fun m => m + leastPrimeDivisor m)
  else 0

/-- The set of values {m + p(m) : m < n, m composite}. -/
def FSet (n : ℕ) : Set ℕ :=
  {k | ∃ m < n, IsComposite m ∧ k = m + leastPrimeDivisor m}

/- ## Basic Properties -/

/-- F(n) ≤ n + √n (trivial upper bound).
    Since any composite m < n has p(m) ≤ √m ≤ √n, we get m + p(m) < n + √n. -/
/- ## The Main Conjectures -/

/-- Erdős Problem #385, Question 1 (OPEN):
    Is F(n) > n for all sufficiently large n?
    Equivalently: for large n, can we always find a composite m < n
    such that m + p(m) > n? -/
def erdos385Question1 : Prop :=
  ∀ᶠ n in atTop, F n > n

/-- Erdős Problem #385, Question 2 (OPEN):
    Does F(n) - n → ∞ as n → ∞?
    This is a stronger statement than Question 1. -/
def erdos385Question2 : Prop :=
  Tendsto (fun n => (F n : ℤ) - n) atTop atTop

/-- Question 1: F(n) > n for all sufficiently large n. -/
/-- Question 2: F(n) - n → ∞. -/
/- ## Connection to Problem #430

Sarosh Adenwalla observed that Question 1 is equivalent to Problem #430:
"For large n, there exists composite m < n with m + p(m) > n."
This asks about the same phenomenon from a different angle.
-/

/-- Question 2 implies Question 1: if F(n) - n → ∞ then certainly
    F(n) > n eventually. -/
theorem q2_implies_q1 : erdos385Question2 → erdos385Question1 := by
  intro h
  unfold erdos385Question2 at h
  unfold erdos385Question1
  rw [Filter.eventually_atTop]
  obtain ⟨N, hN⟩ := Filter.tendsto_atTop_atTop.mp h 1
  exact ⟨N, fun n hn => by have := hN n hn; omega⟩

/- ## Conjectured Lower Bound

It is conjectured that F(n) ≥ n + (1 - o(1))√n. This means for large n,
we can always find a composite m < n such that m + p(m) is close to
n + √n, the trivial upper bound.
-/

/-- The conjectured lower bound: F(n) is eventually close to n + √n. -/
def conjecturedLowerBound : Prop :=
  ∀ ε : ℝ, ε > 0 → ∀ᶠ n in atTop,
    (F n : ℝ) ≥ (n : ℝ) + (1 - ε) * Real.sqrt n

/- ## Examples -/

/-- 4 is composite. -/
example : IsComposite 4 := ⟨by omega, by decide⟩

/-- 9 is composite. -/
example : IsComposite 9 := ⟨by omega, by decide⟩

/-- 6 is composite. -/
example : IsComposite 6 := ⟨by omega, by decide⟩

/- ## Why This Is Hard

The problem connects to deep questions about:
1. The distribution of primes (for bounding gaps)
2. The parity problem in sieve theory
3. Siegel zeros (as discussed by Tao, 2024)

Proving F(n) > n requires understanding when composites m < n
with small prime factors appear close to n, which depends on
the fine structure of prime gaps.
-/

/- ## Derived Results -/

/-- Question 1 implies only finitely many n have F(n) ≤ n. -/
theorem finitely_many_exceptions :
    erdos385Question1 → {n : ℕ | F n ≤ n}.Finite := by
  intro h
  unfold erdos385Question1 at h
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp h
  apply (Set.finite_Iio N).subset
  intro n hn
  simp only [Set.mem_setOf_eq] at hn
  simp only [Set.mem_Iio]
  by_contra h_ge
  push_neg at h_ge
  exact absurd (hN n h_ge) (not_lt.mpr hn)

end Erdos385
