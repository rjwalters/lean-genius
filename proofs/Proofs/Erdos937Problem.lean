/-
Erdős Problem #937: Arithmetic Progressions of Coprime Powerful Numbers

Source: https://erdosproblems.com/937
Status: SOLVED (Bajpai-Bennett-Chan, 2024)

Statement:
Are there infinitely many four-term arithmetic progressions of coprime
powerful numbers (where n is powerful if p|n implies p²|n)?

Answer: YES

Key Results:
- Fermat: No four squares in arithmetic progression
- Without coprimality: Arbitrarily long APs of powerful numbers exist (easy construction)
- Bajpai-Bennett-Chan (2024): Infinitely many 4-term APs of coprime powerful numbers
- Bajpai-Bennett-Chan (2024): Infinitely many 3-term APs of coprime 3-powerful numbers
- Conditional on ABC: Only finitely many 3-term APs of coprime r-powerful numbers for r ≥ 4

References:
- Bajpai, Bennett, Chan (2024): "Arithmetic progressions in squarefull numbers"
- Erdős (1976): "Problems and results on number theoretic properties of consecutive integers"
-/

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.NumberTheory.Divisors
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

open Nat BigOperators Finset

namespace Erdos937

/-
## Part I: Powerful Numbers

A number n is powerful (or squarefull) if for every prime p dividing n,
we have p² also divides n.
-/

/--
**Powerful Number:**
A positive integer n is powerful if every prime factor appears with
exponent at least 2.

Equivalently: for all primes p, if p | n then p² | n.

Examples:
- 1 is powerful (vacuously)
- 4 = 2² is powerful
- 8 = 2³ is powerful
- 9 = 3² is powerful
- 72 = 2³ · 3² is powerful
- 6 = 2 · 3 is NOT powerful (2 appears with exponent 1)
-/
def IsPowerful (n : ℕ) : Prop :=
  n ≥ 1 ∧ ∀ p : ℕ, p.Prime → p ∣ n → p^2 ∣ n

/--
**r-Powerful Number:**
A positive integer n is r-powerful if every prime factor appears with
exponent at least r.
-/
def IsRPowerful (r : ℕ) (n : ℕ) : Prop :=
  n ≥ 1 ∧ ∀ p : ℕ, p.Prime → p ∣ n → p^r ∣ n

/-- 2-powerful is the same as powerful. -/
theorem powerful_eq_2powerful (n : ℕ) : IsPowerful n ↔ IsRPowerful 2 n := by
  simp only [IsPowerful, IsRPowerful]

/-
## Part II: Basic Properties of Powerful Numbers
-/

/-- 1 is powerful (vacuously, no prime divisors). -/
theorem one_is_powerful : IsPowerful 1 := by
  constructor
  · omega
  · intro p hp hdiv
    simp at hdiv
    omega

/-- Every perfect square is powerful. -/
theorem square_is_powerful (n : ℕ) (hn : n ≥ 1) : IsPowerful (n^2) := by
  constructor
  · positivity
  · intro p hp hdiv
    have : p ∣ n := by
      have h := hp.dvd_of_dvd_pow hdiv
      exact h
    exact dvd_pow this (by norm_num)

/-- 4 = 2² is powerful. -/
theorem four_is_powerful : IsPowerful 4 := by
  have h : (4 : ℕ) = 2^2 := by norm_num
  rw [h]
  exact square_is_powerful 2 (by norm_num)

/-- 8 = 2³ is powerful. -/
theorem eight_is_powerful : IsPowerful 8 := by
  constructor
  · omega
  · intro p hp hdiv
    interval_cases p
    · omega
    · simp only [pow_two]
      decide
    · simp at hdiv
      omega

/-- 9 = 3² is powerful. -/
theorem nine_is_powerful : IsPowerful 9 := by
  have h : (9 : ℕ) = 3^2 := by norm_num
  rw [h]
  exact square_is_powerful 3 (by norm_num)

/-- 72 = 8 · 9 = 2³ · 3² is powerful. -/
theorem seventytwo_is_powerful : IsPowerful 72 := by
  constructor
  · omega
  · intro p hp hdiv
    have h72 : (72 : ℕ) = 2^3 * 3^2 := by norm_num
    rw [h72] at hdiv
    interval_cases p
    · omega
    · simp only [pow_two]; decide
    · simp only [pow_two]; decide
    · -- p ≥ 4, so p cannot divide 72 = 2³ · 3²
      have h1 : ¬ (4 : ℕ).Prime := by decide
      omega

/-
## Part III: Arithmetic Progressions
-/

/--
**Arithmetic Progression of Length k:**
A sequence a, a+d, a+2d, ..., a+(k-1)d with common difference d.
-/
def IsArithmeticProgression (terms : List ℕ) : Prop :=
  terms.length ≥ 2 ∧
  ∃ d : ℤ, ∀ i : Fin (terms.length - 1),
    (terms.get ⟨i.val + 1, by omega⟩ : ℤ) - terms.get ⟨i.val, by omega⟩ = d

/--
**Four-term Arithmetic Progression:**
Four numbers a, b, c, d form an AP if b - a = c - b = d - c.
-/
def IsFourTermAP (a b c d : ℕ) : Prop :=
  b > a ∧ c > b ∧ d > c ∧
  (b : ℤ) - a = (c : ℤ) - b ∧ (c : ℤ) - b = (d : ℤ) - c

/--
**Three-term Arithmetic Progression:**
Three numbers a, b, c form an AP if b - a = c - b, i.e., 2b = a + c.
-/
def IsThreeTermAP (a b c : ℕ) : Prop :=
  b > a ∧ c > b ∧ (b : ℤ) - a = (c : ℤ) - b

/-
## Part IV: Coprimality Conditions
-/

/--
**Pairwise Coprime:**
A list of numbers is pairwise coprime if gcd(a_i, a_j) = 1 for all i ≠ j.
-/
def PairwiseCoprime (terms : List ℕ) : Prop :=
  ∀ i j : Fin terms.length, i ≠ j →
    Nat.Coprime (terms.get i) (terms.get j)

/--
**Coprime Four-term AP:**
Four numbers forming an AP where any two are coprime.
-/
def CoprimeFourTermAP (a b c d : ℕ) : Prop :=
  IsFourTermAP a b c d ∧
  Nat.Coprime a b ∧ Nat.Coprime a c ∧ Nat.Coprime a d ∧
  Nat.Coprime b c ∧ Nat.Coprime b d ∧ Nat.Coprime c d

/--
**Coprime Three-term AP:**
Three numbers forming an AP where any two are coprime.
-/
def CoprimeThreeTermAP (a b c : ℕ) : Prop :=
  IsThreeTermAP a b c ∧
  Nat.Coprime a b ∧ Nat.Coprime a c ∧ Nat.Coprime b c

/-
## Part V: The Main Theorem Sets
-/

/--
**Four-term APs of Coprime Powerful Numbers:**
The set of 4-tuples (a,b,c,d) where:
1. All four numbers are powerful
2. They form an arithmetic progression
3. They are pairwise coprime
-/
def coprimePowerfulFourTermAPs : Set (ℕ × ℕ × ℕ × ℕ) :=
  {t : ℕ × ℕ × ℕ × ℕ |
    IsPowerful t.1 ∧ IsPowerful t.2.1 ∧ IsPowerful t.2.2.1 ∧ IsPowerful t.2.2.2 ∧
    CoprimeFourTermAP t.1 t.2.1 t.2.2.1 t.2.2.2}

/--
**Three-term APs of Coprime 3-Powerful Numbers:**
The set of 3-tuples (a,b,c) of pairwise coprime 3-powerful numbers in AP.
-/
def coprime3PowerfulThreeTermAPs : Set (ℕ × ℕ × ℕ) :=
  {t : ℕ × ℕ × ℕ |
    IsRPowerful 3 t.1 ∧ IsRPowerful 3 t.2.1 ∧ IsRPowerful 3 t.2.2 ∧
    CoprimeThreeTermAP t.1 t.2.1 t.2.2}

/-
## Part VI: Fermat's Theorem on Squares
-/

/--
**Fermat's Theorem:**
There are no four distinct squares in arithmetic progression.

This is a classical result: if a², b², c², d² are in AP with a < b < c < d,
then b² - a² = c² - b² = d² - c², which leads to a contradiction.
-/
axiom fermat_no_four_squares_in_AP :
    ¬∃ (a b c d : ℕ), a < b ∧ b < c ∧ c < d ∧
      IsFourTermAP (a^2) (b^2) (c^2) (d^2)

/-
## Part VII: Easy Construction (Without Coprimality)
-/

/--
**Extending APs of Powerful Numbers:**
If a, a+d, ..., a+(k-1)d is an AP of powerful numbers,
then multiplying each by (a+kd)² gives another AP of powerful numbers.

This shows that without coprimality, arbitrarily long APs of powerful
numbers exist.
-/
axiom extend_powerful_AP :
    ∀ (terms : List ℕ), (∀ t ∈ terms, IsPowerful t) → IsArithmeticProgression terms →
      ∃ (extended : List ℕ), extended.length = terms.length + 1 ∧
        (∀ t ∈ extended, IsPowerful t) ∧ IsArithmeticProgression extended

/--
**Existence of Long APs (without coprimality):**
For any k, there exist k powerful numbers in arithmetic progression.
-/
axiom arbitrarily_long_powerful_APs :
    ∀ k : ℕ, k ≥ 2 → ∃ (terms : List ℕ), terms.length = k ∧
      (∀ t ∈ terms, IsPowerful t) ∧ IsArithmeticProgression terms

/-
## Part VIII: Bajpai-Bennett-Chan Theorem (2024)
-/

/--
**Bajpai-Bennett-Chan Theorem (2024):**
There are infinitely many four-term arithmetic progressions of
pairwise coprime powerful numbers.

This settles Erdős Problem #937 affirmatively.
-/
axiom bajpai_bennett_chan_four_term :
    coprimePowerfulFourTermAPs.Infinite

/--
**Bajpai-Bennett-Chan Theorem on 3-Powerful Numbers:**
There are infinitely many three-term arithmetic progressions of
pairwise coprime 3-powerful numbers.
-/
axiom bajpai_bennett_chan_three_term_3powerful :
    coprime3PowerfulThreeTermAPs.Infinite

/-
## Part IX: Erdős's Conjecture and ABC
-/

/--
**Erdős's Conjecture on r-Powerful Numbers:**
For r ≥ 4, there are only finitely many three-term APs of coprime r-powerful numbers.
For r = 3, infinitely many 3-term but finitely many 4-term APs exist.

The r ≥ 4 case is conditional on the ABC conjecture.
-/
def erdosConjectureRPowerful : Prop :=
  -- r ≥ 4: finitely many 3-term APs
  (∀ r ≥ 4, ∃ (S : Finset (ℕ × ℕ × ℕ)), ∀ t : ℕ × ℕ × ℕ,
    (IsRPowerful r t.1 ∧ IsRPowerful r t.2.1 ∧ IsRPowerful r t.2.2 ∧
     CoprimeThreeTermAP t.1 t.2.1 t.2.2) → t ∈ S) ∧
  -- r = 3: infinitely many 3-term, finitely many 4-term
  coprime3PowerfulThreeTermAPs.Infinite ∧
  (∃ (S : Finset (ℕ × ℕ × ℕ × ℕ)), ∀ t : ℕ × ℕ × ℕ × ℕ,
    (IsRPowerful 3 t.1 ∧ IsRPowerful 3 t.2.1 ∧ IsRPowerful 3 t.2.2.1 ∧ IsRPowerful 3 t.2.2.2 ∧
     CoprimeFourTermAP t.1 t.2.1 t.2.2.1 t.2.2.2) → t ∈ S)

/--
**Conditional Result (assuming ABC):**
If the ABC conjecture is true, then for r ≥ 4, there are only finitely many
three-term APs of coprime r-powerful numbers.
-/
axiom abc_implies_finite_rpowerful (r : ℕ) (hr : r ≥ 4) :
    True → -- Placeholder for ABC conjecture
    ∃ (S : Finset (ℕ × ℕ × ℕ)), ∀ t : ℕ × ℕ × ℕ,
      (IsRPowerful r t.1 ∧ IsRPowerful r t.2.1 ∧ IsRPowerful r t.2.2 ∧
       CoprimeThreeTermAP t.1 t.2.1 t.2.2) → t ∈ S

/-
## Part X: Main Results
-/

/--
**Erdős Problem #937: SOLVED**

There are infinitely many four-term arithmetic progressions of
pairwise coprime powerful numbers.

Proved by Bajpai, Bennett, and Chan (2024).
-/
theorem erdos_937 : coprimePowerfulFourTermAPs.Infinite :=
  bajpai_bennett_chan_four_term

/--
**Summary of Known Results:**
1. Without coprimality: arbitrarily long APs of powerful numbers exist
2. With coprimality: infinitely many 4-term APs of powerful numbers (BBC 2024)
3. For 3-powerful: infinitely many 3-term coprime APs (BBC 2024)
4. For r ≥ 4: finitely many 3-term coprime APs (conditional on ABC)
-/
theorem erdos_937_summary :
    coprimePowerfulFourTermAPs.Infinite ∧
    coprime3PowerfulThreeTermAPs.Infinite :=
  ⟨erdos_937, bajpai_bennett_chan_three_term_3powerful⟩

/--
**Contrast with Fermat:**
While Fermat showed no four squares form an AP,
the set of powerful numbers is rich enough to contain
infinitely many coprime 4-term APs.
-/
theorem squares_vs_powerful :
    (¬∃ (a b c d : ℕ), a < b ∧ b < c ∧ c < d ∧
      IsFourTermAP (a^2) (b^2) (c^2) (d^2)) ∧
    coprimePowerfulFourTermAPs.Infinite :=
  ⟨fermat_no_four_squares_in_AP, erdos_937⟩

end Erdos937
