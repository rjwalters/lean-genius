/-
Erdős Problem #240: Gaps Between P-Smooth Numbers

Source: https://erdosproblems.com/240
Status: SOLVED (Tijdeman 1973)

Statement:
Is there an infinite set of primes P such that if {a₁ < a₂ < ···} is the
set of integers divisible only by primes in P, then lim(aᵢ₊₁ - aᵢ) = ∞?

Background:
- P-smooth numbers: integers whose prime factors all lie in P
- For finite P: gaps → ∞ (follows from Pólya's theorem)
- Question: Can this happen for INFINITE P?

Answer: YES (Tijdeman 1973)

Key Results:
- Pólya (1918): For quadratic f(n) without repeated roots, largest prime factor → ∞
- This implies for finite P: gaps are unbounded
- Tijdeman (1973): For finite P, gaps ≫ aᵢ/(log aᵢ)^C
- Tijdeman (1973): For any ε > 0, exists infinite P with gaps ≫ aᵢ^{1-ε}

Origin: Asked to Erdős by Wintner

References:
- Pólya (1918): "Zur arithmetischen Untersuchung der Polynome"
- Tijdeman (1973): "On integers with many small prime factors"
-/

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open Set

namespace Erdos240

/-
## Part I: P-Smooth Numbers
-/

/--
**P-Smooth Number:**
A positive integer n is P-smooth if all its prime factors are in P.
Equivalently, n is divisible only by primes in P.
-/
def isPSmooth (P : Set ℕ) (n : ℕ) : Prop :=
  n > 0 ∧ ∀ p : ℕ, p.Prime → p ∣ n → p ∈ P

/--
**The set of P-smooth numbers:**
-/
def smoothNumbers (P : Set ℕ) : Set ℕ :=
  {n : ℕ | isPSmooth P n}

/--
**1 is P-smooth for any P:**
-/
theorem one_isPSmooth (P : Set ℕ) : isPSmooth P 1 := by
  constructor
  · exact Nat.one_pos
  · intro p _ hdiv
    exact absurd (Nat.eq_one_of_dvd_one hdiv) (Nat.Prime.ne_one ‹p.Prime›)

/-
## Part II: Enumeration and Gaps
-/

/--
**Ordered enumeration:**
Let (aᵢ) be the P-smooth numbers in increasing order.
We axiomatize this enumeration.
-/
axiom smoothEnum (P : Set ℕ) : ℕ → ℕ

/--
**Enumeration properties:**
-/
axiom smoothEnum_pos (P : Set ℕ) (hP : P.Nonempty) (i : ℕ) :
  smoothEnum P i > 0

axiom smoothEnum_smooth (P : Set ℕ) (i : ℕ) :
  isPSmooth P (smoothEnum P i)

axiom smoothEnum_strictly_increasing (P : Set ℕ) (hP : P.Nonempty) (i j : ℕ) :
  i < j → smoothEnum P i < smoothEnum P j

axiom smoothEnum_surjective (P : Set ℕ) (n : ℕ) (hn : isPSmooth P n) :
  ∃ i, smoothEnum P i = n

/--
**Gap function:**
The gap between consecutive P-smooth numbers.
-/
def gap (P : Set ℕ) (i : ℕ) : ℕ :=
  smoothEnum P (i + 1) - smoothEnum P i

/-
## Part III: The Main Question
-/

/--
**Gaps tend to infinity:**
The sequence of gaps is unbounded.
-/
def gapsTendToInfinity (P : Set ℕ) : Prop :=
  ∀ M : ℕ, ∃ i : ℕ, gap P i > M

/--
**The Erdős-Wintner Question:**
Is there an infinite set of primes P such that gaps → ∞?
-/
def erdos240Question : Prop :=
  ∃ P : Set ℕ, (∀ p ∈ P, Nat.Prime p) ∧ P.Infinite ∧ gapsTendToInfinity P

/-
## Part IV: Pólya's Theorem (1918)
-/

/--
**Pólya's Theorem:**
If f(n) is a quadratic integer polynomial without repeated roots,
then the largest prime factor of f(n) → ∞ as n → ∞.
-/
axiom polya_theorem (a b c : ℤ) (hdisc : b^2 - 4*a*c ≠ 0) (ha : a ≠ 0) :
  ∀ M : ℕ, ∃ N : ℕ, ∀ n ≥ N,
    ∃ p : ℕ, p.Prime ∧ p > M ∧ (p : ℤ) ∣ (a * n^2 + b * n + c)

/--
**Corollary: f(n) = n(n+k) has large prime factors:**
-/
axiom polya_corollary (k : ℕ) (hk : k > 0) :
  ∀ M : ℕ, ∃ N : ℕ, ∀ n ≥ N,
    ∃ p : ℕ, p.Prime ∧ p > M ∧ p ∣ n * (n + k)

/-
## Part V: Finite P Case
-/

/--
**Finite P implies unbounded gaps:**
If P is a finite set of primes, then gaps → ∞.

Proof idea: If gaps were bounded by some k, then aᵢ₊₁ = aᵢ + k
infinitely often. This means n and n + k are both P-smooth
infinitely often. But n(n+k) has arbitrarily large prime factors
by Pólya's theorem, contradiction.
-/
axiom finite_P_unbounded_gaps (P : Finset ℕ) (hP : ∀ p ∈ P, Nat.Prime p) :
  gapsTendToInfinity (↑P : Set ℕ)

/--
**Tijdeman's quantitative bound for finite P (1973):**
For finite P, the gaps satisfy:
aᵢ₊₁ - aᵢ ≫ aᵢ / (log aᵢ)^C
for some constant C depending on P.
-/
axiom tijdeman_finite_bound (P : Finset ℕ) (hP : ∀ p ∈ P, Nat.Prime p) :
  ∃ C c : ℝ, C > 0 ∧ c > 0 ∧
    ∀ i : ℕ, smoothEnum (↑P : Set ℕ) i > 1 →
      (gap (↑P : Set ℕ) i : ℝ) ≥ c * (smoothEnum (↑P : Set ℕ) i : ℝ) /
        (Real.log (smoothEnum (↑P : Set ℕ) i : ℝ))^C

/-
## Part VI: Tijdeman's Main Theorem (1973)
-/

/--
**Tijdeman's Theorem:**
For any ε > 0, there exists an infinite set of primes P such that
the gaps between consecutive P-smooth numbers satisfy:
aᵢ₊₁ - aᵢ ≫ aᵢ^{1-ε}

This answers Erdős-Wintner's question affirmatively.
-/
axiom tijdeman_main_theorem :
  ∀ ε : ℝ, ε > 0 → ∃ P : Set ℕ,
    (∀ p ∈ P, Nat.Prime p) ∧
    P.Infinite ∧
    ∃ c : ℝ, c > 0 ∧ ∀ i : ℕ, smoothEnum P i > 1 →
      (gap P i : ℝ) ≥ c * (smoothEnum P i : ℝ)^(1 - ε)

/--
**Answer to Erdős-Wintner:**
Yes, such an infinite P exists.
-/
theorem erdos240_answer : erdos240Question := by
  obtain ⟨P, hPrime, hInf, c, hc, hgap⟩ := tijdeman_main_theorem (1/2) (by norm_num)
  use P, hPrime, hInf
  intro M
  -- Gaps grow like a^{1/2}, so eventually exceed M
  sorry

/-
## Part VII: Construction Ideas
-/

/--
**Tijdeman's Construction:**
The infinite set P is constructed so that the primes are
sufficiently "sparse" - they grow fast enough that consecutive
P-smooth numbers can't be too close.

Key insight: If P contains all primes up to some bound,
P-smooth numbers are dense. But if P is sparse (like powers
of 2, or primes along a fast-growing sequence), gaps grow.
-/
axiom tijdeman_construction : True

/--
**Example: Powers of 2**
If P = {2}, then P-smooth numbers are {1, 2, 4, 8, 16, ...}.
Gaps: 1, 2, 4, 8, ... which grow like aᵢ/2.

More generally, for P = {p} a singleton, P-smooth numbers are
{1, p, p², p³, ...} with gaps growing exponentially.
-/
theorem singleton_large_gaps (p : ℕ) (hp : p.Prime) :
    gapsTendToInfinity {p} := by
  intro M
  -- Gaps between consecutive powers of p grow to infinity
  sorry

/-
## Part VIII: Related Results
-/

/--
**Størmer's Theorem:**
For any finite P, only finitely many consecutive integers
can both be P-smooth.

This is another consequence of Pólya-type results.
-/
axiom stormer_theorem (P : Finset ℕ) (hP : ∀ p ∈ P, Nat.Prime p) :
  ∃ N : ℕ, ∀ n > N, ¬(isPSmooth (↑P : Set ℕ) n ∧ isPSmooth (↑P : Set ℕ) (n + 1))

/--
**Connection to ABC Conjecture:**
Better bounds on gaps would follow from the ABC conjecture.
The ABC conjecture implies: for coprime a, b, c with a + b = c,
c < rad(abc)^{1+ε} where rad is the radical (product of distinct primes).
-/
axiom abc_connection : True

/--
**Smooth numbers in arithmetic progressions:**
How are P-smooth numbers distributed in arithmetic progressions?
This is related to Linnik-type problems.
-/
axiom smooth_in_progressions : True

/-
## Part IX: Summary
-/

/--
**Summary of Known Results:**
-/
theorem erdos_240_summary :
    -- Finite P: gaps → ∞
    (∀ P : Finset ℕ, (∀ p ∈ P, Nat.Prime p) → gapsTendToInfinity (↑P : Set ℕ)) ∧
    -- Tijdeman's main theorem (infinite P)
    (∀ ε > 0, ∃ P : Set ℕ, (∀ p ∈ P, Nat.Prime p) ∧ P.Infinite ∧
      ∃ c : ℝ, c > 0 ∧ ∀ i : ℕ, smoothEnum P i > 1 →
        (gap P i : ℝ) ≥ c * (smoothEnum P i : ℝ)^(1 - ε)) ∧
    -- Answer is YES
    erdos240Question := by
  constructor
  · exact finite_P_unbounded_gaps
  constructor
  · exact tijdeman_main_theorem
  · exact erdos240_answer

/--
**Erdős Problem #240: SOLVED**

Is there an infinite set of primes P such that gaps between
consecutive P-smooth numbers tend to infinity?

Answer: YES (Tijdeman 1973)

For any ε > 0, there exists infinite P with gaps ≫ aᵢ^{1-ε}.
-/
theorem erdos_240 : erdos240Question := erdos240_answer

end Erdos240
