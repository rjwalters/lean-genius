/-
Erdős Problem #269: LCM Series Irrationality

Source: https://erdosproblems.com/269
Status: OPEN (finite P case), SOLVED (infinite P case)

Statement:
Let P be a finite set of primes with |P| >= 2.
Let {a_1 < a_2 < ...} be the set of positive integers whose prime divisors are all in P.
Is the sum Σ_{n=1}^∞ 1/[a_1,...,a_n] irrational?

(where [a_1,...,a_n] denotes the least common multiple)

Known Results:
- Erdős (1973-1974): Problem posed in letter to Fibonacci Quarterly
- If P is infinite, the sum is ALWAYS irrational ("a simple exercise")
- If duplicate summands are removed, the sum is irrational

Key Insight:
The P-smooth numbers (those with all prime factors in P) form a multiplicative
set. The LCM of the first n of them grows in a structured way related to
P-adic valuations.

References:
- Erdős letter to editor, Fibonacci Quarterly Vol. 12 (1974), p. 335
- [ErGr80, p.65]
- [Er88c, p.106]
-/

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Finset.Lattice
import Mathlib.Algebra.Order.LatticeGroup
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Irrational
import Mathlib.Data.Nat.Order.Lemmas
import Mathlib.Topology.Algebra.InfiniteSum.Basic

open Nat BigOperators Finset

namespace Erdos269

/-! ## Part I: P-smooth Numbers -/

/--
**P-smooth Numbers**

A positive integer n is P-smooth if all its prime divisors belong to P.
Also called "P-friable" in some literature.

By convention, 1 is P-smooth for any P (vacuously true: 1 has no prime divisors).

Examples for P = {2, 3}:
- 1, 2, 3, 4, 6, 8, 9, 12, 16, 18, 24, 27, ...
-/
def IsPSmooth (P : Set ℕ) (n : ℕ) : Prop :=
  n > 0 ∧ ∀ p, p.Prime → p ∣ n → p ∈ P

/-- 1 is P-smooth for any P. -/
theorem one_isPSmooth (P : Set ℕ) : IsPSmooth P 1 := by
  constructor
  · exact Nat.one_pos
  · intro p hp hdiv
    have : p = 1 := Nat.eq_one_of_pos_of_self_mul_self_le hp.pos (Nat.le_of_dvd Nat.one_pos hdiv)
    exact absurd this (Nat.Prime.ne_one hp)

/-- If p ∈ P and p is prime, then p is P-smooth. -/
theorem prime_isPSmooth {P : Set ℕ} {p : ℕ} (hp : p.Prime) (hpP : p ∈ P) :
    IsPSmooth P p := by
  constructor
  · exact hp.pos
  · intro q hq hdiv
    have : q = p := (Nat.Prime.eq_one_or_self_of_dvd hp q hdiv).resolve_left hq.ne_one
    rwa [this]

/-- Product of P-smooth numbers is P-smooth. -/
axiom isPSmooth_mul {P : Set ℕ} {m n : ℕ} (hm : IsPSmooth P m) (hn : IsPSmooth P n) :
    IsPSmooth P (m * n)

/-! ## Part II: The Sequence of P-smooth Numbers -/

/--
**The P-smooth Sequence**

The infinite, strictly increasing sequence {a_0, a_1, ...} of all
P-smooth positive integers.

For P = {2, 3}: a = [1, 2, 3, 4, 6, 8, 9, 12, 16, 18, ...]
-/
noncomputable def smoothSeq (P : Set ℕ) : ℕ → ℕ :=
  Nat.nth (IsPSmooth P)

/-- The sequence is strictly increasing. -/
axiom smoothSeq_strictMono (P : Set ℕ) (hP : P.Nonempty) :
    StrictMono (smoothSeq P)

/-- smoothSeq P 0 = 1 for any nonempty P. -/
axiom smoothSeq_zero (P : Set ℕ) (hP : P.Nonempty) : smoothSeq P 0 = 1

/-- Each element is P-smooth. -/
axiom smoothSeq_isPSmooth (P : Set ℕ) (n : ℕ) : IsPSmooth P (smoothSeq P n)

/-! ## Part III: Partial LCM -/

/--
**Partial LCM**

L_n = [a_0, a_1, ..., a_{n-1}] = lcm of first n P-smooth numbers.

Note: L_0 = 1 (empty LCM), L_1 = a_0 = 1, L_2 = lcm(a_0, a_1) = a_1, etc.
-/
noncomputable def partialLcm (P : Set ℕ) (n : ℕ) : ℕ :=
  (Finset.range n).lcm (smoothSeq P)

/-- L_0 = 1 (LCM of empty set). -/
theorem partialLcm_zero (P : Set ℕ) : partialLcm P 0 = 1 := by
  simp [partialLcm]

/-- L_1 = a_0 = 1. -/
theorem partialLcm_one (P : Set ℕ) (hP : P.Nonempty) : partialLcm P 1 = 1 := by
  simp [partialLcm, smoothSeq_zero P hP]

/-- The sequence L_n is non-decreasing. -/
axiom partialLcm_mono (P : Set ℕ) : Monotone (partialLcm P)

/-- L_{n+1} = lcm(L_n, a_n). -/
theorem partialLcm_succ (P : Set ℕ) (n : ℕ) :
    partialLcm P (n + 1) = Nat.lcm (partialLcm P n) (smoothSeq P n) := by
  simp only [partialLcm, Finset.range_succ]
  rw [Finset.lcm_insert (Finset.not_mem_range_self n)]
  ring

/-- L_n is P-smooth (LCM of P-smooth numbers is P-smooth). -/
axiom partialLcm_isPSmooth (P : Set ℕ) (n : ℕ) : IsPSmooth P (partialLcm P n)

/-! ## Part IV: The Series -/

/--
**The LCM Series**

S(P) = Σ_{n=1}^∞ 1/L_n where L_n = [a_0, ..., a_{n-1}].

This series always converges since L_n grows at least exponentially.
-/
noncomputable def lcmSeries (P : Set ℕ) : ℝ :=
  ∑' n, (1 : ℝ) / (partialLcm P n)

/-- The series converges. -/
axiom lcmSeries_summable (P : Set ℕ) (hP : ∃ p ∈ P, p.Prime) :
    Summable (fun n => (1 : ℝ) / (partialLcm P n))

/-- The series is positive. -/
axiom lcmSeries_pos (P : Set ℕ) (hP : ∃ p ∈ P, p.Prime) :
    lcmSeries P > 0

/-! ## Part V: The Main Conjecture (OPEN) -/

/--
**Erdős Problem #269 (OPEN)**

For any finite set P of primes with |P| >= 2, the series
S(P) = Σ_{n=1}^∞ 1/[a_0,...,a_{n-1}] is irrational.
-/
axiom erdos_269 (P : Finset ℕ) (hPrime : ∀ p ∈ P, p.Prime) (hCard : P.card ≥ 2) :
    Irrational (lcmSeries (P : Set ℕ))

/--
**Alternative Statement (Rationality)**

The problem can also be stated as: is the series NOT rational?
-/
def isSeriesRational (P : Set ℕ) : Prop :=
  ∃ q : ℚ, (q : ℝ) = lcmSeries P

theorem erdos_269_equivalent (P : Finset ℕ) (hPrime : ∀ p ∈ P, p.Prime) (hCard : P.card ≥ 2) :
    ¬ isSeriesRational (P : Set ℕ) ↔ Irrational (lcmSeries (P : Set ℕ)) := by
  simp [isSeriesRational, irrational_iff_ne_rational]

/-! ## Part VI: The Infinite Case (SOLVED) -/

/--
**Infinite P Case (Solved)**

If P is an infinite set of primes, the series is ALWAYS irrational.

Erdős described this as "a simple exercise" - the key is that the sequence
of P-smooth numbers grows slowly enough that the series has infinitely many
distinct "p-adic contribution levels" for each prime p ∈ P.
-/
axiom erdos_269_infinite (P : Set ℕ) (hPrime : ∀ p ∈ P, p.Prime) (hInf : P.Infinite) :
    Irrational (lcmSeries P)

/-! ## Part VII: Examples -/

/-- The set {2, 3} gives the 3-smooth numbers. -/
def twoThreeSmooth : Set ℕ := {2, 3}

/-- {2, 3} has two primes. -/
theorem twoThreeSmooth_card : ({2, 3} : Finset ℕ).card = 2 := by native_decide

/-- 2 and 3 are prime. -/
theorem twoThreeSmooth_prime : ∀ p ∈ ({2, 3} : Finset ℕ), p.Prime := by
  intro p hp
  simp at hp
  rcases hp with rfl | rfl
  · exact Nat.prime_two
  · exact Nat.prime_three

/-- For P = {2,3}, the sequence starts 1, 2, 3, 4, 6, 8, 9, ... -/
axiom example_23_seq_0 : smoothSeq twoThreeSmooth 0 = 1
axiom example_23_seq_1 : smoothSeq twoThreeSmooth 1 = 2
axiom example_23_seq_2 : smoothSeq twoThreeSmooth 2 = 3
axiom example_23_seq_3 : smoothSeq twoThreeSmooth 3 = 4
axiom example_23_seq_4 : smoothSeq twoThreeSmooth 4 = 6
axiom example_23_seq_5 : smoothSeq twoThreeSmooth 5 = 8
axiom example_23_seq_6 : smoothSeq twoThreeSmooth 6 = 9

/-- Partial LCMs for {2,3}: L_1=1, L_2=2, L_3=6, L_4=12, L_5=12, ... -/
axiom example_23_lcm_1 : partialLcm twoThreeSmooth 1 = 1
axiom example_23_lcm_2 : partialLcm twoThreeSmooth 2 = 2
axiom example_23_lcm_3 : partialLcm twoThreeSmooth 3 = 6
axiom example_23_lcm_4 : partialLcm twoThreeSmooth 4 = 12
axiom example_23_lcm_5 : partialLcm twoThreeSmooth 5 = 12

/-! ## Part VIII: Structural Properties -/

/--
**P-adic Valuation**

For understanding the series, the key is the p-adic valuation v_p(L_n).
As n increases, v_p(L_n) increases in discrete jumps whenever a new
power of p enters the sequence.
-/

/-- The p-adic valuation of L_n. -/
noncomputable def lcmPadicVal (p n : ℕ) (P : Set ℕ) : ℕ :=
  Nat.padicValNat p (partialLcm P n)

/-- For p ∈ P, the p-adic valuation of L_n is non-decreasing. -/
axiom lcmPadicVal_mono (P : Set ℕ) (p : ℕ) (hp : p.Prime) (hpP : p ∈ P) :
    Monotone (fun n => lcmPadicVal p n P)

/-- v_p(L_n) increases when p^k enters the sequence. -/
axiom lcmPadicVal_jump (P : Set ℕ) (p k n : ℕ) (hp : p.Prime) (hpP : p ∈ P)
    (hk : p ^ k = smoothSeq P n) (hn : n > 0) :
    lcmPadicVal p (n + 1) P > lcmPadicVal p n P

/-! ## Part IX: Why It's Hard -/

/--
**The Difficulty**

For finite P, the series S(P) = Σ 1/L_n has a "finite structure" in some sense.
The L_n eventually become multiples of a fixed number (the LCM of all elements
up to some threshold). But proving irrationality requires understanding the
exact pattern of when L_n increases vs. stays constant.

The problem reduces to showing that the "effective" contributions from each
prime don't conspire to produce a rational sum.
-/

/-- Eventually, L_n stabilizes modulo some fixed M. -/
axiom partialLcm_eventually_periodic (P : Finset ℕ) (hP : P.card ≥ 2)
    (hPrime : ∀ p ∈ P, p.Prime) :
    ∃ M n₀ : ℕ, M > 0 ∧ ∀ n ≥ n₀, M ∣ partialLcm (P : Set ℕ) n

/-! ## Part X: Known Partial Result -/

/--
**Removing Duplicates**

Erdős noted that if we remove duplicate summands (terms where L_n = L_{n-1}),
the resulting sum is irrational.
-/
def distinctLcmTerms (P : Set ℕ) : Set ℕ :=
  { n | n = 0 ∨ partialLcm P n ≠ partialLcm P (n - 1) }

noncomputable def distinctLcmSeries (P : Set ℕ) : ℝ :=
  ∑' n : distinctLcmTerms P, (1 : ℝ) / (partialLcm P n)

/-- The series over distinct LCM values is irrational. -/
axiom erdos_269_distinct (P : Finset ℕ) (hPrime : ∀ p ∈ P, p.Prime) (hCard : P.card ≥ 2) :
    Irrational (distinctLcmSeries (P : Set ℕ))

/-! ## Part XI: Summary -/

/--
**Erdős Problem #269: Summary**

For P = finite set of primes with |P| >= 2:
Let {a_n} be the P-smooth numbers, L_n = [a_0,...,a_{n-1}].

**Question:** Is Σ_{n=1}^∞ 1/L_n irrational?

**Known:**
- For infinite P: YES, always irrational (simple exercise)
- For finite P with duplicates removed: YES, irrational
- For finite P with duplicates: OPEN

**Key Challenge:**
When L_n = L_{n-1} (the new smooth number divides the old LCM),
we get repeated terms. Understanding this pattern is crucial.
-/
theorem erdos_269_summary :
    -- Infinite case is solved
    (∀ P : Set ℕ, (∀ p ∈ P, p.Prime) → P.Infinite → Irrational (lcmSeries P)) ∧
    -- Distinct case is solved for finite P
    (∀ P : Finset ℕ, (∀ p ∈ P, p.Prime) → P.card ≥ 2 →
      Irrational (distinctLcmSeries (P : Set ℕ))) ∧
    -- General finite case is open
    True := by
  exact ⟨erdos_269_infinite, erdos_269_distinct, trivial⟩

/-- The problem remains OPEN for finite P with duplicates. -/
theorem erdos_269_open :
    True := trivial

end Erdos269
