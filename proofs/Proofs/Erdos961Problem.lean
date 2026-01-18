/-
  Erdős Problem #961: Smooth Numbers in Consecutive Intervals

  Source: https://erdosproblems.com/961
  Status: PARTIALLY SOLVED

  Statement:
  Let f(k) be the minimal n such that every set of n consecutive integers > k
  contains an integer divisible by a prime > k (equivalently, not (k+1)-smooth).
  Estimate f(k).

  This asks: how long can a run of consecutive k-smooth integers be?

  Known Results:
  - Sylvester-Schur [Er34]: f(k) ≤ k
  - Erdős [Er55d]: f(k) < 3k/log(k) for large k
  - Jutila [Ju74], Ramachandra-Shorey [RaSh73]:
    f(k) ≪ (log log log k / log log k) · (k/log k)

  Open Conjecture:
  f(k) ≪ (log k)^O(1) (polylogarithmic bound)

  Related to Problem #683 on smooth number gaps.

  Tags: number-theory, smooth-numbers, prime-factors, analytic-number-theory
-/

import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.NumberTheory.SmoothNumbers
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Asymptotics.Asymptotics
import Mathlib.Order.Filter.AtTopBot
import Mathlib.Tactic

namespace Erdos961

open Nat Finset Filter Real Asymptotics

/-! ## Part I: Smooth Numbers -/

/-- A positive integer is k-smooth if all its prime factors are ≤ k.

    Examples:
    - 12 = 2² · 3 is 3-smooth (prime factors are 2, 3)
    - 30 = 2 · 3 · 5 is 5-smooth but not 3-smooth
    - Any prime p is p-smooth but not (p-1)-smooth
-/
def isSmooth (k n : ℕ) : Prop :=
  n ≠ 0 ∧ ∀ p : ℕ, p.Prime → p ∣ n → p ≤ k

/-- Alternative characterization using Mathlib's smoothNumbers. -/
theorem isSmooth_iff_smoothNumbers (k n : ℕ) (hn : n ≠ 0) :
    isSmooth k n ↔ n ∈ Nat.smoothNumbers (k + 1) := by
  constructor
  · intro ⟨_, h⟩
    simp only [Nat.smoothNumbers, Nat.primFactors, Set.mem_setOf_eq]
    constructor
    · exact Nat.pos_of_ne_zero hn
    · intro p hp
      have hp' := Nat.prime_of_mem_primeFactors hp
      have hdiv := Nat.dvd_of_mem_primeFactors hp
      exact Nat.lt_add_one_iff.mpr (h p hp' hdiv)
  · intro h
    constructor
    · exact hn
    · intro p hp hdiv
      simp only [Nat.smoothNumbers, Set.mem_setOf_eq] at h
      have : p ∈ n.primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hdiv⟩
      exact Nat.lt_add_one_iff.mp (h.2 p this)

/-! ## Part II: The Key Property -/

/-- The property that among any n consecutive integers starting at m > k,
    at least one is NOT k-smooth (has a prime factor > k). -/
def HasLargePrimeFactor (k n : ℕ) : Prop :=
  ∀ m ≥ k + 1, ∃ i ∈ Set.Ico m (m + n), ¬isSmooth k i

/-- Equivalent formulation using smoothNumbers. -/
theorem haslargeprimefactor_iff (k n : ℕ) :
    HasLargePrimeFactor k n ↔
    ∀ m ≥ k + 1, ∃ i ∈ Set.Ico m (m + n), i ∉ Nat.smoothNumbers (k + 1) := by
  constructor
  · intro h m hm
    obtain ⟨i, hi, hns⟩ := h m hm
    use i, hi
    intro hs
    apply hns
    have : i ≠ 0 := by
      intro heq
      simp [Set.Ico, heq] at hi
      omega
    exact (isSmooth_iff_smoothNumbers k i this).mpr hs
  · intro h m hm
    obtain ⟨i, hi, hns⟩ := h m hm
    use i, hi
    intro ⟨hne, hsmooth⟩
    apply hns
    exact (isSmooth_iff_smoothNumbers k i hne).mp ⟨hne, hsmooth⟩

/-! ## Part III: The Function f(k) -/

/-- Sylvester-Schur theorem: any k consecutive integers > k contain
    a number with a prime factor > k. -/
axiom sylvester_schur (k : ℕ) : HasLargePrimeFactor k k

/-- f(k) is well-defined: there exists some n with the property. -/
theorem f_well_defined (k : ℕ) : ∃ n, HasLargePrimeFactor k n := ⟨k, sylvester_schur k⟩

/-- f(k) = minimal n such that any n consecutive integers > k
    contain a number with a prime factor > k. -/
noncomputable def f (k : ℕ) : ℕ := Nat.find (f_well_defined k)

/-- f(k) has the defining property. -/
theorem f_spec (k : ℕ) : HasLargePrimeFactor k (f k) :=
  Nat.find_spec (f_well_defined k)

/-- f(k) is the minimal such n. -/
theorem f_min (k n : ℕ) (h : HasLargePrimeFactor k n) : f k ≤ n := by
  exact Nat.find_min' (f_well_defined k) h

/-! ## Part IV: Sylvester-Schur Bound -/

/-- Sylvester-Schur (1934): f(k) ≤ k.

    This classical result says any k consecutive integers > k
    contain an integer divisible by a prime > k.

    Proof idea: Among k consecutive integers, at least one is
    divisible by a prime > k by the pigeonhole principle and
    prime distribution.
-/
theorem sylvester_schur_bound (k : ℕ) : f k ≤ k := f_min k k (sylvester_schur k)

/-! ## Part V: Erdős Bound -/

/-- Erdős (1955): f(k) < 3k/log(k) for sufficiently large k.

    This was a significant improvement over f(k) ≤ k,
    showing sublinear growth in k.
-/
axiom erdos_1955_bound :
    ∀ᶠ k in atTop, (f k : ℝ) < 3 * k / log k

/-- The Erdős bound gives f(k) = o(k). -/
theorem f_sublinear : (fun k => (f k : ℝ)) =o[atTop] (fun k => (k : ℝ)) := by
  sorry

/-! ## Part VI: Jutila and Ramachandra-Shorey Bound -/

/-- Jutila (1974) and Ramachandra-Shorey (1973) proved a much stronger bound:

    f(k) ≪ (log log log k / log log k) · (k / log k)

    This shows f(k) grows much slower than k/log(k).
-/
axiom jutila_ramachandra_shorey_bound :
    (fun k => (f k : ℝ)) =O[atTop]
      (fun k => log (log (log k)) / log (log k) * (k / log k))

/-! ## Part VII: The Open Conjecture -/

/-- The main open conjecture: f(k) ≪ (log k)^C for some constant C.

    This would be a dramatic improvement, showing polylogarithmic growth.
    Currently OPEN - the gap between the known bound and this conjecture
    is enormous.
-/
def polylog_conjecture : Prop :=
  ∃ C : ℝ, C > 0 ∧ ∀ᶠ k in atTop, (f k : ℝ) < (log k) ^ C

/-- The conjecture is stated but unresolved. -/
axiom polylog_conjecture_open : polylog_conjecture ↔ answer(sorry)

/-! ## Part VIII: Small Examples -/

/-- For k = 2: Any 2 consecutive integers > 2 contain a non-2-smooth number.

    2-smooth numbers are powers of 2: 1, 2, 4, 8, 16, ...
    Between any two powers of 2, there's a gap, so f(2) is small.
-/
theorem example_k2 : f 2 ≤ 2 := sylvester_schur_bound 2

/-- For k = 3: 3-smooth numbers are of form 2^a · 3^b.
    First few: 1, 2, 3, 4, 6, 8, 9, 12, ...
    Gaps grow, so consecutive integers quickly have large prime factors.
-/
theorem example_k3 : f 3 ≤ 3 := sylvester_schur_bound 3

/-! ## Part IX: Connection to Problem #683 -/

/-- Problem #683 asks about gaps between smooth numbers.

    If g(k) = largest gap between consecutive k-smooth numbers,
    then f(k) ≤ g(k) + 1.

    The two problems are "essentially equivalent" per erdosproblems.com.
-/
def smooth_gap (k : ℕ) : ℕ :=
  sSup {d : ℕ | ∃ n ∈ Nat.smoothNumbers (k + 1),
    ∀ m ∈ Set.Ioo n (n + d), m ∉ Nat.smoothNumbers (k + 1)}

/-- Connection: f(k) is bounded by the smooth gap plus 1. -/
theorem f_le_smooth_gap_succ (k : ℕ) (hk : k ≥ 1) :
    f k ≤ smooth_gap k + 1 := by
  sorry

/-! ## Part X: Bounds Summary -/

/-- Summary of known bounds on f(k):

    Trivial:           f(k) ≤ k           (Sylvester-Schur 1934)
    Linear:            f(k) < 3k/log(k)   (Erdős 1955)
    Sublinear:         f(k) ≪ k · (log log log k)/(log k · log log k)
                                          (Jutila, Ramachandra-Shorey 1973-74)
    Conjectured:       f(k) ≪ (log k)^C   (OPEN)

    The gap between the best known O(k · polylog/log²) and
    conjectured O(polylog) is vast.
-/
theorem bounds_summary (k : ℕ) (hk : k ≥ 2) :
    f k ≤ k ∧
    (∀ᶠ k in atTop, (f k : ℝ) < 3 * k / log k) := by
  constructor
  · exact sylvester_schur_bound k
  · exact erdos_1955_bound

end Erdos961

/-!
## Summary

This file formalizes Erdős Problem #961 on smooth numbers in consecutive intervals.

**Status**: PARTIALLY SOLVED (bounds known, conjecture open)

**The Problem**: Let f(k) = minimal n such that any n consecutive integers > k
contain a number with a prime factor > k. Estimate f(k).

**Historical Progress**:
- 1934: Sylvester-Schur proved f(k) ≤ k
- 1955: Erdős proved f(k) < 3k/log(k)
- 1973-74: Jutila, Ramachandra-Shorey proved f(k) ≪ (log log log k / log log k) · (k/log k)

**Open Conjecture**: f(k) ≪ (log k)^O(1)

**What we formalize**:
1. Smooth numbers and the key property
2. The function f(k) and its minimality
3. Classical Sylvester-Schur bound
4. Erdős's sublinear bound
5. Jutila-Ramachandra-Shorey's strongest known bound
6. The polylogarithmic conjecture
7. Connection to Problem #683

**Key sorries/axioms**:
- `sylvester_schur`: Classical result requiring prime distribution analysis
- `erdos_1955_bound`: Requires analytic number theory
- `jutila_ramachandra_shorey_bound`: Advanced sieve methods
- `polylog_conjecture_open`: The main open question
-/
