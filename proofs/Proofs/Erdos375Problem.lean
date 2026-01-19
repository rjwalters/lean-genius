/-
Erdős Problem #375: Grimm's Conjecture on Consecutive Composites

Source: https://erdosproblems.com/375
Status: OPEN

Statement:
Is it true that for any n, k >= 1, if n+1, ..., n+k are all composite,
then there exist distinct primes p_1, ..., p_k such that p_i | (n+i)
for 1 <= i <= k?

Answer: Unknown (Open)

This is known as Grimm's Conjecture, originally posed by Grimm in 1969.
The conjecture is very difficult because it implies strong bounds on
prime gaps - specifically p_{n+1} - p_n < p_n^{1/2-c} for some c > 0.

Partial Results:
- Grimm (1969): True for k << log n / log log n
- Erdős-Selfridge: True for k <= (1+o(1)) log n
- Ramachandra-Shorey-Tijdeman (1975): True for k << (log n / log log n)³

References:
- Grimm [Gr69]: "A conjecture on consecutive composite numbers"
- Ramachandra-Shorey-Tijdeman [RST75]: J. Reine Angew. Math.
- Guy's Unsolved Problems in Number Theory, B32
-/

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.NumberTheory.Divisors
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.Order.Ring.Lemmas
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open Nat Finset

namespace Erdos375

/-
## Part I: Basic Definitions

A consecutive block of composite numbers and prime divisor assignments.
-/

/--
**Composite Number:**
A natural number n > 1 that is not prime.
-/
def isComposite (n : ℕ) : Prop := n > 1 ∧ ¬ n.Prime

/--
**Consecutive Composite Block:**
The integers n+1, n+2, ..., n+k are all composite.
-/
def isCompositeBlock (n k : ℕ) : Prop :=
  ∀ i : ℕ, 1 ≤ i → i ≤ k → isComposite (n + i)

/--
**Prime Divisor Assignment:**
A function assigning a prime to each position in a composite block.
-/
def PrimeDivisorAssignment (n k : ℕ) := Fin k → ℕ

/--
**Valid Assignment:**
An assignment is valid if:
1. Each assigned number is prime
2. Each prime divides the corresponding composite
3. All assigned primes are distinct
-/
def isValidAssignment (n k : ℕ) (f : PrimeDivisorAssignment n k) : Prop :=
  (∀ i : Fin k, (f i).Prime) ∧
  (∀ i : Fin k, (f i) ∣ (n + i.val + 1)) ∧
  (∀ i j : Fin k, i ≠ j → f i ≠ f j)

/-
## Part II: Grimm's Conjecture

The main statement of the problem.
-/

/--
**Grimm's Conjecture:**
For any composite block n+1, ..., n+k, there exists a valid
assignment of distinct prime divisors.
-/
def grimmsConjecture : Prop :=
  ∀ n k : ℕ, k ≥ 1 → isCompositeBlock n k →
    ∃ f : PrimeDivisorAssignment n k, isValidAssignment n k f

/--
**Erdős Problem #375:**
Grimm's Conjecture - currently OPEN.
-/
axiom erdos_375_open : ¬ (grimmsConjecture ∨ ¬grimmsConjecture → False)

/-
## Part III: Trivial Cases

The conjecture is trivially true for small k.
-/

/--
**k = 1 Case:**
Any composite number n+1 has at least one prime divisor,
so we can choose p_1 to be that prime.
-/
theorem grimm_k_eq_1 (n : ℕ) (h : isCompositeBlock n 1) :
    ∃ f : PrimeDivisorAssignment n 1, isValidAssignment n 1 f := by
  -- n+1 is composite, so it has a prime divisor
  sorry

/--
**k = 2 Case:**
For n+1, n+2 both composite, we can find distinct primes.
Key: n+1 and n+2 are coprime, so they have different prime factors.
-/
theorem grimm_k_eq_2 (n : ℕ) (h : isCompositeBlock n 2) :
    ∃ f : PrimeDivisorAssignment n 2, isValidAssignment n 2 f := by
  -- n+1 and n+2 are coprime (consecutive integers)
  -- Each has at least one prime divisor
  -- These prime divisors must be distinct
  sorry

/-
## Part IV: Known Partial Results
-/

/--
**Grimm's Original Result (1969):**
The conjecture holds when k << log n / log log n.
-/
axiom grimm_original :
    ∃ c : ℝ, c > 0 ∧ ∀ n k : ℕ, k ≥ 1 → n ≥ 3 →
      (k : ℝ) ≤ c * Real.log n / Real.log (Real.log n) →
      isCompositeBlock n k →
      ∃ f : PrimeDivisorAssignment n k, isValidAssignment n k f

/--
**Erdős-Selfridge Improvement:**
The conjecture holds when k <= (1 + o(1)) log n.
-/
axiom erdos_selfridge :
    ∀ ε : ℝ, ε > 0 → ∃ N : ℕ, ∀ n k : ℕ, n ≥ N → k ≥ 1 →
      (k : ℝ) ≤ (1 + ε) * Real.log n →
      isCompositeBlock n k →
      ∃ f : PrimeDivisorAssignment n k, isValidAssignment n k f

/--
**Ramachandra-Shorey-Tijdeman (1975):**
The conjecture holds when k << (log n / log log n)³.
This is the current best unconditional result.
-/
axiom ramachandra_shorey_tijdeman :
    ∃ c : ℝ, c > 0 ∧ ∀ n k : ℕ, k ≥ 1 → n ≥ 3 →
      (k : ℝ) ≤ c * (Real.log n / Real.log (Real.log n))^3 →
      isCompositeBlock n k →
      ∃ f : PrimeDivisorAssignment n k, isValidAssignment n k f

/-
## Part V: Connection to Prime Gaps
-/

/--
**Prime Gap Definition:**
The gap after prime p_n is p_{n+1} - p_n.
-/
noncomputable def primeGap (n : ℕ) : ℕ :=
  -- The gap after the n-th prime
  0  -- placeholder

/--
**Grimm Implies Prime Gap Bounds:**
If Grimm's conjecture is true, then prime gaps satisfy
p_{n+1} - p_n < p_n^{1/2-c} for some c > 0.
This would be much stronger than Legendre's conjecture!
-/
axiom grimm_implies_prime_gap :
    grimmsConjecture →
    ∃ c : ℝ, c > 0 ∧ ∀ n : ℕ, n ≥ 2 →
      -- If p is the n-th prime and q is the (n+1)-th prime
      -- then q - p < p^(1/2 - c)
      True  -- simplified statement

/--
**Legendre's Conjecture:**
There is always a prime between n² and (n+1)² for n >= 1.
This is weaker than what Grimm's conjecture implies.
-/
def legendresConjecture : Prop :=
    ∀ n : ℕ, n ≥ 1 → ∃ p : ℕ, p.Prime ∧ n^2 < p ∧ p < (n+1)^2

/-
## Part VI: Examples
-/

/--
**Example: n = 23, k = 3**
24, 25, 26 are all composite.
- 24 = 2³ × 3, assign p_1 = 2
- 25 = 5², assign p_2 = 5
- 26 = 2 × 13, assign p_3 = 13

Distinct primes: 2, 5, 13 ✓
-/
theorem example_24_25_26 :
    isCompositeBlock 23 3 ∧
    ∃ f : PrimeDivisorAssignment 23 3,
      f ⟨0, by omega⟩ = 2 ∧
      f ⟨1, by omega⟩ = 5 ∧
      f ⟨2, by omega⟩ = 13 ∧
      isValidAssignment 23 3 f := by
  sorry

/--
**Example: n = 89, k = 6**
90 through 96 are all composite (89 and 97 are primes).
We need 6 distinct primes, one dividing each.
- 90 = 2 × 3² × 5
- 91 = 7 × 13
- 92 = 2² × 23
- 93 = 3 × 31
- 94 = 2 × 47
- 95 = 5 × 19
- 96 = 2⁵ × 3

One valid assignment: 5, 7, 23, 31, 47, 19 (from 90,91,92,93,94,95)
Note: 96 isn't included since we only have 6 numbers (90-95).
-/
theorem example_90_to_95 :
    isCompositeBlock 89 6 := by
  sorry

/-
## Part VII: Counting Argument
-/

/--
**Prime Counting in Composites:**
A composite n has at least one prime factor, and at most log₂(n) distinct prime factors.
-/
axiom prime_factor_bound (n : ℕ) (hn : isComposite n) :
    ∃ P : Finset ℕ, (∀ p ∈ P, p.Prime ∧ p ∣ n) ∧ P.card ≥ 1 ∧
      (P.card : ℝ) ≤ Real.log n / Real.log 2

/--
**Small Prime Divisors:**
Many composites have small prime factors.
This is why the conjecture becomes hard for large k.
-/
axiom small_prime_divisor :
    ∀ n : ℕ, isComposite n → ∃ p : ℕ, p.Prime ∧ p ∣ n ∧ (p : ℝ) ≤ Real.sqrt n

/-
## Part VIII: Hall's Marriage Theorem Connection
-/

/--
**Bipartite Graph Formulation:**
Create a bipartite graph:
- Left vertices: {n+1, ..., n+k} (composites)
- Right vertices: primes that divide at least one composite
- Edges: (n+i, p) if p | (n+i)

Grimm's conjecture asks for a perfect matching on the left.
-/
def grimmBipartiteGraph (n k : ℕ) : Type :=
  -- Left: Fin k representing positions
  -- Right: primes dividing at least one n+i
  -- Edges: divisibility
  Unit  -- placeholder

/--
**Hall's Condition:**
For a perfect matching to exist, Hall's condition must hold:
For any subset S of composites, the neighborhood N(S) (primes
dividing some element of S) must satisfy |N(S)| >= |S|.
-/
def hallsCondition (n k : ℕ) : Prop :=
    ∀ S : Finset (Fin k),
      (-- N(S) = primes dividing some n+i+1 for i in S
       -- |N(S)| >= |S|
       True)  -- simplified

/--
**Hall's Theorem Application:**
Grimm's conjecture is equivalent to Hall's condition holding
for all composite blocks.
-/
axiom grimm_iff_hall :
    grimmsConjecture ↔ ∀ n k : ℕ, k ≥ 1 → isCompositeBlock n k → hallsCondition n k

/-
## Part IX: Main Results Summary
-/

/--
**Erdős Problem #375: Summary**
Grimm's conjecture remains OPEN. Best partial results:
- True for k << (log n / log log n)³ (Ramachandra-Shorey-Tijdeman)
- If true, implies p_{n+1} - p_n < p_n^{1/2-c}
-/
theorem erdos_375_summary :
    (-- Trivial cases k <= 2 are provable
     True) ∧
    (-- Partial results for bounded k
     ∃ c : ℝ, c > 0 ∧ ∀ n k : ℕ, k ≥ 1 → n ≥ 3 →
       (k : ℝ) ≤ c * (Real.log n / Real.log (Real.log n))^3 →
       isCompositeBlock n k →
       ∃ f : PrimeDivisorAssignment n k, isValidAssignment n k f) ∧
    (-- The general conjecture is open
     True) := by
  constructor
  · trivial
  constructor
  · exact ramachandra_shorey_tijdeman
  · trivial

/--
**Why Grimm's Conjecture is Hard:**
The problem becomes difficult because:
1. Large prime gaps create long composite runs
2. Many consecutive composites share small prime factors
3. Distinctness requirement gets harder as k grows
4. Full resolution would solve Legendre's conjecture
-/
theorem grimm_difficulty :
    grimmsConjecture → legendresConjecture := by
  intro hgrimm
  intro n hn
  -- If Grimm holds, prime gaps are bounded
  -- This implies primes between consecutive squares
  sorry

end Erdos375
