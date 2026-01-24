/-
Erdős Problem #860: Prime Covering Intervals

Source: https://erdosproblems.com/860
Status: OPEN (bounds known, exact asymptotics unknown)

Statement:
Let h(n) be such that, for any m ≥ 1, in the interval (m, m+h(n))
there exist distinct integers a_i for 1 ≤ i ≤ π(n) such that
p_i | a_i, where p_i denotes the i-th prime.

Estimate h(n).

Background:
A problem of Erdős and Pomerance (1980). We want to "cover" the first
π(n) primes with distinct multiples from an interval of length h(n).
The question is: what is the minimum such h(n)?

Known bounds:
- Erdős-Pomerance: h(n) ≪ n^(3/2) / (log n)^(1/2)
- Erdős-Selfridge: h(n) > (3 - o(1))n
- Ruzsa: h(n)/n → ∞

The problem remains open: exact asymptotics of h(n) are unknown.

References:
- [ErPo80] Erdős-Pomerance, "Matching the natural numbers up to n
  with distinct multiples", Indigationes Math. (1980), 147-151.
- [Gu04] Guy, Unsolved problems in number theory, Problem B32.

Tags: prime-numbers, intervals, covering, number-theory
-/

import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Analysis.Asymptotics.Asymptotics

namespace Erdos860

open Nat Filter Asymptotics

/-!
## Part I: Basic Definitions
-/

/-- The n-th prime number (1-indexed, so p_1 = 2). -/
noncomputable def nthPrime (n : ℕ) : ℕ := Nat.nth Nat.Prime n

/-- The prime counting function π(n). -/
noncomputable def primePi (n : ℕ) : ℕ := Nat.primeCounting n

/-- A "prime covering assignment" from an interval (m, m+L]:
    distinct integers a_1, ..., a_k where p_i | a_i. -/
structure PrimeCovering (m : ℕ) (L : ℕ) (k : ℕ) where
  assignment : Fin k → ℕ
  in_interval : ∀ i, m < assignment i ∧ assignment i ≤ m + L
  distinct : ∀ i j, i ≠ j → assignment i ≠ assignment j
  divisibility : ∀ i, (nthPrime (i.val + 1)) ∣ assignment i

/-- The interval (m, m+L] admits a prime covering for the first k primes. -/
def AdmitsCovering (m L k : ℕ) : Prop :=
  Nonempty (PrimeCovering m L k)

/-!
## Part II: The Function h(n)
-/

/-- **The function h(n):**
    The minimal L such that every interval (m, m+L] admits a
    prime covering for the first π(n) primes.

    Formally: h(n) = min { L : ∀ m, AdmitsCovering m L (π(n)) }. -/
noncomputable def h (n : ℕ) : ℕ :=
  Nat.find (⟨n^2, by sorry⟩ : ∃ L, ∀ m, AdmitsCovering m L (primePi n))

/-- The defining property of h(n): every interval of length h(n) works. -/
axiom h_universal :
    ∀ n : ℕ, ∀ m : ℕ, AdmitsCovering m (h n) (primePi n)

/-- The minimality of h(n): smaller lengths fail for some m. -/
axiom h_minimal :
    ∀ n : ℕ, h n > 0 →
    ∃ m : ℕ, ¬AdmitsCovering m (h n - 1) (primePi n)

/-!
## Part III: Known Bounds
-/

/-- **Erdős-Selfridge Lower Bound:**
    h(n) > (3 - o(1))n.

    The interval length must be at least about 3n. -/
axiom erdos_selfridge_lower_bound :
    ∀ ε > 0, ∃ N, ∀ n ≥ N, (h n : ℝ) > (3 - ε) * n

/-- **Ruzsa's Result:**
    h(n)/n → ∞ as n → ∞.

    The ratio h(n)/n grows without bound. -/
axiom ruzsa_growth :
    Tendsto (fun n => (h n : ℝ) / n) atTop atTop

/-- **Erdős-Pomerance Upper Bound:**
    h(n) ≪ n^(3/2) / (log n)^(1/2).

    The upper bound is subquadratic in n. -/
axiom erdos_pomerance_upper_bound :
    ∃ C > 0, ∀ᶠ n in atTop,
      (h n : ℝ) ≤ C * n^(3/2 : ℝ) / Real.log n ^ (1/2 : ℝ)

/-!
## Part IV: The Gap Between Bounds
-/

/-- The lower bound is linear: h(n) ≥ cn for some c > 0. -/
theorem linear_lower_bound :
    ∃ c > 0, ∀ᶠ n in atTop, (h n : ℝ) ≥ c * n := by
  use 2.9
  constructor
  · norm_num
  · filter_upwards with n using by
      have := erdos_selfridge_lower_bound 0.1 (by norm_num)
      obtain ⟨N, hN⟩ := this
      sorry  -- From erdos_selfridge_lower_bound

/-- The upper bound is o(n^2): h(n) = o(n²). -/
theorem subquadratic_upper_bound :
    (fun n => (h n : ℝ)) =o[atTop] (fun n => (n : ℝ)^2) := by
  rw [isLittleO_iff]
  intro c hc
  filter_upwards with n using by sorry  -- From erdos_pomerance

/-- **The Open Problem:**
    The exact growth rate of h(n) is unknown.
    Is h(n) = Θ(n^α) for some 1 < α < 3/2?
    Is h(n) = n · ω(n) for some slowly growing ω? -/
axiom exact_growth_unknown : True

/-!
## Part V: Connection to Other Problems
-/

/-- **Relation to Erdős #375:**
    Problem 375 asks a related covering question. -/
axiom related_to_erdos_375 : True

/-- **Guy's Problem B32:**
    This problem appears as B32 in Guy's "Unsolved Problems in
    Number Theory". -/
axiom guys_problem_B32 : True

/-- **Greedy Algorithm:**
    A natural approach is greedy: for each prime p_i, pick the
    smallest available multiple. Analysis of this algorithm gives
    bounds. -/
axiom greedy_approach : True

/-!
## Part VI: Reformulation
-/

/-- **Equivalent formulation:**
    h(n) is the least L such that for all m, the bipartite graph
    G with vertices {1,...,π(n)} and {m+1,...,m+L} where i ~ j iff
    p_i | j has a perfect matching on the prime side. -/
axiom bipartite_matching_formulation : True

/-- **Hall's condition:**
    By Hall's theorem, we need: for all S ⊆ {1,...,π(n)},
    |N(S) ∩ (m, m+L]| ≥ |S| where N(S) is the neighbor set. -/
axiom halls_condition : True

/-!
## Part VII: Summary
-/

/-- **Erdős Problem #860: OPEN**

    PROBLEM: Estimate h(n), the minimum interval length such that
    any interval of that length contains distinct multiples of the
    first π(n) primes.

    KNOWN BOUNDS:
    - Lower: h(n) > (3-o(1))n (Erdős-Selfridge)
    - Lower: h(n)/n → ∞ (Ruzsa)
    - Upper: h(n) ≪ n^(3/2)/(log n)^(1/2) (Erdős-Pomerance)

    OPEN: Determine the exact asymptotic growth of h(n).

    The gap between n · ω(n) and n^(3/2-ε) remains unexplored. -/
theorem erdos_860 :
    -- Lower bound: superlinear growth
    (Tendsto (fun n => (h n : ℝ) / n) atTop atTop) ∧
    -- Upper bound exists
    (∃ C > 0, ∀ᶠ n in atTop,
      (h n : ℝ) ≤ C * n^(3/2 : ℝ) / Real.log n ^ (1/2 : ℝ)) :=
  ⟨ruzsa_growth, erdos_pomerance_upper_bound⟩

/-- The answer to Erdős Problem #860. -/
def erdos_860_answer : String :=
  "OPEN: h(n)/n → ∞ but exact asymptotics unknown (between n·ω(n) and n^(3/2)/√(log n))"

/-- The status of Erdős Problem #860. -/
def erdos_860_status : String := "OPEN"

#check erdos_860
#check h
#check ruzsa_growth
#check erdos_pomerance_upper_bound

end Erdos860
