/-
Erdős Problem #453: Prime Products and Squares

Source: https://erdosproblems.com/453
Status: SOLVED

Statement:
Is it true that, for all sufficiently large n, there exists some i < n such that
  p_n² < p_{n+i} · p_{n-i}
where p_k is the k-th prime?

Answer: NO.

History:
- Erdős-Straus: Originally conjectured the answer is YES
- Selfridge: Conjectured the answer is NO
- Pomerance (1979): Proved Selfridge correct - infinitely many n have
    p_n² > p_{n+i} · p_{n-i} for all i < n

Pomerance's elegant proof uses convex hull geometry:
Consider points (n, log p_n). Since log p_n / n → 0, the non-horizontal part
of the convex hull boundary is concave with infinitely many vertices.
At each vertex n: 2·log p_n > log p_{n-i} + log p_{n+i} for all i < n,
which gives p_n² > p_{n+i} · p_{n-i}.

Tags: Number theory, Primes, Convex geometry, Prime number graph

References:
- Pomerance (1979): "The prime number graph", Math. Comp.
- Guy (2004): Unsolved Problems in Number Theory, Problem A14
-/

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Convex.Basic

open Nat Real

namespace Erdos453

/-
## Part I: The Prime Sequence
-/

/--
**The n-th Prime:**
p_n denotes the n-th prime number (1-indexed: p_1 = 2, p_2 = 3, ...).
-/
noncomputable def nthPrime (n : ℕ) : ℕ :=
  if n = 0 then 0 else Nat.Prime.nthPrime (n - 1)

/--
The first few primes.
-/
theorem nthPrime_values :
    nthPrime 1 = 2 ∧ nthPrime 2 = 3 ∧ nthPrime 3 = 5 ∧ nthPrime 4 = 7 := by
  sorry

/--
All nthPrime values for n ≥ 1 are prime.
-/
axiom nthPrime_is_prime (n : ℕ) (hn : n ≥ 1) : (nthPrime n).Prime

/--
The prime sequence is strictly increasing.
-/
axiom nthPrime_strictMono : StrictMono (fun n => nthPrime (n + 1))

/-
## Part II: The Erdős-Straus Conjecture
-/

/--
**Erdős-Straus Conjecture:**
For all sufficiently large n, there exists i < n such that p_n² < p_{n+i}·p_{n-i}.
-/
def ErdosStrausConjecture : Prop :=
  ∃ N : ℕ, ∀ n ≥ N, ∃ i : ℕ, i < n ∧ i > 0 ∧
    (nthPrime n : ℤ) ^ 2 < (nthPrime (n + i) : ℤ) * (nthPrime (n - i) : ℤ)

/--
**Selfridge's Counter-Conjecture:**
There are infinitely many n such that p_n² > p_{n+i}·p_{n-i} for all i < n.
-/
def SelfridgeConjecture : Prop :=
  ∀ N : ℕ, ∃ n ≥ N,
    ∀ i : ℕ, 0 < i → i < n →
      (nthPrime n : ℤ) ^ 2 > (nthPrime (n + i) : ℤ) * (nthPrime (n - i) : ℤ)

/--
These conjectures are mutually exclusive.
-/
theorem conjectures_mutually_exclusive :
    ErdosStrausConjecture → ¬SelfridgeConjecture := by
  intro hES hS
  obtain ⟨N, hN⟩ := hES
  obtain ⟨n, hn_ge, hn_all⟩ := hS N
  obtain ⟨i, hi_lt, hi_pos, hi_ineq⟩ := hN n hn_ge
  have := hn_all i hi_pos hi_lt
  omega

/-
## Part III: Log-Prime Convexity
-/

/--
**Log-Prime Function:**
a_n = log p_n for the n-th prime.
-/
noncomputable def logPrime (n : ℕ) : ℝ :=
  log (nthPrime n)

/--
**Key Property:**
log p_n / n → 0 as n → ∞.
(Follows from the Prime Number Theorem: p_n ~ n log n.)
-/
axiom logPrime_ratio_tendsto_zero :
    Filter.Tendsto (fun n => logPrime n / n) Filter.atTop (nhds 0)

/--
**Convex Hull Vertex:**
A point (n, a_n) is on the upper boundary of the convex hull if
2·a_n > a_{n-i} + a_{n+i} for all 0 < i < n.
-/
def IsConvexHullVertex (a : ℕ → ℝ) (n : ℕ) : Prop :=
  ∀ i : ℕ, 0 < i → i < n → 2 * a n > a (n - i) + a (n + i)

/--
**Pomerance's Key Lemma:**
For any sequence with a_n = o(n), there are infinitely many convex hull vertices.
-/
axiom pomerance_convex_hull_lemma (a : ℕ → ℝ)
    (h : Filter.Tendsto (fun n => a n / n) Filter.atTop (nhds 0)) :
    ∀ N : ℕ, ∃ n ≥ N, IsConvexHullVertex a n

/-
## Part IV: Pomerance's Theorem (1979)
-/

/--
**From Convexity to Inequality:**
If (n, log p_n) is a convex hull vertex, then p_n² > p_{n-i}·p_{n+i} for all i.
-/
theorem convexity_implies_product_bound (n : ℕ) (hn : n ≥ 2)
    (hv : IsConvexHullVertex logPrime n) :
    ∀ i : ℕ, 0 < i → i < n →
      (nthPrime n : ℤ) ^ 2 > (nthPrime (n + i) : ℤ) * (nthPrime (n - i) : ℤ) := by
  sorry

/--
**Pomerance (1979):**
There are infinitely many n such that p_n² > p_{n+i}·p_{n-i} for all 0 < i < n.
-/
axiom pomerance_1979 :
    ∀ N : ℕ, ∃ n ≥ N,
      ∀ i : ℕ, 0 < i → i < n →
        (nthPrime n : ℤ) ^ 2 > (nthPrime (n + i) : ℤ) * (nthPrime (n - i) : ℤ)

/--
Selfridge was correct.
-/
theorem selfridge_correct : SelfridgeConjecture := pomerance_1979

/--
Erdős-Straus were wrong.
-/
theorem erdos_straus_wrong : ¬ErdosStrausConjecture := by
  intro hES
  exact conjectures_mutually_exclusive hES selfridge_correct

/-
## Part V: Erdős Problem #453 Solution
-/

/--
**Erdős Problem #453: SOLVED**

Is it true that for all large n, there exists i < n with p_n² < p_{n+i}·p_{n-i}?

Answer: NO.

Pomerance (1979) proved there are infinitely many n where
p_n² > p_{n+i}·p_{n-i} for ALL i < n.
-/
theorem erdos_453_solution : ¬ErdosStrausConjecture :=
  erdos_straus_wrong

/--
The negative answer: infinitely many counterexamples exist.
-/
theorem erdos_453_negative_answer :
    ∀ N : ℕ, ∃ n ≥ N,
      ∀ i : ℕ, 0 < i → i < n →
        (nthPrime n : ℤ) ^ 2 > (nthPrime (n + i) : ℤ) * (nthPrime (n - i) : ℤ) :=
  pomerance_1979

/-
## Part VI: The Prime Number Graph
-/

/--
**Prime Number Graph:**
The graph of points (n, p_n) or equivalently (n, log p_n).
This visualization motivated Pomerance's proof.
-/
def primeGraph (n : ℕ) : ℝ × ℝ := (n, logPrime n)

/--
**Geometric Interpretation:**
The primes at convex hull vertices of the prime number graph satisfy the product bound.
-/
theorem geometric_interpretation :
    ∀ n : ℕ, IsConvexHullVertex logPrime n → n ≥ 2 →
      ∀ i : ℕ, 0 < i → i < n →
        (nthPrime n : ℤ) ^ 2 > (nthPrime (n + i) : ℤ) * (nthPrime (n - i) : ℤ) := by
  intro n hv hn i hi_pos hi_lt
  exact convexity_implies_product_bound n hn hv i hi_pos hi_lt

/-
## Part VII: Related Properties
-/

/--
**Log Convexity:**
At convex hull vertices: 2·log p_n > log p_{n-i} + log p_{n+i}.
-/
def LogConvexityProperty (n : ℕ) : Prop :=
  ∀ i : ℕ, 0 < i → i < n → 2 * logPrime n > logPrime (n - i) + logPrime (n + i)

/--
Log convexity is equivalent to being a convex hull vertex.
-/
theorem log_convexity_iff_vertex (n : ℕ) :
    LogConvexityProperty n ↔ IsConvexHullVertex logPrime n := by
  rfl

/--
**From Log to Product:**
2·log p_n > log p_{n-i} + log p_{n+i} implies p_n² > p_{n-i}·p_{n+i}.
-/
axiom log_to_product (n i : ℕ) (hn : n ≥ 2) (hi : 0 < i ∧ i < n)
    (h : 2 * logPrime n > logPrime (n - i) + logPrime (n + i)) :
    (nthPrime n : ℤ) ^ 2 > (nthPrime (n + i) : ℤ) * (nthPrime (n - i) : ℤ)

/-
## Part VIII: Density of Counterexamples
-/

/--
**Infinitude of Counterexamples:**
The set of n violating the Erdős-Straus conjecture is infinite.
-/
theorem counterexample_set_infinite :
    {n : ℕ | ∀ i : ℕ, 0 < i → i < n →
      (nthPrime n : ℤ) ^ 2 > (nthPrime (n + i) : ℤ) * (nthPrime (n - i) : ℤ)}.Infinite := by
  rw [Set.infinite_iff_nat_lt]
  intro N
  obtain ⟨n, hn, h⟩ := pomerance_1979 N
  exact ⟨n, h, hn⟩

/-
## Part IX: Connection to Guy's Collection
-/

/--
**Problem A14 in Guy's UPINT:**
This is Problem A14 in Richard Guy's "Unsolved Problems in Number Theory" (2004).
The problem appears in the section on prime number theory.
-/
theorem guy_problem_A14 :
    -- The Erdős-Straus conjecture is false
    ¬ErdosStrausConjecture :=
  erdos_453_solution

/-
## Part X: Summary
-/

/--
**Erdős Problem #453: Summary**

Problem: For all large n, is there i < n with p_n² < p_{n+i}·p_{n-i}?

Answer: NO.

Key results:
1. Erdős-Straus originally conjectured YES
2. Selfridge conjectured NO
3. Pomerance (1979) proved Selfridge correct
4. Proof uses convex hull of (n, log p_n)
5. Infinitely many n have p_n² > p_{n+i}·p_{n-i} for all i

The problem is SOLVED.
-/
theorem erdos_453_summary :
    -- The original conjecture is false
    ¬ErdosStrausConjecture ∧
    -- Infinitely many counterexamples exist
    SelfridgeConjecture :=
  ⟨erdos_straus_wrong, selfridge_correct⟩

end Erdos453
