/-
  Erdős Problem #454: Prime Sum Deviations

  Source: https://erdosproblems.com/454
  Status: OPEN (partial result by Pomerance 1979)

  Statement:
  Let f(n) = min_{i<n} (p_{n+i} + p_{n-i}), where p_k is the k-th prime.
  Is it true that limsup_{n→∞} (f(n) - 2p_n) = ∞?

  Known Results:
  - Pomerance (1979): The limsup is at least 2.

  Intuition:
  If primes were perfectly "evenly spaced", we'd have p_{n+i} + p_{n-i} ≈ 2p_n
  for all i, giving f(n) ≈ 2p_n. The question asks whether deviations from
  this ideal behavior can be arbitrarily large.

  References:
  [Po79] Pomerance, Carl, "The prime number graph." Math. Comp. (1979), 399-408.

  Tags: number-theory, primes, analytic-number-theory
-/

import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Order.Filter.Basic
import Mathlib.Order.LiminfLimsup
import Mathlib.Topology.Instances.ENat
import Mathlib.Tactic

namespace Erdos454

open Nat Filter

/-! ## Part I: The nth Prime Function -/

/-- The k-th prime number (0-indexed: p_0 = 2, p_1 = 3, p_2 = 5, ...). -/
noncomputable def nthPrime (k : ℕ) : ℕ := k.nth Prime

/-- The first prime is 2. -/
theorem nthPrime_zero : nthPrime 0 = 2 := by
  simp [nthPrime, Nat.nth_prime_zero]

/-- The second prime is 3. -/
theorem nthPrime_one : nthPrime 1 = 3 := by
  simp [nthPrime, Nat.nth_prime_one]

/-- The third prime is 5. -/
theorem nthPrime_two : nthPrime 2 = 5 := by
  simp [nthPrime]
  native_decide

/-- All nth primes are prime. -/
theorem nthPrime_prime (k : ℕ) : (nthPrime k).Prime := Nat.prime_nth_prime k

/-- The nth prime sequence is strictly increasing. -/
theorem nthPrime_strictMono : StrictMono nthPrime := Nat.nth_prime_strictMono

/-! ## Part II: The Function f(n) -/

/-- The sum of symmetric primes around position n.

    For i < n, this computes p_{n+i} + p_{n-i}, measuring how the
    sum of primes equidistant from p_n compares to 2p_n. -/
noncomputable def symmetricPrimeSum (n i : ℕ) (hi : i < n) : ℕ :=
  nthPrime (n + i) + nthPrime (n - i)

/-- f(n) = min_{i<n} (p_{n+i} + p_{n-i})

    This is the minimum sum of primes at equal distances from position n.
    If primes were evenly spaced, f(n) would equal 2p_n. -/
noncomputable def f (n : ℕ) : ℕ :=
  if h : n = 0 then 0
  else ⨅ i : Fin n, nthPrime (n + i) + nthPrime (n - i)

/-- Alternative definition using Finset.inf' for computability intuition. -/
noncomputable def f' (n : ℕ) : ℕ :=
  if h : n = 0 then 0
  else (Finset.range n).inf' (by simp) (fun i => nthPrime (n + i) + nthPrime (n - i))

/-- The two definitions are equivalent. -/
theorem f_eq_f' (n : ℕ) : f n = f' n := by
  sorry

/-! ## Part III: The Deviation from 2p_n -/

/-- The deviation of f(n) from twice the n-th prime.

    This is the key quantity: f(n) - 2p_n.
    If positive, the minimum symmetric sum exceeds 2p_n.
    If negative, there exist i where p_{n+i} + p_{n-i} < 2p_n. -/
noncomputable def deviation (n : ℕ) : ℤ :=
  (f n : ℤ) - 2 * (nthPrime n : ℤ)

/-- The deviation as an extended natural (for limsup computation). -/
noncomputable def deviationENat (n : ℕ) : ℕ∞ :=
  if (f n : ℤ) ≥ 2 * (nthPrime n : ℤ) then
    ((f n : ℤ) - 2 * (nthPrime n : ℤ)).toNat
  else 0

/-! ## Part IV: Understanding Symmetric Prime Sums -/

/-- For i = 0: p_n + p_n = 2p_n, so this term contributes deviation 0. -/
theorem symmetric_sum_at_zero (n : ℕ) (hn : n > 0) :
    nthPrime (n + 0) + nthPrime (n - 0) = 2 * nthPrime n := by
  simp [mul_comm]

/-- The minimum is at most 2p_n (achieved at i = 0). -/
theorem f_le_twice_nthPrime (n : ℕ) (hn : n > 0) : f n ≤ 2 * nthPrime n := by
  sorry

/-- For i > 0, by strict monotonicity of primes:
    p_{n+i} > p_n and p_{n-i} < p_n (assuming n - i ≥ 0). -/
theorem asymmetric_behavior (n i : ℕ) (hi : 0 < i) (hin : i < n) :
    nthPrime (n + i) > nthPrime n ∧ nthPrime (n - i) < nthPrime n := by
  constructor
  · exact nthPrime_strictMono (by omega)
  · exact nthPrime_strictMono (by omega)

/-! ## Part V: Pomerance's Lower Bound -/

/-- **Pomerance (1979)**: The limsup of deviations is at least 2.

    This means for infinitely many n, f(n) - 2p_n ≥ 2, i.e.,
    the minimum symmetric sum exceeds twice the central prime by at least 2. -/
axiom pomerance_1979 : 2 ≤ limsup deviationENat atTop

/-- Corollary: The limsup is positive. -/
theorem limsup_pos : 0 < limsup deviationENat atTop := by
  have h := pomerance_1979
  calc 0 < 2 := by norm_num
    _ ≤ limsup deviationENat atTop := h

/-- Corollary: Infinitely many n have deviation at least 2. -/
theorem infinitely_many_deviation_ge_2 :
    {n : ℕ | deviationENat n ≥ 2}.Infinite := by
  sorry

/-! ## Part VI: The Main Conjecture -/

/-- **Erdős Problem #454 (Main Conjecture)**

    Is limsup_{n→∞} (f(n) - 2p_n) = ∞?

    This asks whether there are n with arbitrarily large deviations,
    meaning the minimum symmetric prime sum can exceed 2p_n by any amount. -/
def Erdos454Conjecture : Prop :=
  limsup deviationENat atTop = ⊤

/-- The negation: deviations are bounded. -/
def Erdos454Negation : Prop :=
  ∃ M : ℕ, limsup deviationENat atTop ≤ M

/-- The conjecture and its negation are complementary. -/
theorem conjecture_iff_not_negation :
    Erdos454Conjecture ↔ ¬Erdos454Negation := by
  sorry

/-! ## Part VII: Heuristic Analysis -/

/-- Heuristic: If prime gaps grow like log p, then p_{n+i} ≈ p_n + i * log(p_n).
    This gives p_{n+i} + p_{n-i} ≈ 2p_n for all i (gaps cancel).
    But prime gaps are irregular, leading to deviations. -/
def primeGapHeuristic (n : ℕ) : Prop :=
  ∃ C : ℝ, ∀ k, |(nthPrime (k + 1) : ℝ) - nthPrime k - Real.log (nthPrime k)| ≤ C

/-- Prime gaps can be large: there exist arbitrarily large gaps. -/
axiom large_prime_gaps_exist :
    ∀ G : ℕ, ∃ k, nthPrime (k + 1) - nthPrime k ≥ G

/-- Connection: Large gaps could cause large deviations. -/
theorem gap_deviation_connection :
    (∀ n, deviation n ≤ 0) → ¬∃ G : ℕ, G > 0 ∧ ∀ k, nthPrime (k + 1) - nthPrime k < G := by
  sorry

/-! ## Part VIII: Examples -/

/-- Example: Computing f(3) = min(p_3 + p_3, p_4 + p_2, p_5 + p_1)
                           = min(5+5, 7+3, 11+3) = min(10, 10, 14) = 10.
    2*p_3 = 2*5 = 10, so deviation(3) = 0. -/
theorem example_f_3 : f 3 = 10 := by
  sorry

/-- Example: 2*p_3 = 10 -/
theorem example_twice_p3 : 2 * nthPrime 3 = 10 := by
  simp [nthPrime]
  native_decide

/-- Example: The deviation at n=3 is 0. -/
theorem example_deviation_3 : deviation 3 = 0 := by
  sorry

/-! ## Part IX: Related Problems -/

/-- Problem #458 is related: it asks about consecutive prime sums.
    Both involve understanding how prime sums deviate from expectations. -/
def relatedToErdos458 : Prop :=
  True -- Placeholder for documentation

/-- The prime number theorem context: p_n ~ n log n.
    This gives f(n) ~ 2n log n on average. -/
axiom prime_number_theorem_asymptotic :
    Tendsto (fun n => (nthPrime n : ℝ) / (n * Real.log n)) atTop (𝓝 1)

/-! ## Part X: What Would Resolve the Conjecture -/

/-- To prove the conjecture (limsup = ∞), one would need to show:
    For every M, there exists n with f(n) - 2p_n > M.

    This requires finding n where all symmetric sums are large. -/
def witnessForConjecture (M : ℕ) : Prop :=
  ∃ n, ∀ i : Fin n, nthPrime (n + i) + nthPrime (n - i) > 2 * nthPrime n + M

/-- To disprove (limsup ≤ M), one would show:
    Eventually, f(n) ≤ 2p_n + M for all n.

    This requires uniform control over prime gaps. -/
def witnessForNegation (M : ℕ) : Prop :=
  ∀ᶠ n in atTop, f n ≤ 2 * nthPrime n + M

/-! ## Part XI: The Prime Number Graph -/

/-- Pomerance's paper "The Prime Number Graph" studies the graph
    where vertex n is connected to m if p_n + p_m = p_k for some k.

    The structure of this graph relates to symmetric prime sums. -/
def primeNumberGraph : SimpleGraph ℕ where
  Adj n m := n ≠ m ∧ ∃ k, nthPrime n + nthPrime m = nthPrime k
  symm := by
    intro n m ⟨hne, hk⟩
    exact ⟨hne.symm, by obtain ⟨k, hk⟩ := hk; exact ⟨k, by ring_nf; exact hk⟩⟩
  loopless := by
    intro n ⟨h, _⟩
    exact h rfl

/-- Goldbach-like property: Can every even number be expressed as
    a sum of two primes from symmetric positions? -/
def goldbachSymmetric : Prop :=
  ∀ m : ℕ, Even m → m > 4 →
    ∃ n i, i < n ∧ nthPrime (n + i) + nthPrime (n - i) = m

end Erdos454

/-!
## Summary

This file formalizes Erdős Problem #454 on prime sum deviations.

**Status**: OPEN (with lower bound by Pomerance 1979)

**The Problem**: Let f(n) = min_{i<n} (p_{n+i} + p_{n-i}).
Is limsup_{n→∞} (f(n) - 2p_n) = ∞?

**Known Results**:
- Pomerance (1979): limsup ≥ 2

**What we formalize**:
1. The nth prime function and its properties
2. The symmetric prime sum function f(n)
3. The deviation f(n) - 2p_n
4. Pomerance's lower bound (axiomatized)
5. The main conjecture
6. Heuristic analysis of prime gaps
7. The Prime Number Graph

**Key axioms**:
- `pomerance_1979`: limsup ≥ 2
- `large_prime_gaps_exist`: arbitrarily large prime gaps exist
- `prime_number_theorem_asymptotic`: p_n ~ n log n

**Intuition**: If primes were evenly spaced, f(n) = 2p_n exactly.
The conjecture asks whether irregular prime spacing causes
arbitrarily large deviations from this ideal.
-/
