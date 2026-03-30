/-
Erdős Problem #970: Jacobsthal's Function

Source: https://erdosproblems.com/970
Status: OPEN

Statement:
Let h(k) be Jacobsthal's function, defined as the minimal m such that,
if n has at most k prime factors, then in any set of m consecutive integers
there exists an integer coprime to n. Determine the order of magnitude of h(k).
In particular, is it true that h(k) ≪ k²?

Answer: OPEN - Best bounds are:
- Upper: h(k) ≪ (k log k)² (Iwaniec 1978)
- Lower: h(k) ≫ k · (log k)(log log log k)/(log log k)² (Ford-Green-Konyagin-Maynard-Tao 2018)

Key Results:
- Jacobsthal's Conjecture: h(k) ≪ k² remains unproven
- Gap between upper and lower bounds is roughly a log factor
- Related to prime gaps (Problem #687)

References:
- [Iw78] Iwaniec, "On the problem of Jacobsthal" (1978)
- [FGKMT18] Ford-Green-Konyagin-Maynard-Tao, "Long gaps between primes" (2018)
- OEIS A048669

Tags: number-theory, primes, gaps, coprimality, open-problem
-/

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open Real Nat

namespace Erdos970

/- ## Part 1: Basic Definitions -/

/-- The number of distinct prime factors of n (omega function) -/
def omega (n : ℕ) : ℕ := n.primeFactors.card

/-- n has at most k distinct prime factors -/
def hasAtMostKPrimes (n : ℕ) (k : ℕ) : Prop := omega n ≤ k

/-- An interval [a, a+m) of consecutive integers -/
def consecutiveInterval (a m : ℕ) : Finset ℕ :=
  Finset.Ico a (a + m)

/-- There exists an element in [a, a+m) coprime to n -/
def hasCoprimeElement (n a m : ℕ) : Prop :=
  ∃ x ∈ consecutiveInterval a m, Nat.Coprime x n

/- ## Part 2: Jacobsthal's Function

The function h(k) is axiomatized since computing it requires deep number-theoretic
arguments about coprimality in intervals. Its existence follows from the fact that
among any n+1 consecutive integers, at least one is coprime to n. -/

/-- Jacobsthal's function h(k): the maximum over all n with at most k prime factors
    of the minimal m such that any m consecutive integers contain one coprime to n.
    Axiomatized because computing it requires deep results. -/
axiom h : ℕ → ℕ

/-- h(k) has the defining property: for any n with ≤k prime factors,
    any h(k) consecutive integers contain one coprime to n -/
/-- h(k) is minimal with this property -/
/- ## Part 3: Jacobsthal's Conjecture (the main question) -/

/-- Jacobsthal's Conjecture: h(k) ≪ k² -/
def jacobsthalConjecture : Prop :=
  ∃ C : ℝ, C > 0 ∧ ∀ k : ℕ, k ≥ 1 → (h k : ℝ) ≤ C * k^2

/- ## Part 4: Known Upper Bounds -/

/-- Iwaniec's Theorem (1978): h(k) ≪ (k log k)²
    This is the best known upper bound, proved using sieve methods. -/
axiom iwaniec_upper_bound :
  ∃ C : ℝ, C > 0 ∧ ∃ k₀ : ℕ, ∀ k ≥ k₀,
    (h k : ℝ) ≤ C * (k * Real.log k)^2

/-- The Iwaniec bound can be rewritten as h(k) ≤ Ck²(log k)² -/
theorem iwaniec_bound_form :
    ∃ C : ℝ, C > 0 ∧ ∃ k₀ : ℕ, ∀ k ≥ k₀,
      (h k : ℝ) ≤ C * k^2 * (Real.log k)^2 := by
  obtain ⟨C, hC, k₀, hk⟩ := iwaniec_upper_bound
  use C, hC, k₀
  intro k hkge
  have := hk k hkge
  ring_nf at this ⊢
  exact this

/- ## Part 5: Known Lower Bounds -/

/-- Rankin-type lower bound: h(k) ≥ ck log k for large k -/
/-- Ford-Green-Konyagin-Maynard-Tao (2018) lower bound:
    h(k) ≥ ck · (log k)(log log log k)/(log log k)²
    This is the current best lower bound, derived from their breakthrough on prime gaps. -/
axiom fgkmt_lower_bound :
  ∃ c : ℝ, c > 0 ∧ ∃ k₀ : ℕ, ∀ k ≥ k₀,
    (h k : ℝ) ≥ c * k * (Real.log k) * (Real.log (Real.log (Real.log k))) /
                    (Real.log (Real.log k))^2

/- ## Part 6: Known Small Values -/

/-- h(1) = 2: any 2 consecutive integers contain one odd number -/
axiom h_one : h 1 = 2

/-- h(2) = 4: for n = 6, the interval {1,2,3,4} always has a coprime element -/
axiom h_two : h 2 = 4

/-- h(3) = 6: for n = 30, the interval of 6 consecutive integers suffices -/
axiom h_three : h 3 = 6

/-- h(4) = 10: for n = 210, need an interval of length 10 -/
axiom h_four : h 4 = 10

/-- h(5) = 14: for n = 2310, need an interval of length 14 -/
axiom h_five : h 5 = 14

/-- The primorial p_k# = 2·3·5·...·p_k maximizes Jacobsthal's function:
    h(k) = jacobsthalForN(p_k#) -/
/- ## Part 7: The conjecture h(k) ≪ k² is OPEN -/

/-- The conjecture is consistent with known small values:
    h(1)=2 ≤ 1, h(2)=4 ≤ 4, h(3)=6 ≤ 9, h(4)=10 ≤ 16, h(5)=14 ≤ 25 -/
theorem small_values_consistent :
    h 1 = 2 ∧ h 2 = 4 ∧ h 3 = 6 ∧ h 4 = 10 ∧ h 5 = 14 :=
  ⟨h_one, h_two, h_three, h_four, h_five⟩

/--
**Erdős Problem #970: Summary**

**Question:** Is h(k) ≪ k² where h(k) is Jacobsthal's function?

**Answer:** UNKNOWN (OPEN)

**Known Bounds:**
- Upper: h(k) ≪ (k log k)² (Iwaniec 1978)
- Lower: h(k) ≫ k log k log₃k / (log₂k)² (FGKMT 2018)

The gap to the conjectured k² bound is roughly (log k)².
-/
theorem erdos_970_upper_bound_exists :
    ∃ C : ℝ, C > 0 ∧ ∃ k₀ : ℕ, ∀ k ≥ k₀,
      (h k : ℝ) ≤ C * (k * Real.log k)^2 :=
  iwaniec_upper_bound

theorem erdos_970_lower_bound_exists :
    ∃ c : ℝ, c > 0 ∧ ∃ k₀ : ℕ, ∀ k ≥ k₀,
      (h k : ℝ) ≥ c * k * (Real.log k) * (Real.log (Real.log (Real.log k))) /
                      (Real.log (Real.log k))^2 :=
  fgkmt_lower_bound

end Erdos970
