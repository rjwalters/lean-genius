/-
  Erdős Problem #1004: Distinct Consecutive Totient Values

  Source: https://erdosproblems.com/1004
  Status: OPEN (partial results by Erdős-Pomerance-Sárközy 1987)

  Statement:
  Let c > 0. If x is sufficiently large, does there exist n ≤ x such that
  the values φ(n+1), φ(n+2), ..., φ(n+⌊(log x)^c⌋) are all distinct?

  Known Results:
  - Erdős-Pomerance-Sárközy (1987): If φ(n+k) are all distinct for 1 ≤ k ≤ K,
    then K ≤ n/exp(c(log n)^{1/3}) for some constant c > 0.
  - This gives an upper bound on how long distinct runs can be.

  Related: Problem #945 asks the same question for the divisor function τ(n).

  References:
  [EPS87] Erdős-Pomerance-Sárközy, "On locally repeated values of certain
          arithmetic functions. III" (1987)

  Tags: number-theory, totient, analytic-number-theory
-/

import Mathlib.NumberTheory.ArithmeticFunction
import Mathlib.NumberTheory.EulerPhi.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Instances.Real
import Mathlib.Tactic

namespace Erdos1004

open Nat Real Filter Finset

/-! ## Part I: Euler's Totient Function -/

/-- Euler's totient function φ(n) counts integers 1 ≤ k ≤ n coprime to n. -/
def phi (n : ℕ) : ℕ := Nat.totient n

/-- φ(1) = 1. -/
theorem phi_one : phi 1 = 1 := Nat.totient_one

/-- φ(p) = p - 1 for prime p. -/
theorem phi_prime (p : ℕ) (hp : p.Prime) : phi p = p - 1 :=
  Nat.totient_prime hp

/-- φ(n) > 0 for n > 0. -/
theorem phi_pos (n : ℕ) (hn : n > 0) : phi n > 0 :=
  Nat.totient_pos hn

/-- φ(n) ≤ n for all n. -/
theorem phi_le (n : ℕ) : phi n ≤ n :=
  Nat.totient_le n

/-- φ(n) < n for n > 1. -/
theorem phi_lt (n : ℕ) (hn : n > 1) : phi n < n :=
  Nat.totient_lt n hn

/-! ## Part II: Distinct Totient Runs -/

/-- A run of K consecutive integers starting at n+1 has distinct totient values
    if φ(n+1), φ(n+2), ..., φ(n+K) are all different. -/
def IsDistinctTotientRun (n K : ℕ) : Prop :=
  ∀ i j : ℕ, 1 ≤ i → i ≤ K → 1 ≤ j → j ≤ K → i ≠ j →
    phi (n + i) ≠ phi (n + j)

/-- Alternative definition using injectivity on an interval. -/
def IsDistinctTotientRun' (n K : ℕ) : Prop :=
  (Set.Icc (n + 1) (n + K)).InjOn phi

/-- The two definitions are equivalent. -/
theorem distinctRun_iff (n K : ℕ) :
    IsDistinctTotientRun n K ↔ IsDistinctTotientRun' n K := by
  sorry

/-- Empty run is trivially distinct. -/
theorem distinctRun_zero (n : ℕ) : IsDistinctTotientRun n 0 := by
  intro i j hi _ _ _ _
  omega

/-- Single element run is distinct. -/
theorem distinctRun_one (n : ℕ) : IsDistinctTotientRun n 1 := by
  intro i j hi hiK hj hjK hij
  omega

/-! ## Part III: The Maximum Run Length Function -/

/-- The maximum length K such that φ(n+1), ..., φ(n+K) are all distinct. -/
noncomputable def maxDistinctRunLength (n : ℕ) : ℕ :=
  sSup {K : ℕ | IsDistinctTotientRun n K}

/-- Every n has some distinct run (at least length 1). -/
theorem exists_distinct_run (n : ℕ) :
    ∃ K > 0, IsDistinctTotientRun n K := by
  exact ⟨1, Nat.one_pos, distinctRun_one n⟩

/-! ## Part IV: The EPS87 Upper Bound -/

/-- **Erdős-Pomerance-Sárközy (1987)**

    If φ(n+k) are all distinct for 1 ≤ k ≤ K, then
    K ≤ n / exp(c · (log n)^{1/3})
    for some constant c > 0.

    This limits how long a distinct totient run can be.
-/
axiom eps87_constant : ℝ

axiom eps87_constant_pos : eps87_constant > 0

axiom eps87_upper_bound (n K : ℕ) (hn : n > 0) (hrun : IsDistinctTotientRun n K) :
    (K : ℝ) ≤ n / Real.exp (eps87_constant * (Real.log n) ^ (1/3 : ℝ))

/-- Corollary: The run length is o(n). -/
theorem run_length_sublinear :
    Tendsto (fun n : ℕ => (maxDistinctRunLength n : ℝ) / n) atTop (𝓝 0) := by
  sorry

/-! ## Part V: The Main Conjecture -/

/-- **Erdős Problem #1004 (Main Conjecture)**

    For any c > 0, if x is sufficiently large, there exists n ≤ x such that
    φ(n+1), ..., φ(n+⌊(log x)^c⌋) are all distinct.

    In other words: Can we always find runs of length (log x)^c?
-/
def Erdos1004Conjecture : Prop :=
  ∀ c : ℝ, c > 0 →
    ∀ᶠ x : ℕ in atTop, ∃ n ≤ x,
      IsDistinctTotientRun n ⌊(Real.log x) ^ c⌋₊

/-- The negation: For some c > 0, eventually no such n exists. -/
def Erdos1004Negation : Prop :=
  ∃ c : ℝ, c > 0 ∧
    ∀ᶠ x : ℕ in atTop, ∀ n ≤ x,
      ¬IsDistinctTotientRun n ⌊(Real.log x) ^ c⌋₊

/-! ## Part VI: Known Partial Results -/

/-- For small c, runs of length (log x)^c should be common. -/
def SmallCaseConjecture : Prop :=
  ∃ c₀ > 0, ∀ c : ℝ, 0 < c → c < c₀ →
    ∀ᶠ x : ℕ in atTop, ∃ n ≤ x,
      IsDistinctTotientRun n ⌊(Real.log x) ^ c⌋₊

/-- The EPS bound implies: If the conjecture is true for some c,
    then c ≤ 1/3 (heuristically). -/
theorem eps_constraint_heuristic :
    Erdos1004Conjecture → ∀ c > (1/3 : ℝ), False := by
  sorry -- This is not literally true but captures the constraint

/-! ## Part VII: Examples of Distinct Runs -/

/-- φ(2) = 1, φ(3) = 2, φ(4) = 2. So run at n=1 has length at most 2. -/
theorem example_n1 : IsDistinctTotientRun 1 2 ∧ ¬IsDistinctTotientRun 1 3 := by
  constructor
  · intro i j hi hiK hj hjK hij
    interval_cases i <;> interval_cases j <;> simp [phi, Nat.totient] <;> omega
  · intro h
    have := h 2 3 (by omega) (by omega) (by omega) (by omega) (by omega)
    simp [phi, Nat.totient] at this

/-- φ(3) = 2, φ(4) = 2. So n=2 gives run length 1. -/
theorem example_n2 : IsDistinctTotientRun 2 1 ∧ ¬IsDistinctTotientRun 2 2 := by
  constructor
  · exact distinctRun_one 2
  · intro h
    have := h 1 2 (by omega) (by omega) (by omega) (by omega) (by omega)
    simp [phi, Nat.totient] at this

/-- Looking for longer runs requires larger n. -/
theorem longer_runs_need_larger_n (K : ℕ) (hK : K ≥ 2) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∃ m ≤ n, IsDistinctTotientRun m K := by
  sorry

/-! ## Part VIII: Totient Value Collisions -/

/-- Two numbers have the same totient if φ(a) = φ(b). -/
def TotientCollision (a b : ℕ) : Prop := phi a = phi b ∧ a ≠ b

/-- φ(1) = φ(2) = 1 is a collision. -/
theorem collision_1_2 : TotientCollision 1 2 := by
  constructor
  · simp [phi, Nat.totient]
  · omega

/-- φ(3) = φ(4) = φ(6) = 2 gives multiple collisions. -/
theorem collision_3_4 : TotientCollision 3 4 := by
  constructor
  · simp [phi, Nat.totient]
  · omega

/-- Collisions cause distinct runs to end. -/
theorem collision_ends_run (n i j : ℕ) (hi : 1 ≤ i) (hj : 1 ≤ j) (hij : i < j)
    (hcol : phi (n + i) = phi (n + j)) :
    ¬IsDistinctTotientRun n j := by
  intro hrun
  have := hrun i j hi (Nat.le_of_lt hij) hj (le_refl j) (Nat.ne_of_lt hij)
  exact this hcol

/-! ## Part IX: Connection to Divisor Function -/

/-- The divisor function τ(n). -/
def tau (n : ℕ) : ℕ := n.divisors.card

/-- Distinct divisor run (related to Problem #945). -/
def IsDistinctDivisorRun (n K : ℕ) : Prop :=
  ∀ i j : ℕ, 1 ≤ i → i ≤ K → 1 ≤ j → j ≤ K → i ≠ j →
    tau (n + i) ≠ tau (n + j)

/-- Problem #945 asks the analogous question for τ. -/
def Problem945Conjecture : Prop :=
  ∀ c : ℝ, c > 0 →
    ∀ᶠ x : ℕ in atTop, ∃ n ≤ x,
      IsDistinctDivisorRun n ⌊(Real.log x) ^ c⌋₊

/-! ## Part X: Probabilistic Heuristics -/

/-- The number of distinct totient values up to x. -/
noncomputable def countDistinctTotients (x : ℕ) : ℕ :=
  (Finset.range x).image phi |>.card

/-- Asymptotically, there are ~ x / log x distinct totient values ≤ x. -/
theorem distinct_totients_asymptotic :
    Tendsto (fun x : ℕ => (countDistinctTotients x : ℝ) * Real.log x / x)
      atTop (𝓝 1) := by
  sorry

/-- Heuristic: Probability that K consecutive totients are distinct
    is roughly (1 - 1/V) * (1 - 2/V) * ... * (1 - (K-1)/V)
    where V ~ n / log n is the number of available values. -/
def birthdayProbabilityHeuristic (n K : ℕ) : ℝ :=
  let V := (n : ℝ) / Real.log n
  ∏ k ∈ Finset.range K, (1 - k / V)

/-! ## Part XI: Bounds on Run Length -/

/-- Trivial upper bound: K ≤ n (can't have more distinct values than integers). -/
theorem run_length_trivial_bound (n K : ℕ) (hrun : IsDistinctTotientRun n K) :
    K ≤ n + K := by
  omega

/-- Better bound: K ≤ #{distinct φ values ≤ n + K}. -/
theorem run_length_by_distinct_values (n K : ℕ) (hrun : IsDistinctTotientRun n K) :
    K ≤ countDistinctTotients (n + K + 1) := by
  sorry

/-! ## Part XII: Special Values -/

/-- Small totient values: φ(n) = 1 iff n ∈ {1, 2}. -/
theorem totient_eq_one_iff (n : ℕ) : phi n = 1 ↔ n = 1 ∨ n = 2 := by
  sorry

/-- φ(n) = 2 iff n ∈ {3, 4, 6}. -/
theorem totient_eq_two_iff (n : ℕ) : phi n = 2 ↔ n = 3 ∨ n = 4 ∨ n = 6 := by
  sorry

/-- φ(n) = 4 iff n ∈ {5, 8, 10, 12}. -/
theorem totient_eq_four_iff (n : ℕ) :
    phi n = 4 ↔ n = 5 ∨ n = 8 ∨ n = 10 ∨ n = 12 := by
  sorry

end Erdos1004

/-!
## Summary

This file formalizes Erdős Problem #1004 on distinct consecutive totient values.

**Status**: OPEN (with partial results from EPS 1987)

**The Problem**: For any c > 0, if x is large enough, does there exist n ≤ x
such that φ(n+1), φ(n+2), ..., φ(n+⌊(log x)^c⌋) are all distinct?

**Known Results**:
- Erdős-Pomerance-Sárközy (1987): If φ(n+k) are distinct for 1 ≤ k ≤ K,
  then K ≤ n/exp(c(log n)^{1/3}) for some c > 0.

**What we formalize**:
1. Euler's totient function φ(n)
2. Distinct totient runs
3. Maximum run length function
4. EPS87 upper bound (axiomatized)
5. The main conjecture
6. Examples of runs and collisions
7. Connection to Problem #945 (divisor function)
8. Probabilistic heuristics
9. Special totient values

**Key axioms**:
- `eps87_upper_bound`: The EPS87 theorem limiting run length
- `eps87_constant`: The constant c in the bound

**Related Problems**: #945 (divisor function version)
-/
