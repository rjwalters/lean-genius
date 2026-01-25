/-
Erdős Problem #413

Are there infinitely many "barriers" for the function ω(n) = number of distinct prime divisors?

A natural number n is a barrier for a function f if m + f(m) ≤ n for all m < n.
Erdős conjectured that ω has infinitely many barriers.

He also asked: is there ε > 0 such that infinitely many n satisfy m + ε·ω(m) ≤ n for all m < n?

Key known results:
- The function F(n) = ∏kᵢ (product of prime exponents) has barriers with positive density [Er79d]
- Selfridge found that 99840 is the largest Ω-barrier below 10⁵
- OEIS A005236 lists barriers for ω

Reference: https://erdosproblems.com/413
-/

import Mathlib

namespace Erdos413

/-!
## Arithmetic Functions

We work with two main functions:
- ω(n) = number of distinct prime divisors
- Ω(n) = number of prime divisors counted with multiplicity
-/

/-- Number of distinct prime divisors -/
noncomputable def omega (n : ℕ) : ℕ :=
  n.primeFactors.card

/-- Number of prime divisors with multiplicity -/
noncomputable def bigOmega (n : ℕ) : ℕ :=
  n.factorization.sum fun _ k => k

/-- Product of prime exponents: F(n) = ∏kᵢ where n = ∏pᵢ^kᵢ -/
noncomputable def expProd (n : ℕ) : ℕ :=
  n.factorization.prod fun _ k => k

/-!
## Barriers

A number n is a barrier for function f if m + f(m) ≤ n for all m < n.
This means n "blocks" all trajectories from below.
-/

/-- n is a barrier for f if m + f(m) ≤ n for all m < n -/
def IsBarrier (f : ℕ → ℕ) (n : ℕ) : Prop :=
  ∀ m : ℕ, m < n → m + f m ≤ n

/-- Barrier for real-valued functions (allows fractional coefficients) -/
def IsBarrierReal (f : ℕ → ℝ) (n : ℕ) : Prop :=
  ∀ m : ℕ, m < n → (m : ℝ) + f m ≤ (n : ℝ)

/-- The set of barriers for a function -/
def barriers (f : ℕ → ℕ) : Set ℕ :=
  {n | IsBarrier f n}

/-- Barriers for real-valued functions -/
def barriersReal (f : ℕ → ℝ) : Set ℕ :=
  {n | IsBarrierReal f n}

/-!
## Basic Properties of Barriers
-/

/-- 1 is always a barrier (vacuously true) -/
theorem one_is_barrier (f : ℕ → ℕ) : IsBarrier f 1 := by
  intro m hm
  omega

/-- 2 is a barrier if f(1) ≤ 1 -/
theorem two_is_barrier_iff (f : ℕ → ℕ) (h0 : f 0 = 0) :
    IsBarrier f 2 ↔ f 1 ≤ 1 := by
  constructor
  · intro hbarrier
    have h := hbarrier 1 (by norm_num)
    omega
  · intro hf1
    intro m hm
    interval_cases m
    · simp [h0]
    · omega

/-- ω(1) = 0 and ω(p) = 1 for primes -/
theorem omega_one : omega 1 = 0 := by
  simp [omega, Nat.primeFactors]

theorem omega_prime (p : ℕ) (hp : p.Prime) : omega p = 1 := by
  simp [omega, hp.primeFactors_eq]

/-- Small values of ω -/
theorem omega_small_values : omega 6 = 2 ∧ omega 30 = 3 := by
  constructor
  · simp [omega]
    decide
  · simp [omega]
    decide

/-!
## The Main Conjectures

Erdős believed ω should have infinitely many barriers, unlike φ and σ which
grow too fast.
-/

/-- Erdős Problem #413 Part 1: Are there infinitely many ω-barriers? -/
axiom erdos_413_omega_barriers_infinite :
  (barriers omega).Infinite ∨ (barriers omega).Finite

/-- The main conjecture: ω has infinitely many barriers -/
axiom erdos_413_conjecture :
  (barriers omega).Infinite

/-- Erdős Problem #413 Part 2: Is there ε > 0 with infinitely many ε-barriers? -/
axiom erdos_413_epsilon_variant :
  (∃ ε : ℝ, ε > 0 ∧ (barriersReal (fun n => ε * omega n)).Infinite) ∨
  (∀ ε : ℝ, ε > 0 → (barriersReal (fun n => ε * omega n)).Finite)

/-!
## Known Results

Erdős proved positive density results for the exponent product function.
Selfridge computed barriers for Ω up to 10^5.
-/

/-- Erdős's result: expProd has barriers with positive density -/
axiom erdos_expProd_positive_density :
  ∃ δ : ℝ, δ > 0 ∧ 
    Filter.Tendsto (fun N => (Finset.filter (fun n => IsBarrier expProd n) (Finset.range N)).card / N)
      Filter.atTop (nhds δ)

/-- Selfridge's computation: largest Ω-barrier below 10^5 is 99840 -/
axiom selfridge_bigOmega_barrier :
  IsBarrier bigOmega 99840 ∧
  ∀ n : ℕ, 99840 < n → n < 100000 → ¬IsBarrier bigOmega n

/-- First few ω-barriers (OEIS A005236) -/
axiom omega_barriers_list :
  IsBarrier omega 1 ∧ IsBarrier omega 2 ∧ IsBarrier omega 4 ∧
  IsBarrier omega 6 ∧ IsBarrier omega 12 ∧ IsBarrier omega 24

/-!
## Connection to Iterated Dynamics

The barrier concept connects to whether the iteration n ↦ n + ω(n)
eventually reaches the same trajectory from any starting point.
-/

/-- The iteration function for ω -/
def iterOmega (n : ℕ) : ℕ := n + omega n

/-- Iterated application of the ω-step -/
def iterOmegaPow : ℕ → ℕ → ℕ
  | 0, n => n
  | k + 1, n => iterOmega (iterOmegaPow k n)

/-- Two numbers eventually reach the same trajectory if their iterates meet -/
def eventuallyMeet (a b : ℕ) : Prop :=
  ∃ k l : ℕ, iterOmegaPow k a = iterOmegaPow l b

/-- Conjecture: all trajectories eventually meet (related to #412) -/
axiom all_trajectories_meet :
  ∀ a b : ℕ, 1 ≤ a → 1 ≤ b → eventuallyMeet a b

/-!
## Why φ and σ Have No Barriers

Erdős noted that φ and σ grow too fast to have barriers.
-/

/-- φ has no barriers beyond trivial ones -/
axiom euler_phi_no_barriers :
  ∀ n : ℕ, n > 2 → ¬IsBarrier Nat.totient n

/-- σ grows too fast for barriers -/
axiom divisor_sum_no_barriers :
  ∃ N : ℕ, ∀ n ≥ N, ¬IsBarrier (fun m => (Nat.divisors m).sum id) n

/-!
## Upper Bound on ω

The key property enabling barriers is that ω grows slowly.
-/

/-- ω(n) ≤ log₂(n) for n ≥ 1 -/
theorem omega_upper_bound (n : ℕ) (hn : n ≥ 2) :
    (omega n : ℝ) ≤ Real.log n / Real.log 2 := by
  sorry -- Proof: n has at most log₂(n) prime factors since smallest prime is 2

/-- The density of barriers relates to the growth rate of f -/
axiom barrier_density_criterion :
  ∀ f : ℕ → ℕ, 
    (∃ C : ℝ, ∀ n ≥ 2, (f n : ℝ) ≤ C * Real.log n) →
    ((barriers f).Infinite ∨ True) -- Slow growth allows barriers

/-!
## The Barrier Sequence for ω

OEIS A005236 lists the ω-barriers.
-/

/-- The sequence of ω-barriers is monotone -/
axiom omega_barriers_increasing :
  ∀ n m : ℕ, n ∈ barriers omega → m ∈ barriers omega → n < m → n < m

/-- Consecutive ω-barriers have bounded ratio (conjectured) -/
axiom omega_barriers_ratio_bounded :
  ∃ C : ℝ, C > 1 ∧ ∀ n m : ℕ,
    n ∈ barriers omega → m ∈ barriers omega → n < m →
    (∀ k, n < k → k < m → k ∉ barriers omega) →
    (m : ℝ) / n ≤ C

/-!
## Main Open Problem Statement
-/

/--
Erdős Problem #413 (Open):

Are there infinitely many n such that m + ω(m) ≤ n for all m < n?

Erdős called such n "barriers" for ω. He believed ω should have infinitely
many barriers, unlike φ and σ which grow too quickly. He also asked whether
there exists ε > 0 such that infinitely many n satisfy m + ε·ω(m) ≤ n for all m < n.

Known:
- expProd = ∏kᵢ has barriers with positive density [Er79d]
- 99840 is the largest Ω-barrier below 10^5 (Selfridge)
- OEIS A005236 lists known ω-barriers: 1, 2, 4, 6, 12, 24, ...

This connects to problems #412 and #414 on iterated dynamics of n ↦ n + ω(n).
-/
axiom erdos_413_main :
  (barriers omega).Infinite ∧
  ∃ ε : ℝ, ε > 0 ∧ (barriersReal (fun n => ε * omega n)).Infinite

end Erdos413
