/-
  Erdős Problem #1057: Counting Carmichael Numbers

  Source: https://erdosproblems.com/1057
  Status: OPEN

  Statement:
  Let C(x) count Carmichael numbers in [1,x]. Is C(x) = x^{1-o(1)}?

  Background:
  A Carmichael number is a composite n satisfying a^n ≡ a (mod n) for all
  integers a. Equivalently (Korselt's criterion): n is squarefree and
  (p-1) | (n-1) for all prime divisors p of n.

  These are the "strongest" Fermat pseudoprimes—they fool the Fermat
  primality test for every base. The smallest is 561 = 3 × 11 × 17.

  Known bounds:
  • Upper (Erdős 1956): C(x) < x·exp(-c·log x·log log log x / log log x)
  • Lower (Lichtman 2022): C(x) > x^{0.3389} for large x
  • Alford-Granville-Pomerance (1994): C(x) → ∞ (infinitely many exist)

  The conjecture C(x) = x^{1-o(1)} asserts Carmichael numbers are quite
  dense—almost achieving density 1 in log scale.

  References:
  [Er56c] Erdős, "On pseudoprimes and Carmichael numbers" (1956)
  [AGP94] Alford-Granville-Pomerance, "There are infinitely many Carmichael numbers"
  [Po89] Pomerance, "Two methods in elementary analytic number theory" (1989)
  [Li22] Lichtman, "Improved bounds on the counting function" (2022)

  Tags: number-theory, carmichael-numbers, pseudoprimes, counting-functions, open-problem
-/

import Mathlib

open Nat BigOperators Finset

/-
## Carmichael Numbers

Definition via Korselt's criterion.
-/

/-- Korselt's criterion: n is squarefree and (p-1) | (n-1) for all prime p | n -/
def satisfiesKorselt (n : ℕ) : Prop :=
  Squarefree n ∧ ∀ p : ℕ, p.Prime → p ∣ n → (p - 1) ∣ (n - 1)

/-- A Carmichael number is a composite satisfying Korselt's criterion -/
def IsCarmichael (n : ℕ) : Prop :=
  n > 1 ∧ ¬n.Prime ∧ satisfiesKorselt n

/-- Fermat's little theorem characterization: a^n ≡ a (mod n) for all a -/
def satisfiesFermat (n : ℕ) : Prop :=
  ∀ a : ℕ, a^n % n = a % n

/-- Korselt's theorem: the two definitions are equivalent -/
axiom korselt_theorem :
  ∀ n : ℕ, n > 1 → ¬n.Prime → (satisfiesKorselt n ↔ satisfiesFermat n)

/-
## Small Carmichael Numbers

The first few Carmichael numbers.
-/

/-- 561 = 3 × 11 × 17 is the smallest Carmichael number -/
axiom carmichael_561 : IsCarmichael 561

/-- 561 = 3 × 11 × 17 -/
theorem factorization_561 : 561 = 3 * 11 * 17 := by native_decide

/-- Verification: 2 | 560, 10 | 560, 16 | 560 -/
theorem korselt_561 : (2 ∣ 560) ∧ (10 ∣ 560) ∧ (16 ∣ 560) := by
  constructor
  · exact ⟨280, rfl⟩
  constructor
  · exact ⟨56, rfl⟩
  · exact ⟨35, rfl⟩

/-- 1105 = 5 × 13 × 17 is the second Carmichael number -/
axiom carmichael_1105 : IsCarmichael 1105

/-- 1729 = 7 × 13 × 19 is the Hardy-Ramanujan taxicab number -/
axiom carmichael_1729 : IsCarmichael 1729

/-- List of first few Carmichael numbers (OEIS A002997) -/
def smallCarmichaels : List ℕ := [561, 1105, 1729, 2465, 2821, 6601, 8911]

/-
## The Counting Function

C(x) counts Carmichael numbers up to x.
-/

/-- C(x): count of Carmichael numbers in [1, x] -/
noncomputable def C (x : ℕ) : ℕ :=
  (Finset.range (x + 1)).filter IsCarmichael |>.card

/-- C is monotone increasing -/
theorem C_mono : ∀ x y : ℕ, x ≤ y → C x ≤ C y := by
  intro x y hxy
  unfold C
  apply Finset.card_le_card
  intro n hn
  simp only [Finset.mem_filter, Finset.mem_range] at hn ⊢
  exact ⟨Nat.lt_of_lt_of_le hn.1 (Nat.add_le_add_right hxy 1), hn.2⟩

/-
## Known Bounds

Upper and lower bounds on C(x).
-/

/-- Erdős's upper bound (1956) -/
axiom erdos_upper_bound :
  ∃ c : ℝ, c > 0 ∧ ∀ x : ℕ, x ≥ 2 →
    (C x : ℝ) < x * Real.exp (-c * Real.log x * Real.log (Real.log (Real.log x)) /
                               Real.log (Real.log x))

/-- Lichtman's lower bound (2022): C(x) > x^{0.3389} -/
axiom lichtman_lower_bound :
  ∃ X : ℕ, ∀ x ≥ X, (C x : ℝ) > x^(0.3389 : ℝ)

/-- Harman's earlier lower bound (2008): C(x) > x^{0.33336704} -/
axiom harman_lower_bound :
  ∃ X : ℕ, ∀ x ≥ X, (C x : ℝ) > x^(0.33336704 : ℝ)

/-- AGP (1994): There are infinitely many Carmichael numbers -/
axiom infinitely_many_carmichaels :
  ∀ N : ℕ, ∃ n > N, IsCarmichael n

/-- AGP lower bound: C(x) > x^{2/7} for large x -/
axiom agp_lower_bound :
  ∃ X : ℕ, ∀ x ≥ X, (C x : ℝ) > x^(2/7 : ℝ)

/-
## The Main Conjecture

Is C(x) = x^{1-o(1)}?
-/

/-- The conjecture: C(x) = x^{1-o(1)} -/
def erdos1057Conjecture : Prop :=
  ∀ ε > 0, ∃ X : ℕ, ∀ x ≥ X, (C x : ℝ) > x^(1 - ε : ℝ)

/-- Equivalent: log C(x) / log x → 1 -/
def erdos1057ConjectureAlt : Prop :=
  Filter.Tendsto (fun x => Real.log (C x) / Real.log x)
    Filter.atTop (nhds 1)

/-- Pomerance's heuristic prediction for the exact order -/
noncomputable def pomeranceOrder (x : ℝ) : ℝ :=
  x * Real.exp (-Real.log x * Real.log (Real.log (Real.log x)) / Real.log (Real.log x))

/-- Pomerance conjecture: C(x) ~ pomeranceOrder(x) -/
def pomeranceConjecture : Prop :=
  Filter.Tendsto (fun x => (C x : ℝ) / pomeranceOrder x)
    Filter.atTop (nhds 1)

/-
## Properties of Carmichael Numbers

Structural results about Carmichael numbers.
-/

/-- Every Carmichael number has at least 3 prime factors -/
axiom carmichael_at_least_3_primes :
  ∀ n : ℕ, IsCarmichael n → n.primeFactors.card ≥ 3

/-- No Carmichael number is a prime power -/
theorem carmichael_not_prime_power (n : ℕ) (h : IsCarmichael n) :
    ¬∃ p k : ℕ, p.Prime ∧ k ≥ 1 ∧ n = p^k := by
  intro ⟨p, k, hp, hk, hn⟩
  have h3 := carmichael_at_least_3_primes n h
  sorry -- n = p^k has only 1 prime factor

/-- Carmichael numbers are odd (except there are no even ones > 2) -/
axiom carmichael_odd :
  ∀ n : ℕ, IsCarmichael n → Odd n

/-
## The Gap

The huge gap between upper and lower bounds.
-/

/-- Upper bound exponent in log scale -/
noncomputable def upperExponent (x : ℝ) : ℝ :=
  1 - Real.log (Real.log (Real.log x)) / Real.log (Real.log x)

/-- Lower bound exponent -/
def lowerExponent : ℝ := 0.3389

/-- The gap: we know lowerExponent < true exponent < upperExponent(x) -/
theorem exponent_gap : lowerExponent < 1 := by
  norm_num [lowerExponent]

/-- The open problem: what is the true exponent? -/
def erdos1057OpenProblem : Prop := erdos1057Conjecture

#check C
#check IsCarmichael
#check erdos1057Conjecture
#check lichtman_lower_bound
#check erdos_upper_bound
