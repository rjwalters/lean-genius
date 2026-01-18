/-
  Erdős Problem #415: Ordering Patterns in Euler's Totient Function

  Source: https://erdosproblems.com/415
  Status: OPEN

  Statement:
  Let F(n) be the largest k such that ALL k! possible ordering patterns
  appear in some sequence φ(m+1), ..., φ(m+k) with m + k ≤ n.

  Questions:
  1. Is F(n) = (c + o(1)) log log log n for some constant c?
  2. Is the strictly decreasing pattern φ(m+1) > φ(m+2) > ... > φ(m+k)
     always the first pattern to fail appearing?
  3. Is the "natural" ordering (mimicking φ(1), ..., φ(k)) the most
     likely pattern to appear?

  Known Results:
  - Erdős (1936): F(n) ≍ log log log n
  - Same holds for σ, τ, ν, and other "decent" multiplicative/additive functions

  The triple-log growth is remarkably slow!

  Related: Problems on arithmetic functions, Chowla's problem
-/

import Mathlib

open Nat Function Finset

/-! ## Arithmetic Functions -/

/-- Euler's totient function φ(n) = count of k ≤ n with gcd(k,n) = 1 -/
def phi : ℕ → ℕ := Nat.totient

/-- Sum of divisors function σ(n) -/
def sigma : ℕ → ℕ := fun n => (Nat.divisors n).sum id

/-- Number of divisors function τ(n) -/
def tau : ℕ → ℕ := fun n => (Nat.divisors n).card

/-- Number of distinct prime divisors ω(n) -/
def omega : ℕ → ℕ := fun n => n.primeFactors.card

/-! ## Ordering Patterns -/

/-- An ordering pattern on k elements is a permutation of Fin k -/
def OrderingPattern (k : ℕ) := Equiv.Perm (Fin k)

/-- The number of ordering patterns on k elements is k! -/
theorem orderingPattern_card (k : ℕ) :
    Fintype.card (OrderingPattern k) = k.factorial := by
  simp [OrderingPattern, Fintype.card_perm]

/-- A sequence of k values realizes an ordering pattern if the relative
    order of values matches the pattern -/
def RealizesPattern {k : ℕ} (seq : Fin k → ℕ) (pattern : OrderingPattern k) : Prop :=
  ∀ i j : Fin k, pattern i < pattern j ↔ seq i < seq j

/-- Check if a sequence of φ values starting at m realizes a pattern -/
def PhiRealizesPattern (m k : ℕ) (pattern : OrderingPattern k) : Prop :=
  RealizesPattern (fun i => phi (m + 1 + i.val)) pattern

/-! ## The Function F(n) -/

/-- A pattern is achievable at n if some φ sequence realizes it -/
def PatternAchievable (n k : ℕ) (pattern : OrderingPattern k) : Prop :=
  ∃ m : ℕ, m + k ≤ n ∧ PhiRealizesPattern m k pattern

/-- All k! patterns are achievable at n -/
def AllPatternsAchievable (n k : ℕ) : Prop :=
  ∀ pattern : OrderingPattern k, PatternAchievable n k pattern

/-- F(n) is the largest k such that all k! patterns appear -/
noncomputable def F (n : ℕ) : ℕ :=
  Nat.find (F_exists n) - 1
where
  F_exists (n : ℕ) : ∃ k : ℕ, ¬AllPatternsAchievable n k := by
    use n + 1  -- Trivially, can't have n+1 consecutive values in [1,n]
    sorry

/-- Alternative definition via supremum -/
noncomputable def F' (n : ℕ) : ℕ :=
  sSup {k : ℕ | AllPatternsAchievable n k}

/-! ## Known Bounds (Erdős 1936) -/

/-- F(n) ≍ log log log n means:
    c₁ log log log n ≤ F(n) ≤ c₂ log log log n for constants c₁, c₂ > 0 -/
def AsymptoticTripleLog (f : ℕ → ℕ) : Prop :=
  ∃ c₁ c₂ : ℝ, c₁ > 0 ∧ c₂ > 0 ∧ ∃ N : ℕ, ∀ n ≥ N,
    c₁ * Real.log (Real.log (Real.log n)) ≤ f n ∧
    (f n : ℝ) ≤ c₂ * Real.log (Real.log (Real.log n))

/-- Erdős (1936): F(n) ≍ log log log n -/
theorem erdos_1936_F_asymptotic : AsymptoticTripleLog F := by
  sorry

/-! ## The Main Questions (OPEN) -/

/-- Question 1: Is there a constant c such that F(n) = (c + o(1)) log log log n? -/
def Question1_ExactConstant : Prop :=
  ∃ c : ℝ, c > 0 ∧ ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N,
    |((F n : ℝ) / Real.log (Real.log (Real.log n))) - c| < ε

/-- The strictly decreasing pattern: φ(m+1) > φ(m+2) > ... > φ(m+k) -/
def StrictlyDecreasingPattern (k : ℕ) : OrderingPattern k :=
  ⟨fun i => ⟨k - 1 - i.val, by omega⟩,
   fun i => ⟨k - 1 - i.val, by omega⟩,
   by intro i; simp; omega,
   by intro i; simp; omega⟩

/-- Question 2: Is the strictly decreasing pattern always the first to fail? -/
def Question2_DecreasingFirst : Prop :=
  ∀ n k : ℕ, ¬AllPatternsAchievable n k →
    ¬PatternAchievable n k (StrictlyDecreasingPattern k)

/-- The "natural" pattern mimics the ordering of φ(1), φ(2), ..., φ(k) -/
noncomputable def NaturalPattern (k : ℕ) : OrderingPattern k := by
  sorry  -- Requires sorting φ(1), ..., φ(k) and extracting the permutation

/-- Question 3: Is the natural pattern the most likely to appear? -/
def Question3_NaturalMostLikely : Prop :=
  ∀ n k : ℕ, ∀ pattern : OrderingPattern k,
    (Finset.univ.filter fun m => m + k ≤ n ∧ PhiRealizesPattern m k (NaturalPattern k)).card ≥
    (Finset.univ.filter fun m => m + k ≤ n ∧ PhiRealizesPattern m k pattern).card

/-! ## Specific Pattern Analysis -/

/-- The strictly increasing pattern -/
def StrictlyIncreasingPattern (k : ℕ) : OrderingPattern k := Equiv.refl (Fin k)

/-- The alternating pattern: low, high, low, high, ... -/
def AlternatingPattern (k : ℕ) : OrderingPattern k := by
  sorry  -- Complex definition

/-- For small k, we can check specific patterns -/

/-- k = 2: Both patterns (increasing and decreasing) appear early -/
theorem patterns_k2_achievable (n : ℕ) (hn : n ≥ 10) :
    AllPatternsAchievable n 2 := by
  sorry

/-- k = 3: All 6 patterns appear for moderate n -/
theorem patterns_k3_achievable (n : ℕ) (hn : n ≥ 100) :
    AllPatternsAchievable n 3 := by
  sorry

/-! ## Properties of φ Relevant to Ordering -/

/-- φ(p) = p - 1 for prime p -/
theorem phi_prime (p : ℕ) (hp : p.Prime) : phi p = p - 1 := by
  exact Nat.totient_prime hp

/-- φ(2p) = p - 1 for odd prime p -/
theorem phi_2p (p : ℕ) (hp : p.Prime) (hodd : p ≠ 2) : phi (2 * p) = p - 1 := by
  sorry

/-- Consecutive primes give increasing φ values -/
theorem phi_consecutive_primes (p q : ℕ) (hp : p.Prime) (hq : q.Prime) (hlt : p < q) :
    phi p < phi q := by
  sorry

/-- φ is highly variable: can be much smaller than n -/
theorem phi_small_values : ∀ ε > 0, ∃ᶠ n in Filter.atTop,
    (phi n : ℝ) < ε * n := by
  sorry

/-! ## Extension to Other Functions -/

/-- The same asymptotic holds for σ -/
def F_sigma (n : ℕ) : ℕ :=
  Nat.find (F_sigma_exists n) - 1
where
  F_sigma_exists (n : ℕ) : ∃ k : ℕ, ¬∀ pattern : OrderingPattern k,
      ∃ m : ℕ, m + k ≤ n ∧ RealizesPattern (fun i => sigma (m + 1 + i.val)) pattern := by
    sorry

theorem erdos_1936_F_sigma_asymptotic : AsymptoticTripleLog F_sigma := by
  sorry

/-- The same asymptotic holds for τ -/
def F_tau (n : ℕ) : ℕ := by sorry

theorem erdos_1936_F_tau_asymptotic : AsymptoticTripleLog F_tau := by
  sorry

/-! ## Why Triple Log? -/

/-- Intuition: The number of patterns is k!, and we need k! ≤ O(n/k) chances.
    k! ≈ (k/e)^k, so k^k ≲ n, giving k ≲ log n / log log n.
    But φ values cluster, reducing independence, adding another log factor. -/

/-- The number of distinct φ values up to n grows like n / log n -/
theorem phi_range_size (n : ℕ) (hn : n ≥ 2) :
    ∃ c : ℝ, c > 0 ∧ (Finset.image phi (Finset.range n)).card ≤ c * n / Real.log n := by
  sorry

/-- Many values share the same φ value (e.g., φ(1) = φ(2) = 1) -/
theorem phi_collisions : ∀ k : ℕ, ∃ v : ℕ,
    (Finset.range 1000000).filter (fun n => phi n = v) |>.card ≥ k := by
  sorry

/-! ## Main Problem Statement -/

/-- Erdős Problem #415: OPEN

    The exact constant c in F(n) = (c + o(1)) log log log n is unknown.
    Whether strictly decreasing is first to fail is unknown.
    Whether natural ordering is most common is unknown.

    Only the asymptotic F(n) ≍ log log log n is established. -/
theorem erdos_415 : AsymptoticTripleLog F := erdos_1936_F_asymptotic

/-- The problem is OPEN -/
theorem erdos_415_open : Question1_ExactConstant ↔ Question1_ExactConstant := Iff.rfl

#check erdos_415
#check Question1_ExactConstant
#check Question2_DecreasingFirst
#check Question3_NaturalMostLikely
