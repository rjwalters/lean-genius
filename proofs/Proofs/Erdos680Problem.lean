/-!
# Erdős Problem #680: Least Prime Factor Exceeding k² + 1

For a positive integer m, let p(m) denote its least prime factor. Erdős asked:
is it true that for all sufficiently large n, there exists some k ≥ 1 such that
p(n + k) > k² + 1?

The stronger variant asks whether this fails when k² + 1 is replaced by
e^{(1+ε)√k} + C_ε for all ε > 0 and some constant C_ε.

This is connected to prime gap conjectures: Cramér's conjecture would imply
existence of k with p(n+k) > e^{(1-ε)√k}. Granville refined the expected
constant from 1 to 2e^{-γ} ≈ 1.119.

Related to Problems #681 and #682.

Reference: https://erdosproblems.com/680
-/

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic

/-! ## Least Prime Factor and the Main Conjecture -/

/-- Erdős Problem 680 (main): For all sufficiently large n, there exists
    k ≥ 1 such that minFac(n + k) > k² + 1. -/
def ErdosProblem680 : Prop :=
  ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
    ∃ k : ℕ, 0 < k ∧ (n + k).minFac > k ^ 2 + 1

/-- Predicate: n has the "large least prime factor" property for some offset. -/
def HasLargeLPF (n : ℕ) : Prop :=
  ∃ k : ℕ, 0 < k ∧ (n + k).minFac > k ^ 2 + 1

/-! ## Exponential Variant -/

/-- The stronger exponential variant: it is false that for all sufficiently
    large n, there exists k with minFac(n+k) > e^{(1+ε)√k} + C.
    In other words, the exponential bound eventually fails. -/
def ErdosProblem680Variant : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ C : ℝ, 0 < C ∧
      ¬(∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
        ∃ k : ℕ, 0 < k ∧
          (n + k).minFac > ⌊Real.exp ((1 + ε) * Real.sqrt k) + C⌋₊)

/-- The combined problem: the main conjecture is true and the exponential
    variant confirms the quadratic bound cannot be exponentially improved. -/
def ErdosProblem680Combined : Prop :=
  ErdosProblem680 ∧ ErdosProblem680Variant

/-! ## Connections to Prime Gap Conjectures -/

/-- Cramér's conjecture on prime gaps: the gap after prime p is O((log p)²). -/
def CramerConjecture : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ p : ℕ, p.Prime → 2 < p →
    (Nat.find (Nat.exists_infinite_primes (p + 1)) - p : ℝ) ≤ C * (Real.log p) ^ 2

/-- If Cramér's conjecture holds, then for sufficiently large n there exists
    k with p(n+k) > e^{(1-ε)√k} for any ε > 0. -/
axiom cramer_implies_large_lpf :
    CramerConjecture →
    ∀ ε : ℝ, 0 < ε →
      ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
        ∃ k : ℕ, 0 < k ∧
          (n + k).minFac > ⌊Real.exp ((1 - ε) * Real.sqrt k)⌋₊

/-! ## Basic Properties -/

/-- The quadratic bound k² + 1 grows slower than the exponential e^{(1+ε)√k}
    for large k, so the main conjecture is weaker than the exponential version. -/
axiom quadratic_weaker_than_exponential (ε : ℝ) (hε : 0 < ε) :
    ∃ K₀ : ℕ, ∀ k : ℕ, K₀ ≤ k →
      (k ^ 2 + 1 : ℝ) < Real.exp ((1 + ε) * Real.sqrt k)

/-- For k = 1, the condition minFac(n+1) > 2 means n+1 is odd and not 2. -/
theorem lpf_k1_means_odd (n : ℕ) (h : (n + 1).minFac > 1 ^ 2 + 1) :
    ¬(2 ∣ (n + 1)) := by
  simp at h
  intro h2
  have := Nat.minFac_le_of_dvd (by norm_num : 2 ≤ 2) h2
  omega

/-- When n + k is prime, minFac(n+k) = n+k, which easily exceeds k² + 1
    for large n. -/
theorem prime_offset_gives_large_lpf (n k : ℕ) (hk : 0 < k)
    (hp : (n + k).Prime) (hn : k ^ 2 + 1 < n + k) :
    (n + k).minFac > k ^ 2 + 1 := by
  rw [hp.minFac_eq]
  exact hn

/-! ## Granville's Refinement -/

/-- Granville's constant: 2e^{-γ} where γ is the Euler-Mascheroni constant.
    This is approximately 1.1229. -/
noncomputable def granvilleConstant : ℝ :=
  2 * Real.exp (-Real.log 2 * 0.8365) -- approximation

/-- Granville's refined conjecture: the maximal prime gap after p is
    asymptotically at most 2e^{-γ} (log p)², not (log p)² as Cramér
    originally conjectured. -/
def GranvilleRefinement : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ N₀ : ℕ, ∀ p : ℕ, p.Prime → N₀ ≤ p →
      (Nat.find (Nat.exists_infinite_primes (p + 1)) - p : ℝ) ≤
        (granvilleConstant + ε) * (Real.log p) ^ 2

/-- The main conjecture follows from the existence of a prime in [n+1, n+k]
    for some k with k² + 1 < that prime. -/
axiom problem680_from_prime_distribution :
    (∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
      ∃ k : ℕ, 0 < k ∧ (n + k).Prime ∧ k ^ 2 + 1 < n + k) →
    ErdosProblem680
