/-
  Erdős Problem #247: Transcendence of Lacunary Sums

  Source: https://erdosproblems.com/247
  Status: OPEN (general case) / SOLVED (strong condition, Erdős 1975)

  Statement:
  Let n₁ < n₂ < ⋯ be a sequence of integers such that
    lim sup_{k→∞} n_k/k = ∞.
  Is Σ_{k=1}^∞ 1/2^{n_k} transcendental?

  Answer: OPEN in general. YES under stronger condition.

  History:
  - Erdős (1975) proved transcendence when lim sup n_k/k^t = ∞ for ALL t ≥ 1
  - The general conjecture (just lim sup n_k/k = ∞) remains open
  - Erdős (1988) noted these problems "seem hopeless at present"

  Key Insight:
  The sum Σ 1/2^{n_k} is a binary expansion with 1s at positions n_k.
  When the sequence grows fast enough (faster than any polynomial),
  the resulting number has a "lacunary" structure that forces transcendence.

  Tags: transcendence, number-theory, lacunary-series, erdos-problem
-/

import Mathlib.RingTheory.Algebraic.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Tactic

namespace Erdos247

/-! ## Part I: The Lacunary Sum -/

/-- The lacunary sum Σ_{k=1}^∞ 1/2^{n_k} for a sequence n : ℕ → ℕ. -/
noncomputable def lacunarySum (n : ℕ → ℕ) : ℝ :=
  ∑' k, (1 : ℝ) / 2 ^ n k

/-! ## Part II: Growth Conditions -/

/-- The weak growth condition: for all C > 0, there exists k with n_k > C * k.
    This is equivalent to lim sup n_k/k = ∞. -/
def HasWeakGrowth (n : ℕ → ℕ) : Prop :=
  ∀ C : ℕ, ∃ k : ℕ, k > 0 ∧ n k > C * k

/-- The strong growth condition: for all t ≥ 1 and all C > 0,
    there exists k with n_k > C * k^t. -/
def HasStrongGrowth (n : ℕ → ℕ) : Prop :=
  ∀ (t : ℕ), t ≥ 1 → ∀ C : ℕ, ∃ k : ℕ, k > 0 ∧ n k > C * k ^ t

/-! ## Part III: The Main Conjecture (OPEN) -/

/-- **Erdős Problem #247** (Open Conjecture)

    If n₁ < n₂ < ⋯ is a strictly increasing sequence with lim sup n_k/k = ∞,
    then Σ 1/2^{n_k} is transcendental.

    Status: OPEN -/
def erdos_247_conjecture : Prop :=
  ∀ (n : ℕ → ℕ), StrictMono n → HasWeakGrowth n →
    Transcendental ℚ (lacunarySum n)

/-! ## Part IV: Erdős's Partial Result (1975) -/

/-- **Erdős's Theorem (1975)**

    If n₁ < n₂ < ⋯ is strictly increasing with lim sup n_k/k^t = ∞
    for ALL t ≥ 1, then Σ 1/2^{n_k} is transcendental.

    Reference: Erdős, P., "Some problems and results on the irrationality
    of the sum of infinite series." J. Math. Sci. (1975).

    The proof uses Liouville-type arguments: if α is algebraic of degree d,
    then |α - p/q| > c/q^d for some c > 0. But lacunary sums can be
    approximated better than this when growth is superpolynomial. -/
axiom erdos_transcendence_strong (n : ℕ → ℕ)
    (hn : StrictMono n) (hg : HasStrongGrowth n) :
    Transcendental ℚ (lacunarySum n)

/-! ## Part V: Examples -/

/-- Factorial is strictly increasing (for k ≥ 1). -/
theorem factorial_strictMono : StrictMono (fun k => (k + 1).factorial) := by
  intro a b hab
  have h1 : 0 < a + 1 := Nat.succ_pos a
  have h2 : a + 1 < b + 1 := Nat.add_lt_add_right hab 1
  exact Nat.factorial_lt_of_lt h1 h2

/-- 2^k is strictly increasing. -/
theorem pow2_strictMono : StrictMono (fun k => 2^k) := by
  intro a b hab
  exact Nat.pow_lt_pow_right (by omega) hab

/-- Factorial grows faster than any polynomial (axiom). -/
axiom factorial_strong_growth : HasStrongGrowth (fun k => (k + 1).factorial)

/-- 2^k grows faster than any polynomial (axiom). -/
axiom pow2_strong_growth : HasStrongGrowth (fun k => 2^k)

/-- Corollary: The sum Σ 1/2^{k!} is transcendental. -/
theorem factorial_sum_transcendental :
    Transcendental ℚ (lacunarySum (fun k => (k + 1).factorial)) :=
  erdos_transcendence_strong _ factorial_strictMono factorial_strong_growth

/-- Corollary: The sum Σ 1/2^{2^k} is transcendental. -/
theorem pow2_sum_transcendental :
    Transcendental ℚ (lacunarySum (fun k => 2^k)) :=
  erdos_transcendence_strong _ pow2_strictMono pow2_strong_growth

/-! ## Part VI: The Gap Between Conditions -/

/-- Example: n_k = k² grows faster than linear but not faster than k². -/
def squareSeq : ℕ → ℕ := fun k => (k + 1)^2

/-- k² is strictly increasing. -/
theorem square_strictMono : StrictMono squareSeq := by
  intro a b hab
  simp only [squareSeq]
  have : a + 1 < b + 1 := Nat.add_lt_add_right hab 1
  exact Nat.pow_lt_pow_left this (by omega)

/-- The sum Σ 1/2^{k²} - transcendence is OPEN. -/
noncomputable def square_sum : ℝ := lacunarySum squareSeq

/-! ## Part VII: Summary -/

/-- Summary of known results for Erdős Problem #247. -/
theorem problem_247_summary :
    -- Erdős's theorem for strong growth
    (∀ (n : ℕ → ℕ), StrictMono n → HasStrongGrowth n →
      Transcendental ℚ (lacunarySum n)) ∧
    -- Factorial sum is transcendental
    Transcendental ℚ (lacunarySum (fun k => (k + 1).factorial)) ∧
    -- Power of 2 sum is transcendental
    Transcendental ℚ (lacunarySum (fun k => 2^k)) :=
  ⟨erdos_transcendence_strong, factorial_sum_transcendental, pow2_sum_transcendental⟩

#check erdos_247_conjecture
#check erdos_transcendence_strong

end Erdos247
