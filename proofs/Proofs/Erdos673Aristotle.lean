/-
  Aristotle targets for Erdős Problem #673
  Routine supporting lemmas for automated proof search.
  See Erdos673Problem.lean for the main formalization.

  Criteria for inclusion:
  - NOT the main open conjecture or deep analytic results
  - Known results provable from definitions or basic Mathlib facts
  - Clean theorem statements with no definition sorries
  - No axioms
-/
import Mathlib

namespace Erdos673Aristotle

open Nat Finset Real Filter

/-- The divisors of n as a sorted list. -/
noncomputable def sortedDivisors (n : ℕ) : List ℕ :=
  (n.divisors.sort (· ≤ ·))

/-- The number of divisors τ(n). -/
def tau (n : ℕ) : ℕ := n.divisors.card

/-- The i-th divisor of n (0-indexed from the sorted list). -/
noncomputable def divisorAt (n : ℕ) (i : ℕ) : ℕ :=
  (sortedDivisors n).getD i 0

/-- G(n) = sum of consecutive divisor ratios dᵢ/dᵢ₊₁. -/
noncomputable def G (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (tau n - 1),
    (divisorAt n i : ℝ) / (divisorAt n (i + 1) : ℝ)

/-- The ratio G(n)/τ(n). -/
noncomputable def GRatio (n : ℕ) : ℝ :=
  if tau n = 0 then 0 else G n / tau n

-- Routine lemma: first divisor of n ≥ 1 is 1
theorem first_divisor_eq_one (n : ℕ) (hn : n ≥ 1) :
    divisorAt n 0 = 1 := by
  sorry

-- Routine lemma: last divisor of n ≥ 1 is n
theorem last_divisor_eq_n (n : ℕ) (hn : n ≥ 1) :
    divisorAt n (tau n - 1) = n := by
  sorry

-- Routine lemma: G(1) = 0 (sum over empty range since tau(1)=1)
theorem G_one : G 1 = 0 := by
  simp [G, tau, Nat.divisors_one]

-- Routine lemma: G(p) = 1/p for prime p
theorem G_prime (p : ℕ) (hp : p.Prime) : G p = 1 / p := by
  sorry

-- Routine lemma: Upper bound G(n) ≤ τ(n) (each ratio ≤ 1)
theorem tao_upper_bound (n : ℕ) (hn : n ≥ 1) :
    G n ≤ tau n := by
  sorry

-- Routine lemma: G(n) ≤ τ(n) - 1 (each ratio < 1, strictly)
theorem G_upper_bound (n : ℕ) (hn : n ≥ 1) :
    G n ≤ tau n - 1 := by
  sorry

-- Routine lemma: G(n)/τ(n) is bounded in [0, 1]
theorem GRatio_bounded (n : ℕ) (hn : n ≥ 1) :
    0 ≤ GRatio n ∧ GRatio n ≤ 1 := by
  sorry

-- Routine lemma: G is not multiplicative (concrete counterexample)
theorem G_not_multiplicative :
    ∃ a b : ℕ, Nat.Coprime a b ∧ a ≥ 2 ∧ b ≥ 2 ∧ G (a * b) ≠ G a * G b := by
  sorry

-- Routine lemma: tau(1) = 1
theorem tau_one : tau 1 = 1 := by
  simp [tau, Nat.divisors_one]

-- Routine lemma: tau(p) = 2 for prime p
theorem tau_prime (p : ℕ) (hp : p.Prime) : tau p = 2 := by
  simp [tau, Nat.Prime.divisors hp]

-- Routine lemma: tau is multiplicative for coprime arguments
theorem tau_multiplicative (m n : ℕ) (hm : m ≥ 1) (hn : n ≥ 1)
    (hcop : Nat.Coprime m n) :
    tau (m * n) = tau m * tau n := by
  simp only [tau]
  rw [hcop.divisors_mul]
  exact Finset.card_product _ _

-- Routine lemma: G(n) ≥ 0 for all n (sum of nonneg ratios)
theorem G_nonneg (n : ℕ) : G n ≥ 0 := by
  unfold G
  apply Finset.sum_nonneg
  intro i _
  exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

end Erdos673Aristotle
