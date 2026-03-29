/-
  Aristotle targets for Erdős Problem #1049
  Routine supporting lemmas for automated proof search.
  See Erdos1049Problem.lean for the main formalization.

  Criteria for inclusion:
  - NOT the main open conjecture (Chowla's conjecture on irrationality)
  - Known results from Mathlib: divisor function multiplicativity,
    geometric series, summability by comparison
  - Clean theorem statements with no definition sorries
  - No axioms
-/
import Mathlib

namespace Erdos1049Aristotle

open BigOperators Nat Real Filter Topology

/-- The divisor counting function τ(n). -/
def tau (n : ℕ) : ℕ := n.divisors.card

-- Routine: τ is multiplicative for coprime arguments
theorem tau_multiplicative (m n : ℕ) (hmn : m.Coprime n) :
    tau (m * n) = tau m * tau n := by
  simp only [tau]
  rw [hmn.divisors_mul]
  exact Finset.card_product _ _

-- Routine: The series ∑ 1/t^n converges for t > 1
theorem inv_pow_summable (t : ℝ) (ht : t > 1) :
    Summable (fun n : ℕ => (1 : ℝ) / t ^ n) := by
  have h1 : (0 : ℝ) ≤ t⁻¹ := inv_nonneg.mpr (by linarith)
  have h2 : t⁻¹ < 1 := inv_lt_one_of_one_lt ht
  have := summable_geometric_of_lt_one h1 h2
  simp_rw [one_div, ← inv_pow]
  exact this

-- Routine: Geometric series ∑_{m≥1} x^m = x/(1-x) for |x| < 1
theorem geometric_inverse_pow (t : ℝ) (d : ℕ) (ht : t > 1) (hd : d ≥ 1) :
    HasSum (fun m : ℕ => if m = 0 then (0 : ℝ) else (1 / t ^ d) ^ m)
      (1 / (t ^ d - 1)) := by
  sorry

-- Routine: The series ∑ n/t^n converges for t > 1
theorem n_div_pow_summable (t : ℝ) (ht : t > 1) :
    Summable (fun n : ℕ => (n : ℝ) / t ^ n) := by
  sorry

-- Routine: t^n - 1 > 0 for t > 1, n ≥ 1
theorem pow_sub_one_pos (t : ℝ) (n : ℕ) (ht : t > 1) (hn : n ≥ 1) :
    t ^ n - 1 > 0 := by
  have h : 1 < t ^ n := one_lt_pow_of_one_lt_of_ne_zero ht (by omega)
  linarith

-- Routine: 1/(t^n - 1) ≤ 2/t^n for t ≥ 2, n ≥ 1
theorem inv_pow_sub_one_bound (t : ℝ) (n : ℕ) (ht : t ≥ 2) (hn : n ≥ 1) :
    1 / (t ^ n - 1) ≤ 2 / t ^ n := by
  have htp : (0 : ℝ) < t ^ n := by positivity
  have h2n : (2 : ℝ) ≤ t ^ n := by
    calc (2 : ℝ) = 2 ^ 1 := by simp
      _ ≤ 2 ^ n := by apply pow_le_pow_right <;> linarith
      _ ≤ t ^ n := by apply pow_le_pow_left (by linarith) ht
  have htm1 : (0 : ℝ) < t ^ n - 1 := by linarith
  rw [div_le_div_iff htm1 htp]
  nlinarith

-- Routine: τ(n) ≤ n (number of divisors bounded by n)
theorem tau_le_self (n : ℕ) : tau n ≤ n := by
  simp only [tau]
  exact Nat.card_divisors_le_self n

-- Routine: If transcendental, then irrational
theorem transcendental_implies_irrational (x : ℝ) (h : ¬IsAlgebraic ℚ x) :
    Irrational x := by
  intro ⟨q, hq⟩
  exact h (hq ▸ isAlgebraic_algebraMap q)

end Erdos1049Aristotle
