import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic

/-
# Complexity Analysis: Cramer's Rule vs Gaussian Elimination (OQ-02)

## Research Question

Can we formalize the complexity analysis showing Cramer's rule is computationally
inferior to Gaussian elimination for solving systems of linear equations?

## Answer: YES

For an n×n system Ax = b:

- **Cramer's rule**: requires (n+1) determinant computations.
  Each n×n determinant via the Leibniz formula uses n·n! multiplications.
  Total: (n+1)·n·n! multiplications.

- **Gaussian elimination**: requires approximately n³ multiplications
  (more precisely ≈ n³/3, but we use n³ as the upper model).

For n ≥ 4: n³ < (n+1)·n·n!, i.e., Gaussian elimination is strictly more efficient.

The ratio (cramers / gauss) = (n+1)·n! / n² grows super-polynomially,
so Gaussian elimination is ASYMPTOTICALLY SUPERIOR by any polynomial factor.

## Mathematical Significance

This complexity gap motivates why Cramer's rule is only used:
- For symbolic/exact computation on small systems
- As a theoretical tool (proof of existence, Cayley-Hamilton connection)
- For 2×2 and 3×3 systems (where the overhead is manageable)

For practical large systems, Gaussian elimination (or LU decomposition) is
orders of magnitude faster.

## Proof Techniques

- Natural number arithmetic and induction
- Factorial growth lemmas
- `nlinarith` for polynomial inequalities
- `decide` for base cases

## Mathematical Structure

Key lemma chain:
  4! > 4²  →  n! > n² (for n ≥ 4, by induction)
           →  (n+1)·n·n! > n³ (main comparison)
           →  asymptotic gap grows without bound
-/

namespace CramersComplexity

open Nat

/-! ## Complexity Models -/

/-- Number of multiplications to compute one n×n determinant via the Leibniz formula:
    n! permutations, each requiring n multiplications to form a product of n entries.
    (Total: n · n! multiplications, not counting additions.) -/
def detMuls (n : ℕ) : ℕ := n * n !

/-- Number of multiplications for Cramer's rule on an n×n system:
    We compute n+1 determinants: det(A) plus det(Aᵢ) for each of the n variables. -/
def cramersRuleMuls (n : ℕ) : ℕ := (n + 1) * detMuls n

/-- Number of multiplications for Gaussian elimination on an n×n system.
    The standard estimate is n³/3; we use n³ as a conservative upper bound. -/
def gaussMuls (n : ℕ) : ℕ := n ^ 3

/-! ## Basic Properties -/

/-- Expand cramersRuleMuls into a single product -/
lemma cramersRuleMuls_eq (n : ℕ) : cramersRuleMuls n = (n + 1) * n * n ! := by
  unfold cramersRuleMuls detMuls; ring

/-- Small examples: n=4 -/
lemma cramer_4 : cramersRuleMuls 4 = 480 := by native_decide
lemma gauss_4 : gaussMuls 4 = 64 := by norm_num [gaussMuls]

/-- Small examples: n=5 -/
lemma cramer_5 : cramersRuleMuls 5 = 3600 := by native_decide
lemma gauss_5 : gaussMuls 5 = 125 := by norm_num [gaussMuls]

/-- Small examples: n=6 -/
lemma cramer_6 : cramersRuleMuls 6 = 30240 := by native_decide
lemma gauss_6 : gaussMuls 6 = 216 := by norm_num [gaussMuls]

/-! ## Key Growth Lemma -/

/-- For n ≥ 4: n! > n².
    Base: 4! = 24 > 16 = 4².
    Inductive: (m+1)! = (m+1)·m! > (m+1)·m² > (m+1)² when m² > m+1 (holds for m ≥ 2). -/
lemma factorial_gt_sq {n : ℕ} (hn : 4 ≤ n) : n ^ 2 < n ! := by
  induction n with
  | zero => omega
  | succ m ih =>
    rcases Nat.lt_or_eq_of_le hn with h | h
    · -- Inductive case: m ≥ 4
      have hm4 : 4 ≤ m := Nat.lt_succ_iff.mp h
      have ihm : m ^ 2 < m ! := ih hm4
      rw [Nat.factorial_succ]
      -- Goal: (m+1)^2 < (m+1) * m!
      -- Since m! ≥ m^2 + 1 (integers), we get:
      -- (m+1)*m! ≥ (m+1)*(m^2+1) = m^3 + m^2 + m + 1 > m^2 + 2m + 1 = (m+1)^2
      -- (since m^3 + m^2 + m + 1 - (m^2 + 2m + 1) = m^3 - m = m(m²-1) ≥ 0 for m ≥ 1)
      nlinarith [Nat.factorial_pos m]
    · -- Base case: n = m + 1 = 4, so m = 3
      have hm3 : m = 3 := by omega
      subst hm3
      decide

/-! ## Main Comparison Theorem -/

/-- For n ≥ 4: Gaussian elimination uses strictly fewer multiplications than Cramer's rule.

    Proof: n³ = n·n² < n·n! (by factorial_gt_sq) ≤ (n+1)·n·n! = cramersRuleMuls n. -/
theorem gauss_beats_cramer {n : ℕ} (hn : 4 ≤ n) : gaussMuls n < cramersRuleMuls n := by
  rw [gaussMuls, cramersRuleMuls_eq]
  have h_sq : n ^ 2 < n ! := factorial_gt_sq hn
  have hpos : 0 < n := by omega
  nlinarith [Nat.factorial_pos n]

/-- Summary: specific speedup ratios -/
theorem cramer_much_worse_at_4 : 7 * gaussMuls 4 < cramersRuleMuls 4 := by
  simp [cramer_4, gauss_4]

theorem cramer_much_worse_at_5 : 28 * gaussMuls 5 < cramersRuleMuls 5 := by
  simp [cramer_5, gauss_5]

theorem cramer_much_worse_at_6 : 139 * gaussMuls 6 < cramersRuleMuls 6 := by
  simp [cramer_6, gauss_6]

/-! ## Asymptotic Superiority -/

/-- For any constant K, Gaussian elimination is eventually K-times more efficient
    than Cramer's rule: ∃ N, ∀ n ≥ N, K · gaussMuls n < cramersRuleMuls n.

    Key idea: cramersRuleMuls n / gaussMuls n = (n+1)·n! / n² → ∞
    because n!/n² ≥ 1 for n ≥ 4, and the (n+1) factor adds a multiplicative n-growth.

    For n ≥ max(4, K):
      K · n³ = K · n · n² < K · n · n!  [since n² < n! for n ≥ 4]
             ≤ n · n · n!              [since K ≤ n]
             ≤ (n+1) · n · n!         [trivially]
             = cramersRuleMuls n
-/
theorem cramer_asymptotically_worse (K : ℕ) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → K * gaussMuls n < cramersRuleMuls n := by
  use max 4 K
  intro n hn
  have hn4 : 4 ≤ n := le_trans (le_max_left 4 K) hn
  have hnK : K ≤ n := le_trans (le_max_right 4 K) hn
  rw [gaussMuls, cramersRuleMuls_eq]
  have h_sq : n ^ 2 < n ! := factorial_gt_sq hn4
  have hpos : 0 < n := by omega
  -- Chain: K * n^3 ≤ n * n^3 = n*n*n^2 < n*n*n! ≤ (n+1)*n*n!
  have step1 : K * n ^ 3 ≤ n * n ^ 3 := mul_le_mul_right' hnK _
  have step2 : n * n ^ 3 < n * n * n ! := by
    have heq : n * n ^ 3 = n * n * n ^ 2 := by ring
    rw [heq]
    exact mul_lt_mul_of_pos_left h_sq (Nat.mul_pos hpos hpos)
  have step3 : n * n * n ! ≤ (n + 1) * n * n ! := by
    apply mul_le_mul_right'
    apply mul_le_mul_right'
    exact Nat.le_succ n
  linarith

/-! ## Threshold Analysis -/

/-- Concrete values for small n.
    Note: Gaussian elimination (n³ model) is strictly better than Cramer's rule
    even for n = 1, 2, 3 — not just for n ≥ 4. -/
lemma cramer_vs_gauss_small :
    cramersRuleMuls 1 = 2 ∧ gaussMuls 1 = 1 ∧
    cramersRuleMuls 2 = 12 ∧ gaussMuls 2 = 8 ∧
    cramersRuleMuls 3 = 72 ∧ gaussMuls 3 = 27 := by
  native_decide

/-- Gaussian elimination (n³ model) beats Cramer's rule for all n ≥ 1:
    the comparison holds for small n by direct computation, and for n ≥ 4
    by the factorial growth argument. -/
theorem complexity_threshold :
    gaussMuls 1 < cramersRuleMuls 1 ∧
    gaussMuls 2 < cramersRuleMuls 2 ∧
    gaussMuls 3 < cramersRuleMuls 3 ∧
    ∀ n : ℕ, 4 ≤ n → gaussMuls n < cramersRuleMuls n := by
  refine ⟨by native_decide, by native_decide, by native_decide,
          fun n hn => gauss_beats_cramer hn⟩

/-! ## Summary -/

/-- The key complexity theorem: Cramer's rule requires exponentially more multiplications
    than Gaussian elimination for large systems, with the gap growing unboundedly. -/
theorem cramer_vs_gauss_summary :
    -- (1) For n ≥ 4: Gaussian elimination is strictly faster
    (∀ n : ℕ, 4 ≤ n → gaussMuls n < cramersRuleMuls n) ∧
    -- (2) The gap grows without bound (for any K, eventually K-times faster)
    (∀ K : ℕ, ∃ N : ℕ, ∀ n : ℕ, N ≤ n → K * gaussMuls n < cramersRuleMuls n) ∧
    -- (3) At n=4: Gaussian needs 64 muls vs Cramer's 480 (7.5× worse)
    (cramersRuleMuls 4 = 480 ∧ gaussMuls 4 = 64) := by
  exact ⟨fun n hn => gauss_beats_cramer hn,
         cramer_asymptotically_worse,
         ⟨cramer_4, gauss_4⟩⟩

end CramersComplexity
