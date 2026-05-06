import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic
import Proofs.CramersRuleOQ02

/-
# Complexity Analysis: LU Decomposition and QR Factorization vs Cramer's Rule

## Research Question (OQ-02 → OQ-02)

Can the complexity comparison be extended to LU decomposition and QR factorization?

## Answer: YES — all cubic-time algorithms vastly outperform Cramer's rule.

For an n×n system Ax = b:

- **Cramer's rule**: (n+1)·n·n! multiplications (super-exponential)
- **Gaussian elimination / LU decomposition**: ≈ n³ multiplications (cubic)
- **QR factorization (Householder)**: ≈ 4n³/3 multiplications (still cubic)

Key results proved:
1. luMuls n = gaussMuls n (LU ≡ Gaussian in our model)
2. qrMuls n = 2·gaussMuls n (QR is at most 2× Gaussian)
3. lu_beats_cramer: luMuls n < cramersRuleMuls n for n ≥ 4
4. qr_beats_cramer: qrMuls n < cramersRuleMuls n for n ≥ 4
5. qr_asymptotically_better: for any K, eventually K·qrMuls n < cramersRuleMuls n

## Algorithm Details

LU decomposition: ≈ n³/3 ops for LU + n² for back-solve → modeled as n³ = gaussMuls n.
QR (Householder): ≈ 4n³/3 ops for reflectors + 3n² for back-solve → modeled as 2n³.

The O(n³) algorithms form an equivalence class; Cramer's O(n·n!) is in a different class.

## References
- Golub & Van Loan, "Matrix Computations" (4th ed., 2013)
- Trefethen & Bau, "Numerical Linear Algebra" (1997)
- Parent: CramersRuleOQ02.lean (Gaussian vs Cramer)

Theorems: 11 | Sorries: 0 | Axioms: 0
-/

namespace CramersComplexityLUQR

open Nat CramersComplexity

/-! ## Complexity Models -/

/-- LU decomposition: ≈ n³/3 flops, modeled conservatively as n³. -/
def luMuls (n : ℕ) : ℕ := n ^ 3

/-- QR factorization (Householder): ≈ 4n³/3 flops, modeled as 2n³. -/
def qrMuls (n : ℕ) : ℕ := 2 * n ^ 3

/-! ## Relationships Between the Three O(n³) Algorithms -/

/-- LU decomposition matches Gaussian elimination in our complexity model. -/
theorem luMuls_eq_gaussMuls (n : ℕ) : luMuls n = gaussMuls n := rfl

/-- Gaussian elimination needs no more operations than QR factorization. -/
theorem gaussMuls_le_qrMuls (n : ℕ) : gaussMuls n ≤ qrMuls n := by
  simp [gaussMuls, qrMuls]

/-- QR factorization uses at most twice as many operations as Gaussian/LU. -/
theorem qrMuls_le_two_gaussMuls (n : ℕ) : qrMuls n ≤ 2 * gaussMuls n := le_refl _

/-- LU and QR are within a factor of 2: they belong to the same complexity class. -/
theorem lu_qr_constant_factor (n : ℕ) : luMuls n ≤ qrMuls n ∧ qrMuls n ≤ 2 * luMuls n :=
  ⟨gaussMuls_le_qrMuls n, le_refl _⟩

/-! ## LU vs Cramer's Rule -/

/-- LU beats Cramer for n ≥ 4: immediate since luMuls = gaussMuls. -/
theorem lu_beats_cramer {n : ℕ} (hn : 4 ≤ n) : luMuls n < cramersRuleMuls n :=
  gauss_beats_cramer hn

/-- LU beats Cramer for all n ≥ 1 (small cases by computation). -/
theorem lu_beats_cramer_all {n : ℕ} (hn : 1 ≤ n) : luMuls n < cramersRuleMuls n := by
  rcases Nat.lt_or_ge n 4 with h | h
  · interval_cases n <;> native_decide
  · exact lu_beats_cramer h

/-! ## QR vs Cramer's Rule -/

/-- Key lemma: 2n³ < n²·n! for n ≥ 4.
    Proof: 2n³ < n·n³ (since 2 < n), and n·n³ = n²·n² < n²·n! (since n² < n!). -/
private lemma two_n_cube_lt_sq_factorial {n : ℕ} (hn : 4 ≤ n) : 2 * n ^ 3 < n ^ 2 * n ! := by
  have hpos : 0 < n := by omega
  have hlt2 : 2 < n := by omega
  have h_sq : n ^ 2 < n ! := factorial_gt_sq hn
  have h1 : 2 * n ^ 3 < n * n ^ 3 :=
    Nat.mul_lt_mul_of_pos_right hlt2 (Nat.pos_pow_of_pos 3 hpos)
  have h2 : n * n ^ 3 = n ^ 2 * n ^ 2 := by ring
  have h3 : n ^ 2 * n ^ 2 < n ^ 2 * n ! :=
    Nat.mul_lt_mul_of_pos_left h_sq (Nat.pos_pow_of_pos 2 hpos)
  linarith

/-- QR factorization beats Cramer's rule for n ≥ 4.
    Chain: 2n³ < n²·n! ≤ (n+1)·n·n! = cramersRuleMuls n. -/
theorem qr_beats_cramer {n : ℕ} (hn : 4 ≤ n) : qrMuls n < cramersRuleMuls n := by
  rw [qrMuls, cramersRuleMuls_eq]
  have h1 : 2 * n ^ 3 < n ^ 2 * n ! := two_n_cube_lt_sq_factorial hn
  -- n² * n! ≤ (n+1) * n * n! since n² = n*n ≤ (n+1)*n
  have h2 : n ^ 2 * n ! ≤ (n + 1) * n * n ! := by
    apply Nat.mul_le_mul_right
    nlinarith [show n ^ 2 = n * n from by ring]
  linarith

/-- QR beats Cramer for all n ≥ 1 (small cases by computation). -/
theorem qr_beats_cramer_all {n : ℕ} (hn : 1 ≤ n) : qrMuls n < cramersRuleMuls n := by
  rcases Nat.lt_or_ge n 4 with h | h
  · interval_cases n <;> native_decide
  · exact qr_beats_cramer h

/-! ## Asymptotic Superiority of QR over Cramer -/

/-- For any constant K, QR is eventually K-times more efficient than Cramer's rule.
    For n ≥ max(4, 2K): K·2·n³ ≤ n·n³ = n²·n² < n²·n! ≤ cramersRuleMuls n. -/
theorem qr_asymptotically_better (K : ℕ) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → K * qrMuls n < cramersRuleMuls n := by
  use max 4 (2 * K)
  intro n hn
  have hn4 : 4 ≤ n := le_trans (le_max_left 4 (2 * K)) hn
  have hn2K : 2 * K ≤ n := le_trans (le_max_right 4 (2 * K)) hn
  rw [qrMuls, cramersRuleMuls_eq]
  have hpos : 0 < n := by omega
  have h_sq : n ^ 2 < n ! := factorial_gt_sq hn4
  -- K·(2n³) ≤ n·n³ (since 2K ≤ n, so K·2 ≤ n)
  have step1 : K * (2 * n ^ 3) ≤ n * n ^ 3 := by nlinarith
  -- n·n³ = n²·n² < n²·n!
  have step2 : n * n ^ 3 < n ^ 2 * n ! := by
    have heq : n * n ^ 3 = n ^ 2 * n ^ 2 := by ring
    nlinarith [Nat.pos_pow_of_pos 2 hpos, heq.symm]
  -- n²·n! ≤ (n+1)·n·n!
  have step3 : n ^ 2 * n ! ≤ (n + 1) * n * n ! := by
    apply Nat.mul_le_mul_right
    nlinarith [show n ^ 2 = n * n from by ring]
  linarith

/-! ## Three-Way and Summary Theorems -/

/-- For n ≥ 4: luMuls n = gaussMuls n ≤ qrMuls n < cramersRuleMuls n. -/
theorem three_way_comparison {n : ℕ} (hn : 4 ≤ n) :
    luMuls n = gaussMuls n ∧
    gaussMuls n ≤ qrMuls n ∧
    qrMuls n < cramersRuleMuls n :=
  ⟨luMuls_eq_gaussMuls n, gaussMuls_le_qrMuls n, qr_beats_cramer hn⟩

/-- All O(n³) algorithms beat Cramer by any multiplicative factor for large n. -/
theorem all_cubic_asymptotically_beat_cramer (K : ℕ) :
    (∃ N, ∀ n, N ≤ n → K * gaussMuls n < cramersRuleMuls n) ∧
    (∃ N, ∀ n, N ≤ n → K * luMuls n < cramersRuleMuls n) ∧
    (∃ N, ∀ n, N ≤ n → K * qrMuls n < cramersRuleMuls n) :=
  ⟨cramer_asymptotically_worse K,
   cramer_asymptotically_worse K,
   qr_asymptotically_better K⟩

/-- Main summary: LU/QR vs Cramer complexity comparison. -/
theorem lu_qr_vs_cramer_summary :
    (∀ n, luMuls n = gaussMuls n) ∧
    (∀ n, qrMuls n = 2 * gaussMuls n) ∧
    (∀ n : ℕ, 4 ≤ n → luMuls n < cramersRuleMuls n) ∧
    (∀ n : ℕ, 4 ≤ n → qrMuls n < cramersRuleMuls n) ∧
    (∀ K : ℕ, ∃ N, ∀ n, N ≤ n → K * qrMuls n < cramersRuleMuls n) :=
  ⟨luMuls_eq_gaussMuls, fun _ => rfl,
   fun n hn => lu_beats_cramer hn,
   fun n hn => qr_beats_cramer hn,
   qr_asymptotically_better⟩

end CramersComplexityLUQR
