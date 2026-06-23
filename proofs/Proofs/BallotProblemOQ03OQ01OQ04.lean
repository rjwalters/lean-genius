/-
  Catalan Number Recurrence: Formal Proof from the Ballot Formula

  Source: ballot-problem-oq-03-oq-01-oq-04
  Status: PROVED

  Statement: The Catalan numbers Cₙ satisfy the convolution recurrence:
    Cₙ₊₁ = ∑_{k=0}^{n} Cₖ · Cₙ₋ₖ

  The Catalan numbers arise from the ballot problem (lattice path counting):
    Cₙ = C(2n,n) - C(2n,n+1) = C(2n,n)/(n+1)

  Proof strategy:
  1. Define Cₙ via the ballot/closed-form formula: Cn n = C(2n,n) - C(2n,n+1).
  2. Prove the key identity: Cn n * (n+1) = C(2n,n) (catalan_formula).
  3. Connect Cn to Mathlib's `catalan` via multiplication cancellation:
     both Cn n * (n+1) and (n+1) * catalan n equal centralBinom n = C(2n,n).
  4. Use Mathlib's catalan_succ' (antidiagonal form) plus
     Finset.Nat.sum_antidiagonal_eq_sum_range_succ to get the range-indexed recurrence.

  References:
  - Mathlib.Combinatorics.Enumerative.Catalan: catalan, catalan_succ', succ_mul_catalan_eq_centralBinom
  - Mathlib.Data.Nat.Choose.Central: centralBinom, centralBinom_eq_two_mul_choose
  - Parent: ballot-problem-oq-03-oq-01 (lattice path LGV lemma)
-/

import Mathlib.Combinatorics.Enumerative.Catalan
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Tactic

open Nat Finset BigOperators

namespace BallotCatalanRecurrence

/-
## Part I: The Ballot-Formula Catalan Number
-/

/-- The ballot-formula Catalan number: Cn n = C(2n,n) - C(2n,n+1).
    This arises from counting monotone lattice paths from (0,0) to (2n,0)
    that stay non-negative (Dyck paths / ballot sequences). -/
def Cn (n : ℕ) : ℕ := Nat.choose (2 * n) n - Nat.choose (2 * n) (n + 1)

/-- Auxiliary identity: C(2n, n+1) * (n+1) = C(2n, n) * n.
    This is the key algebraic identity used in the Catalan formula proof.
    Proof: Use the absorption identity C(m+1,k+1)*(k+1) = (m+1)*C(m,k) twice
    and the symmetry C(2n+1, n+1) = C(2n+1, n). -/
private theorem choose_2n_succ (n : ℕ) :
    Nat.choose (2 * n) (n + 1) * (n + 1) = Nat.choose (2 * n) n * n := by
  rcases n with _ | n
  · simp
  · have h1 := Nat.add_one_mul_choose_eq (2 * n + 1) (n + 1)
    have h2 := Nat.add_one_mul_choose_eq (2 * n + 1) n
    -- choose(2n+1, n+1) = choose(2n+1, n) by symmetry of central binomial row
    rw [Nat.choose_symm_half n] at h1
    -- h1 : (2n+2) * choose(2n+1, n) = choose(2n+2, n+2) * (n+2)
    -- h2 : (2n+2) * choose(2n+1, n) = choose(2n+2, n+1) * (n+1)
    -- Goal: choose(2*(n+1), (n+1)+1) * ((n+1)+1) = choose(2*(n+1), n+1) * (n+1)
    -- Normalize 2*(n+1) = 2*n+1+1 to match h1, h2's form
    simp only [show 2 * (n + 1) = 2 * n + 1 + 1 from by omega]
    linarith

/-- **The ballot-formula Catalan identity**: Cn n * (n + 1) = C(2n, n).
    Proof: Cn n = C(2n,n) - C(2n,n+1), so
    Cn n * (n+1) = C(2n,n)*(n+1) - C(2n,n+1)*(n+1)
               = C(2n,n)*(n+1) - C(2n,n)*n   [by choose_2n_succ]
               = C(2n,n). -/
theorem catalan_formula (n : ℕ) : Cn n * (n + 1) = Nat.choose (2 * n) n := by
  simp only [Cn]
  cases n with
  | zero => simp
  | succ n =>
    set m := n + 1 with hm_def
    set a := Nat.choose (2 * m) m
    set b := Nat.choose (2 * m) (m + 1)
    have h_abs : b * (m + 1) = a * m := choose_2n_succ m
    have h_le : b ≤ a := by
      have h1 : b * m ≤ b * (m + 1) := Nat.mul_le_mul_left b (by omega)
      have h2 : b * m ≤ a * m := h1.trans (le_of_eq h_abs)
      exact Nat.le_of_mul_le_mul_right h2 (by omega)
    zify [h_le] at h_abs ⊢
    linear_combination -h_abs

/-
## Part II: Connecting the Ballot-Formula Cn to Mathlib's catalan
-/

/-- The ballot-formula Catalan number Cn n equals Mathlib's catalan n.

    Proof: Both Cn n * (n+1) and (n+1) * catalan n equal centralBinom n = C(2n,n).
    By multiplication cancellation (n+1 ≠ 0), Cn n = catalan n. -/
theorem Cn_eq_catalan (n : ℕ) : Cn n = catalan n := by
  apply Nat.eq_of_mul_eq_mul_right (Nat.succ_pos n)
  -- Goal: Cn n * (n+1) = catalan n * (n+1)
  have h1 : Cn n * (n + 1) = Nat.centralBinom n := by
    rw [catalan_formula n, Nat.centralBinom_eq_two_mul_choose]
  have h2 : catalan n * (n + 1) = Nat.centralBinom n := by
    rw [mul_comm]
    exact succ_mul_catalan_eq_centralBinom n
  exact h1.trans h2.symm

/-
## Part III: The Catalan Convolution Recurrence
-/

/-- **Catalan Convolution Recurrence** (Ballot Theorem version):

    Cₙ₊₁ = ∑_{k=0}^{n} Cₖ · Cₙ₋ₖ

    Proof:
    1. Rewrite Cn = catalan throughout (via Cn_eq_catalan).
    2. Apply Mathlib's catalan_succ' (antidiagonal form).
    3. Convert antidiagonal sum to range sum via sum_antidiagonal_eq_sum_range_succ. -/
theorem Cn_recurrence (n : ℕ) :
    Cn (n + 1) = ∑ k ∈ Finset.range (n + 1), Cn k * Cn (n - k) := by
  simp_rw [Cn_eq_catalan]
  -- Goal: catalan (n+1) = ∑ k in range (n+1), catalan k * catalan (n-k)
  rw [catalan_succ']
  -- Goal: ∑ ij in antidiagonal n, catalan ij.1 * catalan ij.2
  --       = ∑ k in range (n+1), catalan k * catalan (n-k)
  exact Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun k l => catalan k * catalan l) n

/-
## Part IV: Consequences and Verifications
-/

-- Numerical verification of the recurrence
example : Cn 1 = Cn 0 * Cn 0 := by native_decide
example : Cn 2 = Cn 0 * Cn 1 + Cn 1 * Cn 0 := by native_decide
example : Cn 3 = Cn 0 * Cn 2 + Cn 1 * Cn 1 + Cn 2 * Cn 0 := by native_decide
example : Cn 4 = Cn 0 * Cn 3 + Cn 1 * Cn 2 + Cn 2 * Cn 1 + Cn 3 * Cn 0 := by native_decide

/-- Catalan numbers are strictly positive. -/
theorem Cn_pos (n : ℕ) : 0 < Cn n := by
  apply Nat.pos_of_ne_zero
  intro hzero
  have h : Cn n * (n + 1) = Nat.choose (2 * n) n := catalan_formula n
  have hpos : 0 < Nat.choose (2 * n) n := Nat.choose_pos (by omega)
  simp [hzero] at h
  linarith

/-- The Catalan number C₀ = 1. -/
theorem Cn_zero : Cn 0 = 1 := by simp [Cn]

/-- The Catalan number C₁ = 1. -/
theorem Cn_one : Cn 1 = 1 := by simp [Cn]

/-- The Catalan number C₂ = 2. -/
theorem Cn_two : Cn 2 = 2 := by native_decide

/-- Symmetry: The Catalan recurrence is symmetric in the summands. -/
theorem Cn_recurrence_sym (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), Cn k * Cn (n - k) =
    ∑ k ∈ Finset.range (n + 1), Cn (n - k) * Cn k := by
  congr 1; ext k; ring

/-
## Part V: Connection to the Ballot Theorem
-/

/-- The Catalan recurrence follows from the ballot theorem interpretation:

    Cn n counts lattice paths from (0,0) to (2n,0) that stay non-negative
    (Dyck paths). The "first return decomposition" gives:
    - A Dyck path of length 2(n+1) first returns to 0 at step 2(k+1), for some k ∈ {0,...,n}.
    - The segment from step 1 to step 2k+1 is a Dyck path of length 2k (counted by Cn k).
    - The remainder from step 2k+2 to step 2(n+1) is a Dyck path of length 2(n-k) (Cn (n-k)).
    This decomposition gives exactly the convolution recurrence.

    This theorem provides the algebraic verification of that combinatorial fact. -/
theorem Cn_ballot_recurrence_interpretation (n : ℕ) :
    Cn (n + 1) = ∑ k ∈ Finset.range (n + 1), Cn k * Cn (n - k) :=
  Cn_recurrence n

/-- Summary: Catalan numbers are characterized by the initial condition C₀ = 1
    and the convolution recurrence Cₙ₊₁ = ∑_{k=0}^{n} Cₖ · Cₙ₋ₖ. -/
theorem Cn_characterization :
    Cn 0 = 1 ∧ ∀ n : ℕ, Cn (n + 1) = ∑ k ∈ Finset.range (n + 1), Cn k * Cn (n - k) :=
  ⟨Cn_zero, Cn_recurrence⟩

end BallotCatalanRecurrence
