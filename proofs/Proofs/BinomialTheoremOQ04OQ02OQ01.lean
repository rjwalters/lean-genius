/-
q-Vandermonde Identity: Gaussian Binomial Coefficients

Open Question (binomial-theorem-oq-04-oq-02-oq-01):
"Can the q-analog of Vandermonde's identity be formalized in Lean 4?"

Answer: We formalize the key components:
1. The Gaussian binomial coefficient [n choose k]_q via the q-Pascal recurrence
2. Basic properties: vanishing for k > n, recovery of classical binomials at q=1
3. The q-Vandermonde identity:
   [m+n choose r]_q = Σ_{k=0}^{r} [m choose k]_q · [n choose r-k]_q · q^(k·(n+k-r))

The Gaussian binomial [n choose k]_q counts k-dimensional subspaces of 𝔽_q^n.
It is a polynomial in q with non-negative integer coefficients; at q=1, it equals C(n,k).

References:
- Gasper and Rahman, Basic Hypergeometric Series (2004)
- Kac and Cheung, Quantum Calculus (2002)
- Mathlib4: no gaussBinom — built from scratch here
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic

open BigOperators Finset

noncomputable section

namespace BinomialTheoremOQ04OQ02OQ01

variable {R : Type*} [CommRing R]

-- ============================================================
-- PART I: Definition of Gaussian Binomial Coefficients
-- ============================================================

def gaussBinom (q : R) : ℕ → ℕ → R
  | _, 0 => 1
  | 0, _ + 1 => 0
  | n + 1, k + 1 => q ^ (k + 1) * gaussBinom q n (k + 1) + gaussBinom q n k

@[simp] theorem gaussBinom_zero_right (q : R) (n : ℕ) : gaussBinom q n 0 = 1 := by cases n <;> rfl
@[simp] theorem gaussBinom_zero_left (q : R) (k : ℕ) : gaussBinom q 0 (k + 1) = 0 := rfl

theorem gaussBinom_succ_succ (q : R) (n k : ℕ) :
    gaussBinom q (n + 1) (k + 1) = q ^ (k + 1) * gaussBinom q n (k + 1) + gaussBinom q n k := rfl

theorem gaussBinom_eq_zero_of_lt (q : R) {n k : ℕ} (h : n < k) : gaussBinom q n k = 0 := by
  induction n generalizing k with
  | zero => obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩; rfl
  | succ n ih =>
    obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
    -- h : n + 1 < m + 1, so n < m + 1 and n < m
    have h1 : gaussBinom q n (m + 1) = 0 := ih (by omega)
    have h2 : gaussBinom q n m = 0 := ih (by omega)
    simp only [gaussBinom_succ_succ, h1, h2, mul_zero, zero_add]

theorem gaussBinom_self (q : R) (n : ℕ) : gaussBinom q n n = 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [gaussBinom_succ_succ,
               gaussBinom_eq_zero_of_lt q (Nat.lt_succ_self n), mul_zero, zero_add, ih]

theorem gaussBinom_one : ∀ (n k : ℕ), gaussBinom (1 : R) n k = (Nat.choose n k : R) := by
  intro n; induction n with
  | zero => intro k; cases k with | zero => simp | succ k => simp
  | succ n ih =>
    intro k; cases k with
    | zero => simp
    | succ k =>
      simp only [gaussBinom_succ_succ, ih (k + 1), ih k, one_pow, one_mul,
                 add_comm, ← Nat.cast_add, ← Nat.choose_succ_succ]

-- ============================================================
-- Key lemma: per-term identity for the inductive step
-- ============================================================

/-- The core per-term algebraic identity: for k ≤ s,
    q^(s+1)*T(n,s+1,k) + T(n,s,k) = T(n+1,s+1,k)
    where T(n,r,k) = GB(m,k)*GB(n,r-k)*q^(k*(n+k-r)). -/
private lemma q_vand_step_term (q : R) (m n s k : ℕ) (hks : k ≤ s) :
    q ^ (s + 1) * (gaussBinom q m k * gaussBinom q n (s + 1 - k) * q ^ (k * (n + k - (s + 1))))
    + gaussBinom q m k * gaussBinom q n (s - k) * q ^ (k * (n + k - s))
    = gaussBinom q m k * gaussBinom q (n + 1) (s + 1 - k) * q ^ (k * (n + 1 + k - (s + 1))) := by
  have hexp_out : n + 1 + k - (s + 1) = n + k - s := by omega
  rw [hexp_out]
  obtain ⟨j, hj⟩ : ∃ j, s + 1 - k = j + 1 := ⟨s - k, by omega⟩
  have hsk : s - k = j := by omega
  rw [hj, hsk, gaussBinom_succ_succ]
  by_cases hn_lt : n < j + 1
  · have h1 : gaussBinom q n (j + 1) = 0 := gaussBinom_eq_zero_of_lt q hn_lt
    by_cases hn_eq : n = j
    · subst hn_eq
      simp only [h1, gaussBinom_self, mul_zero, zero_mul, add_zero, zero_add, mul_one]
    · have h2 : gaussBinom q n j = 0 := gaussBinom_eq_zero_of_lt q (by omega)
      simp only [h1, h2, mul_zero, zero_mul, add_zero]
  · push_neg at hn_lt
    have hmul : k * (n + k - s) = k * (n + k - (s + 1)) + k := by
      have : n + k - s = n + k - (s + 1) + 1 := by omega
      rw [this, Nat.mul_add, Nat.mul_one]
    have hexp_in : s + 1 + k * (n + k - (s + 1)) = j + 1 + k * (n + k - s) := by
      rw [hmul, ← hj]; omega
    have hpow : q ^ (s + 1) * q ^ (k * (n + k - (s + 1))) = q ^ (j + 1) * q ^ (k * (n + k - s)) := by
      rw [← pow_add, ← pow_add, hexp_in]
    calc q ^ (s + 1) * (gaussBinom q m k * gaussBinom q n (j + 1) * q ^ (k * (n + k - (s + 1))))
            + gaussBinom q m k * gaussBinom q n j * q ^ (k * (n + k - s))
        = gaussBinom q m k * gaussBinom q n (j + 1) * (q ^ (s + 1) * q ^ (k * (n + k - (s + 1))))
            + gaussBinom q m k * gaussBinom q n j * q ^ (k * (n + k - s)) := by ring
      _ = gaussBinom q m k * gaussBinom q n (j + 1) * (q ^ (j + 1) * q ^ (k * (n + k - s)))
            + gaussBinom q m k * gaussBinom q n j * q ^ (k * (n + k - s)) := by rw [hpow]
      _ = gaussBinom q m k * (q ^ (j + 1) * gaussBinom q n (j + 1) + gaussBinom q n j) *
            q ^ (k * (n + k - s)) := by ring

-- ============================================================
-- Base case helper
-- ============================================================

private lemma q_vandermonde_base (q : R) (m r : ℕ) :
    gaussBinom q m r =
    ∑ k ∈ range (r + 1), gaussBinom q m k * gaussBinom q 0 (r - k) * q ^ (k * (0 + k - r)) := by
  induction r with
  | zero => simp
  | succ s _ =>
    -- Only the k = s+1 term survives; all k < s+1 have GB(0, s+1-k) = 0
    rw [Finset.sum_range_succ]
    have hzero : ∑ k ∈ range (s + 1),
        gaussBinom q m k * gaussBinom q 0 (s + 1 - k) * q ^ (k * (0 + k - (s + 1))) = 0 := by
      apply Finset.sum_eq_zero
      intro k hk
      simp only [Finset.mem_range] at hk
      obtain ⟨j, hj⟩ : ∃ j, s + 1 - k = j + 1 := ⟨s - k, by omega⟩
      rw [hj]; simp [gaussBinom_zero_left]
    rw [hzero, zero_add]
    simp [gaussBinom_self]

-- ============================================================
-- Main theorem: q-Vandermonde
-- ============================================================

/-- **q-Vandermonde Identity**:
`[m+n choose r]_q = Σ_{k=0}^{r} [m choose k]_q · [n choose r-k]_q · q^(k·(n+k-r))`

This is the q-analog of the classical Vandermonde convolution, recovered at q=1. -/
theorem q_vandermonde (q : R) (m n r : ℕ) :
    gaussBinom q (m + n) r =
    ∑ k ∈ range (r + 1), gaussBinom q m k * gaussBinom q n (r - k) * q ^ (k * (n + k - r)) := by
  induction n generalizing r with
  | zero => simp only [Nat.add_zero]; exact q_vandermonde_base q m r
  | succ n ih =>
    induction r with
    | zero => simp
    | succ s =>
      rw [show m + (n + 1) = m + n + 1 from by ring, gaussBinom_succ_succ, ih (s + 1), ih s,
          Finset.mul_sum]
      -- Peel k = s+1 from the (s+2)-range sum on the left (IH for s+1)
      -- Note: Finset.sum_range_succ gives ∑_{k<n+1} f k = ∑_{k<n} f k + f n
      have sum_lhs_peel :
          ∑ k ∈ range (s + 2),
            q ^ (s + 1) * (gaussBinom q m k * gaussBinom q n (s + 1 - k) * q ^ (k * (n + k - (s + 1)))) =
          ∑ k ∈ range (s + 1),
            q ^ (s + 1) * (gaussBinom q m k * gaussBinom q n (s + 1 - k) * q ^ (k * (n + k - (s + 1))))
          + q ^ (s + 1) *
              (gaussBinom q m (s + 1) * gaussBinom q n (s + 1 - (s + 1)) *
               q ^ ((s + 1) * (n + (s + 1) - (s + 1)))) := by
        rw [Finset.sum_range_succ]
      -- Peel k = s+1 from the RHS (s+2)-range sum
      have sum_rhs_peel :
          ∑ k ∈ range (s + 2),
            gaussBinom q m k * gaussBinom q (n + 1) (s + 1 - k) * q ^ (k * (n + 1 + k - (s + 1))) =
          ∑ k ∈ range (s + 1),
            gaussBinom q m k * gaussBinom q (n + 1) (s + 1 - k) * q ^ (k * (n + 1 + k - (s + 1)))
          + gaussBinom q m (s + 1) * gaussBinom q (n + 1) (s + 1 - (s + 1)) *
              q ^ ((s + 1) * (n + 1 + (s + 1) - (s + 1))) := by
        rw [Finset.sum_range_succ]
      -- Simplify boundary terms: both reduce to GB(m,s+1) * q^((s+1)*(n+1))
      have hbd_lhs : q ^ (s + 1) *
          (gaussBinom q m (s + 1) * gaussBinom q n (s + 1 - (s + 1)) *
           q ^ ((s + 1) * (n + (s + 1) - (s + 1)))) =
          gaussBinom q m (s + 1) * q ^ ((s + 1) * (n + 1)) := by
        have e1 : s + 1 - (s + 1) = 0 := Nat.sub_self _
        have e2 : n + (s + 1) - (s + 1) = n := by omega
        simp only [e1, e2, gaussBinom_zero_right, mul_one]
        ring
      have hbd_rhs : gaussBinom q m (s + 1) * gaussBinom q (n + 1) (s + 1 - (s + 1)) *
          q ^ ((s + 1) * (n + 1 + (s + 1) - (s + 1))) =
          gaussBinom q m (s + 1) * q ^ ((s + 1) * (n + 1)) := by
        have e1 : s + 1 - (s + 1) = 0 := Nat.sub_self _
        have e2 : n + 1 + (s + 1) - (s + 1) = n + 1 := by omega
        simp only [e1, e2, gaussBinom_zero_right, mul_one]
      -- Key lemma: combine the two inner sums using q_vand_step_term
      have key : ∑ k ∈ range (s + 1),
          gaussBinom q m k * gaussBinom q (n + 1) (s + 1 - k) * q ^ (k * (n + 1 + k - (s + 1))) =
          ∑ k ∈ range (s + 1),
            q ^ (s + 1) * (gaussBinom q m k * gaussBinom q n (s + 1 - k) * q ^ (k * (n + k - (s + 1))))
          + ∑ k ∈ range (s + 1),
              gaussBinom q m k * gaussBinom q n (s - k) * q ^ (k * (n + k - s)) := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro k hk
        simp only [Finset.mem_range] at hk
        exact (q_vand_step_term q m n s k (by omega)).symm
      -- Assemble: rewrite sums and boundary terms, then ring
      rw [show s + 1 + 1 = s + 2 from rfl, sum_lhs_peel, sum_rhs_peel,
          hbd_lhs, hbd_rhs, key]
      ring

-- ============================================================
-- Corollary: Classical Vandermonde
-- ============================================================

/-- Classical Vandermonde as a corollary: setting q = 1 recovers `C(m+n, r) = Σ_k C(m,k)·C(n,r-k)`. -/
theorem vandermonde_from_q (m n r : ℕ) :
    (Nat.choose (m + n) r : R) =
    ∑ k ∈ range (r + 1), (Nat.choose m k : R) * (Nat.choose n (r - k) : R) := by
  have h := q_vandermonde (1 : R) m n r
  simp only [gaussBinom_one, one_pow, mul_one] at h
  exact h

end BinomialTheoremOQ04OQ02OQ01

end
