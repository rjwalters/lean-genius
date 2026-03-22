/-
  Gaussian q-Binomial Coefficients: Hockey Stick Generalization

  Open Question (arithmetic-series-oq-02-oq-01):
  "Generalize the hockey stick identity to q-binomial coefficients."

  The Gaussian binomial coefficient [n choose k]_q is the q-analog of the
  ordinary binomial coefficient, defined by the recurrence:
    [n+1 choose k+1]_q = q^{k+1} · [n choose k+1]_q + [n choose k]_q
  with [n choose 0]_q = 1 and [0 choose k+1]_q = 0.

  When q = 1, this reduces to the ordinary binomial coefficient C(n, k).

  Reference: V. Kac, P. Cheung, "Quantum Calculus" (Springer, 2002)
-/
import Mathlib

namespace GaussianBinomial

open Finset BigOperators

-- ============================================================
-- Gaussian (q-)Binomial Coefficient
-- ============================================================

/-- The Gaussian binomial coefficient [n choose k]_q, defined recursively via
    q-Pascal's rule. Works in any commutative ring R. -/
noncomputable def qBinom {R : Type*} [CommRing R] (q : R) : ℕ → ℕ → R
  | _, 0 => 1
  | 0, _ + 1 => 0
  | n + 1, k + 1 => q ^ (k + 1) * qBinom q n (k + 1) + qBinom q n k

-- ============================================================
-- Boundary Cases
-- ============================================================

@[simp]
theorem qBinom_zero_right {R : Type*} [CommRing R] (q : R) (n : ℕ) :
    qBinom q n 0 = 1 := by
  cases n <;> simp [qBinom]

@[simp]
theorem qBinom_zero_succ {R : Type*} [CommRing R] (q : R) (k : ℕ) :
    qBinom q 0 (k + 1) = 0 := by
  simp [qBinom]

-- ============================================================
-- q-Pascal's Rule (by definition)
-- ============================================================

/-- q-Pascal's rule: [n+1 choose k+1]_q = q^{k+1} [n choose k+1]_q + [n choose k]_q -/
theorem qBinom_succ_succ {R : Type*} [CommRing R] (q : R) (n k : ℕ) :
    qBinom q (n + 1) (k + 1) = q ^ (k + 1) * qBinom q n (k + 1) + qBinom q n k := by
  simp [qBinom]

-- ============================================================
-- Vanishing: [n choose k]_q = 0 when k > n
-- ============================================================

@[simp]
theorem qBinom_eq_zero_of_lt {R : Type*} [CommRing R] (q : R) {n k : ℕ} (h : n < k) :
    qBinom q n k = 0 := by
  induction n generalizing k with
  | zero => cases k with | zero => omega | succ k => rfl
  | succ n ih =>
    cases k with
    | zero => omega
    | succ k =>
      rw [qBinom_succ_succ, ih (by omega : n < k + 1), ih (by omega : n < k)]
      simp

-- ============================================================
-- Diagonal: [n choose n]_q = 1
-- ============================================================

@[simp]
theorem qBinom_self {R : Type*} [CommRing R] (q : R) (n : ℕ) :
    qBinom q n n = 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [qBinom_succ_succ, qBinom_eq_zero_of_lt q (by omega : n < n + 1),
        mul_zero, zero_add, ih]

-- ============================================================
-- Specialization: q = 1 gives ordinary binomial
-- ============================================================

/-- When q = 1, the q-binomial reduces to the ordinary binomial coefficient. -/
theorem qBinom_one {n k : ℕ} (hk : k ≤ n) :
    qBinom (1 : ℤ) n k = Nat.choose n k := by
  induction n generalizing k with
  | zero =>
    have := Nat.eq_zero_of_le_zero hk; subst this; simp
  | succ n ih =>
    cases k with
    | zero => simp [Nat.choose_zero_right]
    | succ k =>
      rw [qBinom_succ_succ, one_pow, one_mul]
      by_cases hk1 : k + 1 ≤ n
      · rw [ih hk1, ih (by omega : k ≤ n)]
        linarith [Nat.choose_succ_succ n k]
      · have hkn : k = n := by omega
        subst hkn
        rw [qBinom_eq_zero_of_lt (1 : ℤ) (by omega : k < k + 1),
            zero_add, ih (le_refl k)]
        simp [Nat.choose_self]

-- ============================================================
-- q-Simplicial Numbers
-- ============================================================

/-- The q-simplicial number: q-analog of the simplicial number C(n+k, k).
    Specializes to ArithmeticSeriesOQ02.simplicial when q = 1. -/
noncomputable def qSimplicial {R : Type*} [CommRing R] (q : R) (k n : ℕ) : R :=
  qBinom q (n + k) k

@[simp]
theorem qSimplicial_zero_left {R : Type*} [CommRing R] (q : R) (n : ℕ) :
    qSimplicial q 0 n = 1 := by
  simp [qSimplicial]

@[simp]
theorem qSimplicial_start {R : Type*} [CommRing R] (q : R) (k : ℕ) :
    qSimplicial q k 0 = 1 := by
  simp [qSimplicial]

-- ============================================================
-- q-Simplicial Recurrence (q-analog of simplicial_succ_recurrence)
-- ============================================================

/-- The q-simplicial recurrence:
    qS(k+1, n+1) = q^{k+1} · qS(k+1, n) + qS(k, n+1)
    When q = 1, reduces to: S(k+1, n+1) = S(k+1, n) + S(k, n+1). -/
theorem qSimplicial_succ_recurrence {R : Type*} [CommRing R] (q : R) (k n : ℕ) :
    qSimplicial q (k + 1) (n + 1) =
    q ^ (k + 1) * qSimplicial q (k + 1) n + qSimplicial q k (n + 1) := by
  simp only [qSimplicial]
  rw [show n + 1 + (k + 1) = (n + (k + 1)) + 1 from by ring,
      show n + 1 + k = n + (k + 1) from by ring,
      show n + (k + 1) = n + k + 1 from by ring]
  exact qBinom_succ_succ q (n + k + 1) k

-- ============================================================
-- q-Hockey Stick Identity
-- ============================================================

/-- **q-Hockey Stick Identity**: The q-analog of the hockey stick identity.
    ∑_{j=0}^{N} q^{(N-j)(k+1)} · [j+k choose k]_q = [N+k+1 choose k+1]_q
    When q = 1, reduces to: ∑_{j=0}^N C(j+k, k) = C(N+k+1, k+1). -/
theorem qHockeyStick {R : Type*} [CommRing R] (q : R) (k N : ℕ) :
    ∑ j ∈ range (N + 1), q ^ ((N - j) * (k + 1)) * qSimplicial q k j =
    qSimplicial q (k + 1) N := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ]
    -- Last term: j = N+1, so (N+1 - (N+1)) * (k+1) = 0
    simp only [Nat.sub_self, zero_mul, pow_zero, one_mul]
    -- Remaining sum: ∑_{j=0}^{N} q^{(N+1-j)(k+1)} * qS(k, j)
    -- Factor out q^{k+1}: each exponent (N+1-j)(k+1) = (N-j)(k+1) + (k+1)
    have hfactor : ∀ j ∈ Finset.range (N + 1),
        q ^ ((N + 1 - j) * (k + 1)) * qSimplicial q k j =
        q ^ (k + 1) * (q ^ ((N - j) * (k + 1)) * qSimplicial q k j) := by
      intro j hj
      simp only [Finset.mem_range] at hj
      have hsub : N + 1 - j = (N - j) + 1 := by omega
      rw [hsub, add_mul, one_mul, pow_add]
      ring
    rw [Finset.sum_congr rfl hfactor, ← Finset.mul_sum, ih]
    rw [qSimplicial_succ_recurrence]

end GaussianBinomial
