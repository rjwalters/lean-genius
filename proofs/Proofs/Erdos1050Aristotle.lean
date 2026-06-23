/-
  Aristotle targets for Erdős Problem #1050
  Routine supporting lemmas for automated proof search.
  See Erdos1050Problem.lean for the main formalization.

  Criteria for inclusion:
  - NOT the main open conjecture (transcendence conjecture is excluded)
  - Known results: arithmetic facts, convergence, definitional equalities
  - Clean theorem statements with no definition sorries
  - No axioms

  Targets:
  1. denom_nonzero: 2^n - 3 ≠ 0 for n ≥ 2 (simple arithmetic)
  2. denom_sequence: oeis_A331372 n = 2^n - 3 (computation)
  3. denom_growth: 2^n - 3 > 2^(n-1) for n ≥ 3 (inequality)
  4. S_eq_sumTwoMinusThree: two definitions of S agree (definitional)
  5. T_eq_S_1049: T(q, -1) = S_1049(q) (definitional)
  6. transcendence_implies_irrationality: transcendental implies irrational
-/
import Mathlib

namespace Erdos1050

open BigOperators Real

/-- The general series T(q, r) = ∑_{n≥1} 1/(q^n + r). -/
noncomputable def T (q : ℕ) (r : ℚ) : ℝ :=
  ∑' n : ℕ, if n = 0 then 0 else 1 / ((q : ℝ)^n + (r : ℝ))

/-- The specific series S = ∑_{n≥1} 1/(2^n - 3). -/
noncomputable def S : ℝ := T 2 (-3)

/-- Alternative notation for clarity. -/
noncomputable def sumTwoMinusThree : ℝ :=
  ∑' n : ℕ, if n = 0 then 0 else 1 / (2^n - 3 : ℝ)

/-- S_1049(t) = ∑ 1/(t^n - 1). -/
noncomputable def S_1049 (t : ℝ) : ℝ :=
  ∑' n : ℕ, if n = 0 then 0 else 1 / (t^n - 1)

/-- OEIS A331372: Related sequence. -/
def oeis_A331372 : ℕ → ℤ
  | 0 => 1
  | n + 1 => 2^(n+1) - 3

-- Routine: 2^n - 3 ≠ 0 for n ≥ 2 (simple power arithmetic)
theorem denom_nonzero (n : ℕ) (hn : n ≥ 2) : (2 : ℝ)^n - 3 ≠ 0 := by
  have h : (2 : ℝ)^n ≥ 4 := by
    calc (2 : ℝ)^n ≥ 2^2 := by
          apply pow_le_pow_right (by norm_num : (1 : ℝ) ≤ 2) hn
      _ = 4 := by norm_num
  linarith

-- Routine: the OEIS sequence equals 2^n - 3 (simple case analysis on def)
theorem denom_sequence (n : ℕ) (hn : n ≥ 1) :
    oeis_A331372 n = 2^n - 3 := by
  cases n with
  | zero => omega
  | succ m => simp [oeis_A331372]

-- Routine: 2^n - 3 > 2^(n-1) for n ≥ 3 (power inequality)
theorem denom_growth (n : ℕ) (hn : n ≥ 3) :
    (oeis_A331372 n : ℝ) > 2^(n-1) := by
  cases n with
  | zero => omega
  | succ m =>
    simp [oeis_A331372]
    push_cast
    have hm : m ≥ 2 := by omega
    have h2m : (2 : ℝ)^(m + 1) = 2 * 2^m := by ring
    rw [h2m]
    have h2pos : (2 : ℝ)^m ≥ 4 := by
      calc (2 : ℝ)^m ≥ 2^2 := pow_le_pow_right (by norm_num) hm
        _ = 4 := by norm_num
    linarith

-- Routine: the two definitions of S agree (unfold T and simplify)
theorem S_eq_sumTwoMinusThree : S = sumTwoMinusThree := by
  simp only [S, sumTwoMinusThree, T]
  congr 1; ext n
  split
  · simp
  · push_cast; ring_nf

-- Routine: T(q, -1) = S_1049(q) for integer q (definitional equality)
theorem T_eq_S_1049 (q : ℕ) (hq : q ≥ 2) : T q (-1) = S_1049 q := by
  simp only [T, S_1049]
  congr 1; ext n
  split
  · simp
  · push_cast; ring_nf

-- Routine: transcendental implies irrational (known mathematical fact)
theorem transcendence_implies_irrationality :
    (∀ q : ℕ, q ≥ 2 → ∀ r : ℚ, r ≠ 0 →
      (∀ n : ℕ, n ≥ 1 → (r : ℝ) ≠ -((q : ℝ)^n)) →
      Transcendental ℚ (T q r)) →
    ∀ q : ℕ, q ≥ 2 → ∀ r : ℚ, r ≠ 0 →
      (∀ n : ℕ, n ≥ 1 → (r : ℝ) ≠ -((q : ℝ)^n)) →
      Irrational (T q r) := by
  intro hT q hq r hr hn
  exact (hT q hq r hr hn).irrational

end Erdos1050
