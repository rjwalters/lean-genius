/-
Erdős Problem #317: Signed Unit Fraction Approximations

Source: https://erdosproblems.com/317
Status: OPEN

Statement:
Is there some constant c > 0 such that for every n ≥ 1 there exists
δ_k ∈ {-1, 0, 1} for 1 ≤ k ≤ n with:
    0 < |∑_{1≤k≤n} δ_k/k| < c/2^n ?

Related Question:
For sufficiently large n, for any δ_k ∈ {-1, 0, 1}, must we have:
    |∑_{1≤k≤n} δ_k/k| > 1/lcm(1,...,n)
whenever the left-hand side is nonzero?

Known Results:
- Kovac-van Doorn: Upper bound 2^{-n·(log log log n)^{1+o(1)} / log n}
- The strict inequality fails for small n (e.g., 1/2 - 1/3 - 1/4 = -1/12)
- van Doorn's heuristic suggests the weak bound may be optimal

Reference: [ErGr80, p.42]

Tags: number-theory, unit-fractions, diophantine-approximation
-/

import Mathlib

open Finset Filter BigOperators

namespace Erdos317

/- ## Part I: Basic Definitions -/

/-- A sign function δ : Fin n → ℤ with values in {-1, 0, 1} -/
def IsSignFunction (n : ℕ) (δ : Fin n → ℤ) : Prop :=
  ∀ k, δ k ∈ ({-1, 0, 1} : Set ℤ)

/-- The signed unit fraction sum ∑_{k=1}^{n} δ_k/k
    (using 0-indexed Fin n, so k-th term is δ(k)/(k+1)) -/
noncomputable def signedUnitFractionSum (n : ℕ) (δ : Fin n → ℤ) : ℚ :=
  ∑ k : Fin n, (δ k : ℚ) / ((k : ℕ) + 1)

/-- The absolute value of the signed sum as a real number -/
noncomputable def signedSumAbs (n : ℕ) (δ : Fin n → ℤ) : ℝ :=
  |signedUnitFractionSum n δ|

/- ## Part II: The Main Conjecture (Question 1) -/

/-- **Erdős Problem #317 — Question 1 (OPEN)**:
    Is there c > 0 such that for every n ≥ 1, there exists δ with
    0 < |∑ δ_k/k| < c/2^n ? -/
def Question1 : Prop :=
  ∃ c : ℝ, c > 0 ∧ ∀ n : ℕ, n ≥ 1 →
    ∃ δ : Fin n → ℤ, IsSignFunction n δ ∧
      0 < signedSumAbs n δ ∧ signedSumAbs n δ < c / 2^n

/- ## Part III: The Second Question -/

/-- The LCM of 1, 2, ..., n -/
noncomputable def lcm_1_to_n (n : ℕ) : ℕ :=
  (Finset.range n).lcm (· + 1)

/-- **Erdős Problem #317 — Question 2 (OPEN)**:
    For large n, must |∑ δ_k/k| > 1/lcm(1,...,n) when nonzero? -/
def Question2 : Prop :=
  ∀ᶠ n in atTop, ∀ δ : Fin n → ℤ, IsSignFunction n δ →
    signedUnitFractionSum n δ ≠ 0 →
      |signedUnitFractionSum n δ| > 1 / (lcm_1_to_n n : ℚ)

/- ## Part IV: Known Results — Proved -/

/-- The counterexample sign function: δ = (0, 1, -1, -1) for Fin 4 -/
def counterexampleDelta : Fin 4 → ℤ
  | ⟨0, _⟩ => 0
  | ⟨1, _⟩ => 1
  | ⟨2, _⟩ => -1
  | ⟨3, _⟩ => -1
  | ⟨n + 4, h⟩ => absurd h (by omega)

/-- counterexampleDelta is a valid sign function -/
theorem counterexampleDelta_isSign : IsSignFunction 4 counterexampleDelta := by
  intro k
  fin_cases k <;> simp [counterexampleDelta]

/-- The signed sum of the counterexample equals -1/12 -/
theorem counterexample_sum_eq :
    signedUnitFractionSum 4 counterexampleDelta = -1/12 := by
  simp only [signedUnitFractionSum, Fin.sum_univ_four, counterexampleDelta]
  norm_num

/-- Question 2 fails for small n: δ = (0, 1, -1, -1) gives
    0 + 1/2 - 1/3 - 1/4 = -1/12, and lcm(1,2,3,4) = 12,
    so |sum| = 1/12 = 1/lcm — equality, not strict inequality. -/
theorem counterexample_small_n :
    ∃ δ : Fin 4 → ℤ, IsSignFunction 4 δ ∧
      signedUnitFractionSum 4 δ ≠ 0 ∧
      ¬(|signedUnitFractionSum 4 δ| > 1 / (lcm_1_to_n 4 : ℚ)) := by
  refine ⟨counterexampleDelta, counterexampleDelta_isSign, ?_, ?_⟩
  · rw [counterexample_sum_eq]; norm_num
  · rw [counterexample_sum_eq]
    simp only [lcm_1_to_n]
    native_decide

/-- The "all ones" sign function: δ_k = 1 for all k -/
def allOnesDelta (n : ℕ) : Fin n → ℤ := fun _ => 1

/-- allOnesDelta is a valid sign function -/
theorem allOnesDelta_isSign (n : ℕ) : IsSignFunction n (allOnesDelta n) := by
  intro k; right; right; rfl

/-- For n ≥ 1, the all-ones sum equals the n-th harmonic number, which is positive -/
theorem allOnes_sum_pos (n : ℕ) (hn : n ≥ 1) :
    signedSumAbs n (allOnesDelta n) > 0 := by
  simp only [signedSumAbs]
  have hpos : (0 : ℚ) < signedUnitFractionSum n (allOnesDelta n) := by
    simp only [signedUnitFractionSum, allOnesDelta]
    apply Finset.sum_pos
    · intro i _; simp only [Int.cast_one, one_div]; positivity
    · exact Finset.univ_nonempty_iff.mpr ⟨⟨0, hn⟩⟩
  have : (0 : ℝ) < ↑(signedUnitFractionSum n (allOnesDelta n)) := by exact_mod_cast hpos
  linarith [abs_of_pos this]

/-- For every n ≥ 1, there exists a sign function giving a nonzero signed sum.
    (Trivially: all δ_k = 1 gives the harmonic number H_n > 0.) -/
theorem nonzero_signed_sum_exists :
    ∀ n : ℕ, n ≥ 1 →
      ∃ δ : Fin n → ℤ, IsSignFunction n δ ∧ 0 < signedSumAbs n δ := by
  intro n hn
  exact ⟨allOnesDelta n, allOnesDelta_isSign n, allOnes_sum_pos n hn⟩

/- ## Part V: Weak Inequality -/

/-- Each term δ_k/(k+1) in the signed sum has denominator dividing lcm(1,...,n).
    When the sum is expressed over this common denominator, a nonzero sum
    has numerator with absolute value ≥ 1, giving |sum| ≥ 1/lcm(1,...,n). -/
theorem weak_inequality (n : ℕ) (δ : Fin n → ℤ) (_hδ : IsSignFunction n δ)
    (hne : signedUnitFractionSum n δ ≠ 0) :
    |signedUnitFractionSum n δ| ≥ 1 / (lcm_1_to_n n : ℚ) := by
  set L := lcm_1_to_n n
  set S := signedUnitFractionSum n δ
  -- Trivial if L = 0 (then 1/0 = 0 in ℚ, and |S| ≥ 0)
  by_cases hL : (L : ℚ) = 0
  · simp only [hL, div_zero]; exact abs_nonneg _
  have hLQ_pos : (0 : ℚ) < L := lt_of_le_of_ne (Nat.cast_nonneg L) (Ne.symm hL)
  -- Key: L * S is an integer (since each (k+1) divides L)
  have ⟨m, hm⟩ : ∃ m : ℤ, (L : ℚ) * S = m := by
    simp only [S, signedUnitFractionSum, Finset.mul_sum]
    suffices h : ∀ k : Fin n, ∃ m : ℤ,
        (L : ℚ) * ((δ k : ℚ) / ((k.val : ℚ) + 1)) = m from by
      choose f hf using h
      exact ⟨∑ k, f k, by simp_rw [hf, ← Int.cast_sum]⟩
    intro k
    obtain ⟨c, hc⟩ := Finset.dvd_lcm (f := (· + 1))
      (show k.val ∈ Finset.range n from Finset.mem_range.mpr k.isLt)
    exact ⟨δ k * c, by
      have hkne : ((k.val : ℚ) + 1) ≠ 0 := by positivity
      have hLc : (L : ℚ) = ((k.val : ℚ) + 1) * (c : ℚ) := by exact_mod_cast hc
      rw [hLc]; field_simp; push_cast; ring⟩
  -- S ≠ 0 and L ≠ 0 imply m ≠ 0
  have hm_ne : m ≠ 0 := by
    intro h; apply hne
    have : (L : ℚ) * S = 0 := by simp [hm, h]
    exact (mul_eq_zero.mp this).resolve_left (ne_of_gt hLQ_pos)
  -- Conclude: |S| ≥ 1/L, since |S| * L = |m| ≥ 1
  rw [ge_iff_le, div_le_iff₀ hLQ_pos]
  calc (1 : ℚ) ≤ |(m : ℚ)| := by
          exact_mod_cast (show (1 : ℤ) ≤ |m| by
            rcases le_or_gt 0 m with h | h
            · rw [abs_of_nonneg h]; omega
            · rw [abs_of_neg h]; omega)
    _ = |(L : ℚ) * S| := by congr 1; exact hm.symm
    _ = |S| * L := by rw [abs_mul, abs_of_pos hLQ_pos, mul_comm]

/- ## Part VI: Summary -/

/-- Erdős Problem #317: OPEN.
    Q1: Can signed unit fraction sums be made exponentially small (< c/2^n)?
    Q2: For large n, is 1/lcm(1,...,n) a strict lower bound?
    Known: Weak inequality ≥ 1/lcm holds; strict inequality fails for small n.
    Nonzero signed sums exist for every n ≥ 1 (trivially via harmonic number). -/
theorem erdos_317_summary :
    (∀ n δ, IsSignFunction n δ → signedUnitFractionSum n δ ≠ 0 →
      |signedUnitFractionSum n δ| ≥ 1 / (lcm_1_to_n n : ℚ)) ∧
    (∃ δ : Fin 4 → ℤ, IsSignFunction 4 δ ∧
      signedUnitFractionSum 4 δ ≠ 0 ∧
      ¬(|signedUnitFractionSum 4 δ| > 1 / (lcm_1_to_n 4 : ℚ))) ∧
    (∀ n : ℕ, n ≥ 1 →
      ∃ δ : Fin n → ℤ, IsSignFunction n δ ∧ 0 < signedSumAbs n δ) := by
  exact ⟨weak_inequality, counterexample_small_n, nonzero_signed_sum_exists⟩

end Erdos317
