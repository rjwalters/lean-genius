/-
Erdős Problem #480: Sequence Approximation in the Unit Interval

**Question**: Let x₁, x₂, ... ∈ [0, 1] be an infinite sequence. Is it true that
there are infinitely many pairs (m, n) with |x_{m+n} - x_m| ≤ 1/(√5 · n)?

**Status**: SOLVED by Chung and Graham (1984)

**History**: This was originally a conjecture of Donald Newman. Chung and Graham
proved not only that the answer is YES, but found the optimal constant:

  c = 1 + Σ_{k≥1} 1/F_{2k} ≈ 2.535...

where F_m is the m-th Fibonacci number. The bound 1/c ≈ 0.394 is better than
1/√5 ≈ 0.447, and this constant is best possible.

**Key Insight**: The appearance of Fibonacci numbers is not coincidental - they
arise from the continued fraction expansion of 1/φ where φ = (1+√5)/2 is the
golden ratio. The golden ratio has the "worst" approximation properties.

References:
- https://erdosproblems.com/480
- [ChGr84] Chung & Graham, "On irregularities of distribution" (1984), 181-222
-/

import Mathlib

namespace Erdos480

open Set Filter Real

/-!
## The Main Statement

For any sequence in [0,1], infinitely many pairs (m, n) satisfy the
approximation inequality |x_{m+n} - x_m| ≤ 1/(√5 · n).
-/

/-- A sequence is in the unit interval if all its values lie in [0, 1]. -/
def IsUnitIntervalSeq (x : ℕ → ℝ) : Prop :=
  ∀ n, x n ∈ Icc 0 1

/-- The set of good pairs (m, n) where m ≠ 0 and the approximation holds. -/
def GoodPairs (x : ℕ → ℝ) (C : ℝ) : Set (ℕ × ℕ) :=
  {p | p.1 ≠ 0 ∧ p.2 ≠ 0 ∧ |x (p.1 + p.2) - x p.1| ≤ 1 / (C * p.2)}

/-!
## Fibonacci Numbers and the Optimal Constant

The optimal constant involves a sum over even-indexed Fibonacci numbers.
-/

/-- The Chung-Graham constant: c = 1 + Σ_{k≥1} 1/F_{2k} ≈ 2.535... -/
noncomputable def chungGrahamConstant : ℝ :=
  1 + ∑' (k : ℕ+), (1 : ℝ) / Nat.fib (2 * k)

/-- The Chung-Graham constant is approximately 2.535. -/
axiom chungGraham_approx : 2.5 < chungGrahamConstant ∧ chungGrahamConstant < 2.6

/-!
## Newman's Original Conjecture

Newman asked about the bound 1/√5. This is weaker than what Chung-Graham proved.
-/

/--
**Newman's Conjecture (Now Theorem)**: For any unit interval sequence,
there are infinitely many pairs (m, n) with |x_{m+n} - x_m| ≤ 1/(√5 · n).

This was proved by Chung and Graham (1984).
-/
axiom newman_conjecture (x : ℕ → ℝ) (hx : IsUnitIntervalSeq x) :
    (GoodPairs x (Real.sqrt 5)).Infinite

/-!
## The Chung-Graham Theorem

Chung and Graham proved a stronger result with the optimal constant.
-/

/--
**Chung-Graham Theorem (1984)**: The optimal constant C for which
|x_{m+n} - x_m| ≤ 1/(C · n) holds infinitely often is exactly

  c = 1 + Σ_{k≥1} 1/F_{2k} ≈ 2.535...

This is strictly better than √5 ≈ 2.236, and the constant is best possible.
-/
axiom chung_graham_theorem (x : ℕ → ℝ) (hx : IsUnitIntervalSeq x) :
    (GoodPairs x chungGrahamConstant).Infinite

/--
The Chung-Graham constant is optimal: for any ε > 0, there exists a sequence
where |x_{m+n} - x_m| > 1/((c + ε) · n) for all but finitely many pairs.
-/
axiom chung_graham_optimal :
    IsGreatest {C : ℝ | C > 0 ∧ ∀ x : ℕ → ℝ, IsUnitIntervalSeq x →
      (GoodPairs x C).Infinite} chungGrahamConstant

/-!
## Connection to the Golden Ratio

The golden ratio φ = (1 + √5)/2 appears because:
1. Its continued fraction [1; 1, 1, 1, ...] is the "simplest"
2. It is the "worst" approximable irrational
3. Fibonacci numbers F_n/F_{n-1} → φ are the best rational approximations to φ
-/

/-- The golden ratio: φ = (1 + √5)/2 ≈ 1.618... -/
noncomputable def goldenRatio : ℝ := (1 + Real.sqrt 5) / 2

/-- φ² = φ + 1 (defining property). -/
theorem goldenRatio_sq : goldenRatio ^ 2 = goldenRatio + 1 := by
  unfold goldenRatio
  ring_nf
  rw [sq_sqrt (by norm_num : (5 : ℝ) ≥ 0)]
  ring

/-- φ · (φ - 1) = 1 (equivalently, φ - 1 = 1/φ). -/
theorem goldenRatio_reciprocal : goldenRatio * (goldenRatio - 1) = 1 := by
  have h := goldenRatio_sq
  linarith [h]

/-- The relationship √5 = 2φ - 1. -/
theorem sqrt5_eq_goldenRatio : Real.sqrt 5 = 2 * goldenRatio - 1 := by
  unfold goldenRatio
  ring

/-!
## Fibonacci Connection

The Fibonacci sequence appears through Binet's formula:
F_n = (φⁿ - ψⁿ)/√5 where ψ = (1 - √5)/2.
-/

/-- Binet's constant ψ = (1 - √5)/2 (conjugate of φ). -/
noncomputable def binetPsi : ℝ := (1 - Real.sqrt 5) / 2

/-- φ + ψ = 1. -/
theorem golden_conjugate_sum : goldenRatio + binetPsi = 1 := by
  unfold goldenRatio binetPsi
  ring

/-- φ · ψ = -1. -/
theorem golden_conjugate_prod : goldenRatio * binetPsi = -1 := by
  unfold goldenRatio binetPsi
  ring_nf
  rw [sq_sqrt (by norm_num : (5 : ℝ) ≥ 0)]
  ring

/-!
## Why √5?

Newman's original bound 1/√5 comes from:
- The golden ratio φ satisfies φ² = φ + 1
- For the "worst" sequence (related to Sturmian sequences), √5 appears naturally
- The Chung-Graham improvement replaces √5 with the larger constant c ≈ 2.535
-/

/-- √5 < c, so the Chung-Graham bound is stronger. -/
theorem sqrt5_lt_chungGraham : Real.sqrt 5 < chungGrahamConstant := by
  have h1 : Real.sqrt 5 < 2.3 := by
    have h : (5 : ℝ) < 2.3 ^ 2 := by norm_num
    calc Real.sqrt 5 < Real.sqrt (2.3 ^ 2) := Real.sqrt_lt_sqrt (by norm_num) h
      _ = 2.3 := Real.sqrt_sq (by norm_num)
  have h2 := chungGraham_approx.1
  linarith

/-!
## Verified Examples

We verify some basic properties about unit interval sequences.
-/

/-- The constant sequence x_n = c is in [0,1] when 0 ≤ c ≤ 1. -/
theorem constant_seq_unit_interval {c : ℝ} (hc : c ∈ Icc 0 1) :
    IsUnitIntervalSeq (fun _ => c) := fun _ => hc

/-- For constant sequences, |x_{m+n} - x_m| = 0 always. -/
theorem constant_seq_diff_zero {c : ℝ} (m n : ℕ) :
    |(fun _ : ℕ => c) (m + n) - (fun _ : ℕ => c) m| = 0 := by simp

/-- The sequence x_n = n / (n + 1) stays in [0, 1). -/
theorem harmonic_seq_unit_interval :
    IsUnitIntervalSeq (fun n => (n : ℝ) / (n + 1)) := by
  intro n
  constructor
  · positivity
  · have hpos : (0 : ℝ) < n + 1 := by linarith
    rw [div_le_one hpos]
    linarith

/-!
## Summary

Erdős Problem #480 asks about approximation properties of sequences in [0,1].

**What we know**:
1. Newman conjectured: infinitely many (m,n) with |x_{m+n} - x_m| ≤ 1/(√5·n)
2. Chung-Graham (1984): Proved this with optimal constant c ≈ 2.535
3. The constant c = 1 + Σ 1/F_{2k} involves Fibonacci numbers
4. This is connected to the golden ratio being "worst approximable"

**Key insight**: The golden ratio's continued fraction [1;1,1,1,...] makes it
the hardest irrational to approximate by rationals, which is why Fibonacci
numbers and √5 appear in this seemingly unrelated distribution problem.
-/

/-- The main result: Newman's conjecture holds with the optimal constant. -/
theorem erdos_480_summary (x : ℕ → ℝ) (hx : IsUnitIntervalSeq x) :
    (GoodPairs x (Real.sqrt 5)).Infinite ∧
    (GoodPairs x chungGrahamConstant).Infinite :=
  ⟨newman_conjecture x hx, chung_graham_theorem x hx⟩

end Erdos480
