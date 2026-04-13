/-
# Taylor Series Remainder Bounds — Axiom Elimination (OQ-01)

**Open Question (OQ-01)**: Can the two remainder axioms in TaylorSinCosConvergence.lean
be eliminated by bridging sinPartialSum/cosPartialSum to Mathlib's taylorWithinEval?

**Answer**: Yes. This file replaces both axioms with actual proofs:

  `sin_taylor_remainder_bound'`: ‖sin(x) - sinPartialSum n x‖ ≤ |x|^(n+1) / n!
  `cos_taylor_remainder_bound'`: ‖cos(x) - cosPartialSum n x‖ ≤ |x|^(n+1) / n!

**Strategy**:
- Establish parity of iterated derivatives: sin^(k)(0) = 0 for even k; cos^(k)(0) = 0 for odd k
- Prove symmetry: sinPartialSum n (-x) = -sinPartialSum n x (odd function)
                   cosPartialSum n (-x) = cosPartialSum n x (even function)
- Connect: sinPartialSum n x = taylorWithinEval sin n (Icc 0 x) 0 x for x > 0
- Apply: Mathlib's `taylor_mean_remainder_bound` with derivative bound M = 1
- Case split: handle x > 0 directly; x < 0 via symmetry; x = 0 trivially

**Key Mathlib tools**:
- `taylor_mean_remainder_bound`: ‖f x - taylorWithinEval f n (Icc a b) a x‖ ≤ C * (x-a)^(n+1)/n!
- `taylor_within_apply`: unfolds taylorWithinEval as a sum
- `uniqueDiffOn_Icc`: UniqueDiffOn ℝ (Icc a b) for a < b

**Axiom count**: 0 — this file has no axioms and no sorry's.
-/

import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic
import Proofs.TaylorSinCosConvergence

open Set Filter Topology Finset Real
open scoped Nat
open TaylorSinCosConvergence

namespace TaylorSinCosConvergenceOQ01

/-! ## Section I: Parity of iterated derivatives at zero

Every even-order iterated derivative of sin vanishes at 0 (since sin^(k)(0) cycles
through {0, 1, 0, -1} with period 4, giving 0 at positions 0 and 2).
Every odd-order iterated derivative of cos vanishes at 0 (cos^(k)(0) cycles
through {1, 0, -1, 0} with period 4, giving 0 at positions 1 and 3). -/

/-- For even k, iteratedDeriv k sin 0 = 0.
Proof: period-4 reduction then case analysis on k % 4 ∈ {0, 2}. -/
theorem iteratedDeriv_sin_zero_even (k : ℕ) (hk : Even k) :
    iteratedDeriv k Real.sin 0 = 0 := by
  obtain ⟨m, rfl⟩ := hk  -- k = m + m
  have hperiod : iteratedDeriv (m + m) Real.sin = iteratedDeriv ((m + m) % 4) Real.sin := by
    have := Nat.div_add_mod (m + m) 4
    conv_lhs => rw [← this]
    induction ((m + m) / 4) with
    | zero => simp
    | succ p ih =>
      rw [show 4 * (p + 1) + (m + m) % 4 = 4 * p + (m + m) % 4 + 4 from by ring,
          iteratedDeriv_sin_add_four, ih]
  rw [show iteratedDeriv (m + m) Real.sin 0 = iteratedDeriv ((m + m) % 4) Real.sin 0 from
      congr_fun hperiod 0]
  have h : (m + m) % 4 = 0 ∨ (m + m) % 4 = 2 := by omega
  rcases h with h0 | h2
  · rw [h0, iteratedDeriv_sin_zero]; exact Real.sin_zero
  · rw [h2]; exact congr_fun iteratedDeriv_sin_two 0 |>.trans (by simp [Real.sin_zero])

/-- For odd k, iteratedDeriv k cos 0 = 0.
Proof: period-4 reduction then case analysis on k % 4 ∈ {1, 3}. -/
theorem iteratedDeriv_cos_zero_odd (k : ℕ) (hk : Odd k) :
    iteratedDeriv k Real.cos 0 = 0 := by
  obtain ⟨m, rfl⟩ := hk  -- k = 2 * m + 1
  have hperiod : iteratedDeriv (2 * m + 1) Real.cos =
      iteratedDeriv ((2 * m + 1) % 4) Real.cos := by
    have := Nat.div_add_mod (2 * m + 1) 4
    conv_lhs => rw [← this]
    induction ((2 * m + 1) / 4) with
    | zero => simp
    | succ p ih =>
      rw [show 4 * (p + 1) + (2 * m + 1) % 4 = 4 * p + (2 * m + 1) % 4 + 4 from by ring,
          iteratedDeriv_cos_add_four, ih]
  rw [show iteratedDeriv (2 * m + 1) Real.cos 0 = iteratedDeriv ((2 * m + 1) % 4) Real.cos 0 from
      congr_fun hperiod 0]
  have h : (2 * m + 1) % 4 = 1 ∨ (2 * m + 1) % 4 = 3 := by omega
  rcases h with h1 | h3
  · rw [h1]; exact congr_fun iteratedDeriv_cos_one 0 |>.trans (by simp [Real.sin_zero])
  · rw [h3]; exact congr_fun iteratedDeriv_cos_three 0 |>.trans Real.sin_zero

/-! ## Section II: Symmetry of partial sums

sinPartialSum is an odd function; cosPartialSum is an even function.
These follow directly from the parity of the respective derivatives at 0. -/

/-- sinPartialSum n (-x) = -sinPartialSum n x (sin is odd). -/
theorem sinPartialSum_neg (n : ℕ) (x : ℝ) :
    sinPartialSum n (-x) = -sinPartialSum n x := by
  simp only [sinPartialSum, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl; intro k _
  rcases Nat.even_or_odd k with ⟨m, rfl⟩ | ⟨m, rfl⟩
  · -- k = m + m: term vanishes because iteratedDeriv (m+m) sin 0 = 0
    have h := iteratedDeriv_sin_zero_even (m + m) ⟨m, rfl⟩
    simp [h]
  · -- k = 2*m+1: use (-x)^(2m+1) = -(x^(2m+1))
    have hodd : (-x) ^ (2 * m + 1) = -x ^ (2 * m + 1) := Odd.neg_pow ⟨m, rfl⟩ x
    simp only [hodd]; ring

/-- cosPartialSum n (-x) = cosPartialSum n x (cos is even). -/
theorem cosPartialSum_neg (n : ℕ) (x : ℝ) :
    cosPartialSum n (-x) = cosPartialSum n x := by
  simp only [cosPartialSum]
  apply Finset.sum_congr rfl; intro k _
  rcases Nat.even_or_odd k with ⟨m, rfl⟩ | ⟨m, rfl⟩
  · -- k = m+m: (-x)^(m+m) = x^(m+m) (even power)
    have heven : (-x) ^ (m + m) = x ^ (m + m) := Even.neg_pow ⟨m, rfl⟩ x
    simp only [heven]
  · -- k = 2*m+1: term vanishes because iteratedDeriv (2m+1) cos 0 = 0
    have h := iteratedDeriv_cos_zero_odd (2 * m + 1) ⟨m, rfl⟩
    simp [h]

/-- cosPartialSum n 0 = 1.
The k=0 term contributes cos(0) = 1; all other terms vanish since 0^k = 0. -/
theorem cosPartialSum_at_zero' (n : ℕ) : cosPartialSum n 0 = 1 := by
  simp only [cosPartialSum]
  rw [Finset.sum_eq_single 0
    (fun k _ hk => by simp [zero_pow hk])
    (fun h => absurd (Finset.mem_range.mpr n.succ_pos) h)]
  simp [iteratedDeriv_cos_zero, Real.cos_zero]

/-! ## Section III: Connecting partial sums to taylorWithinEval

sinPartialSum n x = taylorWithinEval sin n (Icc 0 x) 0 x when x > 0,
because the iteratedDerivWithin terms on Icc 0 x agree with the global
iteratedDeriv terms (by contDiff_sin and uniqueDiffOn_Icc). -/

/-- sinPartialSum n x = taylorWithinEval Real.sin n (Icc 0 x) 0 x for x > 0. -/
theorem sinPartialSum_eq_taylorWithinEval (n : ℕ) (x : ℝ) (hx : 0 < x) :
    sinPartialSum n x = taylorWithinEval Real.sin n (Icc 0 x) 0 x := by
  rw [taylor_within_apply]
  simp only [sinPartialSum, sub_zero]
  apply Finset.sum_congr rfl; intro k _
  have hd : iteratedDerivWithin k Real.sin (Icc 0 x) 0 = iteratedDeriv k Real.sin 0 :=
    iteratedDerivWithin_sin_eq (uniqueDiffOn_Icc hx) (Set.mem_Icc.mpr ⟨le_refl 0, hx.le⟩)
  rw [hd, smul_eq_mul]; ring

/-- cosPartialSum n x = taylorWithinEval Real.cos n (Icc 0 x) 0 x for x > 0. -/
theorem cosPartialSum_eq_taylorWithinEval (n : ℕ) (x : ℝ) (hx : 0 < x) :
    cosPartialSum n x = taylorWithinEval Real.cos n (Icc 0 x) 0 x := by
  rw [taylor_within_apply]
  simp only [cosPartialSum, sub_zero]
  apply Finset.sum_congr rfl; intro k _
  have hd : iteratedDerivWithin k Real.cos (Icc 0 x) 0 = iteratedDeriv k Real.cos 0 :=
    iteratedDerivWithin_cos_eq (uniqueDiffOn_Icc hx) (Set.mem_Icc.mpr ⟨le_refl 0, hx.le⟩)
  rw [hd, smul_eq_mul]; ring

/-! ## Section IV: Remainder bounds

Main results: both axioms from TaylorSinCosConvergence.lean are proved here.
The proof applies taylor_mean_remainder_bound (which gives C*(x-a)^(n+1)/n!
with C = sup |f^(n+1)|) using the derivative bound M = 1 for sin and cos.

For x < 0 we reduce to x > 0 via the odd/even symmetry proved above. -/

/-- Auxiliary: sin remainder bound for x > 0. -/
private theorem sin_remainder_pos (n : ℕ) (x : ℝ) (hx : 0 < x) :
    ‖Real.sin x - sinPartialSum n x‖ ≤ x ^ (n + 1) / (n ! : ℝ) := by
  rw [sinPartialSum_eq_taylorWithinEval n x hx]
  have hle := hx.le
  calc ‖Real.sin x - taylorWithinEval Real.sin n (Icc 0 x) 0 x‖
      ≤ 1 * (x - 0) ^ (n + 1) / n ! :=
        taylor_mean_remainder_bound hle
          (Real.contDiff_sin.contDiffOn.of_le le_top)
          (Set.mem_Icc.mpr ⟨hle, le_refl x⟩)
          (fun y hy => by
            rw [iteratedDerivWithin_sin_eq (uniqueDiffOn_Icc hx) hy]
            exact norm_iteratedDeriv_sin_le _ _)
    _ = x ^ (n + 1) / n ! := by ring

/-- **Sin Taylor Remainder Bound** (eliminates axiom sin_taylor_remainder_bound):
    ‖sin(x) - sinPartialSum n x‖ ≤ |x|^(n+1) / n!

Proof: case split on sign of x. For x > 0, apply taylor_mean_remainder_bound.
For x = 0, both sides are 0. For x < 0, use the odd symmetry of sinPartialSum. -/
theorem sin_taylor_remainder_bound' (n : ℕ) (x : ℝ) :
    ‖Real.sin x - sinPartialSum n x‖ ≤ |x| ^ (n + 1) / (n ! : ℝ) := by
  rcases lt_trichotomy x 0 with hx | rfl | hx
  · -- Case x < 0: reduce to -x > 0 via sin oddness
    have hpos : 0 < -x := neg_pos.mpr hx
    have heq : ‖Real.sin x - sinPartialSum n x‖ = ‖Real.sin (-x) - sinPartialSum n (-x)‖ := by
      have h : Real.sin x - sinPartialSum n x = -(Real.sin (-x) - sinPartialSum n (-x)) := by
        rw [Real.sin_neg, sinPartialSum_neg]; ring
      rw [h, norm_neg]
    rw [heq, ← abs_neg x, abs_of_pos hpos]
    exact sin_remainder_pos n (-x) hpos
  · -- Case x = 0: both sides are 0
    simp [Real.sin_zero, sinPartialSum_at_zero]
  · -- Case x > 0: direct application
    rw [abs_of_pos hx]
    exact sin_remainder_pos n x hx

/-- Auxiliary: cos remainder bound for x > 0. -/
private theorem cos_remainder_pos (n : ℕ) (x : ℝ) (hx : 0 < x) :
    ‖Real.cos x - cosPartialSum n x‖ ≤ x ^ (n + 1) / (n ! : ℝ) := by
  rw [cosPartialSum_eq_taylorWithinEval n x hx]
  have hle := hx.le
  calc ‖Real.cos x - taylorWithinEval Real.cos n (Icc 0 x) 0 x‖
      ≤ 1 * (x - 0) ^ (n + 1) / n ! :=
        taylor_mean_remainder_bound hle
          (Real.contDiff_cos.contDiffOn.of_le le_top)
          (Set.mem_Icc.mpr ⟨hle, le_refl x⟩)
          (fun y hy => by
            rw [iteratedDerivWithin_cos_eq (uniqueDiffOn_Icc hx) hy]
            exact norm_iteratedDeriv_cos_le _ _)
    _ = x ^ (n + 1) / n ! := by ring

/-- **Cos Taylor Remainder Bound** (eliminates axiom cos_taylor_remainder_bound):
    ‖cos(x) - cosPartialSum n x‖ ≤ |x|^(n+1) / n!

Proof: case split on sign of x. For x > 0, apply taylor_mean_remainder_bound.
For x = 0, both sides are 0. For x < 0, use the even symmetry of cosPartialSum. -/
theorem cos_taylor_remainder_bound' (n : ℕ) (x : ℝ) :
    ‖Real.cos x - cosPartialSum n x‖ ≤ |x| ^ (n + 1) / (n ! : ℝ) := by
  rcases lt_trichotomy x 0 with hx | rfl | hx
  · -- Case x < 0: reduce to -x > 0 via cos evenness
    have hpos : 0 < -x := neg_pos.mpr hx
    have heq : ‖Real.cos x - cosPartialSum n x‖ = ‖Real.cos (-x) - cosPartialSum n (-x)‖ := by
      rw [Real.cos_neg, cosPartialSum_neg]
    rw [heq, ← abs_neg x, abs_of_pos hpos]
    exact cos_remainder_pos n (-x) hpos
  · -- Case x = 0: both sides are 0
    simp [Real.cos_zero, cosPartialSum_at_zero']
  · -- Case x > 0: direct application
    rw [abs_of_pos hx]
    exact cos_remainder_pos n x hx

/-! ## Verification -/

#check sin_taylor_remainder_bound'
#check cos_taylor_remainder_bound'

end TaylorSinCosConvergenceOQ01
