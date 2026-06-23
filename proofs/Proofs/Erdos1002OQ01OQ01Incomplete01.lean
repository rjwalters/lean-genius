import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-
# Erdős #1002 — a priori control of the weighted fractional sum and the zero mean of `deviation`
# (erdos-1002-oq-01-oq-01-incomplete-01)

## The Open Question

**Erdős Problem #1002** (OPEN). For `0 < α < 1` and the *deviation from the
midpoint* `deviation x = 1/2 - {x}`, set
  `f(α, n) = (1/log n) · Σ_{k=1}^{n} deviation(α·k)`.
Does `f(α, n)` have an asymptotic distribution function? The two-parameter
variant has a Cauchy limit (Kesten 1960); the one-parameter case is open.

The companion file `Erdos1002OQ01OQ01.lean` builds toward Weyl-type equidistribution
for the *irrational* case and still carries one analytic `sorry` (the
Stone–Weierstrass uniform approximation by trigonometric polynomials). This file
does **not** depend on that `sorry`: it establishes the unconditional, elementary
backbone of the problem — the pointwise size of `deviation`, the resulting a
priori bound on the weighted sum, and the **zero mean** of `deviation` over a
period, which is the exact analytic reason the average `f(α, n)` does not run off
to infinity.

## Result

Building only on the sorry-free definitions in `Erdos1002Problem.lean`:

1. `neg_half_lt_deviation` / `deviation_le_half` / `abs_deviation_le_half` —
   the sharp pointwise envelope `-1/2 < deviation x ≤ 1/2`, hence
   `|deviation x| ≤ 1/2`. Immediate from `0 ≤ {x} < 1`.

2. `abs_innerSum_le` — the a priori bound `|S(α, n)| ≤ n/2` on the inner sum,
   by the triangle inequality over the pointwise envelope.

3. `abs_f_le` — the normalized a priori bound `|f(α, n)| ≤ (n/2)/log n` for
   `n ≥ 2`. This is the trivial control: the open question is precisely whether
   the true growth is the far smaller `O(1)`-distributed scale, but even the
   crude bound shows `f` is well defined and finite.

4. `integral_deviation_eq_zero` — **the zero mean**: `∫₀¹ deviation x dx = 0`.
   On `[0,1)` we have `{x} = x`, so `deviation x = 1/2 - x` and its integral is
   `1/2 - 1/2 = 0`. This vanishing mean is the structural fact underlying every
   equidistribution statement for `deviation`: the Cesàro/Weyl averages converge
   to this mean, namely `0`, in the irrational case.

## Summary: 0 sorries, 0 axioms, no `native_decide`.
Self-contained: the base `Erdos1002Problem.lean` currently fails to build on the
pinned Mathlib (it imports removed modules `Mathlib.Topology.Instances.Real.Basic`
and `Mathlib.Data.Int.Floor`), so the three definitions are re-declared here
verbatim. The analytic `sorry` in `Erdos1002OQ01OQ01.lean` is neither imported nor
used.
-/

set_option linter.unusedVariables false

open MeasureTheory

namespace Erdos1002OQ01OQ01Incomplete01

-- ============================================================
-- PART 0: The Erdős #1002 definitions (re-declared; see note above)
-- ============================================================

/-- The deviation from the midpoint: `1/2 - {x}`. -/
noncomputable def deviation (x : ℝ) : ℝ :=
  1 / 2 - Int.fract x

/-- The inner sum `S(α, n) = Σ_{k=1}^{n} deviation(α·k)`. -/
noncomputable def innerSum (α : ℝ) (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range n, deviation (α * (k + 1))

/-- The normalized function `f(α, n) = S(α, n) / log n` (and `0` for `n ≤ 1`). -/
noncomputable def f (α : ℝ) (n : ℕ) : ℝ :=
  if n ≤ 1 then 0 else innerSum α n / Real.log n

-- ============================================================
-- PART 1: The pointwise envelope of `deviation`
-- ============================================================

/-- `deviation x > -1/2`, since `{x} < 1`. -/
theorem neg_half_lt_deviation (x : ℝ) : -(1 / 2) < deviation x := by
  unfold deviation
  have := Int.fract_lt_one x
  linarith

/-- `deviation x ≤ 1/2`, since `0 ≤ {x}`. -/
theorem deviation_le_half (x : ℝ) : deviation x ≤ 1 / 2 := by
  unfold deviation
  have := Int.fract_nonneg x
  linarith

/-- The sharp pointwise envelope `|deviation x| ≤ 1/2`. -/
theorem abs_deviation_le_half (x : ℝ) : |deviation x| ≤ 1 / 2 := by
  rw [abs_le]
  exact ⟨(neg_half_lt_deviation x).le, deviation_le_half x⟩

-- ============================================================
-- PART 2: A priori control of the weighted sum
-- ============================================================

/-- **A priori bound on the inner sum** `|S(α, n)| ≤ n/2`, from the triangle
    inequality over the pointwise envelope `|deviation| ≤ 1/2`. -/
theorem abs_innerSum_le (α : ℝ) (n : ℕ) : |innerSum α n| ≤ n / 2 := by
  unfold innerSum
  calc |∑ k ∈ Finset.range n, deviation (α * (k + 1))|
      ≤ ∑ k ∈ Finset.range n, |deviation (α * (k + 1))| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ Finset.range n, (1 / 2 : ℝ) :=
        Finset.sum_le_sum (fun k _ => abs_deviation_le_half _)
    _ = n / 2 := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring

/-- **A priori bound on the normalized sum** `|f(α, n)| ≤ (n/2)/log n` for
    `n ≥ 2`. The crude control showing `f` is finite; the open problem asks for
    the far finer distributional behaviour. -/
theorem abs_f_le (α : ℝ) (n : ℕ) (hn : 2 ≤ n) :
    |f α n| ≤ (n / 2) / Real.log n := by
  have hn1 : (1 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hlog : 0 < Real.log n := Real.log_pos hn1
  unfold f
  rw [if_neg (by omega : ¬ n ≤ 1), abs_div, abs_of_pos hlog]
  gcongr
  exact abs_innerSum_le α n

-- ============================================================
-- PART 3: The zero mean of `deviation`
-- ============================================================

/-- **The zero mean of `deviation`.** `∫₀¹ deviation x dx = 0`. On `[0,1)` the
    fractional part is the identity, so `deviation x = 1/2 - x`, whose integral
    over `[0,1]` is `1/2 - 1/2 = 0`. This vanishing mean is the structural reason
    the equidistribution averages of `deviation` converge to `0`. -/
theorem integral_deviation_eq_zero : ∫ x in (0:ℝ)..1, deviation x = 0 := by
  have hne1 : ∀ᵐ x : ℝ, x ≠ 1 := by
    rw [ae_iff]
    simp only [ne_eq, not_not, Set.setOf_eq_eq_singleton, measure_singleton]
  have hcongr : ∫ x in (0:ℝ)..1, deviation x = ∫ x in (0:ℝ)..1, (1 / 2 - x) := by
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [hne1] with x hx hmem
    rw [Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1)] at hmem
    show deviation x = 1 / 2 - x
    unfold deviation
    rw [Int.fract_eq_self.mpr ⟨hmem.1.le, lt_of_le_of_ne hmem.2 hx⟩]
  rw [hcongr,
    show (∫ x in (0:ℝ)..1, (1 / 2 - x))
        = (∫ x in (0:ℝ)..1, (1 / 2 : ℝ)) - ∫ x in (0:ℝ)..1, x from
      intervalIntegral.integral_sub intervalIntegrable_const
        ((by fun_prop : Continuous fun x : ℝ => x).intervalIntegrable 0 1),
    integral_id, intervalIntegral.integral_const]
  norm_num

/-
## Significance

Erdős #1002 asks whether the normalized weighted fractional sum `f(α, n)` has an
asymptotic distribution function — open for the one-parameter case, despite the
Cauchy limit known for the two-parameter variant (Kesten 1960). The companion
equidistribution file still carries one analytic `sorry` (Stone–Weierstrass).

This file isolates the unconditional, elementary backbone that needs no such
input. The pointwise envelope `|deviation x| ≤ 1/2` is sharp and immediate, and
it propagates to the a priori bounds `|S(α, n)| ≤ n/2` and
`|f(α, n)| ≤ (n/2)/log n`, certifying that `f` is finite and well behaved — the
floor below which the open distributional question lives. Most importantly, the
**zero mean** `∫₀¹ deviation = 0` is proved outright: it is the exact analytic
fact every Weyl/Cesàro equidistribution statement for `deviation` converges to,
and it requires no approximation theory at all. The remaining open content is the
fine distributional behaviour around that mean, not its value.
-/

end Erdos1002OQ01OQ01Incomplete01
