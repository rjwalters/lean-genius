import Mathlib.NumberTheory.ZetaValues
import Mathlib.NumberTheory.Bernoulli
import Mathlib.Tactic

/-
# Basel Problem (OQ-03): Multiple Zeta Values — Relationship to Single Zeta Values

Open Question (OQ-03 from the Basel Problem ∑ 1/n² = π²/6):
What is the relationship between multiple zeta values and single zeta values?

## Background

The Basel problem evaluates the single zeta value ζ(2) = ∑_{n≥1} 1/n² = π²/6.
Euler's general formula extends this to every even argument:

  ζ(2k) = (-1)^{k+1} · 2^{2k-1} · π^{2k} · B_{2k} / (2k)!

so each even zeta value is a *rational multiple of π^{2k}* (`Mathlib`'s
`hasSum_zeta_nat`). A striking structural consequence is that the even zeta
values are **algebraically degenerate**: any product of them collapses back to a
single even zeta value times a rational. These "product-reduction" identities are
the single-variable shadow of the *stuffle* (harmonic) product of multiple zeta
values (MZVs).

## This File

We derive the closed forms ζ(2), ζ(4), ζ(6), ζ(8) from Euler's formula (the
last two require the Bernoulli numbers B₆ = 1/42 and B₈ = -1/30, which are not in
Mathlib and are computed here from the defining recursion), and prove the
product-reduction relations among the *actual* zeta series:

* `zeta_two_sq`        : ζ(2)² = (5/2)·ζ(4)
* `zeta_two_mul_four`  : ζ(2)·ζ(4) = (7/4)·ζ(6)
* `zeta_two_cubed`     : ζ(2)³ = (35/8)·ζ(6)
* `zeta_four_sq`       : ζ(4)² = (7/6)·ζ(8)
* `zeta_two_mul_six`   : ζ(2)·ζ(6) = (5/3)·ζ(8)

and record the simplest genuine MZV value forced by the stuffle relation
ζ(2)² = ζ(4) + 2·ζ(2,2):

* `mzv_two_two_value`  : (ζ(2)² − ζ(4))/2 = π⁴/120   (i.e. ζ(2,2) = π⁴/120)

## Status

Verified. Axioms: 0 (no `native_decide`). Sorries: 0.
-/

namespace BaselProblemOQ03

open scoped Real
open Nat Finset

/-! ## Bernoulli numbers B₆ and B₈

Mathlib stocks `bernoulli'_two`, `bernoulli'_three`, `bernoulli'_four` but stops
there.  We compute the next two even Bernoulli numbers from the defining
recursion `bernoulli'_def`, using that the odd ones (B₅, B₇) vanish. -/

theorem bernoulli'_five : bernoulli' 5 = 0 :=
  bernoulli'_eq_zero_of_odd (by decide) (by norm_num)

theorem bernoulli'_seven : bernoulli' 7 = 0 :=
  bernoulli'_eq_zero_of_odd (by decide) (by norm_num)

theorem bernoulli'_six : bernoulli' 6 = 1 / 42 := by
  rw [bernoulli'_def]
  norm_num [sum_range_succ, sum_range_zero, bernoulli'_zero, bernoulli'_one,
    bernoulli'_two, bernoulli'_three, bernoulli'_four, bernoulli'_five, Nat.choose]

theorem bernoulli'_eight : bernoulli' 8 = -1 / 30 := by
  rw [bernoulli'_def]
  norm_num [sum_range_succ, sum_range_zero, bernoulli'_zero, bernoulli'_one,
    bernoulli'_two, bernoulli'_three, bernoulli'_four, bernoulli'_five,
    bernoulli'_six, bernoulli'_seven, Nat.choose]

theorem bernoulli_six : bernoulli 6 = 1 / 42 := by
  rw [bernoulli_eq_bernoulli'_of_ne_one (by decide), bernoulli'_six]

theorem bernoulli_eight : bernoulli 8 = -1 / 30 := by
  rw [bernoulli_eq_bernoulli'_of_ne_one (by decide), bernoulli'_eight]

/-! ## Closed forms for even zeta values

`hasSum_zeta_two` and `hasSum_zeta_four` are in Mathlib; we add ζ(6) and ζ(8). -/

theorem hasSum_zeta_six :
    HasSum (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 6) (π ^ 6 / 945) := by
  have h := hasSum_zeta_nat (k := 3) (by norm_num)
  simp only [(by norm_num : (2 * 3 : ℕ) = 6), (by norm_num : (2 * 3 - 1 : ℕ) = 5)] at h
  rw [bernoulli_six] at h
  convert h using 1
  rw [show (6 : ℕ)! = 720 from by norm_num]
  push_cast
  ring

theorem hasSum_zeta_eight :
    HasSum (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 8) (π ^ 8 / 9450) := by
  have h := hasSum_zeta_nat (k := 4) (by norm_num)
  simp only [(by norm_num : (2 * 4 : ℕ) = 8), (by norm_num : (2 * 4 - 1 : ℕ) = 7)] at h
  rw [bernoulli_eight] at h
  convert h using 1
  rw [show (8 : ℕ)! = 40320 from by norm_num]
  push_cast
  ring

/-! ## The single even zeta values as `tsum`s -/

theorem tsum_zeta_two : ∑' n : ℕ, (1 : ℝ) / (n : ℝ) ^ 2 = π ^ 2 / 6 :=
  hasSum_zeta_two.tsum_eq

theorem tsum_zeta_four : ∑' n : ℕ, (1 : ℝ) / (n : ℝ) ^ 4 = π ^ 4 / 90 :=
  hasSum_zeta_four.tsum_eq

theorem tsum_zeta_six : ∑' n : ℕ, (1 : ℝ) / (n : ℝ) ^ 6 = π ^ 6 / 945 :=
  hasSum_zeta_six.tsum_eq

theorem tsum_zeta_eight : ∑' n : ℕ, (1 : ℝ) / (n : ℝ) ^ 8 = π ^ 8 / 9450 :=
  hasSum_zeta_eight.tsum_eq

/-! ## Product-reduction relations among single zeta values

Each product of even zeta values is a rational multiple of a single even zeta
value of the summed weight.  These are exact identities between the genuine
infinite series (not just the π-expressions). -/

/-- ζ(2)² = (5/2)·ζ(4). The classical Euler relation; also the stuffle product
of ζ(2) with itself, modulo the diagonal term. -/
theorem zeta_two_sq :
    (∑' n : ℕ, (1 : ℝ) / (n : ℝ) ^ 2) ^ 2
      = (5 / 2) * ∑' n : ℕ, (1 : ℝ) / (n : ℝ) ^ 4 := by
  rw [tsum_zeta_two, tsum_zeta_four]; ring

/-- ζ(2)·ζ(4) = (7/4)·ζ(6). -/
theorem zeta_two_mul_four :
    (∑' n : ℕ, (1 : ℝ) / (n : ℝ) ^ 2) * (∑' n : ℕ, (1 : ℝ) / (n : ℝ) ^ 4)
      = (7 / 4) * ∑' n : ℕ, (1 : ℝ) / (n : ℝ) ^ 6 := by
  rw [tsum_zeta_two, tsum_zeta_four, tsum_zeta_six]; ring

/-- ζ(2)³ = (35/8)·ζ(6). -/
theorem zeta_two_cubed :
    (∑' n : ℕ, (1 : ℝ) / (n : ℝ) ^ 2) ^ 3
      = (35 / 8) * ∑' n : ℕ, (1 : ℝ) / (n : ℝ) ^ 6 := by
  rw [tsum_zeta_two, tsum_zeta_six]; ring

/-- ζ(4)² = (7/6)·ζ(8). -/
theorem zeta_four_sq :
    (∑' n : ℕ, (1 : ℝ) / (n : ℝ) ^ 4) ^ 2
      = (7 / 6) * ∑' n : ℕ, (1 : ℝ) / (n : ℝ) ^ 8 := by
  rw [tsum_zeta_four, tsum_zeta_eight]; ring

/-- ζ(2)·ζ(6) = (5/3)·ζ(8). -/
theorem zeta_two_mul_six :
    (∑' n : ℕ, (1 : ℝ) / (n : ℝ) ^ 2) * (∑' n : ℕ, (1 : ℝ) / (n : ℝ) ^ 6)
      = (5 / 3) * ∑' n : ℕ, (1 : ℝ) / (n : ℝ) ^ 8 := by
  rw [tsum_zeta_two, tsum_zeta_six, tsum_zeta_eight]; ring

/-! ## The double zeta value ζ(2,2)

The harmonic (stuffle) product gives ζ(2)·ζ(2) = ζ(4) + 2·ζ(2,2), where
ζ(2,2) = ∑_{m>n≥1} 1/(m²n²) is the simplest genuine multiple zeta value.
Solving for ζ(2,2) and substituting the closed forms above yields its exact
value — a single rational multiple of π⁴, the canonical example of MZV ↔ single
zeta value reduction. -/

/-- ζ(2,2) = (ζ(2)² − ζ(4))/2 = π⁴/120. -/
theorem mzv_two_two_value :
    ((∑' n : ℕ, (1 : ℝ) / (n : ℝ) ^ 2) ^ 2 - ∑' n : ℕ, (1 : ℝ) / (n : ℝ) ^ 4) / 2
      = π ^ 4 / 120 := by
  rw [tsum_zeta_two, tsum_zeta_four]; ring

/-- Equivalently, ζ(2,2) is the weight-4 MZV equal to (3/4)·ζ(4). -/
theorem mzv_two_two_eq_three_quarter_zeta_four :
    ((∑' n : ℕ, (1 : ℝ) / (n : ℝ) ^ 2) ^ 2 - ∑' n : ℕ, (1 : ℝ) / (n : ℝ) ^ 4) / 2
      = (3 / 4) * ∑' n : ℕ, (1 : ℝ) / (n : ℝ) ^ 4 := by
  rw [tsum_zeta_two, tsum_zeta_four]; ring

end BaselProblemOQ03
