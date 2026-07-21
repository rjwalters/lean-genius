/-
# Erdős Problem #510 (Chowla's Cosine Problem) — Foundational Lemmas

Axiom-free foundational scaffolding for the cosine sum

    cosineSum A θ = ∑_{n ∈ A} cos(n·θ),     minCosineSum A = ⨅_θ cosineSum A θ,

as defined in `Proofs/Erdos510Problem.lean`.

Chowla's cosine problem asks whether there is an absolute constant `c > 0` such
that every finite `A ⊂ ℕ⁺` of size `N` admits an angle `θ` with
`cosineSum A θ < −c√N`.  The deep quantitative bounds (Bourgain, Ruzsa, Bedert)
remain open/hard, but the *elementary structure* of the cosine sum and its
infimum is fully provable from Mathlib.  This file establishes:

* evaluation lemmas: on the empty set, singletons, `insert`, at `θ = 0` and
  `θ = π`;
* the trivial two-sided bound `|cosineSum A θ| ≤ N` (so the sum lives in
  `[−N, N]`);
* evenness `cosineSum A (−θ) = cosineSum A θ` and `2π`-periodicity;
* continuity of `θ ↦ cosineSum A θ`;
* boundedness-below of the range, hence the basic `minCosineSum` bounds
  `−N ≤ minCosineSum A ≤ N` and `minCosineSum A ≤ cosineSum A θ`;
* the exact value `minCosineSum {n} = −1` for `n ≥ 1`.

All results are `0`-axiom / `0`-sorry.  The genuinely open content — the
`−c√N` lower bound — is untouched (it is the mission, not the scaffolding).

Reference: <https://erdosproblems.com/510>
-/

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Indexed
import Proofs.Erdos510Problem

open Finset Real

namespace Erdos510WIP01

variable (A : Finset ℕ) (θ : ℝ)

/-! ## Evaluation lemmas -/

/-- The cosine sum of the empty set is `0`. -/
theorem cosineSum_empty : cosineSum ∅ θ = 0 := by
  simp [cosineSum]

/-- The cosine sum of a singleton is a single cosine. -/
theorem cosineSum_singleton (n : ℕ) : cosineSum {n} θ = Real.cos (n * θ) := by
  simp [cosineSum]

/-- Adding a fresh frequency `n ∉ A` adds one cosine term. -/
theorem cosineSum_insert {n : ℕ} {A : Finset ℕ} (h : n ∉ A) :
    cosineSum (insert n A) θ = Real.cos (n * θ) + cosineSum A θ := by
  simp [cosineSum, Finset.sum_insert h]

/-- At `θ = 0` every term is `cos 0 = 1`, so the sum is the cardinality `N`. -/
theorem cosineSum_zero_angle : cosineSum A 0 = A.card := by
  simp [cosineSum]

/-- At `θ = π` the sum collapses to an alternating sum `∑ (−1)ⁿ`. -/
theorem cosineSum_pi : cosineSum A π = ∑ n ∈ A, (-1 : ℝ) ^ n := by
  simp only [cosineSum]
  exact Finset.sum_congr rfl (fun n _ => Real.cos_nat_mul_pi n)

/-! ## Symmetry and periodicity -/

/-- The cosine sum is even in the angle: `cosineSum A (−θ) = cosineSum A θ`. -/
theorem cosineSum_neg : cosineSum A (-θ) = cosineSum A θ := by
  simp only [cosineSum, mul_neg, Real.cos_neg]

/-- The cosine sum is `2π`-periodic in the angle. -/
theorem cosineSum_add_two_pi : cosineSum A (θ + 2 * π) = cosineSum A θ := by
  simp only [cosineSum]
  refine Finset.sum_congr rfl (fun n _ => ?_)
  rw [show (n : ℝ) * (θ + 2 * π) = n * θ + n * (2 * π) from by ring,
    Real.cos_add_nat_mul_two_pi]

/-! ## Trivial two-sided bound -/

/-- Triangle inequality plus `|cos| ≤ 1`: the cosine sum is bounded by `N`. -/
theorem abs_cosineSum_le_card : |cosineSum A θ| ≤ A.card := by
  simp only [cosineSum]
  calc |∑ n ∈ A, Real.cos (n * θ)| ≤ ∑ n ∈ A, |Real.cos (n * θ)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _n ∈ A, (1 : ℝ) := Finset.sum_le_sum
        (fun n _ => abs_le.mpr ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩)
    _ = A.card := by simp

/-- Upper bound `cosineSum A θ ≤ N`. -/
theorem cosineSum_le_card : cosineSum A θ ≤ A.card :=
  (le_abs_self _).trans (abs_cosineSum_le_card A θ)

/-- Lower bound `−N ≤ cosineSum A θ`. -/
theorem neg_card_le_cosineSum : -(A.card : ℝ) ≤ cosineSum A θ :=
  (abs_le.mp (abs_cosineSum_le_card A θ)).1

/-! ## Continuity -/

/-- `θ ↦ cosineSum A θ` is continuous (a finite sum of continuous cosines). -/
theorem continuous_cosineSum : Continuous (cosineSum A) := by
  show Continuous (fun θ => ∑ n ∈ A, Real.cos (n * θ))
  exact continuous_finsetSum _
    (fun n _ => Real.continuous_cos.comp (continuous_const.mul continuous_id))

/-! ## The infimum `minCosineSum` -/

/-- The range of `cosineSum A` is bounded below (by `−N`). -/
theorem bddBelow_range_cosineSum : BddBelow (Set.range (cosineSum A)) := by
  refine ⟨-(A.card : ℝ), ?_⟩
  rintro x ⟨θ, rfl⟩
  exact neg_card_le_cosineSum A θ

/-- `minCosineSum A` is a lower bound for every cosine sum value. -/
theorem minCosineSum_le : minCosineSum A ≤ cosineSum A θ :=
  ciInf_le (bddBelow_range_cosineSum A) θ

/-- `−N` bounds `minCosineSum A` from below. -/
theorem neg_card_le_minCosineSum : -(A.card : ℝ) ≤ minCosineSum A :=
  le_ciInf (fun θ => neg_card_le_cosineSum A θ)

/-- `minCosineSum A ≤ N` (via the value at `θ = 0`). -/
theorem minCosineSum_le_card : minCosineSum A ≤ A.card :=
  (minCosineSum_le A 0).trans_eq (cosineSum_zero_angle A)

/-- The minimum cosine sum of the empty set is `0`. -/
theorem minCosineSum_empty : minCosineSum ∅ = 0 := by
  have h : cosineSum ∅ = fun _ : ℝ => (0 : ℝ) := funext (fun θ => cosineSum_empty θ)
  simp only [minCosineSum, h]
  exact ciInf_const

/-- Exact value for a single positive frequency: `minCosineSum {n} = −1`
    for `n ≥ 1`.  The bound `−1 ≤ cos` gives `≥ −1`; the angle `θ = π/n`
    (where `cos(n·θ) = cos π = −1`) gives `≤ −1`. -/
theorem minCosineSum_singleton {n : ℕ} (hn : 1 ≤ n) : minCosineSum {n} = -1 := by
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hval : cosineSum {n} (π / n) = -1 := by
    rw [cosineSum_singleton]
    have hπ : (n : ℝ) * (π / n) = π := by field_simp
    rw [hπ, Real.cos_pi]
  apply le_antisymm
  · exact (minCosineSum_le {n} (π / n)).trans_eq hval
  · exact le_ciInf (fun θ => by rw [cosineSum_singleton]; exact Real.neg_one_le_cos _)

/-! ## The infimum is attained -/

/-- **The minimum cosine sum is attained.**  `cosineSum A` is continuous and
`2π`-periodic, so its infimum over all of `ℝ` equals its minimum over the compact
interval `[0, 2π]`, and is realised at some concrete angle `θ₀`.  This upgrades
`minCosineSum` from an `iInf` to an attained minimum — the structural
prerequisite for locating the extremal angle in the Chowla problem. -/
theorem exists_eq_minCosineSum (A : Finset ℕ) :
    ∃ θ₀ : ℝ, cosineSum A θ₀ = minCosineSum A := by
  have hper : Function.Periodic (cosineSum A) (2 * π) := fun θ => cosineSum_add_two_pi A θ
  have himg : cosineSum A '' Set.Icc 0 (0 + 2 * π) = Set.range (cosineSum A) :=
    hper.image_Icc Real.two_pi_pos 0
  have hne : (Set.Icc (0 : ℝ) (0 + 2 * π)).Nonempty :=
    ⟨0, Set.left_mem_Icc.mpr (by have := Real.two_pi_pos; linarith)⟩
  obtain ⟨θ₀, _, hmin⟩ :=
    isCompact_Icc.exists_isMinOn hne (continuous_cosineSum A).continuousOn
  refine ⟨θ₀, le_antisymm ?_ (minCosineSum_le A θ₀)⟩
  -- `cosineSum A θ₀` is a lower bound of the whole range, hence `≤` the infimum
  refine le_ciInf (fun θ => ?_)
  have hmem : cosineSum A θ ∈ Set.range (cosineSum A) := ⟨θ, rfl⟩
  rw [← himg] at hmem
  obtain ⟨y, hy, hyeq⟩ := hmem
  rw [← hyeq]
  exact isMinOn_iff.mp hmin y hy

/-! ## The minimum is nonpositive for positive-frequency sets

For a set `A` of *positive* frequencies (`0 ∉ A`), each term `cos(nθ)` integrates to `0`
over a full period, so `∫₀^{2π} cosineSum A = 0`. Since `minCosineSum A` is a pointwise
lower bound, integrating the constant gives `2π · minCosineSum A ≤ 0`, whence
`minCosineSum A ≤ 0`. This is the elementary sign fact behind the Chowla problem: a
positive-frequency cosine sum must dip to `0` or below somewhere. -/

/-- A single positive-frequency cosine integrates to zero over a full period. -/
theorem integral_cos_mul_eq_zero {n : ℕ} (hn : 1 ≤ n) :
    ∫ θ in (0 : ℝ)..(2 * π), Real.cos ((n : ℝ) * θ) = 0 := by
  have hcn : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  rw [intervalIntegral.integral_comp_mul_left (f := fun x => Real.cos x) hcn, integral_cos]
  have h1 : Real.sin ((n : ℝ) * (2 * π)) = 0 := by
    rw [show (n : ℝ) * (2 * π) = ((2 * n : ℕ) : ℝ) * π by push_cast; ring]
    exact Real.sin_nat_mul_pi (2 * n)
  rw [mul_zero, h1, Real.sin_zero, sub_zero, smul_zero]

/-- `∫₀^{2π} cosineSum A = 0` for a positive-frequency set (`0 ∉ A`). -/
theorem integral_cosineSum_eq_zero (A : Finset ℕ) (hA : 0 ∉ A) :
    ∫ θ in (0 : ℝ)..(2 * π), cosineSum A θ = 0 := by
  simp only [cosineSum]
  rw [intervalIntegral.integral_finsetSum]
  · refine Finset.sum_eq_zero (fun n hn => ?_)
    have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr (fun h => hA (h ▸ hn))
    exact integral_cos_mul_eq_zero hn1
  · intro n _
    exact (Real.continuous_cos.comp (continuous_const.mul continuous_id)).intervalIntegrable _ _

/-- **The Chowla cosine sum is nonpositive at its minimum for positive frequencies.**
If `0 ∉ A` then `minCosineSum A ≤ 0`: since `∫₀^{2π} cosineSum A = 0` and
`minCosineSum A ≤ cosineSum A θ` pointwise, the constant `minCosineSum A` integrates to
`2π · minCosineSum A ≤ 0`. -/
theorem minCosineSum_nonpos (A : Finset ℕ) (hA : 0 ∉ A) : minCosineSum A ≤ 0 := by
  have hint : ∫ θ in (0 : ℝ)..(2 * π), cosineSum A θ = 0 := integral_cosineSum_eq_zero A hA
  have hmono := intervalIntegral.integral_mono_on
    (a := (0 : ℝ)) (b := 2 * π) (μ := MeasureTheory.volume)
    (f := fun _ => minCosineSum A) (g := cosineSum A)
    Real.two_pi_pos.le intervalIntegrable_const
    ((continuous_cosineSum A).intervalIntegrable _ _)
    (fun θ _ => minCosineSum_le A θ)
  rw [intervalIntegral.integral_const, hint] at hmono
  simp only [smul_eq_mul, sub_zero] at hmono
  nlinarith [Real.two_pi_pos]

/-! ## The minimum is *strictly* negative for nonempty positive-frequency sets

The nonpositivity bound above is not tight: for a *nonempty* positive-frequency set the
minimum is strictly below `0`.  The point is that `cosineSum A` cannot be `≡ 0`: it takes
the value `N = A.card ≥ 1` at `θ = 0`.  If its minimum were `0` the (continuous, nonnegative)
integrand would still have integral `0` over a full period, yet it is *strictly* positive on
a whole subinterval near `0` — forcing the period integral to be positive, a contradiction.
So the minimum must be `< 0`, i.e. every nonempty positive-frequency cosine sum genuinely
dips below zero somewhere. -/

/-- **The Chowla cosine sum is strictly negative at its minimum** for a nonempty
positive-frequency set.  If `0 ∉ A` and `A ≠ ∅` then `minCosineSum A < 0`.  Combined with
`∫₀^{2π} cosineSum A = 0`: were the minimum `0`, the nonnegative integrand would be strictly
positive on a subinterval about `θ = 0` (where `cosineSum A 0 = A.card ≥ 1`), making the
period integral positive — impossible. This strengthens `minCosineSum_nonpos` and is the
qualitative core of the Chowla problem (the quantitative `−c√N` bound stays deep). -/
theorem minCosineSum_neg (A : Finset ℕ) (hA : 0 ∉ A) (hne : A.Nonempty) :
    minCosineSum A < 0 := by
  rcases (minCosineSum_nonpos A hA).lt_or_eq with h | h
  · exact h
  exfalso
  -- If the minimum is `0`, the sum is pointwise `≥ 0`.
  have hnn : ∀ θ, 0 ≤ cosineSum A θ := fun θ => h ▸ minCosineSum_le A θ
  -- The sum is strictly positive at `θ = 0` (value `A.card ≥ 1`).
  have hc0 : 0 < cosineSum A 0 := by
    rw [cosineSum_zero_angle]; exact_mod_cast Finset.card_pos.mpr hne
  -- `{θ | 0 < cosineSum A θ}` is open and contains `0`, so it holds on a ball `(−ε, ε)`.
  have hopen : IsOpen {θ : ℝ | 0 < cosineSum A θ} :=
    isOpen_lt continuous_const (continuous_cosineSum A)
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hopen 0 hc0
  -- Work on the interval `[δ/2, δ]` with `δ = min ε π`, safely inside `(0, 2π)`.
  set δ := min ε π with hδ
  have hδpos : 0 < δ := lt_min hε Real.pi_pos
  have hδle : δ ≤ π := min_le_right _ _
  have hδε : δ ≤ ε := min_le_left _ _
  have hcd : ∀ x ∈ Set.Ioo (δ / 2) δ, 0 < cosineSum A x := by
    intro x hx
    apply hball
    rw [Real.ball_eq_Ioo]
    exact ⟨by simp only [zero_sub]; linarith [hx.1], by simpa using lt_of_lt_of_le hx.2 hδε⟩
  -- Strict positivity of the middle integral, nonnegativity of the two outer ones.
  have hpos : 0 < ∫ x in (δ / 2)..δ, cosineSum A x :=
    intervalIntegral.intervalIntegral_pos_of_pos_on
      ((continuous_cosineSum A).intervalIntegrable _ _) hcd (by linarith)
  have hn1 : 0 ≤ ∫ x in (0 : ℝ)..(δ / 2), cosineSum A x :=
    intervalIntegral.integral_nonneg (by linarith) (fun u _ => hnn u)
  have hn3 : 0 ≤ ∫ x in δ..(2 * π), cosineSum A x :=
    intervalIntegral.integral_nonneg (by linarith [Real.pi_pos]) (fun u _ => hnn u)
  -- Split `∫₀^{2π} = ∫₀^{δ/2} + ∫_{δ/2}^{δ} + ∫_δ^{2π}`, which is then `> 0`.
  have i1 : IntervalIntegrable (cosineSum A) MeasureTheory.volume 0 (δ / 2) :=
    (continuous_cosineSum A).intervalIntegrable _ _
  have i2 : IntervalIntegrable (cosineSum A) MeasureTheory.volume (δ / 2) δ :=
    (continuous_cosineSum A).intervalIntegrable _ _
  have i3 : IntervalIntegrable (cosineSum A) MeasureTheory.volume δ (2 * π) :=
    (continuous_cosineSum A).intervalIntegrable _ _
  have hadd1 := intervalIntegral.integral_add_adjacent_intervals i1 i2
  have hadd2 := intervalIntegral.integral_add_adjacent_intervals (i1.trans i2) i3
  have hint : ∫ θ in (0 : ℝ)..(2 * π), cosineSum A θ = 0 := integral_cosineSum_eq_zero A hA
  linarith [hadd1, hadd2, hpos, hn1, hn3, hint]

/-- **Every nonempty positive-frequency cosine sum dips below zero.**  There is an angle
`θ` with `cosineSum A θ < 0`.  Immediate from `minCosineSum_neg` and the attainment of the
minimum (`exists_eq_minCosineSum`): the minimizing angle already realises a negative value. -/
theorem exists_angle_cosineSum_neg (A : Finset ℕ) (hA : 0 ∉ A) (hne : A.Nonempty) :
    ∃ θ : ℝ, cosineSum A θ < 0 := by
  obtain ⟨θ₀, hθ₀⟩ := exists_eq_minCosineSum A
  exact ⟨θ₀, hθ₀.trans_lt (minCosineSum_neg A hA hne)⟩

end Erdos510WIP01
