/-
Copyright (c) 2024-2026 lean-genius contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-
# Generalized Euler constant for an arbitrary antitone summand (OQ-01 · OQ-02 · OQ-02)

The parent file (`AntitoneIntegralSumComparisonOQ01OQ02`) specialized the antitone
integral test to `f x = 1/x` and identified the limit of the harmonic defect
`Hₙ − log(n+1)` with Mathlib's Euler–Mascheroni constant `γ`.  That answered the
convergence question *for the single function `1/x`*.

This file lifts the phenomenon to **every** antitone, nonnegative summand.  For such an
`f` on `[1, ∞)` define the **defect sequence**

  `D f n := (∑_{i<n} f(1+i)) − ∫₁^{1+n} f`.

The two-sided integral-test sandwich (Mathlib's `AntitoneOn.integral_le_sum` and
`AntitoneOn.sum_le_integral`) forces `D f` to be **monotone non-decreasing** and bounded
above by `f 1`, hence convergent.  Its limit

  `generalizedEuler f := ⨆ n, D f n`

is the *generalized Euler constant* of `f`: for `f = 1/x` it is the classical `γ`, and the
construction requires nothing beyond `f` being antitone and nonnegative — divergence of
`∑ f` is exactly what makes the constant a nontrivial invariant rather than a shifted tail.

## Main results

* `defect_nonneg`   : `0 ≤ D f n` (the upper Riemann sum dominates the integral).
* `defect_le`       : `D f n ≤ f 1` (a uniform bound, via a telescoping lower Riemann sum).
* `defect_monotone` : `Monotone (D f)` (each step adds `f(1+n) − ∫` of a unit cell `≥ 0`).
* `tendsto_defect`  : `D f → generalizedEuler f`, the bounded-monotone limit.
* `generalizedEuler_mem_Icc` : `generalizedEuler f ∈ [0, f 1]`.

Everything reduces to the Mathlib sum/integral comparison library; the file is `sorry`-free
and uses only standard foundational axioms.
-/

namespace AntitoneIntegralSumComparisonOQ01OQ02OQ02

open Finset Filter Topology MeasureTheory intervalIntegral

variable {f : ℝ → ℝ}

/-- The **generalized Euler defect**: the excess of the right-open Riemann sum
`∑_{i<n} f(1+i)` over the integral `∫₁^{1+n} f`. -/
noncomputable def defect (f : ℝ → ℝ) (n : ℕ) : ℝ :=
  (∑ i ∈ Finset.range n, f (1 + (i : ℝ))) - ∫ x in (1 : ℝ)..(1 + (n : ℝ)), f x

@[simp] theorem defect_zero : defect f 0 = 0 := by
  simp [defect]

/-- An antitone function on `[1, ∞)` is interval-integrable on any subinterval `[a, b]`
with `1 ≤ a ≤ b`. -/
theorem intervalIntegrable_of_antitone (hmono : AntitoneOn f (Set.Ici 1)) {a b : ℝ}
    (ha : (1 : ℝ) ≤ a) (hb : a ≤ b) : IntervalIntegrable f MeasureTheory.volume a b := by
  apply AntitoneOn.intervalIntegrable
  rw [Set.uIcc_of_le hb]
  exact hmono.mono (fun x hx => le_trans ha hx.1)

/-- Restriction of the antitone hypothesis to the finite window `[1, 1+n]`. -/
private theorem antitone_window (hmono : AntitoneOn f (Set.Ici 1)) (n : ℕ) :
    AntitoneOn f (Set.Icc (1 : ℝ) (1 + (n : ℝ))) :=
  hmono.mono Set.Icc_subset_Ici_self

/-- **The defect is nonnegative.**  The upper Riemann sum `∑_{i<n} f(1+i)` dominates the
integral `∫₁^{1+n} f`, directly from `AntitoneOn.integral_le_sum`. -/
theorem defect_nonneg (hmono : AntitoneOn f (Set.Ici 1)) (n : ℕ) : 0 ≤ defect f n := by
  have h := (antitone_window hmono n).integral_le_sum
  simp only [defect]
  linarith [h]

/-- **Uniform upper bound `f 1`.**  Subtracting the shifted (lower) Riemann sum
`∑_{i<n} f(1+(i+1))` — which lies below the integral — telescopes to `f 1 − f(1+n)`, and
`f(1+n) ≥ 0`. -/
theorem defect_le (hmono : AntitoneOn f (Set.Ici 1))
    (hnonneg : ∀ x, (1 : ℝ) ≤ x → 0 ≤ f x) (n : ℕ) : defect f n ≤ f 1 := by
  have h := (antitone_window hmono n).sum_le_integral
  -- telescoping of the difference of the two Riemann sums
  have htel : (∑ i ∈ Finset.range n, f (1 + (i : ℝ)))
      - (∑ i ∈ Finset.range n, f (1 + ((i + 1 : ℕ) : ℝ))) = f 1 - f (1 + (n : ℝ)) := by
    rw [← Finset.sum_sub_distrib]
    have := Finset.sum_range_sub' (fun i : ℕ => f (1 + (i : ℝ))) n
    simpa using this
  have hfn : 0 ≤ f (1 + (n : ℝ)) := hnonneg _ (le_add_of_nonneg_right (Nat.cast_nonneg n))
  simp only [defect]
  linarith [h, htel, hfn]

/-- **One-cell integral bound.**  On `[1+n, 1+n+1]` the antitone `f` satisfies
`∫ f ≤ f(1+n)`; this is `AntitoneOn.integral_le_sum` with a single subinterval. -/
private theorem integral_cell_le (hmono : AntitoneOn f (Set.Ici 1)) (n : ℕ) :
    (∫ x in (1 + (n : ℝ))..(1 + (n : ℝ) + 1), f x) ≤ f (1 + (n : ℝ)) := by
  have hanti : AntitoneOn f (Set.Icc (1 + (n : ℝ)) (1 + (n : ℝ) + ((1 : ℕ) : ℝ))) :=
    hmono.mono (fun x hx => le_trans (le_add_of_nonneg_right (Nat.cast_nonneg n)) hx.1)
  have h := hanti.integral_le_sum
  simpa using h

/-- **Monotone step.**  `D f n ≤ D f (n+1)`: the increment equals `f(1+n) − ∫` over the unit
cell `[1+n, 1+n+1]`, which is `≥ 0` by `integral_cell_le`. -/
theorem defect_le_succ (hmono : AntitoneOn f (Set.Ici 1)) (n : ℕ) :
    defect f n ≤ defect f (n + 1) := by
  have hsplit : (∫ x in (1 : ℝ)..(1 + ((n + 1 : ℕ) : ℝ)), f x)
      = (∫ x in (1 : ℝ)..(1 + (n : ℝ)), f x)
        + ∫ x in (1 + (n : ℝ))..(1 + (n : ℝ) + 1), f x := by
    have hab : IntervalIntegrable f MeasureTheory.volume 1 (1 + (n : ℝ)) :=
      intervalIntegrable_of_antitone hmono (le_refl 1) (le_add_of_nonneg_right (Nat.cast_nonneg n))
    have hbc : IntervalIntegrable f MeasureTheory.volume (1 + (n : ℝ)) (1 + (n : ℝ) + 1) :=
      intervalIntegrable_of_antitone hmono (le_add_of_nonneg_right (Nat.cast_nonneg n)) (by linarith)
    have hcast : (1 : ℝ) + ((n + 1 : ℕ) : ℝ) = 1 + (n : ℝ) + 1 := by push_cast; ring
    rw [hcast, ← intervalIntegral.integral_add_adjacent_intervals hab hbc]
  have hcell := integral_cell_le hmono n
  simp only [defect, Finset.sum_range_succ, hsplit]
  linarith [hcell]

/-- **The defect sequence is monotone non-decreasing.** -/
theorem defect_monotone (hmono : AntitoneOn f (Set.Ici 1)) : Monotone (defect f) :=
  monotone_nat_of_le_succ (defect_le_succ hmono)

/-- The range of the defect sequence is bounded above (by `f 1`). -/
theorem defect_bddAbove (hmono : AntitoneOn f (Set.Ici 1))
    (hnonneg : ∀ x, (1 : ℝ) ≤ x → 0 ≤ f x) : BddAbove (Set.range (defect f)) :=
  ⟨f 1, by rintro _ ⟨n, rfl⟩; exact defect_le hmono hnonneg n⟩

/-- The **generalized Euler constant** of an antitone nonnegative summand `f`: the limit of
its defect sequence. -/
noncomputable def generalizedEuler (f : ℝ → ℝ) : ℝ := ⨆ n, defect f n

/-- **Convergence of the defect sequence** to the generalized Euler constant — the bounded
monotone convergence theorem applied to `D f`. -/
theorem tendsto_defect (hmono : AntitoneOn f (Set.Ici 1))
    (hnonneg : ∀ x, (1 : ℝ) ≤ x → 0 ≤ f x) :
    Tendsto (defect f) atTop (𝓝 (generalizedEuler f)) :=
  tendsto_atTop_ciSup (defect_monotone hmono) (defect_bddAbove hmono hnonneg)

/-- The generalized Euler constant is `≤ f 1`. -/
theorem generalizedEuler_le (hmono : AntitoneOn f (Set.Ici 1))
    (hnonneg : ∀ x, (1 : ℝ) ≤ x → 0 ≤ f x) : generalizedEuler f ≤ f 1 :=
  ciSup_le (defect_le hmono hnonneg)

/-- The generalized Euler constant is nonnegative. -/
theorem generalizedEuler_nonneg (hmono : AntitoneOn f (Set.Ici 1))
    (hnonneg : ∀ x, (1 : ℝ) ≤ x → 0 ≤ f x) : 0 ≤ generalizedEuler f := by
  have hbdd := defect_bddAbove hmono hnonneg
  calc (0 : ℝ) = defect f 0 := (defect_zero).symm
    _ ≤ generalizedEuler f := le_ciSup hbdd 0

/-- **Packaged enclosure.**  The generalized Euler constant of any antitone nonnegative
summand lies in `[0, f 1]`. -/
theorem generalizedEuler_mem_Icc (hmono : AntitoneOn f (Set.Ici 1))
    (hnonneg : ∀ x, (1 : ℝ) ≤ x → 0 ≤ f x) : generalizedEuler f ∈ Set.Icc (0 : ℝ) (f 1) :=
  ⟨generalizedEuler_nonneg hmono hnonneg, generalizedEuler_le hmono hnonneg⟩

end AntitoneIntegralSumComparisonOQ01OQ02OQ02
