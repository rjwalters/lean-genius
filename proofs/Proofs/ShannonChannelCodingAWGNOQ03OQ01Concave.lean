/-
# Shannon AWGN water-filling, oq-03-oq-01 — concavity of the capacity in power

Source: parallel-Gaussian-channel water-filling (see
`ShannonChannelCodingAWGNOQ03OQ01.lean`, namespace `ShannonWaterFilling`, which
proves optimality of `Pᵢ⋆ = (μ − Nᵢ)₊`).

The companion `…Monotone.lean` records the structural *monotonicities* of the
per-channel and parallel rates (in power and in noise), and `…EqualNoise.lean`
records the *concavity* of the special **equal-noise** scalar capacity
`(n/2)·log(1 + P/(n·c))`.  Neither supplies the concavity of the **general**
water-filling capacity.  This file fills that gap, all axiom-free / sorry-free:

* `perUseCapacity_concaveOn`       — a single AWGN sub-channel `½ log(1 + P/N)`
  (`N > 0`) is concave in the allotted power `P` on `[0, ∞)`.  The arbitrary-noise
  generalisation of the equal-noise `rate_equalNoise_concaveOn_power`.
* `perUseCapacity_strictConcaveOn` — the *strict* sharpening: `½ log(1 + P/N)` is
  strictly concave in `P`.
* `parallelRate_concaveOn_power`   — **the headline**: the total parallel-channel
  rate `R(P) = ∑ᵢ ½ log(1 + Pᵢ/Nᵢ)` is *jointly* concave in the whole power
  **vector** `P` on the nonnegative orthant `{P | ∀ i, 0 ≤ Pᵢ}`.  This is the
  concavity that turns the water-filling power-allocation problem into a *convex*
  program — the structural reason the KKT/water-filling solution
  (`waterfilling_optimal`) is globally optimal, and that time-sharing power across
  allocations is never strictly better than a single convex-combined allocation.

The single-channel proofs compose the concavity of `Real.log`
(`strictConcaveOn_log_Ioi`) with the affine reparametrisation `P ↦ 1 + P/N` and the
nonnegative scaling `½` — mirroring the equal-noise argument.  The joint result
pulls each per-channel concavity back through the linear coordinate evaluation
`P ↦ Pᵢ` (`ConcaveOn.comp_linearMap`) onto the common orthant and sums the terms
(`ConcaveOn.add`).

Tags: information-theory, shannon, awgn, water-filling, capacity, concavity, convex-program
-/

import Mathlib
import Proofs.ShannonChannelCodingAWGNOQ03OQ01

set_option linter.unusedSectionVars false

namespace ShannonWaterFilling

open scoped BigOperators

/-! ## Single-channel concavity in the allotted power -/

/-- **Concavity of a single sub-channel's rate in power.**  For positive noise
`N`, the per-use AWGN capacity `½ log(1 + P/N)` is concave in the allotted power
`P` on `[0, ∞)`: a convex combination of two power levels achieves at least the
convex combination of their rates (time-sharing power is never strictly better
than averaging it).  The arbitrary-noise generalisation of the equal-noise
`rate_equalNoise_concaveOn_power`; the proof composes the concavity of `Real.log`
with the affine reparametrisation `P ↦ 1 + P/N` and the nonnegative scaling `½`. -/
theorem perUseCapacity_concaveOn {N : ℝ} (hN : 0 < N) :
    ConcaveOn ℝ (Set.Ici 0) (fun P => perUseCapacity P N) := by
  have hNne : N ≠ 0 := hN.ne'
  refine ⟨convex_Ici 0, fun x hx y hy a b ha hb hab => ?_⟩
  simp only [Set.mem_Ici] at hx hy
  unfold perUseCapacity
  have hux : (0 : ℝ) < 1 + x / N := by
    have : 0 ≤ x / N := div_nonneg hx hN.le; linarith
  have huy : (0 : ℝ) < 1 + y / N := by
    have : 0 ≤ y / N := div_nonneg hy hN.le; linarith
  have hsum : a * (1 + x / N) + b * (1 + y / N) = 1 + (a * x + b * y) / N := by
    field_simp
    linear_combination N * hab
  have hstep : a * Real.log (1 + x / N) + b * Real.log (1 + y / N)
      ≤ Real.log (a * (1 + x / N) + b * (1 + y / N)) := by
    have := (strictConcaveOn_log_Ioi.concaveOn).2 (Set.mem_Ioi.mpr hux)
      (Set.mem_Ioi.mpr huy) ha hb hab
    simpa only [smul_eq_mul] using this
  simp only [smul_eq_mul]
  calc a * (1 / 2 * Real.log (1 + x / N)) + b * (1 / 2 * Real.log (1 + y / N))
      = 1 / 2 * (a * Real.log (1 + x / N) + b * Real.log (1 + y / N)) := by ring
    _ ≤ 1 / 2 * Real.log (a * (1 + x / N) + b * (1 + y / N)) :=
        mul_le_mul_of_nonneg_left hstep (by norm_num)
    _ = 1 / 2 * Real.log (1 + (a * x + b * y) / N) := by rw [hsum]

/-- **Strict concavity of a single sub-channel's rate in power.**  For positive
noise `N`, the per-use AWGN capacity `½ log(1 + P/N)` is *strictly* concave in `P`
on `[0, ∞)`, sharpening `perUseCapacity_concaveOn`.  The affine reparametrisation
`P ↦ 1 + P/N` is injective, so distinct power levels map to distinct positive
arguments where `Real.log` is strictly concave (`strictConcaveOn_log_Ioi`), and the
strictly positive scaling `½` preserves the strict inequality. -/
theorem perUseCapacity_strictConcaveOn {N : ℝ} (hN : 0 < N) :
    StrictConcaveOn ℝ (Set.Ici 0) (fun P => perUseCapacity P N) := by
  have hNne : N ≠ 0 := hN.ne'
  refine ⟨convex_Ici 0, fun x hx y hy hxy a b ha hb hab => ?_⟩
  simp only [Set.mem_Ici] at hx hy
  unfold perUseCapacity
  have hux : (0 : ℝ) < 1 + x / N := by
    have : 0 ≤ x / N := div_nonneg hx hN.le; linarith
  have huy : (0 : ℝ) < 1 + y / N := by
    have : 0 ≤ y / N := div_nonneg hy hN.le; linarith
  have hne_arg : (1 + x / N) ≠ (1 + y / N) := by
    intro h
    apply hxy
    have hk2 : x / N = y / N := by linarith
    field_simp [hNne] at hk2
    linarith
  have hsum : a * (1 + x / N) + b * (1 + y / N) = 1 + (a * x + b * y) / N := by
    field_simp
    linear_combination N * hab
  have hstep : a * Real.log (1 + x / N) + b * Real.log (1 + y / N)
      < Real.log (a * (1 + x / N) + b * (1 + y / N)) := by
    have := strictConcaveOn_log_Ioi.2 (Set.mem_Ioi.mpr hux) (Set.mem_Ioi.mpr huy)
      hne_arg ha hb hab
    simpa only [smul_eq_mul] using this
  simp only [smul_eq_mul]
  calc a * (1 / 2 * Real.log (1 + x / N)) + b * (1 / 2 * Real.log (1 + y / N))
      = 1 / 2 * (a * Real.log (1 + x / N) + b * Real.log (1 + y / N)) := by ring
    _ < 1 / 2 * Real.log (a * (1 + x / N) + b * (1 + y / N)) :=
        mul_lt_mul_of_pos_left hstep (by norm_num)
    _ = 1 / 2 * Real.log (1 + (a * x + b * y) / N) := by rw [hsum]

/-! ## A finite sum of concave functions is concave -/

/-- **A finite sum of functions concave on a common convex set is concave.**  If
each `g i` is concave on the convex set `s`, so is `x ↦ ∑ i ∈ t, g i x`.  Proved by
`Finset` induction from `concaveOn_const` (empty sum) and `ConcaveOn.add` (insert
step). -/
theorem concaveOn_finset_sum {E κ : Type*} [AddCommMonoid E] [Module ℝ E]
    {s : Set E} (hs : Convex ℝ s) {g : κ → E → ℝ} (h : ∀ i, ConcaveOn ℝ s (g i))
    (t : Finset κ) : ConcaveOn ℝ s (fun x => ∑ i ∈ t, g i x) := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa using concaveOn_const (0 : ℝ) hs
  | @insert a t ha ih =>
      have heq : (fun x => ∑ i ∈ insert a t, g i x)
          = (g a) + (fun x => ∑ i ∈ t, g i x) := by
        funext x; rw [Finset.sum_insert ha]; rfl
      rw [heq]
      exact (h a).add ih

/-! ## The headline: joint concavity of the parallel-channel capacity -/

variable {ι : Type*} [Fintype ι]

/-- **The parallel-Gaussian capacity is jointly concave in the power vector.**  For
a positive noise profile `N`, the total rate `R(P) = ∑ᵢ ½ log(1 + Pᵢ/Nᵢ)` is
concave as a function of the whole power **vector** `P` on the nonnegative orthant
`{P | ∀ i, 0 ≤ Pᵢ}`.

This is the structural concavity behind water-filling: the feasible set
`{P | Pᵢ ≥ 0, ∑ Pᵢ ≤ Pₜₒₜ}` is convex and the objective `R` is concave, so the
power-allocation problem is a *convex program*.  Consequently the KKT
water-filling point (`waterfilling_optimal`) is a *global* optimum, and no
time-sharing of two feasible allocations beats their convex combination.

Each per-channel term `P ↦ ½ log(1 + Pᵢ/Nᵢ)` is `perUseCapacity_concaveOn` pulled
back through the linear coordinate map `P ↦ Pᵢ` (`ConcaveOn.comp_linearMap`,
restricted to the orthant by `ConcaveOn.subset`); `concaveOn_finset_sum` adds the
terms. -/
theorem parallelRate_concaveOn_power (N : ι → ℝ) (hN : ∀ i, 0 < N i) :
    ConcaveOn ℝ (Set.univ.pi fun _ : ι => Set.Ici (0 : ℝ))
      (fun P => parallelRate N P) := by
  set s : Set (ι → ℝ) := Set.univ.pi fun _ : ι => Set.Ici (0 : ℝ) with hs_def
  have hs : Convex ℝ s := convex_pi fun i _ => convex_Ici 0
  have hmem : ∀ (P : ι → ℝ), P ∈ s ↔ ∀ i, 0 ≤ P i := by
    intro P; rw [hs_def, Set.mem_univ_pi]; simp only [Set.mem_Ici]
  -- each coordinate term is concave on the orthant `s`
  have hterm : ∀ i, ConcaveOn ℝ s (fun P : ι → ℝ => perUseCapacity (P i) (N i)) := by
    intro i
    have hc := (perUseCapacity_concaveOn (hN i)).comp_linearMap
      (LinearMap.proj (R := ℝ) (φ := fun _ : ι => ℝ) i)
    have hsub : s ⊆ (LinearMap.proj (R := ℝ) (φ := fun _ : ι => ℝ) i) ⁻¹' Set.Ici 0 := by
      intro P hP
      simp only [Set.mem_preimage, LinearMap.proj_apply, Set.mem_Ici]
      exact (hmem P).mp hP i
    have hres := hc.subset hsub hs
    simpa [Function.comp, LinearMap.proj_apply] using hres
  have hsum := concaveOn_finset_sum hs hterm (Finset.univ : Finset ι)
  simpa only [parallelRate] using hsum

end ShannonWaterFilling
