import Mathlib.MeasureTheory.Function.Egorov
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic

/-
# Sharpness of Egorov's Theorem: the Finite-Measure Hypothesis is Essential

## What This Proves

**Egorov's theorem** says: on a measure space of *finite* measure, if
`fₙ → g` almost everywhere then for every `ε > 0` there is a set of measure `≤ ε`
off which `fₙ → g` *uniformly*. The parent gallery proof (`egorov-theorem-oq-01`)
formalizes the theorem, a worked example (`xⁿ` on `[0,1]`), and the sharpness of
the *removed null set* (`xⁿ` is non-uniform on all of `[0,1)`).

This file establishes a different, complementary sharpness: the **finiteness of
the ambient measure** cannot be dropped. On the infinite-measure space `(ℝ, vol)`
there is a sequence converging to `0` *everywhere* yet admitting **no**
finite-measure set off which the convergence is uniform — so the Egorov
conclusion fails outright.

The witnesses are the **marching indicators**

  `fₙ = 𝟙_{[n, n+1]}`     (`marching n = (Icc n (n+1)).indicator 1`).

* `marching_tendsto_zero` — for every `x : ℝ`, `fₙ(x) → 0`. (For a fixed `x`,
  once `n > x` the bump `[n, n+1]` has marched past `x`, so `fₙ(x) = 0`.)
  Convergence holds at *every* point, not merely almost everywhere.

* `marching_not_tendstoUniformlyOn_of_volume_lt_top` — for **any** set `s` of
  finite Lebesgue measure, `fₙ` does *not* converge uniformly to `0` on `sᶜ`.
  Indeed uniformity on `sᶜ` (with `ε = 1/2`) would force `[n, n+1] ⊆ s` for all
  large `n`, hence `[N, ∞) ⊆ s`, contradicting `vol s < ∞`.

* `volume_finite_hypothesis_essential` — packaging: there is no finite-measure
  set off which `fₙ → 0` uniformly.

* `marching_not_tendstoUniformlyOn_univ` — the `s = ∅` special case: `fₙ` is
  non-uniform even on all of `ℝ`.

## Why It Is Not in Mathlib

Mathlib has the abstract Egorov theorem but no formalized counterexample showing
the finite-measure hypothesis is necessary. The marching-indicator construction,
its everywhere-pointwise convergence, and the no-finite-exceptional-set
obstruction are the new content.

## Axiom Status

Fully verified: 0 sorries, 0 `axiom` declarations, no `native_decide`. Relies
only on Mathlib's measure theory and the foundational axioms `propext`,
`Classical.choice`, `Quot.sound`.
-/

open MeasureTheory Filter Set Topology
open scoped ENNReal

namespace EgorovTheoremOQ01OQ03

/-- The **marching indicators** `fₙ = 𝟙_{[n, n+1]}` on `ℝ`: a unit bump on the
interval `[n, n+1]` that marches off to `+∞` as `n → ∞`. -/
noncomputable def marching (n : ℕ) : ℝ → ℝ :=
  Set.indicator (Set.Icc (n : ℝ) (n + 1)) 1

/-- The marching indicators converge to `0` at **every** point of `ℝ`: for a
fixed `x`, once `n > x` the bump `[n, n+1]` lies entirely to the right of `x`, so
`fₙ(x) = 0` from then on. -/
theorem marching_tendsto_zero (x : ℝ) :
    Tendsto (fun n => marching n x) atTop (𝓝 (0 : ℝ)) := by
  obtain ⟨N, hN⟩ := exists_nat_gt x
  have hev : ∀ᶠ n in atTop, marching n x = 0 := by
    rw [eventually_atTop]
    refine ⟨N, fun n hn => ?_⟩
    apply Set.indicator_of_notMem
    rw [Set.mem_Icc]
    rintro ⟨hle, _⟩
    have hxn : x < (n : ℝ) := lt_of_lt_of_le hN (by exact_mod_cast hn)
    linarith
  exact (tendsto_congr' hev).mpr tendsto_const_nhds

/-- **Sharpness of Egorov: the finite-measure hypothesis is essential.** For
*any* set `s ⊆ ℝ` of finite Lebesgue measure, the marching indicators do not
converge uniformly to `0` on the complement `sᶜ`. Hence no finite-measure
exceptional set can rescue uniform convergence on the infinite-measure space `ℝ`,
even though `fₙ → 0` everywhere pointwise. -/
theorem marching_not_tendstoUniformlyOn_of_volume_lt_top
    {s : Set ℝ} (hs : volume s < ⊤) :
    ¬ TendstoUniformlyOn marching (fun _ => (0 : ℝ)) atTop sᶜ := by
  intro h
  rw [Metric.tendstoUniformlyOn_iff] at h
  obtain ⟨N, hN⟩ := eventually_atTop.mp (h (1 / 2) (by norm_num))
  -- Uniformity with `ε = 1/2` forces every `[n, n+1]` with `n ≥ N` into `s`,
  -- so `[N, ∞) ⊆ s`.
  have hsub : Set.Ici (N : ℝ) ⊆ s := by
    intro x hx
    have hx0 : (0 : ℝ) ≤ x := le_trans (Nat.cast_nonneg N) hx
    by_contra hxs
    -- `x ∈ sᶜ`; let `n = ⌊x⌋₊ ≥ N`, so `x ∈ [n, n+1]` and `fₙ(x) = 1`.
    set n := ⌊x⌋₊ with hn_def
    have hnN : N ≤ n := Nat.le_floor hx
    have hmem : x ∈ Set.Icc (n : ℝ) (n + 1) := by
      constructor
      · exact Nat.floor_le hx0
      · exact (Nat.lt_floor_add_one x).le
    have hval : marching n x = 1 := by
      unfold marching
      rw [Set.indicator_of_mem hmem, Pi.one_apply]
    have hdist := hN n hnN x hxs
    rw [hval] at hdist
    simp only [Real.dist_eq] at hdist
    norm_num at hdist
  -- But `[N, ∞)` has infinite measure, contradicting `vol s < ∞`.
  have hle : volume (Set.Ici (N : ℝ)) ≤ volume s := measure_mono hsub
  rw [Real.volume_Ici] at hle
  exact hs.ne (top_le_iff.mp hle)

/-- **The finite-measure hypothesis of Egorov's theorem cannot be dropped.**
There is no finite-measure set `s` such that `fₙ → 0` uniformly off `s`, despite
`fₙ → 0` everywhere on `ℝ`. -/
theorem volume_finite_hypothesis_essential :
    ¬ ∃ s : Set ℝ, volume s < ⊤ ∧
      TendstoUniformlyOn marching (fun _ => (0 : ℝ)) atTop sᶜ := by
  rintro ⟨s, hs, h⟩
  exact marching_not_tendstoUniformlyOn_of_volume_lt_top hs h

/-- The `s = ∅` special case: the marching indicators do not converge uniformly
to `0` on all of `ℝ`, even though they converge to `0` at every point. -/
theorem marching_not_tendstoUniformlyOn_univ :
    ¬ TendstoUniformlyOn marching (fun _ => (0 : ℝ)) atTop Set.univ := by
  have h := marching_not_tendstoUniformlyOn_of_volume_lt_top
    (s := (∅ : Set ℝ)) (by simp)
  rwa [Set.compl_empty] at h

/-! ## The same counterexample, seen through integrals: mass escaping to infinity

The marching indicators converge to `0` at every point, yet each one carries a *fixed
unit of mass* that simply slides off to `+∞`. This is the integral-side face of the very
same infinite-measure pathology that defeats Egorov: on a finite-measure space Egorov
would force uniform convergence off a small set and hence control the integrals, but here
the integrals stay pinned at `1` while the pointwise limit is `0`. So `(ℝ, vol)` also
witnesses the failure of the limit–integral interchange `lim ∫ fₙ ≠ ∫ lim fₙ`. -/

/-- Each marching indicator integrates to exactly `1`: it is the indicator of a unit-length
interval, whose Lebesgue measure is `1`. The mass is conserved for every `n` even as the
bump marches off to `+∞`. -/
theorem marching_integral_eq_one (n : ℕ) :
    ∫ x, marching n x ∂volume = 1 := by
  have hmar : marching n = Set.indicator (Set.Icc (n : ℝ) (n + 1)) (fun _ => (1 : ℝ)) := rfl
  rw [hmar, integral_indicator measurableSet_Icc, setIntegral_const,
    Real.volume_real_Icc_of_le (by linarith : (n : ℝ) ≤ (n : ℝ) + 1), smul_eq_mul]
  ring

/-- **Mass escapes to infinity.** Although `fₙ → 0` everywhere (`marching_tendsto_zero`), the
integrals `∫ fₙ = 1` do *not* tend to `0 = ∫ (lim fₙ)`: the same marching counterexample that
breaks Egorov's finite-measure hypothesis also breaks the limit–integral interchange on
`(ℝ, vol)`. The integral sequence is constantly `1`, so it converges to `1 ≠ 0`. -/
theorem marching_integral_not_tendsto_zero :
    ¬ Tendsto (fun n => ∫ x, marching n x ∂volume) atTop (𝓝 (0 : ℝ)) := by
  simp only [marching_integral_eq_one]
  rw [tendsto_const_nhds_iff]
  norm_num

/-! ## The same counterexample, seen through convergence in measure

On a *finite*-measure space, almost-everywhere convergence implies convergence in
measure (this is the easy half behind Egorov). The marching indicators show this too
fails on `(ℝ, vol)`: they converge to `0` at every point, yet for the threshold
`ε = 1/2` the bad set `{x : 1/2 ≤ |fₙ(x)|}` is exactly `[n, n+1]`, of constant measure
`1`, which does not tend to `0`. So `fₙ` does **not** converge to `0` in measure. -/

/-- **No convergence in measure.** Despite `fₙ → 0` everywhere (`marching_tendsto_zero`),
the marching indicators do not converge to `0` in measure on `(ℝ, vol)`: for `ε = 1/2`
the measure of `{x : 1/2 ≤ ‖fₙ(x)‖}` is the constant `1` (the length of `[n, n+1]`),
so it cannot tend to `0`. This is the convergence-in-measure face of the infinite-measure
pathology — on a finite-measure space a.e. convergence *would* force convergence in
measure. -/
theorem marching_not_tendstoInMeasure :
    ¬ TendstoInMeasure volume marching atTop (fun _ => (0 : ℝ)) := by
  intro h
  have hpos : (0 : ℝ≥0∞) < 1 / 2 := ENNReal.half_pos one_ne_zero
  have hmeas := h (1 / 2) hpos
  have hvol : ∀ n : ℕ,
      volume {x : ℝ | 1 / 2 ≤ edist (marching n x) ((fun _ => (0 : ℝ)) x)} = 1 := by
    intro n
    have hset : {x : ℝ | 1 / 2 ≤ edist (marching n x) ((fun _ => (0 : ℝ)) x)}
        = Set.Icc (n : ℝ) (n + 1) := by
      ext x
      simp only [Set.mem_setOf_eq]
      by_cases hx : x ∈ Set.Icc (n : ℝ) (n + 1)
      · have hval : marching n x = 1 := by
          unfold marching; rw [Set.indicator_of_mem hx, Pi.one_apply]
        constructor
        · intro _; exact hx
        · intro _
          rw [hval, edist_dist, Real.dist_eq, sub_zero, abs_one, ENNReal.ofReal_one]
          exact ENNReal.half_le_self
      · have hval : marching n x = 0 := by
          unfold marching; rw [Set.indicator_of_notMem hx]
        constructor
        · intro hle
          rw [hval, edist_self] at hle
          exact absurd hle (not_le.mpr hpos)
        · intro hxIcc; exact absurd hxIcc hx
    rw [hset, Real.volume_Icc, show ((n : ℝ) + 1) - n = 1 from by ring, ENNReal.ofReal_one]
  have htend : Tendsto (fun _ : ℕ => (1 : ℝ≥0∞)) atTop (𝓝 0) := hmeas.congr hvol
  rw [tendsto_const_nhds_iff] at htend
  exact one_ne_zero htend

end EgorovTheoremOQ01OQ03
