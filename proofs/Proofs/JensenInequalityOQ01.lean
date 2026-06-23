/-
# The Equality Case of Strict Jensen, and the Sharp Weighted AM–GM Equality

This file isolates the **equality case** of the finite weighted Jensen inequality for a
*strictly* convex function, and specializes it — through the strict convexity of `exp` — to the
sharp equality case of the **weighted arithmetic–geometric mean inequality**.

The abstract input is Mathlib's `StrictConvexOn.map_sum_eq_iff`: for a strictly convex `f`,
strictly positive weights `w` summing to `1`, and points `p i` in the domain,

    f (∑ i, w i • p i) = ∑ i, w i • f (p i)   ↔   the points `p i` are all (equal to their mean).

Specializing `f = exp` and `p i = log (z i)` turns Jensen's inequality into weighted AM–GM, and the
equality case into the statement that geometric and arithmetic means coincide **iff all the data
are equal**. This is precisely the route by which Mathlib establishes
`Real.geom_mean_eq_arith_mean_weighted_iff'`; here we package the bridge explicitly and supply the
strict inequality directly from `StrictConvexOn.map_sum_lt`, together with the familiar
two-variable instance `√(ab) = (a+b)/2 ↔ a = b`.

## Main results

* `jensen_eq_iff` — the abstract equality case of strict Jensen (a clean re-export).
* `weighted_amgm_le` — the weighted AM–GM inequality `∏ zᵢ^{wᵢ} ≤ ∑ wᵢ zᵢ`.
* `weighted_amgm_eq_iff` — equality `∏ zᵢ^{wᵢ} = ∑ wᵢ zᵢ` holds **iff** all `zᵢ` are equal.
* `weighted_amgm_lt_of_ne` — if some two values differ, the inequality is strict; proved directly
  through `strictConvexOn_exp.map_sum_lt`, making the Jensen → AM–GM bridge explicit.
* `amgm_two_eq_iff` — the concrete two-variable equality case `√(ab) = (a+b)/2 ↔ a = b`.

All results are fully machine-checked: 0 sorries, 0 axioms, no `native_decide`.
-/

import Mathlib

open Finset Real

variable {ι : Type*} {s : Finset ι} {w z : ι → ℝ}

/-! ## The abstract equality case of strict Jensen -/

/-- **Equality case of strict Jensen's inequality.**

For a strictly convex `f`, strictly positive weights `ω` summing to `1`, and points `p i` in the
domain `S`, Jensen's inequality `f(∑ ω • p) ≤ ∑ ω • f(p)` is an *equality* exactly when every point
equals the (weighted) center of mass — i.e. the data are constant. This is a clean re-export of
Mathlib's `StrictConvexOn.map_sum_eq_iff`, recorded here as the foundation for the AM–GM corollary
below. -/
theorem jensen_eq_iff {f : ℝ → ℝ} {S : Set ℝ} {t : Finset ι} {ω : ι → ℝ} {p : ι → ℝ}
    (hf : StrictConvexOn ℝ S f) (h₀ : ∀ i ∈ t, 0 < ω i) (h₁ : ∑ i ∈ t, ω i = 1)
    (hmem : ∀ i ∈ t, p i ∈ S) :
    f (∑ i ∈ t, ω i • p i) = ∑ i ∈ t, ω i • f (p i) ↔ ∀ j ∈ t, p j = ∑ i ∈ t, ω i • p i :=
  hf.map_sum_eq_iff h₀ h₁ hmem

/-! ## Weighted AM–GM and its equality case -/

/-- **Weighted arithmetic–geometric mean inequality.** For nonnegative weights summing to `1` and
nonnegative data, the weighted geometric mean is at most the weighted arithmetic mean. -/
theorem weighted_amgm_le (hw : ∀ i ∈ s, 0 ≤ w i) (hw' : ∑ i ∈ s, w i = 1)
    (hz : ∀ i ∈ s, 0 ≤ z i) :
    ∏ i ∈ s, z i ^ w i ≤ ∑ i ∈ s, w i * z i :=
  Real.geom_mean_le_arith_mean_weighted s w z hw hw' hz

/-- **Equality case of weighted AM–GM.** With *strictly positive* weights summing to `1` and
nonnegative data, the weighted geometric and arithmetic means coincide **iff all the data are
equal**.

This restates Mathlib's `Real.geom_mean_eq_arith_mean_weighted_iff'` (whose center-of-mass right
side `∀ j, z j = ∑ w • z` we convert to the symmetric "all equal" form), the latter itself being a
specialization of `strictConvexOn_exp.map_sum_eq_iff`. -/
theorem weighted_amgm_eq_iff (hw : ∀ i ∈ s, 0 < w i) (hw' : ∑ i ∈ s, w i = 1)
    (hz : ∀ i ∈ s, 0 ≤ z i) :
    ∏ i ∈ s, z i ^ w i = ∑ i ∈ s, w i * z i ↔ ∀ j ∈ s, ∀ k ∈ s, z j = z k := by
  rw [Real.geom_mean_eq_arith_mean_weighted_iff' s w z hw hw' hz]
  constructor
  · intro h j hj k hk; rw [h j hj, h k hk]
  · intro h j hj
    calc z j = ∑ i ∈ s, w i * z j := by rw [← Finset.sum_mul, hw', one_mul]
      _ = ∑ i ∈ s, w i * z i := Finset.sum_congr rfl fun i hi => by rw [h i hi j hj]

/-- **Strict weighted AM–GM.** With strictly positive weights summing to `1` and strictly positive
data, if two of the values differ then the weighted geometric mean is *strictly* less than the
weighted arithmetic mean.

The proof goes directly through the strict Jensen inequality `StrictConvexOn.map_sum_lt` for
`exp`: writing `z i = exp (log (z i))`, the geometric mean is `exp (∑ w • log z)` and the arithmetic
mean is `∑ w • exp (log z)`, so strict convexity of `exp` on a non-constant family gives the strict
gap. This is the explicit Jensen → AM–GM bridge. -/
theorem weighted_amgm_lt_of_ne (hw : ∀ i ∈ s, 0 < w i) (hw' : ∑ i ∈ s, w i = 1)
    (hz : ∀ i ∈ s, 0 < z i) (hne : ∃ j ∈ s, ∃ k ∈ s, z j ≠ z k) :
    ∏ i ∈ s, z i ^ w i < ∑ i ∈ s, w i * z i := by
  -- The geometric mean rewrites as `exp` of the weighted mean of the logs.
  have hgeo : Real.exp (∑ i ∈ s, w i • Real.log (z i)) = ∏ i ∈ s, z i ^ w i := by
    rw [Real.exp_sum]
    refine Finset.prod_congr rfl fun i hi => ?_
    rw [smul_eq_mul, Real.rpow_def_of_pos (hz i hi), mul_comm]
  -- The arithmetic mean rewrites as the weighted mean of `exp (log (z i)) = z i`.
  have harith : ∑ i ∈ s, w i • Real.exp (Real.log (z i)) = ∑ i ∈ s, w i * z i := by
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [smul_eq_mul, Real.exp_log (hz i hi)]
  -- Non-constant data ⇒ non-constant logs, by injectivity of `log` on the positives.
  obtain ⟨j, hj, k, hk, hjk⟩ := hne
  have hlog : ∃ j ∈ s, ∃ k ∈ s, Real.log (z j) ≠ Real.log (z k) :=
    ⟨j, hj, k, hk, fun h =>
      hjk (Real.log_injOn_pos (Set.mem_Ioi.mpr (hz j hj)) (Set.mem_Ioi.mpr (hz k hk)) h)⟩
  have hlt := strictConvexOn_exp.map_sum_lt hw hw' (fun i _ => Set.mem_univ (Real.log (z i))) hlog
  rwa [hgeo, harith] at hlt

/-! ## The two-variable instance -/

/-- **Two-variable AM–GM equality case.** For nonnegative reals, the geometric mean `√(ab)` equals
the arithmetic mean `(a+b)/2` exactly when `a = b`. The forward direction is the classic
`(√a − √b)² = 0`. -/
theorem amgm_two_eq_iff {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.sqrt (a * b) = (a + b) / 2 ↔ a = b := by
  constructor
  · intro h
    have hab : Real.sqrt a * Real.sqrt b = (a + b) / 2 := by rw [← Real.sqrt_mul ha]; exact h
    have hu : Real.sqrt a ^ 2 = a := Real.sq_sqrt ha
    have hv : Real.sqrt b ^ 2 = b := Real.sq_sqrt hb
    have key : (Real.sqrt a - Real.sqrt b) ^ 2 = 0 := by nlinarith [hu, hv, hab]
    have huv : Real.sqrt a = Real.sqrt b :=
      sub_eq_zero.mp (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp key)
    rw [← Real.sq_sqrt ha, ← Real.sq_sqrt hb, huv]
  · rintro rfl
    rw [Real.sqrt_mul_self ha]; ring
