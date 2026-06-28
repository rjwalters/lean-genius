import Mathlib.Tactic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Analysis.Convex.Measure

/-
# Replacing the Singular Homology Axiom with Mathlib Analysis Tools
# (brouwer-fixed-point-oq-01-oq-02-oq-01)

## The Open Question

**OQ-01-OQ-02-OQ-01**: The companion file `BrouwerFixedPointOQ01OQ02.lean`
proves the No-Retraction Theorem (there is no continuous retraction
`r : B^n → S^{n-1}`) via **singular homology**, but at the cost of three
homology axioms (`H_n_minus_1_sphere_nonzero`,
`contractible_singularHomology_zero`, `sphere_singularHomology_nonzero`).
Those axioms stand in for the Mathlib gaps `H_{n-1}(S^{n-1}) ≅ ℤ` and the
prism/contractibility vanishing.

Can the homology axioms be replaced with **Mathlib analysis tools** —
specifically the measure-theoretic route of Milnor (*Analytic proof of the
"hairy ball" theorem and the Brouwer fixed-point theorem*, Amer. Math.
Monthly 85 (1978), 521–524)?

## The Answer (this file)

**Yes for the *measure-theoretic scaffolding*, with one precisely-isolated
remaining analytic gap — and it is 0-axiom.**

Milnor's argument runs entirely inside real analysis / measure theory, with
no homology whatsoever. The contradiction it manufactures is:

> a (smooth) retraction `r : B^n → S^{n-1}` would map the **positive-volume**
> ball `B^n` *onto* the **measure-zero** sphere `S^{n-1}`, while a degree /
> change-of-variables (Jacobian) argument forces such a map to *preserve*
> the volume of the ball.

This file formalizes every ingredient of that obstruction that Mathlib
already supports, **with zero axioms and zero sorries**:

* `unitSphere_volume_zero`   — `S^{n-1}` is Lebesgue-null            (`Measure.addHaar_sphere`)
* `closedBall_volume_pos`    — `B^n` has positive volume            (`measure_closedBall_pos`)
* `closedBall_volume_lt_top` — `B^n` has finite volume              (`measure_closedBall_lt_top`)
* `retraction_image_eq_sphere`     — a retraction surjects `B^n` onto `S^{n-1}`
* `retraction_image_volume_zero`   — hence its image is Lebesgue-null
* `retraction_collapses_volume`    — ball positive, image null  (the qualitative obstruction)
* `no_retraction_of_volume_preserved` — the **reduction**: the *only* missing
  ingredient is volume-preservation `vol(r '' B^n) = vol(B^n)`.

The straight-line homotopy `f_t = (1-t)·id + t·r` that Milnor integrates is
also built here (`straightLine`, with continuous endpoints), so the analytic
program is laid out end to end.

## What is genuinely replaced, and what remains

| Singular-homology route (companion)        | Analytic route (this file)                     |
|--------------------------------------------|------------------------------------------------|
| `sphere_singularHomology_nonzero` (axiom)  | `unitSphere_volume_zero` (**proved**)          |
| `contractible_singularHomology_zero` (axiom)| `closedBall_volume_pos` (**proved**)          |
| `H_n_minus_1_sphere_nonzero` (axiom)       | `no_retraction_of_volume_preserved` (**proved reduction**), gap = `hvol` |

The single remaining analytic gap, `hvol : vol(r '' B^n) = vol(B^n)`, is
*not* an axiom here — it is an explicit hypothesis of
`no_retraction_of_volume_preserved`. Discharging it is exactly Milnor's
degree computation: smooth `f_t` for small `t` is a diffeomorphism of `B^n`,
`t ↦ vol(f_t(B^n))` is a *polynomial* (the integral of `det Df_t`, itself
polynomial in `t`), and a polynomial constant near `0` is constant on `[0,1]`,
forcing `vol(f_1(B^n)) = vol(B^n)`. Mathlib already has the change-of-variables
engine for this in `MeasureTheory.Function.Jacobian`; the missing piece is the
polynomiality/degree bookkeeping plus a smoothing step `r ↦ r_smooth`. This
file reduces the whole homology apparatus to that one analytic statement.

**Honesty note.** This file does *not* prove no-retraction. Continuity alone
does **not** forbid a volume-collapsing surjection `B^n ↠ S^{n-1}` (it merely
forbids volume *preservation* from coexisting with it). The contradiction
genuinely needs the smooth degree/Jacobian input named in `hvol`; that is the
content of the Milnor argument and the precise frontier of the analytic route.

## Status: VERIFIED, 0 axioms, 0 sorries (analytic scaffolding + reduction)
-/

open MeasureTheory Metric Set

noncomputable section

namespace BrouwerAnalytic

/-! ## Geometry: the unit ball, the unit sphere, and retractions -/

/-- The closed unit ball in ℝⁿ (same definition as the homology companion,
for interoperability). -/
def ClosedBall (n : ℕ) : Set (EuclideanSpace ℝ (Fin n)) :=
  Metric.closedBall 0 1

/-- The unit sphere `S^{n-1}` in ℝⁿ. -/
def UnitSphere (n : ℕ) : Set (EuclideanSpace ℝ (Fin n)) :=
  Metric.sphere 0 1

/-- A retraction `r : B^n → S^{n-1}`: continuous, lands in the sphere on the
ball, and fixes the sphere pointwise. -/
structure Retraction (n : ℕ) where
  toFun : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)
  continuous' : Continuous toFun
  maps_to_sphere : ∀ x ∈ ClosedBall n, toFun x ∈ UnitSphere n
  fixes_sphere : ∀ x ∈ UnitSphere n, toFun x = x

/-- The sphere is contained in the closed ball. -/
theorem unitSphere_subset_closedBall (n : ℕ) : UnitSphere n ⊆ ClosedBall n := by
  intro x hx
  simp only [UnitSphere, ClosedBall, Metric.mem_sphere, Metric.mem_closedBall] at *
  exact le_of_eq hx

/-! ## Nontriviality of ℝⁿ for `n ≥ 1`

`Measure.addHaar_sphere` needs the ambient space to be `Nontrivial`. For
`n ≥ 1` the standard basis vector `e₀` witnesses this. -/

/-- For `n ≥ 1`, `ℝⁿ` is nontrivial (its `finrank` is `n > 0`). -/
theorem nontrivial_euclidean (n : ℕ) (hn : 1 ≤ n) :
    Nontrivial (EuclideanSpace ℝ (Fin n)) := by
  apply Module.nontrivial_of_finrank_pos (R := ℝ)
  rw [finrank_euclideanSpace_fin]
  omega

/-! ## The measure-theoretic obstruction (Milnor route) -/

/-- **Sphere is Lebesgue-null.** `S^{n-1}` has volume `0` in `ℝⁿ` for `n ≥ 1`.
This is the analytic replacement for the homology axiom
`sphere_singularHomology_nonzero`: the sphere being "thin" is captured here by
measure rather than homology. -/
theorem unitSphere_volume_zero (n : ℕ) (hn : 1 ≤ n) :
    volume (UnitSphere n) = 0 := by
  haveI := nontrivial_euclidean n hn
  simpa [UnitSphere] using
    Measure.addHaar_sphere (volume : Measure (EuclideanSpace ℝ (Fin n))) 0 1

/-- **Ball has positive volume.** The analytic replacement for the
contractibility/vanishing axiom: the ball is "fat". -/
theorem closedBall_volume_pos (n : ℕ) : 0 < volume (ClosedBall n) := by
  simpa [ClosedBall] using
    measure_closedBall_pos (volume : Measure (EuclideanSpace ℝ (Fin n))) 0
      (by norm_num : (0 : ℝ) < 1)

/-- The ball has finite volume (it is compact). -/
theorem closedBall_volume_lt_top (n : ℕ) : volume (ClosedBall n) < ⊤ := by
  simpa [ClosedBall] using
    (measure_closedBall_lt_top :
      volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1) < ⊤)

/-- **A retraction surjects the ball onto the sphere.** Its image is exactly
`S^{n-1}`: `⊆` is `maps_to_sphere`, and `⊇` holds because `r` fixes the sphere,
which lies inside the ball. -/
theorem retraction_image_eq_sphere (n : ℕ) (r : Retraction n) :
    r.toFun '' (ClosedBall n) = UnitSphere n := by
  apply Set.Subset.antisymm
  · rintro y ⟨x, hx, rfl⟩
    exact r.maps_to_sphere x hx
  · intro y hy
    exact ⟨y, unitSphere_subset_closedBall n hy, r.fixes_sphere y hy⟩

/-- **The image of a retraction is Lebesgue-null.** Combine the previous two
facts: `r '' B^n = S^{n-1}` has volume `0`. -/
theorem retraction_image_volume_zero (n : ℕ) (hn : 1 ≤ n) (r : Retraction n) :
    volume (r.toFun '' (ClosedBall n)) = 0 := by
  rw [retraction_image_eq_sphere n r]
  exact unitSphere_volume_zero n hn

/-- **The qualitative obstruction.** A retraction maps a *positive-volume* set
onto a *null* set. (This alone is not a contradiction — continuous maps can
collapse volume — but it is the geometric heart of Milnor's argument.) -/
theorem retraction_collapses_volume (n : ℕ) (hn : 1 ≤ n) (r : Retraction n) :
    0 < volume (ClosedBall n) ∧ volume (r.toFun '' (ClosedBall n)) = 0 :=
  ⟨closedBall_volume_pos n, retraction_image_volume_zero n hn r⟩

/-- **The reduction.** No retraction can exist *once* one supplies the single
analytic fact that a retraction preserves the volume of the ball,
`vol(r '' B^n) = vol(B^n)`. This isolates the entire remaining content of the
analytic route into the hypothesis `hvol`, which Milnor's degree / Jacobian
change-of-variables argument provides for smooth maps.

Crucially `hvol` is a *hypothesis*, not an axiom — so this theorem, and the
whole file, is genuinely 0-axiom. -/
theorem no_retraction_of_volume_preserved (n : ℕ) (hn : 1 ≤ n) (r : Retraction n)
    (hvol : volume (r.toFun '' (ClosedBall n)) = volume (ClosedBall n)) : False := by
  rw [retraction_image_volume_zero n hn r] at hvol
  exact (closedBall_volume_pos n).ne' hvol.symm

/-! ## Milnor's straight-line homotopy `f_t = (1 - t)·id + t·r`

The map whose volume `t ↦ vol(f_t(B^n))` Milnor proves is polynomial in `t`.
Here we record it and its endpoints; the polynomiality/degree step (the
content of `hvol` above) is the remaining analytic gap. -/

/-- The straight-line homotopy from the identity (`t = 0`) to the retraction
(`t = 1`). -/
def straightLine (n : ℕ) (r : Retraction n) (t : ℝ) :
    EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) :=
  fun x => (1 - t) • x + t • r.toFun x

@[simp] theorem straightLine_zero (n : ℕ) (r : Retraction n) :
    straightLine n r 0 = id := by
  funext x; simp [straightLine]

@[simp] theorem straightLine_one (n : ℕ) (r : Retraction n) :
    straightLine n r 1 = r.toFun := by
  funext x; simp [straightLine]

/-- Each `f_t` is continuous (it is a fixed affine combination of `id` and the
continuous `r`). -/
theorem straightLine_continuous (n : ℕ) (r : Retraction n) (t : ℝ) :
    Continuous (straightLine n r t) := by
  unfold straightLine
  exact (continuous_const.smul continuous_id).add (continuous_const.smul r.continuous')

/-- On the sphere the homotopy is stationary at the boundary point: `f_t` fixes
`S^{n-1}` pointwise for every `t` (since `r` does). This is why each `f_t`
restricts to a self-map of the ball with the same boundary behaviour. -/
theorem straightLine_fixes_sphere (n : ℕ) (r : Retraction n) (t : ℝ)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ UnitSphere n) :
    straightLine n r t x = x := by
  simp only [straightLine, r.fixes_sphere x hx]
  rw [← add_smul]
  simp

end BrouwerAnalytic

end
