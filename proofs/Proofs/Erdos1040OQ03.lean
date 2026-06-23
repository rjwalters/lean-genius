/-
Erdős Problem #1040 — open question oq-03:
"Is the quantity μ(F) — the infimum of the area |{z : |f(z)| < 1}| over monic
polynomials f with roots in F — controlled by a simple geometric invariant?"

The parent entry (#1040) studies the *measure* of polynomial lemniscates and
whether the transfinite diameter of the root set F determines
   μ(F) = inf { |{z : |f(z)| < 1}| : f monic, roots ⊆ F }.
That question is OPEN. This companion isolates and fully PROVES the elementary
quantitative *upper* bounds on the lemniscate area that any such infimum must
respect, using only the geometric confinement of the lemniscate to unit balls
about the roots (the mechanism developed for #1042).

For a monic f(z) = ∏ᵢ (z - rootᵢ) of degree n the lemniscate {z : |f(z)| < 1}
is contained in the union of the OPEN UNIT BALLS centred at the roots: a point
that is ≥ 1 away from every root has |f| = ∏ᵢ|z - rootᵢ| ≥ 1. Taking Lebesgue
(area) measure on ℂ ≅ ℝ² and using finite subadditivity together with the area
π of a unit disc gives at once the unconditional bound
   area {|f| < 1} ≤ n · π.
When in addition the roots lie in the closed unit disc (|rootᵢ| ≤ 1, the setting
of #1039/#1040), the same confinement forces {|f| < 1} ⊆ B(0, 2), so the area is
bounded by a CONSTANT independent of the degree:
   area {|f| < 1} ≤ 4π.

Both bounds are axiom-free and self-contained. They are deliberately ELEMENTARY:
the sharp classical inequality is Pólya's `area ≤ π` for every monic degree-n
polynomial (proved via logarithmic capacity / the isoperimetric inequality),
which the constant `4π` here approximates to within a factor of 4 by purely
metric means. Nothing below depends on the parent's axioms.
-/

import Mathlib

open Complex BigOperators MeasureTheory Metric
open scoped ENNReal NNReal

namespace Erdos1040OQ03

/-- A monic polynomial `f(z) = ∏ᵢ (z - rootᵢ)` of a given degree, recorded by its
list of roots. -/
structure RootedPoly where
  degree : ℕ
  roots : Fin degree → ℂ

/-- The monic polynomial `f(z) = ∏ᵢ (z - rootᵢ)` evaluated at `z`. -/
noncomputable def RootedPoly.eval (p : RootedPoly) (z : ℂ) : ℂ :=
  ∏ i : Fin p.degree, (z - p.roots i)

/-- The lemniscate of `p`, the open sublevel set `{z : |f(z)| < 1}`. -/
def lem (p : RootedPoly) : Set ℂ :=
  {z : ℂ | ‖p.eval z‖ < 1}

/-- The polynomial map `z ↦ f(z)` is continuous (a finite product of the
continuous maps `z ↦ z - rootᵢ`). -/
theorem continuous_eval (p : RootedPoly) : Continuous p.eval := by
  unfold RootedPoly.eval
  exact continuous_finset_prod _ fun i _ => continuous_id.sub continuous_const

/-- The lemniscate is open: it is the preimage of the open ray `(-∞, 1)` under the
continuous map `z ↦ ‖f(z)‖`. -/
theorem isOpen_lem (p : RootedPoly) : IsOpen (lem p) := by
  have h : Continuous fun z => ‖p.eval z‖ := (continuous_eval p).norm
  show IsOpen ((fun z => ‖p.eval z‖) ⁻¹' Set.Iio 1)
  exact h.isOpen_preimage (Set.Iio 1) isOpen_Iio

/-- Each root of `f` lies in the lemniscate: `f(rootᵢ) = 0`, and `‖0‖ = 0 < 1`. -/
theorem root_mem_lem (p : RootedPoly) (i : Fin p.degree) : p.roots i ∈ lem p := by
  have h0 : p.eval (p.roots i) = 0 := by
    unfold RootedPoly.eval
    exact Finset.prod_eq_zero (Finset.mem_univ i) (sub_self _)
  show ‖p.eval (p.roots i)‖ < 1
  rw [h0, norm_zero]; norm_num

/-- In positive degree the lemniscate is nonempty (it contains the first root). -/
theorem lem_nonempty (p : RootedPoly) (hp : 0 < p.degree) : (lem p).Nonempty :=
  ⟨p.roots ⟨0, hp⟩, root_mem_lem p ⟨0, hp⟩⟩

/-- **Confinement core.** Every point of the lemniscate lies within distance 1 of
some root: if `z` were `≥ 1` away from all roots then
`‖f(z)‖ = ∏ᵢ‖z - rootᵢ‖ ≥ 1`, contradicting `z ∈ lem p`. -/
theorem lem_near_root (p : RootedPoly) {z : ℂ} (hz : z ∈ lem p) :
    ∃ i : Fin p.degree, ‖z - p.roots i‖ < 1 := by
  by_contra h
  push_neg at h
  have h1 : (1 : ℝ) ≤ ‖p.eval z‖ := by
    unfold RootedPoly.eval
    rw [norm_prod]
    exact Finset.one_le_prod' fun i _ => h i
  have hz' : ‖p.eval z‖ < 1 := hz
  exact absurd hz' (not_lt.mpr h1)

/-- **Geometric confinement.** The lemniscate is contained in the union of the
open unit balls centred at the roots of `f`. -/
theorem lem_subset_iUnion_ball (p : RootedPoly) :
    lem p ⊆ ⋃ i : Fin p.degree, Metric.ball (p.roots i) 1 := by
  intro z hz
  obtain ⟨i, hi⟩ := lem_near_root p hz
  refine Set.mem_iUnion.mpr ⟨i, ?_⟩
  rw [Metric.mem_ball, dist_eq_norm]
  exact hi

/-- The lemniscate is bounded: it sits inside a finite union of unit balls. -/
theorem isBounded_lem (p : RootedPoly) : Bornology.IsBounded (lem p) := by
  have hb : Bornology.IsBounded (⋃ i : Fin p.degree, Metric.ball (p.roots i) 1) :=
    isBounded_iUnion.mpr fun _ => Metric.isBounded_ball
  exact hb.subset (lem_subset_iUnion_ball p)

/-- **Unconditional area bound.** The Lebesgue (area) measure of the lemniscate is
at most `degree · π`: the lemniscate is covered by `degree` unit balls, each of
area `π`, and measure is finitely subadditive. -/
theorem volume_lem_le_degree_mul_pi (p : RootedPoly) :
    volume (lem p) ≤ (p.degree : ℝ≥0∞) * (NNReal.pi : ℝ≥0∞) := by
  calc volume (lem p)
      ≤ volume (⋃ i : Fin p.degree, Metric.ball (p.roots i) 1) :=
        measure_mono (lem_subset_iUnion_ball p)
    _ ≤ ∑ i : Fin p.degree, volume (Metric.ball (p.roots i) 1) :=
        measure_iUnion_fintype_le volume (fun i => Metric.ball (p.roots i) 1)
    _ = ∑ _i : Fin p.degree, (NNReal.pi : ℝ≥0∞) := by
        simp only [Complex.volume_ball, ENNReal.ofReal_one, one_pow, one_mul]
    _ = (p.degree : ℝ≥0∞) * (NNReal.pi : ℝ≥0∞) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- **Confinement to a fixed disc.** If all roots lie in the closed unit disc then
the whole lemniscate lies in the open disc of radius `2` about the origin: every
lemniscate point is within distance 1 of some root, and that root is within
distance 1 of the origin. -/
theorem lem_subset_ball_two (p : RootedPoly) (h : ∀ i, ‖p.roots i‖ ≤ 1) :
    lem p ⊆ Metric.ball (0 : ℂ) 2 := by
  intro z hz
  obtain ⟨i, hi⟩ := lem_near_root p hz
  rw [Metric.mem_ball]
  calc dist z 0 ≤ dist z (p.roots i) + dist (p.roots i) 0 := dist_triangle z (p.roots i) 0
    _ = ‖z - p.roots i‖ + ‖p.roots i‖ := by rw [dist_eq_norm, dist_eq_norm, sub_zero]
    _ < 1 + 1 := add_lt_add_of_lt_of_le hi (h i)
    _ = 2 := by norm_num

/-- Area of the disc of radius `2` in `ℂ` is `4π`. -/
theorem volume_ball_two : volume (Metric.ball (0 : ℂ) 2) = ENNReal.ofReal (4 * Real.pi) := by
  have h4 : (2 : ℝ) ^ 2 = 4 := by norm_num
  rw [Complex.volume_ball, ← ENNReal.ofReal_coe_nnreal, NNReal.coe_real_pi,
      ← ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 2), h4,
      ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4)]

/-- **Degree-free area bound.** When the roots lie in the closed unit disc the
lemniscate area is bounded by the CONSTANT `4π`, independent of the degree —
the elementary metric counterpart of Pólya's sharp `area ≤ π`. -/
theorem volume_lem_le_four_pi (p : RootedPoly) (h : ∀ i, ‖p.roots i‖ ≤ 1) :
    volume (lem p) ≤ ENNReal.ofReal (4 * Real.pi) := by
  rw [← volume_ball_two]
  exact measure_mono (lem_subset_ball_two p h)

/-- **Capstone.** For a monic polynomial whose roots lie in the closed unit disc,
the lemniscate `{z : |f(z)| < 1}` is confined to the open disc of radius `2` and
its area satisfies both the unconditional bound `≤ degree · π` and the
degree-free bound `≤ 4π`. The *positions* of the roots, not merely the
transfinite diameter of the ambient set, therefore cap the lemniscate area. -/
theorem confinement_area_bound (p : RootedPoly) (h : ∀ i, ‖p.roots i‖ ≤ 1) :
    lem p ⊆ Metric.ball (0 : ℂ) 2 ∧
      volume (lem p) ≤ (p.degree : ℝ≥0∞) * (NNReal.pi : ℝ≥0∞) ∧
      volume (lem p) ≤ ENNReal.ofReal (4 * Real.pi) :=
  ⟨lem_subset_ball_two p h, volume_lem_le_degree_mul_pi p, volume_lem_le_four_pi p h⟩

end Erdos1040OQ03
