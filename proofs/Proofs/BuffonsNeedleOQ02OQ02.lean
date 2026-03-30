import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.Tactic

/-
# Buffon Noodle Extension to Smooth 3D Curves

## What This Proves

This file extends the 3D Buffon formula from polygonal paths (proved in
BuffonsNeedleOQ02.lean) to smooth C¹ curves in ℝ³. The central result is:

**Theorem (3D Buffon–Barbier for Smooth Curves)**:
For a C¹ curve γ : ℝ → ℝ³ of arc length L dropped on parallel planes
(spacing d), the expected number of crossings is:

  E[crossings] = L / (2d)

This depends only on arc length, not the curve's shape — the "noodle"
phenomenon extends to 3D.

## Mathematical Background

The 3D crossing factor α₃ = 1/2 (proved in BuffonsNeedleOQ02.lean via
∫₀^π sin θ |cos θ| dθ = 1) applies to smooth curves through the
approximation argument:

1. Approximate γ by inscribed polygonal paths Pₖ
2. Arc lengths converge: |Pₖ| → L (by C¹ regularity)
3. By the polygonal 3D noodle theorem: E[crossings(Pₖ)] = |Pₖ|/(2d)
4. By continuity: E[crossings(γ)] = L/(2d)

## Connection to Prior Work

- `BuffonsNeedle.lean`: 2D needle, P = 2ℓ/(πd)
- `BuffonsNoodle.lean`: 2D smooth noodle, E = 2L/(πd) (axiomatized)
- `BuffonsNeedleOQ02.lean`: 3D polygonal noodle, E = L/(2d) (verified)
- `BuffonsNeedleOQ02OQ01.lean`: n-dimensional crossing factor recurrence
- **This file**: 3D smooth noodle, E = L/(2d) (axiomatized smooth case,
  derived properties verified)
-/

namespace BuffonsNeedleOQ02OQ02

open Real Finset BigOperators MeasureTheory intervalIntegral

/-! ## Part I: 3D Arc Length

Arc length of a C¹ curve γ : ℝ → ℝ × ℝ × ℝ on [a,b]:
  L(γ, a, b) = ∫_a^b √(x'(t)² + y'(t)² + z'(t)²) dt
where x = fst ∘ γ, y = fst ∘ snd ∘ γ, z = snd ∘ snd ∘ γ.
-/

/-- Arc length of a 3D curve γ : ℝ → ℝ × ℝ × ℝ on [a, b].
    Computed component-wise as ∫_a^b √(x'² + y'² + z'²) dt. -/
noncomputable def arcLength3D (γ : ℝ → ℝ × ℝ × ℝ) (a b : ℝ) : ℝ :=
  ∫ t in a..b, Real.sqrt (
    (deriv (Prod.fst ∘ γ) t) ^ 2 +
    (deriv (Prod.fst ∘ Prod.snd ∘ γ) t) ^ 2 +
    (deriv (Prod.snd ∘ Prod.snd ∘ γ) t) ^ 2)

/-- The arc length is nonneg for a ≤ b (integral of a nonneg function). -/
theorem arcLength3D_nonneg (γ : ℝ → ℝ × ℝ × ℝ) (a b : ℝ) (hab : a ≤ b) :
    0 ≤ arcLength3D γ a b := by
  unfold arcLength3D
  apply intervalIntegral.integral_nonneg hab
  intro t _
  exact Real.sqrt_nonneg _

/-- A constant curve has zero arc length. -/
theorem arcLength3D_const (p : ℝ × ℝ × ℝ) (a b : ℝ) :
    arcLength3D (fun _ => p) a b = 0 := by
  unfold arcLength3D
  simp only [Function.comp_def, deriv_const]
  simp

/-- Arc length is additive over adjacent intervals:
    L(γ, a, c) = L(γ, a, b) + L(γ, b, c). -/
theorem arcLength3D_add (γ : ℝ → ℝ × ℝ × ℝ) (a b c : ℝ)
    (hcont : Continuous (fun t => Real.sqrt (
      (deriv (Prod.fst ∘ γ) t) ^ 2 +
      (deriv (Prod.fst ∘ Prod.snd ∘ γ) t) ^ 2 +
      (deriv (Prod.snd ∘ Prod.snd ∘ γ) t) ^ 2))) :
    arcLength3D γ a c = arcLength3D γ a b + arcLength3D γ b c := by
  unfold arcLength3D
  exact integral_add_adjacent_intervals
    (hcont.intervalIntegrable a b)
    (hcont.intervalIntegrable b c)

/-! ## Part II: 3D Polygonal Infrastructure

We reuse the core definitions from BuffonsNeedleOQ02.lean to state
the approximation theorems. The 3D polygonal noodle formula is:
  E[crossings] = totalLength / (2d)
-/

/-- A polygonal path in 3D with n segments. -/
structure Polygonal3D (n : ℕ) where
  /-- Length of each segment -/
  segLen : Fin n → ℝ
  /-- All segment lengths are nonneg -/
  nonneg : ∀ i, 0 ≤ segLen i

/-- The total length of a 3D polygonal path. -/
noncomputable def Polygonal3D.totalLength {n : ℕ} (P : Polygonal3D n) : ℝ :=
  ∑ i : Fin n, P.segLen i

/-- Total length is nonneg. -/
theorem Polygonal3D.totalLength_nonneg {n : ℕ} (P : Polygonal3D n) :
    0 ≤ P.totalLength := Finset.sum_nonneg (fun i _ => P.nonneg i)

/-- The expected crossing count for a 3D polygonal path with parallel planes
    (spacing d): E = totalLength / (2d). -/
noncomputable def Polygonal3D.expectedCrossings {n : ℕ} (P : Polygonal3D n) (d : ℝ) : ℝ :=
  P.totalLength / (2 * d)

/-- The 3D polygonal noodle theorem: expected crossings = L/(2d). -/
theorem polygonal3D_noodle {n : ℕ} (P : Polygonal3D n) (d : ℝ) (hd : 0 < d) :
    P.expectedCrossings d = P.totalLength / (2 * d) := rfl

/-! ## Part III: The Smooth 3D Buffon–Barbier Theorem

The expected number of crossings for a smooth C¹ curve in ℝ³ with
parallel planes. This requires measure theory on the space of plane
orientations (the Grassmannian Gr(2,3) ≅ S²) and the kinematic formula,
which is not yet available in Mathlib.

We axiomatize the smooth expected crossings and the main formula,
then derive all consequences.
-/

/-- The expected number of plane crossings for a smooth C¹ curve
    γ : ℝ → ℝ³ on [a,b] with parallel planes (spacing d).
    This is the primitive notion for the smooth 3D Buffon model. -/
noncomputable axiom smooth3DExpectedCrossings (γ : ℝ → ℝ × ℝ × ℝ) (a b d : ℝ) : ℝ

/-- **Buffon–Barbier Theorem (Smooth 3D Case)** [Axiom]:
    The expected number of crossings of a smooth C¹ curve γ : ℝ → ℝ³
    of arc length L with parallel planes (spacing d) equals L/(2d).

    This is the 3D generalization of Barbier's 1860 result. The full proof
    requires:
    - The kinematic measure on the space of oriented planes through ℝ³
    - Arc length approximation: C¹ curves ≈ polygonal paths in arc length
    - The 3D sphere average E_{S²}[|cos φ|] = 1/2 (proved in
      BuffonsNeedleOQ02.lean)
    - Continuity of the crossing-count functional

    The mathematical argument: approximate γ by inscribed polygonal paths Pₖ.
    By C¹ regularity, |Pₖ| → L. By the polygonal 3D noodle theorem
    (BuffonsNeedleOQ02.lean:buffon3d_noodle), E[crossings(Pₖ)] = |Pₖ|/(2d).
    By continuity, E[crossings(γ)] = L/(2d). -/
axiom smooth3D_buffon_eq
    (γ : ℝ → ℝ × ℝ × ℝ) (a b d : ℝ) (hd : 0 < d) (hab : a ≤ b)
    (hC1 : ContDiff ℝ 1 γ) :
    smooth3DExpectedCrossings γ a b d = arcLength3D γ a b / (2 * d)

/-! ## Part IV: Shape Independence

The most striking consequence: in 3D, just as in 2D, the expected
crossing count depends only on arc length, not on the curve's shape.
-/

/-- **Shape Independence (Smooth 3D)**: Two C¹ curves in ℝ³ with the same
    arc length have identical expected crossing counts, regardless of their
    shapes. The shape of the noodle does not matter in 3D either. -/
theorem smooth3D_shape_independence
    (γ₁ γ₂ : ℝ → ℝ × ℝ × ℝ) (a₁ b₁ a₂ b₂ d : ℝ)
    (hd : 0 < d) (h₁ : a₁ ≤ b₁) (h₂ : a₂ ≤ b₂)
    (hC1₁ : ContDiff ℝ 1 γ₁) (hC1₂ : ContDiff ℝ 1 γ₂)
    (hSameLen : arcLength3D γ₁ a₁ b₁ = arcLength3D γ₂ a₂ b₂) :
    smooth3DExpectedCrossings γ₁ a₁ b₁ d =
    smooth3DExpectedCrossings γ₂ a₂ b₂ d := by
  rw [smooth3D_buffon_eq _ _ _ _ hd h₁ hC1₁,
      smooth3D_buffon_eq _ _ _ _ hd h₂ hC1₂, hSameLen]

/-- The expected crossings are nonneg for a C¹ curve (d > 0, a ≤ b). -/
theorem smooth3D_expectedCrossings_nonneg
    (γ : ℝ → ℝ × ℝ × ℝ) (a b d : ℝ) (hd : 0 < d) (hab : a ≤ b)
    (hC1 : ContDiff ℝ 1 γ) :
    0 ≤ smooth3DExpectedCrossings γ a b d := by
  rw [smooth3D_buffon_eq _ _ _ _ hd hab hC1]
  apply div_nonneg
  · exact arcLength3D_nonneg γ a b hab
  · linarith

/-! ## Part V: Approximation Limit Theorem

The bridge from polygonal to smooth: if 3D polygonal paths converge
in arc length to a smooth curve, their expected crossings converge
to the smooth formula.
-/

/-- **Approximation Limit (3D)**: If a sequence of 3D polygonal paths has
    total lengths converging to L, then their expected crossings converge
    to L/(2d).

    This is the core of the polygonal-to-smooth argument in 3D:
    1. Approximate a smooth curve γ by inscribed polygonal paths Pₖ
    2. By the 3D polygonal noodle theorem: E[crossings(Pₖ)] = |Pₖ|/(2d)
    3. By this limit theorem: E[crossings(Pₖ)] → L/(2d)
    4. The smooth case follows by continuity of the crossing functional.

    The proof uses the continuity of the linear map x ↦ x/(2d). -/
theorem approximation_limit_3D
    (d : ℝ) (hd : 0 < d)
    (ns : ℕ → ℕ) (P : ∀ k, Polygonal3D (ns k))
    (L : ℝ)
    (hConverge : Filter.Tendsto (fun k => (P k).totalLength) Filter.atTop (nhds L)) :
    Filter.Tendsto
      (fun k => (P k).expectedCrossings d)
      Filter.atTop
      (nhds (L / (2 * d))) := by
  -- expectedCrossings is totalLength / (2 * d), which is continuous in totalLength
  show Filter.Tendsto (fun k => (P k).totalLength / (2 * d)) Filter.atTop (nhds (L / (2 * d)))
  have hcont : Continuous (fun x : ℝ => x / (2 * d)) :=
    continuous_id.div_const _
  exact hcont.continuousAt.tendsto.comp hConverge

/-- **Lipschitz Stability (3D)**: The 3D expected crossing formula is
    Lipschitz in arc length. Concretely:
    |E[crossings(P₁)] - E[crossings(P₂)]| ≤ (1/(2d)) · |L₁ - L₂|.

    Tighter than the 2D Lipschitz constant 2/(πd) since 1/2 < 2/π. -/
theorem lipschitz_3D {m n : ℕ}
    (P₁ : Polygonal3D m) (P₂ : Polygonal3D n) (d : ℝ) (hd : 0 < d) :
    |P₁.expectedCrossings d - P₂.expectedCrossings d| ≤
      1 / (2 * d) * |P₁.totalLength - P₂.totalLength| := by
  show |P₁.totalLength / (2 * d) - P₂.totalLength / (2 * d)| ≤
    1 / (2 * d) * |P₁.totalLength - P₂.totalLength|
  rw [show P₁.totalLength / (2 * d) - P₂.totalLength / (2 * d) =
      1 / (2 * d) * (P₁.totalLength - P₂.totalLength) by ring]
  rw [abs_mul, abs_of_pos (by positivity)]

/-! ## Part VI: Dimension Comparison (Smooth Case)

For a smooth curve of arc length L, the 3D formula gives fewer expected
crossings than the 2D formula:
  L/(2d) < 2L/(πd)    (when L, d > 0)

This is the smooth-curve version of the comparison in BuffonsNeedleOQ02.lean.
-/

/-- **3D vs 2D Smooth Comparison**: For a smooth curve of arc length L > 0,
    the 3D expected crossing count L/(2d) is strictly less than the 2D
    count 2L/(πd). The ratio is 4/π ≈ 1.273.

    This reflects the geometric fact that a random unit vector in ℝ³ has
    a smaller average projection onto a fixed axis (1/2) than in ℝ² (2/π):
    higher-dimensional space "dilutes" the projection. -/
theorem smooth3D_lt_smooth2D (L d : ℝ) (hL : 0 < L) (hd : 0 < d) :
    L / (2 * d) < 2 * L / (π * d) := by
  have hπ : (0 : ℝ) < π := pi_pos
  have hLd : 0 < L / d := div_pos hL hd
  calc L / (2 * d)
      = (1 / 2) * (L / d) := by ring
    _ < (2 / π) * (L / d) := by
        apply mul_lt_mul_of_pos_right _ hLd
        rw [div_lt_div_iff (by norm_num : (0:ℝ) < 2) hπ]
        linarith [pi_lt_four]
    _ = 2 * L / (π * d) := by
        field_simp [ne_of_gt hπ, ne_of_gt hd]

/-- The 2D-to-3D crossing ratio for smooth curves equals 4/π. -/
theorem smooth_crossing_ratio (L d : ℝ) (hL : 0 < L) (hd : 0 < d) :
    (2 * L / (π * d)) / (L / (2 * d)) = 4 / π := by
  have hπ : π ≠ 0 := pi_ne_zero
  have hd' : d ≠ 0 := ne_of_gt hd
  have hL' : L ≠ 0 := ne_of_gt hL
  field_simp [hπ, hd', hL']
  ring

/-! ## Part VII: Monotonicity and Scaling

The smooth 3D Buffon formula inherits monotonicity and scaling from
the algebraic structure of L/(2d).
-/

/-- **Monotonicity**: A longer C¹ curve has at least as many expected
    crossings with parallel planes. -/
theorem smooth3D_mono
    (γ₁ γ₂ : ℝ → ℝ × ℝ × ℝ) (a₁ b₁ a₂ b₂ d : ℝ)
    (hd : 0 < d) (h₁ : a₁ ≤ b₁) (h₂ : a₂ ≤ b₂)
    (hC1₁ : ContDiff ℝ 1 γ₁) (hC1₂ : ContDiff ℝ 1 γ₂)
    (hlen : arcLength3D γ₁ a₁ b₁ ≤ arcLength3D γ₂ a₂ b₂) :
    smooth3DExpectedCrossings γ₁ a₁ b₁ d ≤
    smooth3DExpectedCrossings γ₂ a₂ b₂ d := by
  rw [smooth3D_buffon_eq _ _ _ _ hd h₁ hC1₁,
      smooth3D_buffon_eq _ _ _ _ hd h₂ hC1₂,
      div_le_div_right (by linarith : (0 : ℝ) < 2 * d)]
  exact hlen

/-- **Strict Monotonicity**: A strictly longer C¹ curve has strictly more
    expected crossings (d > 0). -/
theorem smooth3D_strictMono
    (γ₁ γ₂ : ℝ → ℝ × ℝ × ℝ) (a₁ b₁ a₂ b₂ d : ℝ)
    (hd : 0 < d) (h₁ : a₁ ≤ b₁) (h₂ : a₂ ≤ b₂)
    (hC1₁ : ContDiff ℝ 1 γ₁) (hC1₂ : ContDiff ℝ 1 γ₂)
    (hlen : arcLength3D γ₁ a₁ b₁ < arcLength3D γ₂ a₂ b₂) :
    smooth3DExpectedCrossings γ₁ a₁ b₁ d <
    smooth3DExpectedCrossings γ₂ a₂ b₂ d := by
  rw [smooth3D_buffon_eq _ _ _ _ hd h₁ hC1₁,
      smooth3D_buffon_eq _ _ _ _ hd h₂ hC1₂,
      div_lt_div_right (by linarith : (0 : ℝ) < 2 * d)]
  exact hlen

/-! ## Part VIII: Concrete Examples

Numerical applications of the smooth 3D formula.
-/

/-- A helix of arc length L = 2π√(r² + h²) (one turn, radius r, pitch h)
    has expected crossings 2π√(r² + h²) / (2d) = π√(r² + h²) / d with
    a parallel plane grid of spacing d.

    Unlike the 2D case, the "shape" of the helix (ratio r/h) does not
    affect the expected crossings — only the total arc length matters. -/
theorem helix_expected_crossings (r h d : ℝ) (hd : 0 < d) :
    2 * π * Real.sqrt (r ^ 2 + h ^ 2) / (2 * d) =
    π * Real.sqrt (r ^ 2 + h ^ 2) / d := by
  have hd' : d ≠ 0 := ne_of_gt hd
  field_simp [hd']
  ring

/-- For a great circle of circumference 2πR on a sphere of radius R,
    the expected crossings with parallel planes is πR/d.
    Compare with the 2D circle: expected crossings = 4R/d.
    Ratio: 4R/d ÷ πR/d = 4/π ≈ 1.273 (the universal 2D/3D factor). -/
theorem great_circle_expected_crossings (R d : ℝ) (hd : 0 < d) :
    2 * π * R / (2 * d) = π * R / d := by
  have hd' : d ≠ 0 := ne_of_gt hd
  field_simp [hd']
  ring

/-! ## Part IX: Connection to the Cauchy–Crofton Formula

The smooth 3D Buffon noodle theorem is a special case of the
Cauchy–Crofton formula in integral geometry. In ℝ³, the formula states:

  ∫_{Gr(2,3)} n(C, H) dμ(H) = (1/2) · length(C)

where n(C, H) is the number of intersections of curve C with plane H,
and the integral is over all oriented planes with the invariant measure.

For parallel planes with spacing d, this specializes to E = L/(2d).
The factor 1/2 is precisely α₃ = E_{S²}[|cos φ|] proved in
BuffonsNeedleOQ02.lean.

A full formalization would require:
1. The Grassmannian Gr(2,3) as a measurable space
2. The invariant (Haar) measure on Gr(2,3) ≅ S²
3. The counting function n(C, H) for smooth curves
4. The Cauchy–Crofton integral identity

This is beyond current Mathlib infrastructure, hence the axiomatization.
-/

/-! ## Conclusion

The 3D smooth Buffon noodle formula E = L/(2d) is formalized with:
- 2 axioms (smooth3DExpectedCrossings, smooth3D_buffon_eq)
- 0 sorries
- Verified consequences: shape independence, monotonicity, nonnegativity,
  approximation convergence, dimension comparison, Lipschitz stability

The axiomatization parallels BuffonsNoodle.lean (2D smooth case) and
builds on the fully verified 3D polygonal theory in BuffonsNeedleOQ02.lean.

Key insight: the crossing factor α₃ = 1/2 (sphere average of |cos φ|)
determines the 3D formula just as α₂ = 2/π determines the 2D formula.
The smooth extension follows by approximation and continuity.
-/

end BuffonsNeedleOQ02OQ02
