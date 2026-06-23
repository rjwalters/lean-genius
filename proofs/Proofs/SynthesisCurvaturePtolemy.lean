import Proofs.PtolemysComplexProof
import Proofs.PtolemysTheoremOQ01OQ02
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic

/-!
# Synthesis: Curvature-Parametrized Ptolemy via curvatureSin

This file introduces the `curvatureSin K t` function, which unifies the
trigonometric function appearing in Ptolemy-type theorems across all three
constant-curvature geometries:

- **κ > 0 (spherical)**: `curvatureSin K t = sin(√K · t) / √K`
- **κ = 0 (Euclidean)**: `curvatureSin 0 t = t` (identity function)
- **κ < 0 (hyperbolic)**: `curvatureSin K t = sinh(√|K| · t) / √|K|`

Special cases: `curvatureSin 1 = Real.sin`, `curvatureSin (-1) = Real.sinh`.

## The Unified Ptolemy Theorem

For cyclic quadrilaterals in κ-geometry with curvature K, the Ptolemy equality takes
the form:

  curvatureSin K (d(a,c)/2) · curvatureSin K (d(b,d)/2)
  = curvatureSin K (d(a,b)/2) · curvatureSin K (d(c,d)/2)
  + curvatureSin K (d(a,d)/2) · curvatureSin K (d(b,c)/2)

The Ptolemy **inequality** (≤) holds for ALL quadrilaterals (not just cyclic ones).

## Results Proved

1. `curvatureSin_zero`: curvatureSin 0 t = t (Euclidean case)
2. `curvatureSin_one`: curvatureSin 1 t = sin t (unit sphere)
3. `curvatureSin_neg_one`: curvatureSin (-1) t = sinh t (unit hyperbolic plane)
4. `curvatureSin_zero_right`: curvatureSin K 0 = 0 for any K
5. `curvatureSin_odd`: curvatureSin K (-t) = -curvatureSin K t (odd function)
6. `curvatureSin_hasDerivAt_zero`: HasDerivAt (curvatureSin K) 1 0 (normalization)
7. `curvatureSin_deriv_zero`: deriv (curvatureSin K) 0 = 1
8. `spherical_ptolemy_eq_curvatureSin`: Spherical Ptolemy equality (K=1)
   restated in curvatureSin language — valid for concyclic unit-sphere points
9. `spherical_ptolemy_ineq_curvatureSin`: Spherical Ptolemy INEQUALITY (K=1)
   for ALL four unit-circle points in ℂ — no concyclicity needed

## What's New

`PtolemysTheoremOQ01OQ02.lean` proves the spherical Ptolemy EQUALITY for CYCLIC points.
This file proves the spherical Ptolemy INEQUALITY for ALL unit-circle points in ℂ.

The key insight: the inequality holds unconditionally (only chord-arc + Ptolemy inequality
for ℂ are needed), while equality requires the concyclicity hypothesis.

## Proof Chain for `spherical_ptolemy_ineq_curvatureSin`

1. curvatureSin 1 t = sin t (by curvatureSin_one)
2. Chord-arc identity: ‖z_i - z_j‖ = 2·sin(arccos(⟨z_i,z_j⟩)/2) for unit-circle points
   (from SphericalPtolemy.unit_sphere_chord_via_sin in PtolemysTheoremOQ01OQ02.lean)
3. So sin(arccos(⟨z_i,z_j⟩)/2) = ‖z_i - z_j‖ / 2
4. The inequality reduces to: (‖z₁-z₃‖/2)·(‖z₂-z₄‖/2) ≤ ...
5. Scale by 1/4 from ptolemy_inequality (PtolemysComplexProof.lean)

## Hyperbolic Case (Conjecture)

The K = -1 (hyperbolic) case is stated below with sorry. It requires:
- Poincaré disk metric infrastructure (~800-1200 lines, not in Mathlib)
- Hyperbolic circle definition and conformal factor cancellation
See PtolemysTheoremOQ01OQ02.lean (Hyperbolic Case Survey) for details.
-/

set_option linter.unusedVariables false

open Real EuclideanGeometry

-- ============================================================
-- PART 1: The curvatureSin Function
-- ============================================================

/-- The **curvatureSin K** function for curvature K ∈ ℝ:

- K > 0 (spherical): `curvatureSin K t = sin(√K · t) / √K`
- K = 0 (Euclidean): `curvatureSin 0 t = t`
- K < 0 (hyperbolic): `curvatureSin K t = sinh(√|K| · t) / √|K|`

This is the `sn_K` function from constant-curvature geometry, unifying the
trigonometric/hyperbolic functions in Ptolemy-type theorems across all three
geometries. The K=0 case is the continuous limit: `lim_{K→0} sin(√K·t)/√K = t`.

Special values: `curvatureSin 1 t = sin t`, `curvatureSin (-1) t = sinh t`.
-/
noncomputable def curvatureSin (K t : ℝ) : ℝ :=
  if K = 0 then t
  else if 0 < K then Real.sin (Real.sqrt K * t) / Real.sqrt K
  else Real.sinh (Real.sqrt (-K) * t) / Real.sqrt (-K)

-- ============================================================
-- PART 2: Basic Properties
-- ============================================================

/-- For K = 0, curvatureSin is the identity function: curvatureSin 0 t = t. -/
@[simp]
lemma curvatureSin_zero (t : ℝ) : curvatureSin 0 t = t := by
  simp [curvatureSin]

/-- For K > 0, curvatureSin is sin(√K · t) / √K. -/
lemma curvatureSin_pos {K : ℝ} (hK : 0 < K) (t : ℝ) :
    curvatureSin K t = Real.sin (Real.sqrt K * t) / Real.sqrt K := by
  simp only [curvatureSin, if_neg (ne_of_gt hK), if_pos hK]

/-- For K < 0, curvatureSin is sinh(√|K| · t) / √|K|. -/
lemma curvatureSin_neg {K : ℝ} (hK : K < 0) (t : ℝ) :
    curvatureSin K t = Real.sinh (Real.sqrt (-K) * t) / Real.sqrt (-K) := by
  simp only [curvatureSin, if_neg (ne_of_lt hK), if_neg (not_lt.mpr (le_of_lt hK))]

/-- For K = 1 (unit sphere), curvatureSin 1 t = sin t.

This follows from sin(√1 · t) / √1 = sin(t) / 1 = sin(t). -/
lemma curvatureSin_one (t : ℝ) : curvatureSin 1 t = Real.sin t := by
  rw [curvatureSin_pos one_pos, Real.sqrt_one, one_mul, div_one]

/-- For K = -1 (unit hyperbolic plane), curvatureSin (-1) t = sinh t.

This follows from sinh(√1 · t) / √1 = sinh(t) / 1 = sinh(t). -/
lemma curvatureSin_neg_one (t : ℝ) : curvatureSin (-1) t = Real.sinh t := by
  rw [curvatureSin_neg (by norm_num : (-1 : ℝ) < 0)]
  have h : -(-1 : ℝ) = 1 := by norm_num
  rw [h, Real.sqrt_one, one_mul, div_one]

/-- curvatureSin K 0 = 0 for any K. This is consistent with curvatureSin being an
odd function with curvatureSin K 0 = 0 in all three geometries. -/
@[simp]
lemma curvatureSin_zero_right (K : ℝ) : curvatureSin K 0 = 0 := by
  unfold curvatureSin
  split_ifs <;> simp [Real.sin_zero, Real.sinh_zero]

-- ============================================================
-- PART 2b: Structural Properties
-- ============================================================

/-- **Oddness**: curvatureSin K is an odd function of t.

Since sin and sinh are both odd, and the K=0 case is the identity (also odd),
curvatureSin K (-t) = -curvatureSin K t for all K and t. -/
lemma curvatureSin_odd (K t : ℝ) : curvatureSin K (-t) = -curvatureSin K t := by
  unfold curvatureSin
  split_ifs with hK0 hKpos
  · ring
  · rw [mul_neg, Real.sin_neg, neg_div]
  · rw [mul_neg, Real.sinh_neg, neg_div]

/-- Auxiliary: HasDerivAt for Real.sinh. The derivative of sinh is cosh. -/
private theorem hasDerivAt_sinh (x : ℝ) : HasDerivAt Real.sinh (Real.cosh x) x := by
  have h1 := Real.hasDerivAt_exp x
  have h2 := (Real.hasDerivAt_exp (-x)).comp x (hasDerivAt_neg x)
  have hsinhDef : Real.sinh = fun y => (Real.exp y - Real.exp (-y)) / 2 := by
    ext y; exact Real.sinh_eq y
  rw [hsinhDef]
  have hcoshEq : Real.cosh x = (Real.exp x + Real.exp (-x)) / 2 := Real.cosh_eq x
  rw [hcoshEq]
  convert (h1.sub h2).div_const 2 using 1
  ring

/-- **Normalization**: The derivative of curvatureSin K at t = 0 is 1 for all K.

This is the defining normalization condition for the sn_K function:
- K = 0: d/dt [t] |₀ = 1
- K > 0: d/dt [sin(√K·t)/√K] |₀ = cos(0) = 1
- K < 0: d/dt [sinh(√|K|·t)/√|K|] |₀ = cosh(0) = 1

Together with curvatureSin K 0 = 0, this characterizes curvatureSin K as the
unique solution to y'' + K·y = 0 with y(0) = 0, y'(0) = 1. -/
theorem curvatureSin_hasDerivAt_zero (K : ℝ) : HasDerivAt (curvatureSin K) 1 0 := by
  by_cases hK0 : K = 0
  · -- K = 0: curvatureSin 0 = id, derivative is 1
    subst hK0
    have hfun : curvatureSin 0 = id := by ext t; simp [curvatureSin]
    rw [hfun]
    exact hasDerivAt_id 0
  · by_cases hKpos : 0 < K
    · -- K > 0: d/dt [sin(√K·t)/√K] |₀ = cos(0)·√K/√K = 1
      have hS : (Real.sqrt K : ℝ) ≠ 0 := Real.sqrt_ne_zero'.mpr hKpos
      have hfun : curvatureSin K = fun t => Real.sin (Real.sqrt K * t) / Real.sqrt K := by
        ext t; simp [curvatureSin, if_neg hK0, if_pos hKpos]
      rw [hfun]
      have h1 : HasDerivAt (fun t => Real.sqrt K * t) (Real.sqrt K) 0 :=
        (hasDerivAt_id 0).const_mul (Real.sqrt K)
      have h2 : HasDerivAt Real.sin (Real.cos (Real.sqrt K * 0)) (Real.sqrt K * 0) :=
        Real.hasDerivAt_sin (Real.sqrt K * 0)
      have h3 : HasDerivAt (fun t => Real.sin (Real.sqrt K * t))
          (Real.cos (Real.sqrt K * 0) * Real.sqrt K) 0 :=
        h2.comp 0 h1
      have h4 : HasDerivAt (fun t => Real.sin (Real.sqrt K * t) / Real.sqrt K)
          (Real.cos (Real.sqrt K * 0) * Real.sqrt K / Real.sqrt K) 0 :=
        h3.div_const (Real.sqrt K)
      simp only [mul_zero, Real.cos_zero, one_mul, div_self hS] at h4
      exact h4
    · -- K < 0: d/dt [sinh(√|K|·t)/√|K|] |₀ = cosh(0)·√|K|/√|K| = 1
      have hKneg : K < 0 := lt_of_le_of_ne (not_lt.mp hKpos) hK0
      have hNK : (0 : ℝ) < -K := neg_pos.mpr hKneg
      have hS : (Real.sqrt (-K) : ℝ) ≠ 0 := Real.sqrt_ne_zero'.mpr hNK
      have hfun : curvatureSin K = fun t => Real.sinh (Real.sqrt (-K) * t) / Real.sqrt (-K) := by
        ext t; simp [curvatureSin, if_neg hK0, if_neg (not_lt.mpr (le_of_lt hKneg))]
      rw [hfun]
      have h1 : HasDerivAt (fun t => Real.sqrt (-K) * t) (Real.sqrt (-K)) 0 :=
        (hasDerivAt_id 0).const_mul (Real.sqrt (-K))
      have h2 : HasDerivAt Real.sinh (Real.cosh (Real.sqrt (-K) * 0)) (Real.sqrt (-K) * 0) :=
        hasDerivAt_sinh (Real.sqrt (-K) * 0)
      have h3 : HasDerivAt (fun t => Real.sinh (Real.sqrt (-K) * t))
          (Real.cosh (Real.sqrt (-K) * 0) * Real.sqrt (-K)) 0 :=
        h2.comp 0 h1
      have h4 : HasDerivAt (fun t => Real.sinh (Real.sqrt (-K) * t) / Real.sqrt (-K))
          (Real.cosh (Real.sqrt (-K) * 0) * Real.sqrt (-K) / Real.sqrt (-K)) 0 :=
        h3.div_const (Real.sqrt (-K))
      simp only [mul_zero, Real.cosh_zero, one_mul, div_self hS] at h4
      exact h4

/-- The derivative of curvatureSin K at 0 equals 1 (corollary using `deriv`). -/
theorem curvatureSin_deriv_zero (K : ℝ) : deriv (curvatureSin K) 0 = 1 :=
  (curvatureSin_hasDerivAt_zero K).deriv

-- ============================================================
-- PART 3: Spherical Ptolemy Equality in curvatureSin 1 Language
-- ============================================================

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- **Spherical Ptolemy Equality** (curvatureSin 1 formulation)

For four unit-sphere points in a real inner product space, on a common circle,
with diagonals crossing at p, the Ptolemy equality holds in curvatureSin 1:

  curvatureSin 1 (d(a,c)/2) · curvatureSin 1 (d(b,d)/2)
  = curvatureSin 1 (d(a,b)/2) · curvatureSin 1 (d(c,d)/2)
  + curvatureSin 1 (d(a,d)/2) · curvatureSin 1 (d(b,c)/2)

where d(x,y) = arccos(⟨x,y⟩) is the spherical geodesic distance.

**Proof**: Since curvatureSin 1 t = sin t, this is the direct restatement of
`SphericalPtolemy.spherical_ptolemy` (PtolemysTheoremOQ01OQ02.lean).

**Equality requires concyclicity** (Cospherical + angle condition at p). The
corresponding inequality without these conditions is proved separately in
`spherical_ptolemy_ineq_curvatureSin`.
-/
theorem spherical_ptolemy_eq_curvatureSin {a b c d p : V}
    (h_cosph : Cospherical ({a, b, c, d} : Set V))
    (h_apc : ∠ a p c = Real.pi)
    (h_bpd : ∠ b p d = Real.pi)
    (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hc : ‖c‖ = 1) (hd : ‖d‖ = 1) :
    curvatureSin 1 (arccos ⟪a, c⟫_ℝ / 2) * curvatureSin 1 (arccos ⟪b, d⟫_ℝ / 2) =
    curvatureSin 1 (arccos ⟪a, b⟫_ℝ / 2) * curvatureSin 1 (arccos ⟪c, d⟫_ℝ / 2) +
    curvatureSin 1 (arccos ⟪a, d⟫_ℝ / 2) * curvatureSin 1 (arccos ⟪b, c⟫_ℝ / 2) := by
  simp only [curvatureSin_one]
  exact SphericalPtolemy.spherical_ptolemy h_cosph h_apc h_bpd ha hb hc hd

-- ============================================================
-- PART 4: Spherical Ptolemy Inequality (NEW)
-- ============================================================

/-- **Spherical Ptolemy Inequality** (curvatureSin 1 formulation) — **NEW**

For any four unit-circle points in ℂ (NOT necessarily concyclic), the Ptolemy
inequality holds:

  curvatureSin 1 (d(z₁,z₃)/2) · curvatureSin 1 (d(z₂,z₄)/2)
  ≤ curvatureSin 1 (d(z₁,z₂)/2) · curvatureSin 1 (d(z₃,z₄)/2)
  + curvatureSin 1 (d(z₂,z₃)/2) · curvatureSin 1 (d(z₁,z₄)/2)

where d(z_i, z_j) = arccos(⟨z_i, z_j⟩_ℝ) is the spherical arc distance.

**Equality** holds if and only if the four points are concyclic in cyclic order
(the equality direction from `spherical_ptolemy_eq_curvatureSin`).

**Proof**:
1. curvatureSin 1 t = sin t  (curvatureSin_one)
2. Chord-arc identity: ‖z_i - z_j‖ = 2·sin(arccos(⟨z_i,z_j⟩)/2)
   (SphericalPtolemy.unit_sphere_chord_via_sin — unit circle points in ℂ viewed as ℝ-IPS)
3. So sin(arccos(⟨z_i,z_j⟩)/2) = ‖z_i - z_j‖ / 2
4. Substituting, goal becomes: ‖z₁-z₃‖/2·‖z₂-z₄‖/2 ≤ ‖z₁-z₂‖/2·‖z₃-z₄‖/2 + ‖z₂-z₃‖/2·‖z₁-z₄‖/2
5. This is ptolemy_inequality / 4  (ptolemy_inequality from PtolemysComplexProof.lean)
-/
theorem spherical_ptolemy_ineq_curvatureSin (z₁ z₂ z₃ z₄ : ℂ)
    (h1 : ‖z₁‖ = 1) (h2 : ‖z₂‖ = 1) (h3 : ‖z₃‖ = 1) (h4 : ‖z₄‖ = 1) :
    curvatureSin 1 (arccos (⟪z₁, z₃⟫_ℝ) / 2) * curvatureSin 1 (arccos (⟪z₂, z₄⟫_ℝ) / 2) ≤
    curvatureSin 1 (arccos (⟪z₁, z₂⟫_ℝ) / 2) * curvatureSin 1 (arccos (⟪z₃, z₄⟫_ℝ) / 2) +
    curvatureSin 1 (arccos (⟪z₂, z₃⟫_ℝ) / 2) * curvatureSin 1 (arccos (⟪z₁, z₄⟫_ℝ) / 2) := by
  simp only [curvatureSin_one]
  -- Step 1: Chord-arc identity for unit circle points in ℂ (ℂ is an ℝ-inner product space)
  have h13 : ‖z₁ - z₃‖ = 2 * sin (arccos (⟪z₁, z₃⟫_ℝ) / 2) :=
    SphericalPtolemy.unit_sphere_chord_via_sin h1 h3
  have h24 : ‖z₂ - z₄‖ = 2 * sin (arccos (⟪z₂, z₄⟫_ℝ) / 2) :=
    SphericalPtolemy.unit_sphere_chord_via_sin h2 h4
  have h12 : ‖z₁ - z₂‖ = 2 * sin (arccos (⟪z₁, z₂⟫_ℝ) / 2) :=
    SphericalPtolemy.unit_sphere_chord_via_sin h1 h2
  have h34 : ‖z₃ - z₄‖ = 2 * sin (arccos (⟪z₃, z₄⟫_ℝ) / 2) :=
    SphericalPtolemy.unit_sphere_chord_via_sin h3 h4
  have h23 : ‖z₂ - z₃‖ = 2 * sin (arccos (⟪z₂, z₃⟫_ℝ) / 2) :=
    SphericalPtolemy.unit_sphere_chord_via_sin h2 h3
  have h14 : ‖z₁ - z₄‖ = 2 * sin (arccos (⟪z₁, z₄⟫_ℝ) / 2) :=
    SphericalPtolemy.unit_sphere_chord_via_sin h1 h4
  -- Step 2: Express sin values as half chord lengths
  have s13 : sin (arccos (⟪z₁, z₃⟫_ℝ) / 2) = ‖z₁ - z₃‖ / 2 := by linarith
  have s24 : sin (arccos (⟪z₂, z₄⟫_ℝ) / 2) = ‖z₂ - z₄‖ / 2 := by linarith
  have s12 : sin (arccos (⟪z₁, z₂⟫_ℝ) / 2) = ‖z₁ - z₂‖ / 2 := by linarith
  have s34 : sin (arccos (⟪z₃, z₄⟫_ℝ) / 2) = ‖z₃ - z₄‖ / 2 := by linarith
  have s23 : sin (arccos (⟪z₂, z₃⟫_ℝ) / 2) = ‖z₂ - z₃‖ / 2 := by linarith
  have s14 : sin (arccos (⟪z₁, z₄⟫_ℝ) / 2) = ‖z₁ - z₄‖ / 2 := by linarith
  -- Step 3: Rewrite goal in terms of chord lengths
  rw [s13, s24, s12, s34, s23, s14]
  -- Goal: ‖z₁-z₃‖/2 * (‖z₂-z₄‖/2) ≤ ‖z₁-z₂‖/2 * (‖z₃-z₄‖/2) + ‖z₂-z₃‖/2 * (‖z₁-z₄‖/2)
  -- Step 4: Scale by 1/4 from ptolemy_inequality
  have hP := ptolemy_inequality z₁ z₂ z₃ z₄
  -- hP : ‖z₁-z₃‖ * ‖z₂-z₄‖ ≤ ‖z₁-z₂‖ * ‖z₃-z₄‖ + ‖z₂-z₃‖ * ‖z₁-z₄‖
  have lhs_eq : ‖z₁ - z₃‖ / 2 * (‖z₂ - z₄‖ / 2) = ‖z₁ - z₃‖ * ‖z₂ - z₄‖ / 4 := by ring
  have rhs_eq : ‖z₁ - z₂‖ / 2 * (‖z₃ - z₄‖ / 2) + ‖z₂ - z₃‖ / 2 * (‖z₁ - z₄‖ / 2) =
                (‖z₁ - z₂‖ * ‖z₃ - z₄‖ + ‖z₂ - z₃‖ * ‖z₁ - z₄‖) / 4 := by ring
  rw [lhs_eq, rhs_eq]
  linarith

-- ============================================================
-- PART 5: Hyperbolic Case (Conjecture — K < 0)
-- ============================================================

/-!
## Hyperbolic Ptolemy Theorem (Conjecture for K = -1)

For four points on a common hyperbolic circle in the Poincaré disk D = {z : ℂ | ‖z‖ < 1},
with hyperbolic geodesic distance `d_H`, the unified Ptolemy theorem should give:

  curvatureSin (-1) (d_H(z₁,z₃)/2) · curvatureSin (-1) (d_H(z₂,z₄)/2)
  = curvatureSin (-1) (d_H(z₁,z₂)/2) · curvatureSin (-1) (d_H(z₃,z₄)/2)
  + curvatureSin (-1) (d_H(z₁,z₄)/2) · curvatureSin (-1) (d_H(z₂,z₃)/2)

i.e. (since curvatureSin (-1) t = sinh t):

  sinh(d_H(z₁,z₃)/2) · sinh(d_H(z₂,z₄)/2)
  = sinh(d_H(z₁,z₂)/2) · sinh(d_H(z₃,z₄)/2) + sinh(d_H(z₁,z₄)/2) · sinh(d_H(z₂,z₃)/2)

The key identity `sinh(d_H(z,w)/2) = |z - w| / √((1-|z|²)(1-|w|²))` requires:
1. Poincaré disk metric as a metric space structure in Lean (~300 lines)
2. Möbius transformations as hyperbolic isometries (~400-500 lines)
3. Hyperbolic circle = Euclidean circle in D + conformal factor cancellation (~200 lines)

**Total infrastructure**: ~800-1200 lines (currently blocked in Mathlib).
See the Hyperbolic Case Survey in PtolemysTheoremOQ01OQ02.lean for details.
-/

-- ============================================================
-- Summary
-- ============================================================

#check @curvatureSin
#check @curvatureSin_zero
#check @curvatureSin_one
#check @curvatureSin_neg_one
#check @curvatureSin_zero_right
#check @curvatureSin_odd
#check @curvatureSin_hasDerivAt_zero
#check @curvatureSin_deriv_zero
#check @spherical_ptolemy_eq_curvatureSin
#check @spherical_ptolemy_ineq_curvatureSin

