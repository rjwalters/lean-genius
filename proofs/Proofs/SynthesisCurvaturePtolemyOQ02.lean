import Proofs.PtolemysComplexProof
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Tactic

/-!
# Hyperbolic Ptolemy Theorem in the Poincaré Disk (K = -1)  —  OQ-02

The synthesis file `SynthesisCurvaturePtolemy.lean` unifies the Euclidean
(K = 0) and spherical (K > 0) Ptolemy theorems through its `curvatureSin K`
function, and leaves the **hyperbolic case** (K = -1) as a *conjecture*, with the
remark that a full treatment "requires the Poincaré disk metric as a metric
space (~800-1200 lines), currently blocked in Mathlib".

This file discharges that conjecture as a **fully verified theorem** (no
`sorry`, no `axiom`, no structure-encoded assumption). The observation is that
the heavy metric-space infrastructure is *not needed* for the Ptolemy relation
itself. Everything reduces to the Euclidean `ptolemy_inequality` already proved
in `PtolemysComplexProof.lean`.

## The conformal chord

Define the **conformal chord** of the Poincaré disk `D = {z : ℂ | ‖z‖ < 1}`:

  `poincareChord z w = ‖z - w‖ / √((1 - ‖z‖²)(1 - ‖w‖²))`.

The standard hyperbolic-geometry identity is `poincareChord z w = sinh(d_H/2)`,
where `d_H` is the K = -1 geodesic distance. In the notation of the parent file,
`sinh = curvatureSin (-1)`, so `poincareChord z w = curvatureSin (-1) (d_H/2)`.

## Why the metric machinery is unnecessary

For four points in `D`, every product `poincareChord zᵢ zⱼ · poincareChord zₖ zₗ`
in the Ptolemy relation carries the **same** denominator

  `√((1-‖z₁‖²)(1-‖z₂‖²)(1-‖z₃‖²)(1-‖z₄‖²))`,

because the indices `{i,j,k,l}` are always a permutation of `{1,2,3,4}`. Clearing
that common (strictly positive) denominator turns the hyperbolic Ptolemy
inequality/equality **directly** into the Euclidean one. This "conformal-factor
cancellation" is the entire content of the hyperbolic case — no Poincaré metric
space, Möbius isometries, or hyperbolic-circle theory are required.

## The distance and the sinh bridge

We take the **standard closed form** of the Poincaré disk metric as the
definition of the distance:

  `poincareDist z w = 2 · arsinh( poincareChord z w )`

(equivalently `arcosh(1 + 2 s²)` with `s = poincareChord z w`, using the identity
`arcosh(1 + 2 s²) = 2 · arsinh s`). This is the textbook disk metric. With it,
the bridge identity

  `sinh(poincareDist z w / 2) = sinh(arsinh s) = s = poincareChord z w`

is one line (`Real.sinh_arsinh`), letting us restate the theorems in the exact
`sinh(d_H/2)` form of the parent's conjecture.

## Honesty note

- The reduction to the Euclidean Ptolemy theorem is **unconditional and fully
  machine-checked** (`verified`, 0 sorries / 0 axioms).
- `poincareDist` is *defined* by the standard closed form of the disk metric; we
  do **not** re-derive that this closed form is a genuine metric (triangle
  inequality, Möbius-invariance). No such fact is assumed anywhere below — the
  proofs use only algebra and the Euclidean Ptolemy inequality.
- We phrase the final statements with `Real.sinh` rather than importing the
  parent's `curvatureSin` (which currently sits behind an unrelated
  Mathlib-notation breakage in a sibling file). Since `curvatureSin (-1) = sinh`
  by the parent's `curvatureSin_neg_one`, the statements are identical.

## Results

1. `poincareChord`               — the conformal chord `s(z,w) = sinh(d_H/2)`.
2. `poincareChord_comm`          — symmetry `s(z,w) = s(w,z)`.
3. `hyperbolic_ptolemy_inequality`
                                 — Ptolemy inequality for `s` on four disk points.
4. `hyperbolic_ptolemy_equality` — Ptolemy equality under the proportionality
                                   (concyclicity) condition.
5. `poincareDist` / `sinh_poincareDist_half`
                                 — the disk metric and the `sinh(d_H/2) = s` bridge.
6. `hyperbolic_ptolemy_inequality_sinh` / `hyperbolic_ptolemy_equality_sinh`
                                 — the conjectured statements in `sinh(d_H/2)` form,
                                   discharged.
-/

set_option linter.unusedVariables false

-- ============================================================
-- PART 1: The conformal chord function of the Poincaré disk
-- ============================================================

/-- The **conformal chord** of the Poincaré disk model:

  `poincareChord z w = ‖z - w‖ / √((1 - ‖z‖²)(1 - ‖w‖²))`.

For `z, w` in the open unit disk this equals `sinh(d_H(z,w) / 2)`, where `d_H` is
the hyperbolic (K = -1) geodesic distance. It is the building block of the
hyperbolic Ptolemy relation. -/
noncomputable def poincareChord (z w : ℂ) : ℝ :=
  ‖z - w‖ / Real.sqrt ((1 - ‖z‖ ^ 2) * (1 - ‖w‖ ^ 2))

/-- Inside the open unit disk the conformal factor `1 - ‖z‖²` is strictly
positive. -/
lemma one_sub_normSq_pos {z : ℂ} (hz : ‖z‖ < 1) : 0 < 1 - ‖z‖ ^ 2 := by
  nlinarith [norm_nonneg z, hz]

/-- Split the single square root in `poincareChord` into a product of two square
roots (valid because each conformal factor is nonnegative). -/
lemma poincareChord_eq_div_mul {z w : ℂ} (hz : ‖z‖ < 1) (hw : ‖w‖ < 1) :
    poincareChord z w =
      ‖z - w‖ / (Real.sqrt (1 - ‖z‖ ^ 2) * Real.sqrt (1 - ‖w‖ ^ 2)) := by
  rw [poincareChord, Real.sqrt_mul (one_sub_normSq_pos hz).le]

/-- The conformal chord is symmetric: `poincareChord z w = poincareChord w z`. -/
lemma poincareChord_comm (z w : ℂ) : poincareChord z w = poincareChord w z := by
  unfold poincareChord
  rw [norm_sub_rev, mul_comm (1 - ‖z‖ ^ 2) (1 - ‖w‖ ^ 2)]

-- ============================================================
-- PART 2: Hyperbolic Ptolemy inequality (all four disk points)
-- ============================================================

/-- **Hyperbolic Ptolemy Inequality** in the Poincaré disk.

For any four points `z₁, z₂, z₃, z₄` in the open unit disk,

  `s(z₁,z₃)·s(z₂,z₄) ≤ s(z₁,z₂)·s(z₃,z₄) + s(z₂,z₃)·s(z₁,z₄)`,

where `s = poincareChord = sinh(d_H/2)`. No concyclicity hypothesis is needed.

**Proof.** Each product `s(zᵢ,zⱼ)·s(zₖ,zₗ)` equals
`‖zᵢ-zⱼ‖·‖zₖ-zₗ‖ / √∏ₘ(1-‖zₘ‖²)` — the denominator is the *same* for all three
products because `{i,j,k,l} = {1,2,3,4}`. Dividing the Euclidean
`ptolemy_inequality` by this common positive denominator gives the claim. -/
theorem hyperbolic_ptolemy_inequality (z₁ z₂ z₃ z₄ : ℂ)
    (h1 : ‖z₁‖ < 1) (h2 : ‖z₂‖ < 1) (h3 : ‖z₃‖ < 1) (h4 : ‖z₄‖ < 1) :
    poincareChord z₁ z₃ * poincareChord z₂ z₄ ≤
    poincareChord z₁ z₂ * poincareChord z₃ z₄ +
    poincareChord z₂ z₃ * poincareChord z₁ z₄ := by
  have n1 : Real.sqrt (1 - ‖z₁‖ ^ 2) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.mpr (one_sub_normSq_pos h1))
  have n2 : Real.sqrt (1 - ‖z₂‖ ^ 2) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.mpr (one_sub_normSq_pos h2))
  have n3 : Real.sqrt (1 - ‖z₃‖ ^ 2) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.mpr (one_sub_normSq_pos h3))
  have n4 : Real.sqrt (1 - ‖z₄‖ ^ 2) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.mpr (one_sub_normSq_pos h4))
  -- Express each opposite/diagonal product over the common denominator.
  have e13_24 : poincareChord z₁ z₃ * poincareChord z₂ z₄ =
      ‖z₁ - z₃‖ * ‖z₂ - z₄‖ /
        (Real.sqrt (1 - ‖z₁‖ ^ 2) * Real.sqrt (1 - ‖z₂‖ ^ 2) *
         Real.sqrt (1 - ‖z₃‖ ^ 2) * Real.sqrt (1 - ‖z₄‖ ^ 2)) := by
    rw [poincareChord_eq_div_mul h1 h3, poincareChord_eq_div_mul h2 h4]
    field_simp
    ring
  have e12_34 : poincareChord z₁ z₂ * poincareChord z₃ z₄ =
      ‖z₁ - z₂‖ * ‖z₃ - z₄‖ /
        (Real.sqrt (1 - ‖z₁‖ ^ 2) * Real.sqrt (1 - ‖z₂‖ ^ 2) *
         Real.sqrt (1 - ‖z₃‖ ^ 2) * Real.sqrt (1 - ‖z₄‖ ^ 2)) := by
    rw [poincareChord_eq_div_mul h1 h2, poincareChord_eq_div_mul h3 h4]
    field_simp
    ring
  have e23_14 : poincareChord z₂ z₃ * poincareChord z₁ z₄ =
      ‖z₂ - z₃‖ * ‖z₁ - z₄‖ /
        (Real.sqrt (1 - ‖z₁‖ ^ 2) * Real.sqrt (1 - ‖z₂‖ ^ 2) *
         Real.sqrt (1 - ‖z₃‖ ^ 2) * Real.sqrt (1 - ‖z₄‖ ^ 2)) := by
    rw [poincareChord_eq_div_mul h2 h3, poincareChord_eq_div_mul h1 h4]
    field_simp
    ring
  rw [e13_24, e12_34, e23_14, div_add_div_same]
  gcongr
  exact ptolemy_inequality z₁ z₂ z₃ z₄

-- ============================================================
-- PART 3: Hyperbolic Ptolemy equality (concyclic condition)
-- ============================================================

/-- **Hyperbolic Ptolemy Equality** in the Poincaré disk.

If the opposite-side products of the four disk points are positively
proportional in `ℂ` — the algebraic form of concyclicity in cyclic order,
`(z₂-z₃)(z₁-z₄) = t·(z₁-z₂)(z₃-z₄)` with `t ≥ 0` — then the hyperbolic Ptolemy
inequality is an **equality**:

  `s(z₁,z₃)·s(z₂,z₄) = s(z₁,z₂)·s(z₃,z₄) + s(z₂,z₃)·s(z₁,z₄)`.

Same common-denominator reduction, now to `ptolemy_equality_of_proportional`. -/
theorem hyperbolic_ptolemy_equality (z₁ z₂ z₃ z₄ : ℂ)
    (h1 : ‖z₁‖ < 1) (h2 : ‖z₂‖ < 1) (h3 : ‖z₃‖ < 1) (h4 : ‖z₄‖ < 1)
    (t : ℝ) (ht : 0 ≤ t)
    (hprop : (z₂ - z₃) * (z₁ - z₄) = (t : ℂ) * ((z₁ - z₂) * (z₃ - z₄))) :
    poincareChord z₁ z₃ * poincareChord z₂ z₄ =
    poincareChord z₁ z₂ * poincareChord z₃ z₄ +
    poincareChord z₂ z₃ * poincareChord z₁ z₄ := by
  have n1 : Real.sqrt (1 - ‖z₁‖ ^ 2) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.mpr (one_sub_normSq_pos h1))
  have n2 : Real.sqrt (1 - ‖z₂‖ ^ 2) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.mpr (one_sub_normSq_pos h2))
  have n3 : Real.sqrt (1 - ‖z₃‖ ^ 2) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.mpr (one_sub_normSq_pos h3))
  have n4 : Real.sqrt (1 - ‖z₄‖ ^ 2) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.mpr (one_sub_normSq_pos h4))
  have e13_24 : poincareChord z₁ z₃ * poincareChord z₂ z₄ =
      ‖z₁ - z₃‖ * ‖z₂ - z₄‖ /
        (Real.sqrt (1 - ‖z₁‖ ^ 2) * Real.sqrt (1 - ‖z₂‖ ^ 2) *
         Real.sqrt (1 - ‖z₃‖ ^ 2) * Real.sqrt (1 - ‖z₄‖ ^ 2)) := by
    rw [poincareChord_eq_div_mul h1 h3, poincareChord_eq_div_mul h2 h4]
    field_simp
    ring
  have e12_34 : poincareChord z₁ z₂ * poincareChord z₃ z₄ =
      ‖z₁ - z₂‖ * ‖z₃ - z₄‖ /
        (Real.sqrt (1 - ‖z₁‖ ^ 2) * Real.sqrt (1 - ‖z₂‖ ^ 2) *
         Real.sqrt (1 - ‖z₃‖ ^ 2) * Real.sqrt (1 - ‖z₄‖ ^ 2)) := by
    rw [poincareChord_eq_div_mul h1 h2, poincareChord_eq_div_mul h3 h4]
    field_simp
    ring
  have e23_14 : poincareChord z₂ z₃ * poincareChord z₁ z₄ =
      ‖z₂ - z₃‖ * ‖z₁ - z₄‖ /
        (Real.sqrt (1 - ‖z₁‖ ^ 2) * Real.sqrt (1 - ‖z₂‖ ^ 2) *
         Real.sqrt (1 - ‖z₃‖ ^ 2) * Real.sqrt (1 - ‖z₄‖ ^ 2)) := by
    rw [poincareChord_eq_div_mul h2 h3, poincareChord_eq_div_mul h1 h4]
    field_simp
    ring
  rw [e13_24, e12_34, e23_14, div_add_div_same,
      ptolemy_equality_of_proportional z₁ z₂ z₃ z₄ t ht hprop]

-- ============================================================
-- PART 4: The Poincaré metric and the sinh(d_H/2) bridge
-- ============================================================

/-- The **Poincaré disk distance** in closed form:

  `poincareDist z w = 2 · arsinh( poincareChord z w )`.

This is the standard closed form of the K = -1 hyperbolic metric (equivalently
`arcosh(1 + 2 s²)` with `s = poincareChord z w`). We take it as the definition;
no metric-space axioms are used below. -/
noncomputable def poincareDist (z w : ℂ) : ℝ :=
  2 * Real.arsinh (poincareChord z w)

/-- **Bridge identity**: the hyperbolic sine of the half-distance is exactly the
conformal chord, i.e. `sinh(d_H(z,w)/2) = poincareChord z w`.

In the parent's notation `curvatureSin (-1) = sinh`, so this reads
`curvatureSin (-1) (d_H/2) = poincareChord z w`. It is immediate from
`sinh (arsinh x) = x`. -/
lemma sinh_poincareDist_half (z w : ℂ) :
    Real.sinh (poincareDist z w / 2) = poincareChord z w := by
  have h : poincareDist z w / 2 = Real.arsinh (poincareChord z w) := by
    rw [poincareDist]; ring
  rw [h, Real.sinh_arsinh]

-- ============================================================
-- PART 5: The conjectured statements, in sinh(d_H/2) form
-- ============================================================

/-- **Hyperbolic Ptolemy Inequality — `sinh(d_H/2)` form** (the parent's
conjectured statement, now discharged).

For four points in the open Poincaré disk, with hyperbolic distance `d_H`:

  `sinh(d_H(z₁,z₃)/2) · sinh(d_H(z₂,z₄)/2)`
  `≤ sinh(d_H(z₁,z₂)/2) · sinh(d_H(z₃,z₄)/2)`
  `  + sinh(d_H(z₁,z₄)/2) · sinh(d_H(z₂,z₃)/2)`.

Since `curvatureSin (-1) = sinh`, this is exactly the parent's conjectured
hyperbolic Ptolemy inequality. Via the bridge identity it is
`hyperbolic_ptolemy_inequality`. -/
theorem hyperbolic_ptolemy_inequality_sinh (z₁ z₂ z₃ z₄ : ℂ)
    (h1 : ‖z₁‖ < 1) (h2 : ‖z₂‖ < 1) (h3 : ‖z₃‖ < 1) (h4 : ‖z₄‖ < 1) :
    Real.sinh (poincareDist z₁ z₃ / 2) * Real.sinh (poincareDist z₂ z₄ / 2) ≤
    Real.sinh (poincareDist z₁ z₂ / 2) * Real.sinh (poincareDist z₃ z₄ / 2) +
    Real.sinh (poincareDist z₁ z₄ / 2) * Real.sinh (poincareDist z₂ z₃ / 2) := by
  simp only [sinh_poincareDist_half]
  have key := hyperbolic_ptolemy_inequality z₁ z₂ z₃ z₄ h1 h2 h3 h4
  rw [mul_comm (poincareChord z₁ z₄) (poincareChord z₂ z₃)]
  exact key

/-- **Hyperbolic Ptolemy Equality — `sinh(d_H/2)` form** (the parent's
conjectured statement under the concyclicity/proportionality condition).

Via the bridge identity this is `hyperbolic_ptolemy_equality`. -/
theorem hyperbolic_ptolemy_equality_sinh (z₁ z₂ z₃ z₄ : ℂ)
    (h1 : ‖z₁‖ < 1) (h2 : ‖z₂‖ < 1) (h3 : ‖z₃‖ < 1) (h4 : ‖z₄‖ < 1)
    (t : ℝ) (ht : 0 ≤ t)
    (hprop : (z₂ - z₃) * (z₁ - z₄) = (t : ℂ) * ((z₁ - z₂) * (z₃ - z₄))) :
    Real.sinh (poincareDist z₁ z₃ / 2) * Real.sinh (poincareDist z₂ z₄ / 2) =
    Real.sinh (poincareDist z₁ z₂ / 2) * Real.sinh (poincareDist z₃ z₄ / 2) +
    Real.sinh (poincareDist z₁ z₄ / 2) * Real.sinh (poincareDist z₂ z₃ / 2) := by
  simp only [sinh_poincareDist_half]
  have key := hyperbolic_ptolemy_equality z₁ z₂ z₃ z₄ h1 h2 h3 h4 t ht hprop
  rw [key]; ring

-- ============================================================
-- Summary
-- ============================================================

#check @poincareChord
#check @poincareChord_comm
#check @hyperbolic_ptolemy_inequality
#check @hyperbolic_ptolemy_equality
#check @poincareDist
#check @sinh_poincareDist_half
#check @hyperbolic_ptolemy_inequality_sinh
#check @hyperbolic_ptolemy_equality_sinh
