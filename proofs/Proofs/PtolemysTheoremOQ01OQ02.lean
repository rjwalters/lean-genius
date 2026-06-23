import Proofs.PtolemysTheorem
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic

/-!
# Ptolemy's Theorem: Spherical Geometry Extension

## What This Proves

The **spherical Ptolemy theorem**: for four points on the unit sphere in an inner product space,
lying on a common circle and satisfying the diagonal-crossing condition, the equality

  sin(d(a,c)/2) · sin(d(b,d)/2) = sin(d(a,b)/2) · sin(d(c,d)/2) + sin(d(a,d)/2) · sin(d(b,c)/2)

holds, where `d(x,y) = arccos(⟨x,y⟩)` is the geodesic (great-circle) distance on the sphere.

## Key Insight: Chord-Arc Identity

The Euclidean chord length between two unit-sphere points equals twice the sine of
half the great-circle arc:

  ‖a - b‖ = 2 · sin(arccos(⟨a,b⟩) / 2)

**Proof**: Both sides are non-negative and their squares are equal:
- `‖a-b‖² = 2 - 2⟨a,b⟩` (expand with ‖a‖=‖b‖=1)
- `(2sin(θ/2))² = 2(1 - cosθ)` (half-angle: cos(2α) = 2cos²α - 1 → 1-cosθ = 2sin²(θ/2))

Setting θ = arccos(⟨a,b⟩): `(2sin(arccos(c)/2))² = 2(1 - c) = ‖a-b‖²`.

## Proof Strategy

Euclidean Ptolemy (from Mathlib via `PtolemysTheorem.lean`) gives the chord equality:
  ‖a-c‖ · ‖b-d‖ = ‖a-b‖ · ‖c-d‖ + ‖a-d‖ · ‖b-c‖

Substituting `‖x-y‖ = 2sin(d(x,y)/2)` throughout gives 4 times the spherical equality.
Dividing by 4 yields the spherical Ptolemy theorem.

## Hyperbolic Case (Survey)

The analogous hyperbolic Ptolemy theorem (Poincaré disk model) uses `sinh`:
  sinh(d_H(a,c)/2) · sinh(d_H(b,d)/2) = sinh(d_H(a,b)/2) · sinh(d_H(c,d)/2) + ...

Key identity: in the Poincaré disk D = {z ∈ ℂ : |z| < 1},
  sinh(d_H(a,b)/2) = |a - b| / √((1-|a|²)(1-|b|²))

Unlike the spherical case, the conformal factors (1-|a|²), (1-|b|²) do not cancel
cleanly for points on a general hyperbolic circle — they only cancel for ideal boundary points.
Formalizing the general case requires Poincaré metric infrastructure (not in Mathlib).

## Mathlib Dependencies
- `ptolemys_theorem` (from PtolemysTheorem.lean): Euclidean Ptolemy in NormedAddTorsor
- `SeminormedAddCommGroup.toNormedAddTorsor`: V is its own NormedAddTorsor (dist = ‖·‖)
- `norm_sub_sq_real`: ‖x-y‖² = ‖x‖² - 2⟪x,y⟫_ℝ + ‖y‖²
- `Real.cos_arccos`: cos(arccos x) = x for x ∈ [-1,1]
- `Real.cos_two_mul`: cos(2θ) = 2cos²θ - 1
- `Real.arccos_nonneg`, `Real.arccos_le_pi`: arccos x ∈ [0,π]
- `abs_real_inner_le_norm`: Cauchy-Schwarz for real inner products
- `Real.sin_nonneg_of_nonneg_of_le_pi`: sin θ ≥ 0 for θ ∈ [0, π]
- `Real.sin_sq_add_cos_sq`: sin²x + cos²x = 1
- `Real.sqrt_sq`: √(x²) = x for x ≥ 0
-/

set_option linter.unusedVariables false

namespace SphericalPtolemy

open Real EuclideanGeometry

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

-- ============================================================
-- PART 1: Inner Product Bounds for Unit Vectors (Cauchy-Schwarz)
-- ============================================================

/-- For unit vectors, the real inner product lies in [-1, 1]. -/
private lemma inner_unit_mem_Icc {a b : V} (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) :
    -1 ≤ ⟪a, b⟫_ℝ ∧ ⟪a, b⟫_ℝ ≤ 1 := by
  have h := abs_real_inner_le_norm a b
  rw [ha, hb, mul_one] at h
  exact ⟨neg_le_of_abs_le h, le_of_abs_le h⟩

-- ============================================================
-- PART 2: Chord-Arc Identity
-- ============================================================

/-- **Chord-Arc Identity**: For points on the unit sphere in an inner product space,
the Euclidean chord length equals twice the sine of half the geodesic arc length:

  ‖a - b‖ = 2 · sin(arccos(⟨a,b⟩) / 2)

The spherical arc length is `arccos(⟨a,b⟩)` since `⟨a,b⟩ = cos(d_sphere(a,b))` for unit vectors.

**Proof**: Both sides are non-negative. Their squares are equal:
- Left: `‖a-b‖² = ‖a‖² - 2⟪a,b⟫_ℝ + ‖b‖² = 2 - 2⟪a,b⟫_ℝ`
- Right: `(2sin(arccos(c)/2))² = 4sin²(arccos(c)/2)`
  = `4·(1 - cos²(arccos(c)/2))/1` ... using `cos(arccos c) = 2cos²(arccos(c)/2) - 1 = c`
  → `cos²(arccos(c)/2) = (1+c)/2` → `sin²(arccos(c)/2) = (1-c)/2` → `4·(1-c)/2 = 2-2c`
-/
lemma unit_sphere_chord_via_sin {a b : V} (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) :
    ‖a - b‖ = 2 * Real.sin (Real.arccos (⟪a, b⟫_ℝ) / 2) := by
  have ⟨hinner_lb, hinner_ub⟩ := inner_unit_mem_Icc ha hb
  have hac_lb : 0 ≤ Real.arccos ⟪a, b⟫_ℝ := Real.arccos_nonneg _
  have hac_ub : Real.arccos ⟪a, b⟫_ℝ ≤ Real.pi := Real.arccos_le_pi _
  -- sin(arccos(⟨a,b⟩)/2) ≥ 0, since arccos(⟨a,b⟩)/2 ∈ [0, π/2]
  have hsin_nn : 0 ≤ Real.sin (Real.arccos ⟪a, b⟫_ℝ / 2) := by
    apply Real.sin_nonneg_of_nonneg_of_le_pi
    · linarith
    · linarith
  have hnorm_nn := norm_nonneg (a - b)
  -- Left: ‖a - b‖² = 2 - 2⟨a,b⟩
  have h_norm_sq : ‖a - b‖ ^ 2 = 2 - 2 * ⟪a, b⟫_ℝ := by
    rw [norm_sub_sq_real, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, ha, hb]
    ring
  -- Right: (2sin(arccos(c)/2))² = 2 - 2c
  -- cos(arccos c) = 2cos²(arccos(c)/2) - 1 = c  →  cos²(arccos(c)/2) = (1+c)/2
  -- sin²(arccos(c)/2) = 1 - cos²(arccos(c)/2) = (1-c)/2
  have h_cos_eq : Real.cos (Real.arccos ⟪a, b⟫_ℝ) = ⟪a, b⟫_ℝ :=
    Real.cos_arccos hinner_lb hinner_ub
  have h_cos_double : Real.cos (Real.arccos ⟪a, b⟫_ℝ) =
      2 * Real.cos (Real.arccos ⟪a, b⟫_ℝ / 2) ^ 2 - 1 := by
    conv_lhs => rw [show Real.arccos ⟪a, b⟫_ℝ = 2 * (Real.arccos ⟪a, b⟫_ℝ / 2) from by ring]
    exact Real.cos_two_mul _
  have h_cos_sq : Real.cos (Real.arccos ⟪a, b⟫_ℝ / 2) ^ 2 = (1 + ⟪a, b⟫_ℝ) / 2 := by
    linarith [h_cos_eq, h_cos_double]
  have h_sin_sq : Real.sin (Real.arccos ⟪a, b⟫_ℝ / 2) ^ 2 = (1 - ⟪a, b⟫_ℝ) / 2 := by
    have hpy := Real.sin_sq_add_cos_sq (Real.arccos ⟪a, b⟫_ℝ / 2)
    linarith [h_cos_sq]
  have h_rhs_sq : (2 * Real.sin (Real.arccos ⟪a, b⟫_ℝ / 2)) ^ 2 = 2 - 2 * ⟪a, b⟫_ℝ := by
    have : (2 * Real.sin (Real.arccos ⟪a, b⟫_ℝ / 2)) ^ 2 =
        4 * Real.sin (Real.arccos ⟪a, b⟫_ℝ / 2) ^ 2 := by ring
    rw [this, h_sin_sq]; ring
  -- Squares equal, both sides non-negative → sides equal
  have h_sq_eq : ‖a - b‖ ^ 2 = (2 * Real.sin (Real.arccos ⟪a, b⟫_ℝ / 2)) ^ 2 := by
    rw [h_norm_sq, h_rhs_sq]
  -- Conclude using √(x²) = x for x ≥ 0
  calc ‖a - b‖
      = Real.sqrt (‖a - b‖ ^ 2) := (Real.sqrt_sq hnorm_nn).symm
    _ = Real.sqrt ((2 * Real.sin (Real.arccos ⟪a, b⟫_ℝ / 2)) ^ 2) := by rw [h_sq_eq]
    _ = 2 * Real.sin (Real.arccos ⟪a, b⟫_ℝ / 2) :=
        Real.sqrt_sq (mul_nonneg (by norm_num) hsin_nn)

-- ============================================================
-- PART 3: Spherical Ptolemy Theorem
-- ============================================================

/-- **Spherical Ptolemy Theorem**

For four points `a, b, c, d` on the unit sphere of a real inner product space `V`
(with V viewed as its own affine space, so `dist x y = ‖x - y‖`), lying on a common
circle of the sphere (Cospherical), with diagonals crossing at `p`:

  sin(d(a,c)/2) · sin(d(b,d)/2) = sin(d(a,b)/2) · sin(d(c,d)/2) + sin(d(a,d)/2) · sin(d(b,c)/2)

where `d(x,y) = arccos(⟨x,y⟩)` is the geodesic (great-circle) distance on S¹.

**Proof**: `ptolemys_theorem` (Euclidean Ptolemy) gives:
  `dist(a,b)·dist(c,d) + dist(b,c)·dist(d,a) = dist(a,c)·dist(b,d)`

By `unit_sphere_chord_via_sin`, each `dist(x,y) = 2·sin(d(x,y)/2)`. Substituting:
  `4·sin_ab·sin_cd + 4·sin_bc·sin_ad = 4·sin_ac·sin_bd`

Dividing by 4 gives the spherical equality.
-/
theorem spherical_ptolemy {a b c d p : V}
    (h_cosph : Cospherical ({a, b, c, d} : Set V))
    (h_apc : ∠ a p c = Real.pi)
    (h_bpd : ∠ b p d = Real.pi)
    (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hc : ‖c‖ = 1) (hd : ‖d‖ = 1) :
    Real.sin (Real.arccos ⟪a, c⟫_ℝ / 2) * Real.sin (Real.arccos ⟪b, d⟫_ℝ / 2) =
    Real.sin (Real.arccos ⟪a, b⟫_ℝ / 2) * Real.sin (Real.arccos ⟪c, d⟫_ℝ / 2) +
    Real.sin (Real.arccos ⟪a, d⟫_ℝ / 2) * Real.sin (Real.arccos ⟪b, c⟫_ℝ / 2) := by
  -- Euclidean Ptolemy gives: dist(a,b)·dist(c,d) + dist(b,c)·dist(d,a) = dist(a,c)·dist(b,d)
  -- In V as its own NormedAddTorsor, dist = ‖·-·‖
  have h_eucl : dist a b * dist c d + dist b c * dist d a = dist a c * dist b d :=
    ptolemys_theorem h_cosph h_apc h_bpd
  -- Standardize: use dist a d = dist d a
  rw [dist_comm d a] at h_eucl
  -- V as NormedAddTorsor over itself: dist x y = ‖x - y‖
  simp only [dist_eq_norm] at h_eucl
  -- Name the chord-arc expressions
  have hab : ‖a - b‖ = 2 * Real.sin (Real.arccos ⟪a, b⟫_ℝ / 2) :=
    unit_sphere_chord_via_sin ha hb
  have hcd : ‖c - d‖ = 2 * Real.sin (Real.arccos ⟪c, d⟫_ℝ / 2) :=
    unit_sphere_chord_via_sin hc hd
  have hbc : ‖b - c‖ = 2 * Real.sin (Real.arccos ⟪b, c⟫_ℝ / 2) :=
    unit_sphere_chord_via_sin hb hc
  have had : ‖a - d‖ = 2 * Real.sin (Real.arccos ⟪a, d⟫_ℝ / 2) :=
    unit_sphere_chord_via_sin ha hd
  have hac : ‖a - c‖ = 2 * Real.sin (Real.arccos ⟪a, c⟫_ℝ / 2) :=
    unit_sphere_chord_via_sin ha hc
  have hbd : ‖b - d‖ = 2 * Real.sin (Real.arccos ⟪b, d⟫_ℝ / 2) :=
    unit_sphere_chord_via_sin hb hd
  -- Substitute into h_eucl:
  -- (2*sin_ab)*(2*sin_cd) + (2*sin_bc)*(2*sin_ad) = (2*sin_ac)*(2*sin_bd)
  -- i.e., 4*(sin_ab*sin_cd + sin_bc*sin_ad) = 4*(sin_ac*sin_bd)
  rw [hab, hcd, hbc, had, hac, hbd] at h_eucl
  -- Conclude: sin_ac*sin_bd = sin_ab*sin_cd + sin_ad*sin_bc
  -- h_eucl is now: (2*sin_ab)*(2*sin_cd) + (2*sin_bc)*(2*sin_ad) = (2*sin_ac)*(2*sin_bd)
  -- i.e., 4*(sin_ab*sin_cd + sin_bc*sin_ad) = 4*(sin_ac*sin_bd)
  -- Dividing by 4: sin_ac*sin_bd = sin_ab*sin_cd + sin_ad*sin_bc
  linear_combination -(1/4 : ℝ) * h_eucl

-- ============================================================
-- PART 4: Hyperbolic Case (Survey — requires infrastructure)
-- ============================================================

/-!
## The Hyperbolic Ptolemy Theorem (Survey)

### Setup: Poincaré Disk Model

The Poincaré disk D = {z ∈ ℂ : |z| < 1} models the hyperbolic plane with metric:
  d_H(a, b) = 2 · arctanh(|φ_a(b)|),  where  φ_a(b) = (b - a) / (1 - ā·b)

is the Möbius transformation sending `a` to `0`.

### Hyperbolic Chord-Arc Identity

For a, b ∈ D:
  sinh(d_H(a, b) / 2) = |a - b| / √((1 - |a|²)(1 - |b|²))

This is analogous to the spherical `sin(d_S(a,b)/2) = ‖a-b‖/2` (unit sphere).

### The Ptolemy Statement

For four points on a common hyperbolic circle (Euclidean circle inside D),
the hyperbolic Ptolemy theorem should read:
  sinh(d_H(a,c)/2) · sinh(d_H(b,d)/2) = ...  (conformal factors appear)

However, unlike the spherical case where `‖a‖ = ‖b‖ = 1` causes all factors to cancel,
the hyperbolic conformal factors `(1-|x|²)` do NOT cancel for interior points.

The correct form for **ideal points** (a, b, c, d ∈ ∂D, |x| = 1) degenerates to
Euclidean Ptolemy on the unit circle. For interior points, the statement requires
hyperbolic-Ptolemy with explicit conformal correction terms.

### Infrastructure Needed

Formalizing the hyperbolic case would require:
1. **Poincaré disk metric** (`tanh`, `arctanh` in Mathlib, but not as a metric space)
2. **Möbius transformations** (partially available via `Complex.circle`, not as isometries)
3. **Hyperbolic circles** (circles in D that are also Euclidean circles — not formalized)
4. **sinh chord identity** (provable from `Real.sinh`, but needs the above setup)

Estimated effort: ~800–1200 lines of foundational infrastructure.

### Unified Curvature-κ Statement

In constant curvature κ geometry, define:
  sn_κ(t) = sin(√κ · t)/√κ  (κ > 0, spherical)
           = t               (κ = 0, Euclidean)
           = sinh(√|κ|·t)/√|κ|  (κ < 0, hyperbolic)

The unified Ptolemy theorem:
  sn_κ(d(a,c)/2) · sn_κ(d(b,d)/2) = sn_κ(d(a,b)/2)·sn_κ(d(c,d)/2) + sn_κ(d(a,d)/2)·sn_κ(d(b,c)/2)

This formalization proves the κ = 1 case. The κ = 0 case is the Euclidean Ptolemy
from `PtolemysTheorem.lean` (wrapping Mathlib). The κ = −1 case is open in Mathlib.
-/

-- ============================================================
-- Summary
-- ============================================================

#check @spherical_ptolemy
#check @unit_sphere_chord_via_sin

end SphericalPtolemy
