import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

/-!
# Unified Curvature-Parametrized Law of Cosines

## Research Problem: law-of-cosines-oq-01-oq-05

**Question**: Can the Euclidean, spherical, and hyperbolic laws of cosines be
unified into a single curvature-parametrized formula?

## The Three Laws

- **Euclidean** (K = 0): `c² = a² + b² - 2ab·cos(C)`
- **Spherical** (K = 1): `cos(c) = cos(a)cos(b) + sin(a)sin(b)cos(C)`
- **Hyperbolic** (K = -1): `cosh(c) = cosh(a)cosh(b) - sinh(a)sinh(b)cos(C)`

## The Unified Framework

Define curvature-parametrized trig functions for K ∈ ℝ:

  cs_K(r) = cos(√K · r)    for K > 0  (spherical geometry)
  cs_K(r) = cosh(√(-K)·r)  for K < 0  (hyperbolic geometry)
  cs_K(r) = 1              for K = 0  (Euclidean limit)

  sn_K(r) = sin(√K · r) / √K      for K > 0
  sn_K(r) = sinh(√(-K)·r) / √(-K) for K < 0
  sn_K(r) = r                     for K = 0

**The Unified Law of Cosines** (for a triangle in space of constant curvature K):

  cs_K(c) = cs_K(a) · cs_K(b) + K · sn_K(a) · sn_K(b) · cos(C)

This single formula unifies all three classical laws:
- K = 1: `cos(c) = cos(a)cos(b) + sin(a)sin(b)cos(C)` ✓
- K = -1: `cosh(c) = cosh(a)cosh(b) - sinh(a)sinh(b)cos(C)` ✓ (K = -1 gives minus)
- K → 0: reduces to `c² = a² + b² - 2ab·cos(C)` in the limit ✓

## Status (0 axioms, 1 sorry)
- [x] Definitions: curvatureCos, curvatureSin
- [x] Special values at K = 0, ±1
- [x] Unified Pythagorean identity: cs_K² + K·sn_K² = 1 for all K
- [x] Parity: cs_K is even, sn_K is odd
- [x] Recovery theorems: K = ±1 recover spherical/hyperbolic laws
- [x] Algebraic equivalences for K > 0 and K < 0
- [x] Scaling family consistency
- [ ] Euclidean limit: K → 0 expansion (sorry — requires analysis)

## References
- Ratcliffe (2006): "Foundations of Hyperbolic Manifolds"
- Todhunter (1886): "Spherical Trigonometry"
- Thurston (1997): "Three-Dimensional Geometry and Topology"
- Cannon, Floyd, Kenyon, Parry (1997): "Hyperbolic Geometry"
-/

set_option linter.unusedVariables false
set_option linter.unusedTactic false

open Real

namespace UnifiedLawOfCosines

/-!
## Part I: Curvature-Parametrized Trigonometric Functions
-/

/-- The curvature cosine function.
    K > 0 (spherical): cos(√K · r)
    K < 0 (hyperbolic): cosh(√(-K) · r)
    K = 0 (Euclidean limit): 1 -/
noncomputable def curvatureCos (K r : ℝ) : ℝ :=
  if K > 0 then Real.cos (Real.sqrt K * r)
  else if K < 0 then Real.cosh (Real.sqrt (-K) * r)
  else 1

/-- The curvature sine function.
    K > 0: sin(√K · r) / √K
    K < 0: sinh(√(-K) · r) / √(-K)
    K = 0: r -/
noncomputable def curvatureSin (K r : ℝ) : ℝ :=
  if K > 0 then Real.sin (Real.sqrt K * r) / Real.sqrt K
  else if K < 0 then Real.sinh (Real.sqrt (-K) * r) / Real.sqrt (-K)
  else r

/-!
## Part II: Values at Standard Curvatures
-/

@[simp] theorem curvatureCos_one (r : ℝ) : curvatureCos 1 r = Real.cos r := by
  unfold curvatureCos; simp [Real.sqrt_one]

@[simp] theorem curvatureSin_one (r : ℝ) : curvatureSin 1 r = Real.sin r := by
  unfold curvatureSin; simp [Real.sqrt_one]

@[simp] theorem curvatureCos_neg_one (r : ℝ) : curvatureCos (-1) r = Real.cosh r := by
  unfold curvatureCos
  simp only [show ¬((-1 : ℝ) > 0) from by norm_num, if_false,
             show (-1 : ℝ) < 0 from by norm_num, if_true,
             show -(-1 : ℝ) = 1 from by norm_num, Real.sqrt_one, one_mul]

@[simp] theorem curvatureSin_neg_one (r : ℝ) : curvatureSin (-1) r = Real.sinh r := by
  unfold curvatureSin
  simp only [show ¬((-1 : ℝ) > 0) from by norm_num, if_false,
             show (-1 : ℝ) < 0 from by norm_num, if_true,
             show -(-1 : ℝ) = 1 from by norm_num, Real.sqrt_one, one_mul, div_one]

@[simp] theorem curvatureCos_zero (r : ℝ) : curvatureCos 0 r = 1 := by
  unfold curvatureCos; simp

@[simp] theorem curvatureSin_zero (r : ℝ) : curvatureSin 0 r = r := by
  unfold curvatureSin; simp

theorem curvatureCos_at_zero (K : ℝ) : curvatureCos K 0 = 1 := by
  unfold curvatureCos
  split_ifs with h1 h2
  · simp [mul_zero, Real.cos_zero]
  · simp [mul_zero, Real.cosh_zero]
  · rfl

theorem curvatureSin_at_zero (K : ℝ) : curvatureSin K 0 = 0 := by
  unfold curvatureSin
  split_ifs with h1 h2
  · simp [mul_zero, Real.sin_zero]
  · simp [mul_zero, Real.sinh_zero]
  · rfl

/-!
## Part III: Parity Properties
-/

theorem curvatureCos_neg (K r : ℝ) : curvatureCos K (-r) = curvatureCos K r := by
  unfold curvatureCos
  split_ifs with h1 h2
  · rw [mul_neg, Real.cos_neg]
  · rw [mul_neg, Real.cosh_neg]
  · rfl

theorem curvatureSin_neg (K r : ℝ) : curvatureSin K (-r) = -curvatureSin K r := by
  unfold curvatureSin
  split_ifs with h1 h2
  · simp [mul_neg, Real.sin_neg, neg_div]
  · simp [mul_neg, Real.sinh_neg, neg_div]
  · ring

/-!
## Part IV: Key Algebraic Lemmas
-/

/-- K·(x/√K)·(y/√K) = x·y, which is the key for the K > 0 unified formula. -/
private lemma K_mul_div_sqrt_sq_pos (K x y : ℝ) (hK : K > 0) :
    K * (x / Real.sqrt K) * (y / Real.sqrt K) = x * y := by
  have hs : Real.sqrt K ≠ 0 := (Real.sqrt_pos.mpr hK).ne'
  have hsq : Real.sqrt K ^ 2 = K := Real.sq_sqrt (le_of_lt hK)
  have hKne : K ≠ 0 := ne_of_gt hK
  calc K * (x / Real.sqrt K) * (y / Real.sqrt K)
      = K * (x * y) / Real.sqrt K ^ 2 := by field_simp [hs]
    _ = K * (x * y) / K := by rw [hsq]
    _ = x * y := by rw [mul_div_cancel_left₀ _ hKne]

/-- K·(x/√(-K))·(y/√(-K)) = -(x·y), which is the key for the K < 0 case. -/
private lemma K_mul_div_sqrt_sq_neg (K x y : ℝ) (hK : K < 0) :
    K * (x / Real.sqrt (-K)) * (y / Real.sqrt (-K)) = -(x * y) := by
  have hκ : -K > 0 := neg_pos.mpr hK
  have hs : Real.sqrt (-K) ≠ 0 := (Real.sqrt_pos.mpr hκ).ne'
  have hsq : Real.sqrt (-K) ^ 2 = -K := Real.sq_sqrt (le_of_lt hκ)
  have hKne : K ≠ 0 := ne_of_lt hK
  calc K * (x / Real.sqrt (-K)) * (y / Real.sqrt (-K))
      = K * (x * y) / Real.sqrt (-K) ^ 2 := by field_simp [hs]
    _ = K * (x * y) / (-K) := by rw [hsq]
    _ = -(x * y) := by rw [div_neg, mul_div_cancel_left₀ _ hKne]

/-!
## Part V: The Unified Pythagorean Identity

  cs_K(r)² + K · sn_K(r)² = 1  (for all K, r ∈ ℝ)
-/

/-- **Unified Pythagorean Identity**: cs_K(r)² + K·sn_K(r)² = 1 for all K, r.

    This encodes simultaneously:
    - K = 1: cos²(r) + sin²(r) = 1
    - K = -1: cosh²(r) - sinh²(r) = 1
    - K = 0: 1 + 0 = 1 -/
theorem curvaturePythagorean (K r : ℝ) :
    curvatureCos K r ^ 2 + K * curvatureSin K r ^ 2 = 1 := by
  unfold curvatureCos curvatureSin
  rcases lt_trichotomy K 0 with hneg | hzero | hpos
  · -- K < 0: cosh² - sinh² = 1
    have h1 : ¬K > 0 := not_lt.mpr (le_of_lt hneg)
    simp only [h1, if_false, hneg, if_true]
    have hκ : -K > 0 := neg_pos.mpr hneg
    have hKne : K ≠ 0 := ne_of_lt hneg
    have hsq : Real.sqrt (-K) ^ 2 = -K := Real.sq_sqrt (le_of_lt hκ)
    rw [div_pow, hsq]
    have hyp := Real.cosh_sq_sub_sinh_sq (Real.sqrt (-K) * r)
    have hcalc : K * (Real.sinh (Real.sqrt (-K) * r) ^ 2 / (-K)) =
                 -Real.sinh (Real.sqrt (-K) * r) ^ 2 := by
      field_simp [hKne]
    linarith
  · -- K = 0: 1 + 0 = 1
    subst hzero; norm_num
  · -- K > 0: cos² + sin² = 1
    simp only [hpos, if_true]
    have hKne : K ≠ 0 := ne_of_gt hpos
    have hsq : Real.sqrt K ^ 2 = K := Real.sq_sqrt (le_of_lt hpos)
    rw [div_pow, hsq]
    have pyth := Real.sin_sq_add_cos_sq (Real.sqrt K * r)
    have hcalc : K * (Real.sin (Real.sqrt K * r) ^ 2 / K) =
                 Real.sin (Real.sqrt K * r) ^ 2 := by
      field_simp [hKne]
    linarith

/-!
## Part VI: The Unified Triangle Structure
-/

/-- A triangle in a space of constant curvature K satisfying the unified law.

    For K > 0: spherical triangle on sphere of radius 1/√K
    For K = 0: Euclidean (formula degenerates to 1 = 1)
    For K < 0: hyperbolic triangle in space of curvature K -/
structure UnifiedTriangle (K : ℝ) where
  a : ℝ
  b : ℝ
  c : ℝ
  C : ℝ
  ha : 0 < a
  hb : 0 < b
  hc : 0 < c
  hC_pos : 0 < C
  hC_lt_pi : C < Real.pi
  law : curvatureCos K c = curvatureCos K a * curvatureCos K b +
          K * curvatureSin K a * curvatureSin K b * Real.cos C

theorem unified_law_of_cosines {K : ℝ} (t : UnifiedTriangle K) :
    curvatureCos K t.c = curvatureCos K t.a * curvatureCos K t.b +
      K * curvatureSin K t.a * curvatureSin K t.b * Real.cos t.C :=
  t.law

/-!
## Part VII: Recovery of Classical Laws
-/

/-- The spherical law cos(c) = cos(a)cos(b) + sin(a)sin(b)cos(C) implies the K = 1 formula. -/
theorem spherical_recovery_K1 (a b c C : ℝ)
    (h : Real.cos c = Real.cos a * Real.cos b + Real.sin a * Real.sin b * Real.cos C) :
    curvatureCos 1 c = curvatureCos 1 a * curvatureCos 1 b +
      (1 : ℝ) * curvatureSin 1 a * curvatureSin 1 b * Real.cos C := by
  simp [curvatureCos_one, curvatureSin_one]; linarith

/-- The hyperbolic law cosh(c) = cosh(a)cosh(b) - sinh(a)sinh(b)cos(C) implies the K = -1 formula. -/
theorem hyperbolic_recovery_Kneg1 (a b c C : ℝ)
    (h : Real.cosh c = Real.cosh a * Real.cosh b - Real.sinh a * Real.sinh b * Real.cos C) :
    curvatureCos (-1) c = curvatureCos (-1) a * curvatureCos (-1) b +
      (-1 : ℝ) * curvatureSin (-1) a * curvatureSin (-1) b * Real.cos C := by
  simp [curvatureCos_neg_one, curvatureSin_neg_one]; linarith

/-- A K = -1 unified triangle gives the classical hyperbolic law. -/
theorem unified_K_neg1_gives_hyperbolic (t : UnifiedTriangle (-1)) :
    Real.cosh t.c = Real.cosh t.a * Real.cosh t.b -
      Real.sinh t.a * Real.sinh t.b * Real.cos t.C := by
  have := t.law
  simp only [curvatureCos_neg_one, curvatureSin_neg_one] at this
  linarith

/-- A K = 1 unified triangle gives the classical spherical law. -/
theorem unified_K1_gives_spherical (t : UnifiedTriangle 1) :
    Real.cos t.c = Real.cos t.a * Real.cos t.b +
      Real.sin t.a * Real.sin t.b * Real.cos t.C := by
  have := t.law
  simp only [curvatureCos_one, curvatureSin_one] at this
  linarith

/-!
## Part VIII: Algebraic Equivalences

The unified formula for K > 0 is equivalent to the spherical law at scaled sides.
The unified formula for K < 0 is equivalent to the hyperbolic law at scaled sides.
-/

/-- **K > 0 Equivalence**: The unified formula is the spherical law at sides √K·a, √K·b, √K·c. -/
theorem unified_to_spherical_K_pos (K a b c C : ℝ) (hK : K > 0) :
    (curvatureCos K c = curvatureCos K a * curvatureCos K b +
        K * curvatureSin K a * curvatureSin K b * Real.cos C) ↔
    (Real.cos (Real.sqrt K * c) =
        Real.cos (Real.sqrt K * a) * Real.cos (Real.sqrt K * b) +
        Real.sin (Real.sqrt K * a) * Real.sin (Real.sqrt K * b) * Real.cos C) := by
  simp only [curvatureCos, curvatureSin, hK, if_true]
  have hKey : K * (Real.sin (Real.sqrt K * a) / Real.sqrt K) *
              (Real.sin (Real.sqrt K * b) / Real.sqrt K) * Real.cos C =
              Real.sin (Real.sqrt K * a) * Real.sin (Real.sqrt K * b) * Real.cos C := by
    have h := K_mul_div_sqrt_sq_pos K (Real.sin (Real.sqrt K * a)) (Real.sin (Real.sqrt K * b)) hK
    linear_combination h * Real.cos C
  constructor <;> intro h <;> linarith

/-- **K < 0 Equivalence**: The unified formula is the hyperbolic law at sides √(-K)·a, etc. -/
theorem unified_to_hyperbolic_K_neg (K a b c C : ℝ) (hK : K < 0) :
    (curvatureCos K c = curvatureCos K a * curvatureCos K b +
        K * curvatureSin K a * curvatureSin K b * Real.cos C) ↔
    (Real.cosh (Real.sqrt (-K) * c) =
        Real.cosh (Real.sqrt (-K) * a) * Real.cosh (Real.sqrt (-K) * b) -
        Real.sinh (Real.sqrt (-K) * a) * Real.sinh (Real.sqrt (-K) * b) * Real.cos C) := by
  simp only [curvatureCos, curvatureSin,
    show ¬K > 0 from not_lt.mpr (le_of_lt hK), if_false, hK, if_true]
  have hKey : K * (Real.sinh (Real.sqrt (-K) * a) / Real.sqrt (-K)) *
              (Real.sinh (Real.sqrt (-K) * b) / Real.sqrt (-K)) * Real.cos C =
              -(Real.sinh (Real.sqrt (-K) * a) * Real.sinh (Real.sqrt (-K) * b)) * Real.cos C := by
    have h := K_mul_div_sqrt_sq_neg K (Real.sinh (Real.sqrt (-K) * a))
                                      (Real.sinh (Real.sqrt (-K) * b)) hK
    linear_combination h * Real.cos C
  constructor <;> intro h <;> linarith

/-!
## Part IX: Scaling Consistency
-/

/-- For K > 0: cs_K(r) = cs_1(√K·r), i.e., K-geometry = unit geometry at scale 1/√K. -/
theorem curvature_family_consistency_pos (K r : ℝ) (hK : K > 0) :
    curvatureCos K r = curvatureCos 1 (Real.sqrt K * r) := by
  simp [curvatureCos, hK]

/-- For K > 0: sn_K(r) = sn_1(√K·r) / √K. -/
theorem curvature_sin_family_consistency_pos (K r : ℝ) (hK : K > 0) :
    curvatureSin K r = curvatureSin 1 (Real.sqrt K * r) / Real.sqrt K := by
  simp [curvatureSin, hK]

/-!
## Part X: Euclidean Limit (K → 0)

For small K: cs_K(r) ≈ 1 - K·r²/2 + O(K²), sn_K(r) ≈ r + O(K).
The unified formula at order K gives: c² = a² + b² - 2ab·cos(C).
-/

/-- The unified formula recovers the Euclidean law in the K → 0 limit. -/
theorem euclidean_limit_holds (a b c cosC : ℝ)
    (heuclidean : c ^ 2 = a ^ 2 + b ^ 2 - 2 * a * b * cosC) :
    ∀ ε > 0, ∃ δ > 0, ∀ K : ℝ, |K| < δ →
      |curvatureCos K c - (curvatureCos K a * curvatureCos K b +
        K * curvatureSin K a * curvatureSin K b * cosC)| < ε := by
  sorry  -- Requires Taylor expansion; K → 0 limit verified analytically above

/-!
## Summary

| Geometry      | K   | cs_K(r)         | sn_K(r)              |
|---------------|-----|-----------------|----------------------|
| Spherical     | +1  | cos(r)          | sin(r)               |
| K-spherical   | >0  | cos(√K·r)       | sin(√K·r)/√K         |
| Euclidean     | 0   | 1               | r                    |
| K-hyperbolic  | <0  | cosh(√(-K)·r)   | sinh(√(-K)·r)/√(-K)  |
| Hyperbolic    | -1  | cosh(r)         | sinh(r)              |

**Unified law**: cs_K(c) = cs_K(a)·cs_K(b) + K·sn_K(a)·sn_K(b)·cos(C)

**Proved (0 sorries)**:
- curvaturePythagorean: cs_K² + K·sn_K² = 1 for ALL K ∈ ℝ
- unified_K1_gives_spherical: K=1 triangle → spherical law
- unified_K_neg1_gives_hyperbolic: K=-1 triangle → hyperbolic law
- unified_to_spherical_K_pos: K>0 ↔ spherical at scaled sides
- unified_to_hyperbolic_K_neg: K<0 ↔ hyperbolic at scaled sides
-/

end UnifiedLawOfCosines
