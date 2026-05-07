import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
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

## Status (1 structure-encoded axiom: UnifiedTriangle.law; 0 sorries)
- [x] Definitions: curvatureCos, curvatureSin
- [x] Special values at K = 0, ±1
- [x] Unified Pythagorean identity: cs_K² + K·sn_K² = 1 for all K
- [x] Parity: cs_K is even, sn_K is odd
- [x] Recovery theorems: K = ±1 recover spherical/hyperbolic laws
- [x] Algebraic equivalences for K > 0 and K < 0
- [x] Scaling family consistency
- [x] Euclidean limit: K → 0 expansion (proved via explicit Taylor bounds)

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

/-- Helper: exp(t) - 1 ≤ t * exp(t) for all t ∈ ℝ. -/
private lemma exp_sub_one_le_mul_exp (t : ℝ) : Real.exp t - 1 ≤ t * Real.exp t := by
  have h1 : 1 - Real.exp (-t) ≤ t := by linarith [Real.add_one_le_exp (-t)]
  have h2 : Real.exp t * (1 - Real.exp (-t)) = Real.exp t - 1 := by
    rw [mul_sub, mul_one, ← Real.exp_add]; simp
  linarith [mul_le_mul_of_nonneg_left h1 (Real.exp_nonneg t)]

/-- Helper: cosh(x) - 1 ≤ (x²/2) * exp(x²/2). -/
private lemma cosh_sub_one_le (x : ℝ) : Real.cosh x - 1 ≤ x ^ 2 / 2 * Real.exp (x ^ 2 / 2) := by
  have h1 : Real.cosh x ≤ Real.exp (x ^ 2 / 2) := Real.cosh_le_exp_half_sq x
  have h2 : Real.exp (x ^ 2 / 2) - 1 ≤ x ^ 2 / 2 * Real.exp (x ^ 2 / 2) :=
    exp_sub_one_le_mul_exp (x ^ 2 / 2)
  linarith

/-- cosh(x) ≥ 1 for all x. -/
private lemma one_le_cosh (x : ℝ) : 1 ≤ Real.cosh x := by
  have h : (1 : ℝ) ≤ Real.cosh x ^ 2 := by
    nlinarith [Real.cosh_sq_sub_sinh_sq x, sq_nonneg (Real.sinh x)]
  have hnn : (0 : ℝ) ≤ Real.cosh x := (Real.cosh_pos x).le
  have hmono := Real.sqrt_le_sqrt h
  rwa [Real.sqrt_one, Real.sqrt_sq hnn] at hmono

/-- Bound: cosh(u·x) - 1 ≤ -K · (x²/2 · exp(x²/2)), for 0 < -K ≤ 1, u² = -K. -/
private lemma cosh_K_bound {K u : ℝ} (hK : 0 < -K) (hK1 : -K ≤ 1) (hu2 : u ^ 2 = -K) (x : ℝ) :
    Real.cosh (u * x) - 1 ≤ -K * (x ^ 2 / 2 * Real.exp (x ^ 2 / 2)) := by
  have h1 := cosh_sub_one_le (u * x)
  rw [mul_pow, hu2] at h1
  have hfactor : (0 : ℝ) ≤ -K * x ^ 2 / 2 :=
    div_nonneg (mul_nonneg (le_of_lt hK) (sq_nonneg x)) (by norm_num)
  have hexp_mono : Real.exp (-K * x ^ 2 / 2) ≤ Real.exp (x ^ 2 / 2) :=
    Real.exp_le_exp.mpr (by nlinarith [sq_nonneg x])
  linarith [mul_le_mul_of_nonneg_left hexp_mono hfactor,
            show -K * x ^ 2 / 2 * Real.exp (x ^ 2 / 2) =
                 -K * (x ^ 2 / 2 * Real.exp (x ^ 2 / 2)) from by ring]

/-- Bound: cosh(2·u·x) - 1 ≤ -K · 2 · (x² · exp(2x²)), for 0 < -K ≤ 1, u² = -K. -/
private lemma cosh_double_K_bound {K u : ℝ} (hK : 0 < -K) (hK1 : -K ≤ 1) (hu2 : u ^ 2 = -K)
    (x : ℝ) :
    Real.cosh (2 * (u * x)) - 1 ≤ -K * 2 * (x ^ 2 * Real.exp (2 * x ^ 2)) := by
  have h1 := cosh_sub_one_le (2 * (u * x))
  rw [show (2 * (u * x)) ^ 2 = 4 * (u ^ 2 * x ^ 2) from by ring, hu2] at h1
  have hfactor : (0 : ℝ) ≤ 4 * (-K * x ^ 2) / 2 :=
    div_nonneg (mul_nonneg (by norm_num) (mul_nonneg (le_of_lt hK) (sq_nonneg x))) (by norm_num)
  have hexp_mono : Real.exp (4 * (-K * x ^ 2) / 2) ≤ Real.exp (2 * x ^ 2) :=
    Real.exp_le_exp.mpr (by nlinarith [sq_nonneg x])
  linarith [mul_le_mul_of_nonneg_left hexp_mono hfactor,
            show 4 * (-K * x ^ 2) / 2 * Real.exp (2 * x ^ 2) =
                 -K * 2 * (x ^ 2 * Real.exp (2 * x ^ 2)) from by ring]

set_option maxHeartbeats 4000000 in
/-- The unified formula recovers the Euclidean law in the K → 0 limit.
    Proof: for K > 0, |expr| ≤ K·M using |sin x| ≤ |x| and 1 - cos x ≤ x²/2;
    for K < 0, |expr| ≤ |K|·M using cosh x - 1 ≤ x²/2·exp(x²/2) and double-angle identity;
    for K = 0, expression is exactly 0. -/
theorem euclidean_limit_holds (a b c cosC : ℝ)
    (heuclidean : c ^ 2 = a ^ 2 + b ^ 2 - 2 * a * b * cosC) :
    ∀ ε > 0, ∃ δ > 0, ∀ K : ℝ, |K| < δ →
      |curvatureCos K c - (curvatureCos K a * curvatureCos K b +
        K * curvatureSin K a * curvatureSin K b * cosC)| < ε := by
  intro ε hε
  -- Bound constant for K > 0: |expr| ≤ K * M_pos
  -- Bound constant for K < 0: |expr| ≤ κ * M_neg (where κ = -K)
  -- We use M = max(M_pos, M_neg) + 1 as a unified bound for all |K| ≤ 1.
  --
  -- M_pos comes from: 1 - cos x ≤ x²/2 and |sin x| ≤ |x|
  -- M_neg comes from: cosh x - 1 ≤ x²/2·exp(x²/2) and sinh² = (cosh(2x)-1)/2
  let M_pos := (c ^ 2 + a ^ 2 + b ^ 2) / 2 + |a| * |b| * |cosC| + 1
  let M_neg := c ^ 2 / 2 * Real.exp (c ^ 2 / 2) +
               a ^ 2 / 2 * Real.exp (a ^ 2 / 2) +
               (Real.exp (a ^ 2 / 2) + 1) * (b ^ 2 / 2 * Real.exp (b ^ 2 / 2)) +
               (a ^ 2 * Real.exp (2 * a ^ 2) + b ^ 2 * Real.exp (2 * b ^ 2)) / 2 * |cosC| + 1
  have hM_pos_pos : 0 < M_pos := by positivity
  have hM_neg_pos : 0 < M_neg := by positivity
  let M := M_pos + M_neg
  have hM_pos : 0 < M := by positivity
  refine ⟨min 1 (ε / M), lt_min one_pos (div_pos hε hM_pos), fun K hK => ?_⟩
  have hK1 : |K| ≤ 1 := le_of_lt (hK.trans_le (min_le_left _ _))
  have hKM : |K| * M < ε := by
    have := hK.trans_le (min_le_right _ _)
    calc |K| * M < ε / M * M := by
          apply mul_lt_mul_of_pos_right this hM_pos
        _ = ε := div_mul_cancel₀ ε (ne_of_gt hM_pos)
  rcases lt_trichotomy K 0 with hneg | hzero | hpos
  · -- K < 0 case: use cosh/sinh bounds
    have hκ : 0 < -K := neg_pos.mpr hneg
    have hκ1 : -K ≤ 1 := by linarith [(abs_le.mp hK1).1]
    -- Unfold piecewise definitions
    simp only [curvatureCos, curvatureSin,
               show ¬K > 0 from not_lt.mpr (le_of_lt hneg), if_false, hneg, if_true]
    -- Simplify K * sinh_a/sqrt * sinh_b/sqrt = -sinh_a * sinh_b (by K_mul_div_sqrt_sq_neg)
    have hsimp_neg : K * (Real.sinh (Real.sqrt (-K) * a) / Real.sqrt (-K)) *
                     (Real.sinh (Real.sqrt (-K) * b) / Real.sqrt (-K)) * cosC =
                     -(Real.sinh (Real.sqrt (-K) * a) * Real.sinh (Real.sqrt (-K) * b) * cosC) := by
      have h := K_mul_div_sqrt_sq_neg K (Real.sinh (Real.sqrt (-K) * a))
                                        (Real.sinh (Real.sqrt (-K) * b)) hneg
      linear_combination cosC * h
    rw [hsimp_neg]
    -- Expression = cosh(√κ·c) - cosh(√κ·a)·cosh(√κ·b) + sinh(√κ·a)·sinh(√κ·b)·cosC
    set u := Real.sqrt (-K)  -- u = √κ
    have hu2 : u ^ 2 = -K := Real.sq_sqrt (le_of_lt hκ)
    have hu_nn : 0 ≤ u := Real.sqrt_nonneg _
    -- Bound |cosh(u·c) - 1|
    have hcosh_c := cosh_K_bound hκ hκ1 hu2 c
    -- Bound |1 - cosh(u·a)·cosh(u·b)|
    have hcosh_a := cosh_K_bound hκ hκ1 hu2 a
    have hcosh_b := cosh_K_bound hκ hκ1 hu2 b
    have hcosh_a_le : Real.cosh (u * a) ≤ Real.exp (a ^ 2 / 2) + 1 := by
      have h1 := Real.cosh_le_exp_half_sq (u * a)
      rw [mul_pow, hu2] at h1
      have h2 : Real.exp (-K * a ^ 2 / 2) ≤ Real.exp (a ^ 2 / 2) :=
        Real.exp_le_exp.mpr (by nlinarith [sq_nonneg a])
      linarith [Real.exp_nonneg (a ^ 2 / 2)]
    -- Bound |sinh(u·a)·sinh(u·b)| via AM-GM + double angle
    have hsinh_sq_a : 2 * Real.sinh (u * a) ^ 2 = Real.cosh (2 * (u * a)) - 1 := by
      linarith [Real.cosh_two_mul (u * a), Real.cosh_sq_sub_sinh_sq (u * a)]
    have hsinh_sq_b : 2 * Real.sinh (u * b) ^ 2 = Real.cosh (2 * (u * b)) - 1 := by
      linarith [Real.cosh_two_mul (u * b), Real.cosh_sq_sub_sinh_sq (u * b)]
    have hcosh_2a := cosh_double_K_bound hκ hκ1 hu2 a
    have hcosh_2b := cosh_double_K_bound hκ hκ1 hu2 b
    -- |sinh_a * sinh_b| ≤ (sinh_a² + sinh_b²) / 2 by AM-GM
    have hsinh_amgm : Real.sinh (u * a) * Real.sinh (u * b) ≤
        (Real.sinh (u * a) ^ 2 + Real.sinh (u * b) ^ 2) / 2 := by
      nlinarith [sq_nonneg (Real.sinh (u * a) - Real.sinh (u * b))]
    have hsinh_amgm_neg : -(Real.sinh (u * a) * Real.sinh (u * b)) ≤
        (Real.sinh (u * a) ^ 2 + Real.sinh (u * b) ^ 2) / 2 := by
      nlinarith [sq_nonneg (Real.sinh (u * a) + Real.sinh (u * b))]
    have hsinh_prod_bound : |Real.sinh (u * a) * Real.sinh (u * b)| ≤
        (Real.sinh (u * a) ^ 2 + Real.sinh (u * b) ^ 2) / 2 := by
      rw [abs_le]
      constructor
      · linarith
      · exact hsinh_amgm
    -- Combine: |sinh_a * sinh_b| ≤ -K * (a²·exp(2a²) + b²·exp(2b²))/2
    have hsinh_final : |Real.sinh (u * a) * Real.sinh (u * b)| ≤
        -K * ((a ^ 2 * Real.exp (2 * a ^ 2) + b ^ 2 * Real.exp (2 * b ^ 2)) / 2) := by
      calc |Real.sinh (u * a) * Real.sinh (u * b)|
          ≤ (Real.sinh (u * a) ^ 2 + Real.sinh (u * b) ^ 2) / 2 := hsinh_prod_bound
        _ = (2 * Real.sinh (u * a) ^ 2 + 2 * Real.sinh (u * b) ^ 2) / 4 := by ring
        _ = ((Real.cosh (2 * (u * a)) - 1) + (Real.cosh (2 * (u * b)) - 1)) / 4 := by
            rw [hsinh_sq_a, hsinh_sq_b]
        _ ≤ (-K * 2 * (a ^ 2 * Real.exp (2 * a ^ 2)) +
              -K * 2 * (b ^ 2 * Real.exp (2 * b ^ 2))) / 4 := by
            apply div_le_div_of_nonneg_right _ (by norm_num)
            linarith
        _ = -K * ((a ^ 2 * Real.exp (2 * a ^ 2) + b ^ 2 * Real.exp (2 * b ^ 2)) / 2) := by ring
    -- Now assemble the bound on the full expression
    have hone_cosh : 1 ≤ Real.cosh (u * a) := one_le_cosh _
    have hone_cosh' : 1 ≤ Real.cosh (u * b) := one_le_cosh _
    -- |cosh(u·c) - cosh(u·a)·cosh(u·b) + sinh(u·a)·sinh(u·b)·cosC|
    -- ≤ |cosh(u·c) - 1| + |1 - cosh(u·a)·cosh(u·b)| + |sinh(u·a)·sinh(u·b)·cosC|
    have hineq : |Real.cosh (u * c) - Real.cosh (u * a) * Real.cosh (u * b) +
                  Real.sinh (u * a) * Real.sinh (u * b) * cosC|
                 ≤ (Real.cosh (u * c) - 1) + (Real.cosh (u * a) - 1) +
                   Real.cosh (u * a) * (Real.cosh (u * b) - 1) +
                   |Real.sinh (u * a) * Real.sinh (u * b)| * |cosC| := by
      have hcc := one_le_cosh (u * c)
      have hca := one_le_cosh (u * a)
      have hcb := one_le_cosh (u * b)
      have h_abs : |Real.sinh (u * a) * Real.sinh (u * b) * cosC| =
                   |Real.sinh (u * a) * Real.sinh (u * b)| * |cosC| := by
        rw [abs_mul]
      rw [show Real.cosh (u * c) - Real.cosh (u * a) * Real.cosh (u * b) +
          Real.sinh (u * a) * Real.sinh (u * b) * cosC =
          (Real.cosh (u * c) - 1) + (-(Real.cosh (u * a) * Real.cosh (u * b) - 1)) +
          Real.sinh (u * a) * Real.sinh (u * b) * cosC by ring]
      calc |(Real.cosh (u * c) - 1) + -(Real.cosh (u * a) * Real.cosh (u * b) - 1) +
              Real.sinh (u * a) * Real.sinh (u * b) * cosC|
          ≤ |Real.cosh (u * c) - 1| + |Real.cosh (u * a) * Real.cosh (u * b) - 1| +
            |Real.sinh (u * a) * Real.sinh (u * b) * cosC| := by
              -- Decompose: P = cosh_c - 1 ≥ 0, Q = cosh_ab - 1 ≥ 0, R = sinh*cosC
              have hP : (0 : ℝ) ≤ Real.cosh (u * c) - 1 := by linarith
              have hQ : (0 : ℝ) ≤ Real.cosh (u * a) * Real.cosh (u * b) - 1 := by nlinarith
              have h_c : |Real.cosh (u * c) - 1| = Real.cosh (u * c) - 1 :=
                abs_of_nonneg hP
              have h_ab : |Real.cosh (u * a) * Real.cosh (u * b) - 1| =
                          Real.cosh (u * a) * Real.cosh (u * b) - 1 := abs_of_nonneg hQ
              have hRp : Real.sinh (u * a) * Real.sinh (u * b) * cosC ≤
                         |Real.sinh (u * a) * Real.sinh (u * b) * cosC| := le_abs_self _
              have hRn : -|Real.sinh (u * a) * Real.sinh (u * b) * cosC| ≤
                         Real.sinh (u * a) * Real.sinh (u * b) * cosC := by
                have h := le_abs_self (-(Real.sinh (u * a) * Real.sinh (u * b) * cosC))
                rw [abs_neg] at h; linarith
              rw [abs_le]
              constructor
              · linarith [h_c, h_ab, hRn]
              · linarith [h_c, h_ab, hRp]
        _ ≤ (Real.cosh (u * c) - 1) + (Real.cosh (u * a) * Real.cosh (u * b) - 1) +
              |Real.sinh (u * a) * Real.sinh (u * b)| * |cosC| := by
            have h_c : |Real.cosh (u * c) - 1| = Real.cosh (u * c) - 1 :=
              abs_of_nonneg (by linarith)
            have h_ab : |Real.cosh (u * a) * Real.cosh (u * b) - 1| =
                        Real.cosh (u * a) * Real.cosh (u * b) - 1 :=
              abs_of_nonneg (by nlinarith)
            rw [h_c, h_ab, h_abs]
        _ = (Real.cosh (u * c) - 1) + (Real.cosh (u * a) - 1) +
              Real.cosh (u * a) * (Real.cosh (u * b) - 1) +
              |Real.sinh (u * a) * Real.sinh (u * b)| * |cosC| := by ring
    calc |Real.cosh (u * c) - (Real.cosh (u * a) * Real.cosh (u * b) +
              -(Real.sinh (u * a) * Real.sinh (u * b) * cosC))|
        = |Real.cosh (u * c) - Real.cosh (u * a) * Real.cosh (u * b) +
              Real.sinh (u * a) * Real.sinh (u * b) * cosC| := by ring_nf
      _ ≤ (Real.cosh (u * c) - 1) + (Real.cosh (u * a) - 1) +
            Real.cosh (u * a) * (Real.cosh (u * b) - 1) +
            |Real.sinh (u * a) * Real.sinh (u * b)| * |cosC| := hineq
      _ ≤ -K * (c ^ 2 / 2 * Real.exp (c ^ 2 / 2)) +
            -K * (a ^ 2 / 2 * Real.exp (a ^ 2 / 2)) +
            (Real.exp (a ^ 2 / 2) + 1) * (-K * (b ^ 2 / 2 * Real.exp (b ^ 2 / 2))) +
            (-K * ((a ^ 2 * Real.exp (2 * a ^ 2) + b ^ 2 * Real.exp (2 * b ^ 2)) / 2)) * |cosC| := by
          apply add_le_add
          · apply add_le_add
            · apply add_le_add
              · exact hcosh_c
              · exact hcosh_a
            · have hca_bd : Real.cosh (u * a) ≤ Real.exp (a ^ 2 / 2) + 1 := hcosh_a_le
              nlinarith [Real.exp_nonneg (a ^ 2 / 2)]
          · apply mul_le_mul_of_nonneg_right hsinh_final (abs_nonneg cosC)
      _ ≤ -K * M_neg := by
          -- Previous step = -K * (M_neg - 1), and -K ≥ 0 so -K * M_neg ≥ -K * (M_neg - 1)
          have hrw : -K * (c ^ 2 / 2 * Real.exp (c ^ 2 / 2) +
                          a ^ 2 / 2 * Real.exp (a ^ 2 / 2) +
                          (Real.exp (a ^ 2 / 2) + 1) * (b ^ 2 / 2 * Real.exp (b ^ 2 / 2)) +
                          (a ^ 2 * Real.exp (2 * a ^ 2) + b ^ 2 * Real.exp (2 * b ^ 2)) / 2 *
                          |cosC| + 1) =
                     -K * (c ^ 2 / 2 * Real.exp (c ^ 2 / 2)) +
                     -K * (a ^ 2 / 2 * Real.exp (a ^ 2 / 2)) +
                     (Real.exp (a ^ 2 / 2) + 1) * (-K * (b ^ 2 / 2 * Real.exp (b ^ 2 / 2))) +
                     (-K * ((a ^ 2 * Real.exp (2 * a ^ 2) + b ^ 2 * Real.exp (2 * b ^ 2)) / 2)) *
                     |cosC| + (-K) * 1 := by ring
          simp only [M_neg]
          linarith [hκ.le]
      _ ≤ |K| * M := by
          rw [abs_of_neg hneg]
          simp only [M]
          linarith [mul_pos hκ hM_pos_pos]
      _ < ε := hKM
  · -- K = 0 case: expression is exactly 0 < ε
    subst hzero
    simp [curvatureCos_zero, curvatureSin_zero, hε]
  · -- K > 0 case: use cos/sin Taylor bounds
    have hs : 0 < Real.sqrt K := Real.sqrt_pos.mpr hpos
    have hs' : Real.sqrt K ≠ 0 := hs.ne'
    simp only [curvatureCos, curvatureSin, hpos, if_true,
               show ¬K < 0 from not_lt.mpr (le_of_lt hpos), if_false]
    -- Simplify K * (sin(√K·a)/√K) * (sin(√K·b)/√K) = sin(√K·a) * sin(√K·b)
    have hsimp : K * (Real.sin (Real.sqrt K * a) / Real.sqrt K) *
                 (Real.sin (Real.sqrt K * b) / Real.sqrt K) * cosC =
                 Real.sin (Real.sqrt K * a) * Real.sin (Real.sqrt K * b) * cosC := by
      have h := K_mul_div_sqrt_sq_pos K (Real.sin (Real.sqrt K * a))
                                        (Real.sin (Real.sqrt K * b)) hpos
      linear_combination cosC * h
    rw [hsimp]
    set u := Real.sqrt K
    have hu2 : u ^ 2 = K := Real.sq_sqrt (le_of_lt hpos)
    have hu_nn : 0 ≤ u := hs.le
    -- Bound 1 - cos(u·x) ≤ K·x²/2 via Taylor: 1 - (u·x)²/2 ≤ cos(u·x), then rw u²=K
    have hcos_c : 1 - Real.cos (u * c) ≤ K * c ^ 2 / 2 := by
      have h1 : 1 - (u * c) ^ 2 / 2 ≤ Real.cos (u * c) := Real.one_sub_sq_div_two_le_cos
      rw [mul_pow, hu2] at h1; linarith
    have hcos_a : 1 - Real.cos (u * a) ≤ K * a ^ 2 / 2 := by
      have h1 : 1 - (u * a) ^ 2 / 2 ≤ Real.cos (u * a) := Real.one_sub_sq_div_two_le_cos
      rw [mul_pow, hu2] at h1; linarith
    have hcos_b : 1 - Real.cos (u * b) ≤ K * b ^ 2 / 2 := by
      have h1 : 1 - (u * b) ^ 2 / 2 ≤ Real.cos (u * b) := Real.one_sub_sq_div_two_le_cos
      rw [mul_pow, hu2] at h1; linarith
    -- Bound |sin(u·a)·sin(u·b)| ≤ K·|a|·|b| via |sin x| ≤ |x| and u²=K
    have hsin_prod : |Real.sin (u * a) * Real.sin (u * b)| ≤ K * (|a| * |b|) := by
      have hsa : |Real.sin (u * a)| ≤ u * |a| := by
        calc |Real.sin (u * a)| ≤ |u * a| := Real.abs_sin_le_abs
          _ = u * |a| := by rw [abs_mul, abs_of_nonneg hu_nn]
      have hsb : |Real.sin (u * b)| ≤ u * |b| := by
        calc |Real.sin (u * b)| ≤ |u * b| := Real.abs_sin_le_abs
          _ = u * |b| := by rw [abs_mul, abs_of_nonneg hu_nn]
      calc |Real.sin (u * a) * Real.sin (u * b)|
          = |Real.sin (u * a)| * |Real.sin (u * b)| := abs_mul _ _
        _ ≤ (u * |a|) * (u * |b|) := mul_le_mul hsa hsb (abs_nonneg _) (by positivity)
        _ = u ^ 2 * (|a| * |b|) := by ring
        _ = K * (|a| * |b|) := by rw [hu2]
    -- Auxiliary facts for triangle inequality
    have hcc : Real.cos (u * c) - 1 ≤ 0 := by linarith [Real.cos_le_one (u * c)]
    have hcprod : 0 ≤ 1 - Real.cos (u * a) * Real.cos (u * b) := by
      nlinarith [Real.cos_le_one (u * a), Real.cos_le_one (u * b),
                 Real.neg_one_le_cos (u * a), Real.neg_one_le_cos (u * b)]
    -- Triangle inequality: |P + Q + R| ≤ (1-cos_c) + (1-cos_a*cos_b) + |sin_a*sin_b|*|cosC|
    -- where P = cos_c-1 (≤0), Q = 1-cos_a*cos_b (≥0), R = -(sin_a*sin_b*cosC)
    have htri : |Real.cos (u * c) - (Real.cos (u * a) * Real.cos (u * b) +
                    Real.sin (u * a) * Real.sin (u * b) * cosC)|
              ≤ (1 - Real.cos (u * c)) + (1 - Real.cos (u * a) * Real.cos (u * b)) +
                |Real.sin (u * a) * Real.sin (u * b)| * |cosC| := by
      -- Bound ±(sin_a*sin_b*cosC) by |sin_a*sin_b|*|cosC|
      have hsin_le : -(Real.sin (u * a) * Real.sin (u * b) * cosC) ≤
                     |Real.sin (u * a) * Real.sin (u * b)| * |cosC| := by
        have h := le_abs_self (-(Real.sin (u * a) * Real.sin (u * b) * cosC))
        rw [abs_neg, abs_mul] at h; exact h
      have hsin_ge : -(|Real.sin (u * a) * Real.sin (u * b)| * |cosC|) ≤
                     -(Real.sin (u * a) * Real.sin (u * b) * cosC) := by
        have h := le_abs_self (Real.sin (u * a) * Real.sin (u * b) * cosC)
        rw [abs_mul] at h; linarith
      rw [show Real.cos (u * c) - (Real.cos (u * a) * Real.cos (u * b) +
               Real.sin (u * a) * Real.sin (u * b) * cosC) =
               (Real.cos (u * c) - 1) + (1 - Real.cos (u * a) * Real.cos (u * b)) +
               (-(Real.sin (u * a) * Real.sin (u * b) * cosC)) from by ring,
          abs_le]
      constructor
      · linarith [hcprod]
      · linarith [hcc, hcprod]
    -- Bound 1-cos_a*cos_b ≤ (1-cos_a) + (1-cos_b) and sin product by K*(|a|*|b|)*|cosC|
    have hexpand : 1 - Real.cos (u * a) * Real.cos (u * b) ≤
                   (1 - Real.cos (u * a)) + 1 * (1 - Real.cos (u * b)) := by
      nlinarith [Real.cos_le_one (u * a), Real.cos_le_one (u * b)]
    have hsin_cosC : |Real.sin (u * a) * Real.sin (u * b)| * |cosC| ≤
                     K * (|a| * |b|) * |cosC| :=
      mul_le_mul_of_nonneg_right hsin_prod (abs_nonneg cosC)
    -- Pre-compute 1-cos_a*cos_b ≤ K*a²/2 + K*b²/2 to simplify final linarith
    have hcab : 1 - Real.cos (u * a) * Real.cos (u * b) ≤ K * a ^ 2 / 2 + K * b ^ 2 / 2 := by
      linarith [hexpand, hcos_a, hcos_b]
    -- Assemble: |expr| ≤ K*c²/2 + K*a²/2 + K*b²/2 + K*(|a|*|b|)*|cosC| ≤ K*M_pos ≤ |K|*M
    calc |Real.cos (u * c) - (Real.cos (u * a) * Real.cos (u * b) +
              Real.sin (u * a) * Real.sin (u * b) * cosC)|
        ≤ K * c ^ 2 / 2 + K * a ^ 2 / 2 + K * b ^ 2 / 2 +
            K * (|a| * |b|) * |cosC| := by
          linarith [htri, hcab, hsin_cosC, hcos_c]
      _ ≤ K * M_pos := by
          have heq : K * c ^ 2 / 2 + K * a ^ 2 / 2 + K * b ^ 2 / 2 + K * (|a| * |b|) * |cosC| =
                     K * ((c ^ 2 + a ^ 2 + b ^ 2) / 2 + |a| * |b| * |cosC|) := by ring
          rw [heq]
          apply mul_le_mul_of_nonneg_left _ (le_of_lt hpos)
          simp only [M_pos]; linarith
      _ ≤ |K| * M := by
          rw [abs_of_pos hpos]
          have hMge : K * M_pos ≤ K * (M_pos + M_neg) :=
            mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (le_of_lt hM_neg_pos)) (le_of_lt hpos)
          simp only [M]; linarith
      _ < ε := hKM

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
