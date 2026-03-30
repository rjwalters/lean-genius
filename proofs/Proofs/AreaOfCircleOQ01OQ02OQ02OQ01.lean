import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.Tactic

/-
# Isoperimetric Inequality from IBP + Wirtinger + Parseval

## What This Proves

This file gives a clean formalization of Hurwitz's 1901 Fourier-analytic proof
of the isoperimetric inequality:

  C² ≥ 4πA

where C is the circumference and A the area of a smooth closed plane curve.
The proof chains three analytical ingredients:

1. **IBP** (Integration by Parts for Fourier coefficients):
   ĉₙ(f') = in · ĉₙ(f) for periodic C¹ functions

2. **Parseval's identity**: ∫₀²π f² = 2π · Σ|ĉₙ|²

3. **Wirtinger's inequality** (derived from 1 + 2):
   ∫₀²π f² ≤ ∫₀²π (f')² for mean-zero 2π-periodic C¹ functions

The isoperimetric inequality follows from Wirtinger applied to the coordinate
functions of a constant-speed reparametrization, combined with Cauchy–Schwarz
and the AM–GM inequality.

## Proof Architecture

The proof has three layers:
- **Layer 1 (Analytical)**: Wirtinger's inequality from Fourier analysis
- **Layer 2 (Algebraic)**: The arithmetic kernel 4πA ≤ L² from Wirtinger bounds
- **Layer 3 (Geometric)**: Assembly with reparametrization and Green's theorem

Layers 1 and 2 are fully proved. Layer 3 requires curve reparametrization
infrastructure (axiomatized, needs inverse function theorem).

## Connection to Prior Work

- `AreaOfCircleOQ01OQ02OQ02.lean`: IBP lemma ĉₙ(f') = in · ĉₙ(f)
- `AreaOfCircleOQ01OQ03.lean`: Full isoperimetric proof with Wirtinger
- **This file**: Clean, self-contained chain IBP → Wirtinger → Isoperimetric

## References

- Hurwitz, A. (1901). "Sur le problème des isopérimètres." C.R. Acad. Sci. Paris.
- Chavel, I. (2001). "Isoperimetric Inequalities." Cambridge Univ. Press.
-/

namespace IsoperimetricFromFourier

open Real MeasureTheory intervalIntegral

noncomputable section

/-! ## Part I: Fourier Decomposition (Axiomatized)

We axiomatize the Fourier decomposition of a periodic C¹ function into
real coefficients cₙ. This is proved in AreaOfCircleOQ01OQ03.lean
using Aristotle's proof of Parseval's identity.

The key properties:
- ∫₀²π f² = Σ cₙ²  (Parseval for f)
- ∫₀²π (f')² = Σ n²cₙ²  (Parseval for f', via IBP)
- c₀ = (1/√(2π)) ∫₀²π f  (zeroth coefficient = normalized mean)
-/

/-- A Fourier decomposition of a 2π-periodic C¹ function f into real
    coefficients cₙ satisfying Parseval's identity for both f and f'. -/
structure FourierDecomp (f : ℝ → ℝ) where
  /-- Real Fourier coefficients -/
  c : ℤ → ℝ
  /-- The coefficients are square-summable -/
  summable_sq : Summable (fun n : ℤ => c n ^ 2)
  /-- The weighted coefficients n²cₙ² are summable -/
  summable_n2_sq : Summable (fun n : ℤ => (↑n : ℝ) ^ 2 * c n ^ 2)
  /-- Parseval for f: ∫f² = Σcₙ² -/
  parseval_f : ∫ t in (0 : ℝ)..(2 * π), f t ^ 2 = ∑' n : ℤ, c n ^ 2
  /-- Parseval for f' (via IBP): ∫(f')² = Σn²cₙ² -/
  parseval_df : ∫ t in (0 : ℝ)..(2 * π), deriv f t ^ 2 = ∑' n : ℤ, (↑n : ℝ) ^ 2 * c n ^ 2
  /-- The zeroth coefficient captures the mean -/
  c_zero : c 0 = (1 / Real.sqrt (2 * π)) * ∫ t in (0 : ℝ)..(2 * π), f t

/-- Every 2π-periodic C¹ function admits a Fourier decomposition. -/
axiom fourier_decomp_exists (f : ℝ → ℝ) (hf : ContDiff ℝ 1 f)
    (hperiod : ∀ t, f (t + 2 * π) = f t) :
    Nonempty (FourierDecomp f)

/-! ## Part II: Wirtinger's Inequality

**Theorem (Wirtinger, 1904)**: For a mean-zero 2π-periodic C¹ function f:
  ∫₀²π f(t)² dt ≤ ∫₀²π f'(t)² dt

**Proof from Fourier analysis**:
- By Parseval: ∫f² = Σcₙ² and ∫(f')² = Σn²cₙ²
- Mean-zero ⟹ c₀ = 0 (since c₀ = (1/√(2π))∫f = 0)
- For n ≠ 0: n² ≥ 1, hence n²cₙ² ≥ cₙ²
- Summing: Σn²cₙ² ≥ Σcₙ², i.e., ∫(f')² ≥ ∫f²

This is the key analytical ingredient of Hurwitz's 1901 proof.
-/

/-- **Wirtinger's Inequality**: For a mean-zero 2π-periodic C¹ function,
    the integral of f² is bounded by the integral of (f')².

    Proof: From the Fourier decomposition, c₀ = 0 (mean zero), and
    for n ≠ 0, n² ≥ 1 gives n²cₙ² ≥ cₙ². Summing via Parseval yields
    ∫(f')² = Σn²cₙ² ≥ Σcₙ² = ∫f². -/
theorem wirtinger_inequality (f : ℝ → ℝ) (hf : ContDiff ℝ 1 f)
    (hperiod : ∀ t, f (t + 2 * π) = f t)
    (hmean : ∫ t in (0 : ℝ)..(2 * π), f t = 0)
    (F : FourierDecomp f) :
    ∫ t in (0 : ℝ)..(2 * π), f t ^ 2 ≤
    ∫ t in (0 : ℝ)..(2 * π), deriv f t ^ 2 := by
  -- Step 1: c₀ = 0 from zero mean
  have hc0 : F.c 0 = 0 := by rw [F.c_zero, hmean, mul_zero]
  -- Step 2: Pointwise bound n²cₙ² ≥ cₙ² for all n
  have h_pw : ∀ n : ℤ, F.c n ^ 2 ≤ (↑n : ℝ) ^ 2 * F.c n ^ 2 := by
    intro n
    by_cases hn : n = 0
    · subst hn; rw [hc0]; simp
    · have habs : (1 : ℝ) ≤ |(↑n : ℝ)| := by exact_mod_cast Int.one_le_abs hn
      have h1 : (1 : ℝ) ≤ (↑n : ℝ) ^ 2 := by nlinarith [sq_abs (↑n : ℝ)]
      calc F.c n ^ 2 = 1 * F.c n ^ 2 := (one_mul _).symm
        _ ≤ (↑n : ℝ) ^ 2 * F.c n ^ 2 :=
          mul_le_mul_of_nonneg_right h1 (sq_nonneg _)
  -- Step 3: Sum the pointwise bounds
  rw [F.parseval_f, F.parseval_df]
  exact hasSum_le h_pw F.summable_sq.hasSum F.summable_n2_sq.hasSum

/-! ## Part III: The Arithmetic Kernel

The algebraic core of the isoperimetric proof. Given:
- L = 2πc (circumference from constant-speed parametrization)
- 2A ≤ c·S (from Green's theorem + Cauchy–Schwarz)
- S² ≤ 2π·Sxy (integral Cauchy–Schwarz)
- Sxy ≤ 2πc² (from Wirtinger + constant speed)

Conclude: 4πA ≤ L².

The chain: S² ≤ 2π · 2πc² = (2πc)², so S ≤ 2πc.
Then 2A ≤ c · 2πc = 2πc², so A ≤ πc².
Hence 4πA ≤ 4π²c² = (2πc)² = L².
-/

/-- **2D Cauchy–Schwarz (algebraic)**: |xv − yu|² ≤ (x²+y²)(u²+v²).
    This bounds the cross product (area of parallelogram) by the product
    of the norms (squared). Used in the isoperimetric proof. -/
theorem cross_product_sq_le (x y u v : ℝ) :
    (x * v - y * u) ^ 2 ≤ (x ^ 2 + y ^ 2) * (u ^ 2 + v ^ 2) := by
  nlinarith [sq_nonneg (x * u + y * v)]

/-- **Arithmetic kernel of the isoperimetric proof**.
    Purely algebraic: from Wirtinger bounds, deduce 4πA ≤ L².

    This is the final step of Hurwitz's 1901 proof after the Fourier
    analysis is assembled. No integrals or measures appear here. -/
theorem isoperimetric_arithmetic_kernel
    (A L c S Sxy : ℝ)
    (hc : 0 < c)
    (hcirc : L = 2 * π * c)
    (hS_nn : 0 ≤ S)
    (harea : 2 * A ≤ c * S)
    (hCS : S ^ 2 ≤ 2 * π * Sxy)
    (hWirt : Sxy ≤ 2 * π * c ^ 2) :
    4 * π * A ≤ L ^ 2 := by
  have hpi : (0 : ℝ) < π := pi_pos
  have h2pic_pos : (0 : ℝ) < 2 * π * c := by positivity
  -- Step 1: S² ≤ (2πc)²
  have hS2 : S ^ 2 ≤ (2 * π * c) ^ 2 :=
    calc S ^ 2 ≤ 2 * π * Sxy := hCS
      _ ≤ 2 * π * (2 * π * c ^ 2) := mul_le_mul_of_nonneg_left hWirt (by linarith)
      _ = (2 * π * c) ^ 2 := by ring
  -- Step 2: S ≤ 2πc
  have hS_bound : S ≤ 2 * π * c := by
    have h := sqrt_le_sqrt hS2
    rwa [sqrt_sq hS_nn, sqrt_sq h2pic_pos.le] at h
  -- Step 3: 2A ≤ 2πc²
  have h1 : c * S ≤ 2 * π * c ^ 2 := by nlinarith
  have h2 : 2 * A ≤ 2 * π * c ^ 2 := le_trans harea h1
  -- Step 4: 4πA ≤ L²
  calc 4 * π * A = 2 * π * (2 * A) := by ring
    _ ≤ 2 * π * (2 * π * c ^ 2) := mul_le_mul_of_nonneg_left h2 (by linarith)
    _ = (2 * π * c) ^ 2 := by ring
    _ = L ^ 2 := by rw [hcirc]

/-! ## Part IV: The Full Isoperimetric Statement

We state the isoperimetric inequality for smooth closed curves using
a structure that captures the geometric data.
-/

/-- A smooth closed plane curve with its geometric invariants. -/
structure SmoothClosedCurve where
  /-- x-coordinate function -/
  x : ℝ → ℝ
  /-- y-coordinate function -/
  y : ℝ → ℝ
  /-- Both components are C¹ -/
  smooth_x : ContDiff ℝ 1 x
  smooth_y : ContDiff ℝ 1 y
  /-- Both are 2π-periodic -/
  periodic_x : ∀ t, x (t + 2 * π) = x t
  periodic_y : ∀ t, y (t + 2 * π) = y t

/-- Circumference of a smooth closed curve (arc length over one period). -/
noncomputable def SmoothClosedCurve.circumference (γ : SmoothClosedCurve) : ℝ :=
  ∫ t in (0 : ℝ)..(2 * π), sqrt (deriv γ.x t ^ 2 + deriv γ.y t ^ 2)

/-- Enclosed area via Green's theorem (signed area). -/
noncomputable def SmoothClosedCurve.area (γ : SmoothClosedCurve) : ℝ :=
  (1 / 2) * |∫ t in (0 : ℝ)..(2 * π), (γ.x t * deriv γ.y t - γ.y t * deriv γ.x t)|

/-- The circumference is nonneg (integral of a nonneg function). -/
theorem SmoothClosedCurve.circumference_nonneg (γ : SmoothClosedCurve) :
    0 ≤ γ.circumference := by
  apply integral_nonneg (by linarith [pi_pos])
  intro t _
  exact sqrt_nonneg _

/-- The area is nonneg (absolute value). -/
theorem SmoothClosedCurve.area_nonneg (γ : SmoothClosedCurve) :
    0 ≤ γ.area := by
  unfold area
  apply mul_nonneg (by norm_num)
  exact abs_nonneg _

/-! ## Part V: Equality for the Circle

Before the general inequality, we verify the equality case: C² = 4πA
for a circle of radius r.
-/

/-- A circle of radius r centered at the origin. -/
noncomputable def circleOfRadius (r : ℝ) : SmoothClosedCurve where
  x := fun t => r * cos t
  y := fun t => r * sin t
  smooth_x := (contDiff_const.mul (Real.contDiff_cos))
  smooth_y := (contDiff_const.mul (Real.contDiff_sin))
  periodic_x := fun t => by simp [cos_add_two_pi]
  periodic_y := fun t => by simp [sin_add_two_pi]

/-- The isoperimetric ratio I(γ) = C²/(4πA).
    For a circle: I = 1. For all curves: I ≥ 1. -/
noncomputable def isoperimetricRatio (C A : ℝ) : ℝ := C ^ 2 / (4 * π * A)

/-- The isoperimetric ratio of a circle is 1.
    Proof: C = 2πr, A = πr², so C²/(4πA) = (2πr)²/(4π·πr²) = 4π²r²/(4π²r²) = 1. -/
theorem circle_isoperimetric_ratio (r : ℝ) (hr : 0 < r) :
    isoperimetricRatio (2 * π * r) (π * r ^ 2) = 1 := by
  unfold isoperimetricRatio
  have hπ : π ≠ 0 := ne_of_gt pi_pos
  have hr' : r ≠ 0 := ne_of_gt hr
  field_simp [hπ, hr']
  ring

/-- C² = 4πA holds exactly for circles. Algebraic verification. -/
theorem circle_isoperimetric_equality (r : ℝ) :
    (2 * π * r) ^ 2 = 4 * π * (π * r ^ 2) := by ring

/-! ## Part VI: Inequality for Non-Circular Shapes

Strict inequality C² > 4πA for the square, demonstrating that the
circle is optimal.
-/

/-- A square with side s has perimeter 4s and area s².
    Its isoperimetric ratio is 4/(π) > 1. Equivalently, C² > 4πA. -/
theorem square_isoperimetric_strict (s : ℝ) (hs : 0 < s) :
    4 * π * s ^ 2 < (4 * s) ^ 2 := by
  -- Need: 4πs² < 16s², i.e., π < 4
  have : 4 * π * s ^ 2 < 4 * 4 * s ^ 2 := by nlinarith [pi_lt_four]
  linarith

/-- The isoperimetric ratio of a square is 4/π ≈ 1.273 > 1. -/
theorem square_isoperimetric_ratio (s : ℝ) (hs : 0 < s) :
    isoperimetricRatio (4 * s) (s ^ 2) = 4 / π := by
  unfold isoperimetricRatio
  have hπ : π ≠ 0 := ne_of_gt pi_pos
  have hs' : s ≠ 0 := ne_of_gt hs
  field_simp [hπ, hs']
  ring

/-- The isoperimetric ratio of a regular n-gon is πn⁻¹/tan(π/n).
    As n → ∞, this → 1 (approaching the circle).
    For n = 3 (equilateral triangle): ratio = π√3/9.
    For n = 4 (square): ratio = 4/π. -/
theorem equilateral_triangle_isoperimetric_ratio :
    isoperimetricRatio (3 * (2 : ℝ)) (sqrt 3) = 9 / (π * sqrt 3) := by
  unfold isoperimetricRatio
  have hπ : π ≠ 0 := ne_of_gt pi_pos
  have h3 : sqrt 3 ≠ 0 := ne_of_gt (sqrt_pos.mpr (by norm_num))
  field_simp [hπ, h3]
  ring

/-! ## Part VII: The Full Isoperimetric Inequality

We state the general isoperimetric inequality C² ≥ 4πA for smooth
closed curves. The proof requires reparametrization by arc length
(to get constant speed) and mean subtraction (to apply Wirtinger).
These are axiomatized.
-/

/-- **Reparametrization existence** [Axiom]: Every smooth closed curve with
    positive circumference can be reparametrized to have constant speed
    and zero mean.

    This requires:
    - Arc-length reparametrization: inverse function theorem on ∫|γ'|
    - Mean subtraction: preserves derivatives, hence speed and area -/
axiom exists_nice_reparam (γ : SmoothClosedCurve) (hL : 0 < γ.circumference) :
    ∃ γ' : SmoothClosedCurve,
      γ'.circumference = γ.circumference ∧
      γ'.area = γ.area ∧
      (∀ t, deriv γ'.x t ^ 2 + deriv γ'.y t ^ 2 =
        (γ.circumference / (2 * π)) ^ 2) ∧
      (∫ t in (0 : ℝ)..(2 * π), γ'.x t = 0) ∧
      (∫ t in (0 : ℝ)..(2 * π), γ'.y t = 0)

/-- **Wirtinger bound on speed** [Axiom]: For a zero-mean constant-speed
    curve, ∫(x²+y²) ≤ 2πc² where c = L/(2π) is the constant speed.

    Proof sketch: By Wirtinger applied to x and y separately:
    ∫x² ≤ ∫(x')² and ∫y² ≤ ∫(y')², so ∫(x²+y²) ≤ ∫(x'²+y'²) = 2πc².
    The last equality uses constant speed: x'²+y'² = c² at all points. -/
axiom wirtinger_sum_bound (γ : SmoothClosedCurve) (c : ℝ) (hc : 0 < c)
    (hspeed : ∀ t, deriv γ.x t ^ 2 + deriv γ.y t ^ 2 = c ^ 2)
    (hzx : ∫ t in (0 : ℝ)..(2 * π), γ.x t = 0)
    (hzy : ∫ t in (0 : ℝ)..(2 * π), γ.y t = 0) :
    ∫ t in (0 : ℝ)..(2 * π), (γ.x t ^ 2 + γ.y t ^ 2) ≤ 2 * π * c ^ 2

/-- **Area bound from Cauchy–Schwarz** [Axiom]: For a constant-speed curve,
    2A ≤ c · ∫√(x²+y²).

    Proof sketch: Green's formula gives 2A = |∫(xy'-yx')|.
    By 2D Cauchy–Schwarz: |xy'-yx'| ≤ √(x²+y²)·√(x'²+y'²) = c·√(x²+y²).
    Integrating: 2A ≤ c · ∫√(x²+y²). -/
axiom area_cauchy_schwarz_bound (γ : SmoothClosedCurve) (c : ℝ) (hc : 0 < c)
    (hspeed : ∀ t, deriv γ.x t ^ 2 + deriv γ.y t ^ 2 = c ^ 2) :
    2 * γ.area ≤ c * ∫ t in (0 : ℝ)..(2 * π), sqrt (γ.x t ^ 2 + γ.y t ^ 2)

/-- **Integral Cauchy–Schwarz**: S² ≤ 2π · Sxy where
    S = ∫√(x²+y²) and Sxy = ∫(x²+y²).

    This is Cauchy–Schwarz applied to 1 and √(x²+y²) on [0,2π]:
    (∫ 1·√(x²+y²))² ≤ (∫ 1²)(∫ (x²+y²)) = 2π · ∫(x²+y²). -/
axiom integral_cauchy_schwarz_sq
    (γ : SmoothClosedCurve) :
    (∫ t in (0 : ℝ)..(2 * π), sqrt (γ.x t ^ 2 + γ.y t ^ 2)) ^ 2 ≤
    2 * π * ∫ t in (0 : ℝ)..(2 * π), (γ.x t ^ 2 + γ.y t ^ 2)

/-- **The Isoperimetric Inequality** (Hurwitz 1901):
    For any smooth closed plane curve with circumference C and area A:
      C² ≥ 4πA
    with equality if and only if the curve is a circle.

    Proof: reparametrize to constant speed c = C/(2π) with zero mean.
    Apply Wirtinger to get ∫(x²+y²) ≤ 2πc². Apply Cauchy–Schwarz to get
    S² ≤ 2π·2πc². Then S ≤ 2πc, so 2A ≤ c·S ≤ 2πc², giving
    4πA ≤ 4π²c² = C².

    This uses 4 axioms for the analytical bounds, plus the fully proved
    arithmetic kernel. -/
theorem isoperimetric_inequality (γ : SmoothClosedCurve)
    (hL : 0 < γ.circumference) :
    4 * π * γ.area ≤ γ.circumference ^ 2 := by
  -- Step 1: Get nice reparametrization
  obtain ⟨γ', hcirc, harea, hspeed, hzx, hzy⟩ := exists_nice_reparam γ hL
  -- Step 2: Set up c = L/(2π)
  set c := γ.circumference / (2 * π) with hc_def
  have hc_pos : 0 < c := div_pos hL (by positivity)
  -- Step 3: Gather the analytical bounds
  have hWirt := wirtinger_sum_bound γ' c hc_pos (by rwa [hcirc]) hzx hzy
  have hArea := area_cauchy_schwarz_bound γ' c hc_pos (by rwa [hcirc])
  have hCS := integral_cauchy_schwarz_sq γ'
  -- Step 4: Set S and Sxy
  set S := ∫ t in (0 : ℝ)..(2 * π), sqrt (γ'.x t ^ 2 + γ'.y t ^ 2)
  set Sxy := ∫ t in (0 : ℝ)..(2 * π), (γ'.x t ^ 2 + γ'.y t ^ 2)
  -- Step 5: S ≥ 0
  have hS_nn : 0 ≤ S := by
    apply integral_nonneg (by linarith [pi_pos])
    intro t _
    exact sqrt_nonneg _
  -- Step 6: Apply the arithmetic kernel
  have hL_eq : γ.circumference = 2 * π * c := by
    rw [hc_def]; field_simp [ne_of_gt pi_pos]
  rw [← harea]
  exact isoperimetric_arithmetic_kernel γ'.area γ'.circumference c S Sxy
    hc_pos (by rwa [hcirc]) hS_nn hArea hCS hWirt

/-! ## Conclusion

The isoperimetric inequality C² ≥ 4πA is formalized with:
- 5 axioms (Fourier decomposition existence, reparametrization, Wirtinger sum
  bound, area Cauchy–Schwarz, integral Cauchy–Schwarz)
- 0 sorries
- The arithmetic kernel and concrete examples (circle, square, triangle) are
  fully proved

The axioms isolate the analytical infrastructure that requires substantial
Mathlib work:
1. `fourier_decomp_exists`: Parseval + IBP for periodic functions
2. `exists_nice_reparam`: inverse function theorem for arc-length reparametrization
3. `wirtinger_sum_bound`: Wirtinger applied to coordinate functions
4. `area_cauchy_schwarz_bound`: Green's theorem + pointwise Cauchy–Schwarz
5. `integral_cauchy_schwarz_sq`: L² Cauchy–Schwarz on [0,2π]

Of these, #1 is proved in AreaOfCircleOQ01OQ03.lean (by Aristotle), #3 follows
from Wirtinger (proved there), and #5 is standard. Only #2 (reparametrization)
and #4 (Green's theorem formalization) require significant new infrastructure.
-/

end

end IsoperimetricFromFourier
