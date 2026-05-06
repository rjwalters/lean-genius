import Mathlib
import Proofs.GreensTheoremOQ01

/-
# Generalized Stokes Theorem: ∫_M dω = ∫_{∂M} ω

## What This Formalizes

The generalized Stokes theorem unifies the fundamental integral theorems
of calculus into a single identity: the integral of the exterior derivative
of a differential form over a manifold equals the integral of the form
over the boundary.

Special cases:
- **1D (FTC)**: ∫_[a,b] F'(x)dx = F(b) - F(a)
  M = [a,b], ω = F (0-form), dω = F'dx (1-form)
- **2D (Green)**: ∮_∂D (Pdx + Qdy) = ∬_D (∂Q/∂x - ∂P/∂y) dA
  ω = Pdx + Qdy (1-form), dω = (∂Q/∂x - ∂P/∂y)dx∧dy (2-form)
- **3D surface (Stokes)**: ∮_∂S F⃗·dr⃗ = ∬_S (∇×F⃗)·dS⃗
- **3D volume (Gauss)**: ∬_∂V F⃗·dS⃗ = ∭_V (∇·F⃗) dV

## Approach

We define differential k-forms concretely in dimensions 1 and 2, define
the exterior derivative d, and prove:
1. Stokes in 1D = FTC Part 2 (from Mathlib, no sorries)
2. The d² = 0 property (Clairaut/Schwarz symmetry of mixed partials)
3. Poincaré lemma in 1D: closed forms are exact
4. Green's theorem as Stokes in 2D (from Mathlib, via GreensTheoremOQ01)

## Mathlib Dependencies

- `integral_eq_sub_of_hasDerivAt_of_le` : FTC Part 2
- `integral_eq_sub_of_hasDerivAt` : FTC (general orientation)
- `IntervalIntegrable` : Integrability conditions
- `HasDerivAt`, `deriv` : Derivative API
- `is_const_of_deriv_eq_zero` : Mean value theorem consequence
-/

namespace GeneralizedStokes

open MeasureTheory Set Filter Topology intervalIntegral

-- ═══════════════════════════════════════════════════════════════
-- PART I: Differential Forms in 1D
-- ═══════════════════════════════════════════════════════════════

/-
In 1D, the de Rham complex is:

  Ω⁰(ℝ) --d→ Ω¹(ℝ)

where Ω⁰(ℝ) = {functions F : ℝ → ℝ} and Ω¹(ℝ) = {f(x)dx}.
The exterior derivative d takes F to F'(x)dx.
Integration of a 1-form over [a,b] is ∫_a^b f(x) dx.
Integration of a 0-form over ∂[a,b] = {b} - {a} is F(b) - F(a).
-/

/-- The exterior derivative in 1D: d(F) = F'(x)dx.
    Takes a 0-form (function) to a 1-form (coefficient of dx). -/
noncomputable def extDeriv1D (F : ℝ → ℝ) : ℝ → ℝ := deriv F

/-- Integration of a 1-form f(x)dx over the oriented interval [a,b]. -/
noncomputable def intForm1D (f : ℝ → ℝ) (a b : ℝ) : ℝ :=
  ∫ x in a..b, f x

/-- Boundary integration of a 0-form F over ∂[a,b] = {b} - {a}.
    The boundary of [a,b] consists of the endpoint b with orientation +1
    and the endpoint a with orientation -1. -/
def bdryEval (F : ℝ → ℝ) (a b : ℝ) : ℝ := F b - F a

-- ═══════════════════════════════════════════════════════════════
-- PART II: Stokes Theorem in 1D = Fundamental Theorem of Calculus
-- ═══════════════════════════════════════════════════════════════

/-- **Stokes' theorem in 1D** (= FTC Part 2):
    ∫_M dω = ∫_{∂M} ω
    where M = [a,b], ω = F (a 0-form), dω = F'(x)dx (a 1-form).

    This is the foundational case of the generalized Stokes theorem:
    the integral of the exterior derivative over the manifold equals
    the integral of the form over the boundary. -/
theorem stokes_1d {F : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b)
    (hF_cont : ContinuousOn F (Icc a b))
    (hF_deriv : ∀ x ∈ Ioo a b, HasDerivAt F (deriv F x) x)
    (hF_int : IntervalIntegrable (deriv F) volume a b) :
    intForm1D (extDeriv1D F) a b = bdryEval F a b := by
  unfold intForm1D extDeriv1D bdryEval
  exact integral_eq_sub_of_hasDerivAt_of_le hab hF_cont hF_deriv hF_int

/-- Stokes 1D for differentiable functions with continuous derivative.
    This is the cleanest statement matching the classical FTC. -/
theorem stokes_1d_differentiable {F : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b)
    (hF_diff : Differentiable ℝ F)
    (hF'_cont : Continuous (deriv F)) :
    intForm1D (extDeriv1D F) a b = bdryEval F a b := by
  apply stokes_1d hab
  · exact hF_diff.continuous.continuousOn
  · exact fun x _ => hF_diff.differentiableAt.hasDerivAt
  · exact hF'_cont.intervalIntegrable a b

/-- Stokes 1D is orientation-reversing: reversing the interval negates the integral.
    This corresponds to reversing the orientation of the manifold M.
    This holds unconditionally (even for non-integrable functions, where both sides are 0). -/
theorem stokes_1d_orientation (F : ℝ → ℝ) (a b : ℝ) :
    intForm1D (extDeriv1D F) b a = -intForm1D (extDeriv1D F) a b := by
  unfold intForm1D extDeriv1D
  exact intervalIntegral.integral_symm b a

-- ═══════════════════════════════════════════════════════════════
-- PART III: d² = 0 in 1D
-- ═══════════════════════════════════════════════════════════════

/-
In 1D there are no 2-forms, so d² = 0 is vacuously true:
the de Rham complex Ω⁰ → Ω¹ has no further step.

The interesting consequence is the Poincaré lemma:
if a 1-form f(x)dx has "zero exterior derivative" (automatically true in 1D),
then it is exact: f(x)dx = d(F) for some F.
-/

/-- Every continuous 1-form in 1D is exact (= d of some 0-form).
    This is the 1D Poincaré lemma: closed ⟹ exact.
    The antiderivative F(x) = ∫_a^x f(t) dt satisfies dF = f. -/
theorem poincare_1d {f : ℝ → ℝ} {a : ℝ} (hf : Continuous f) :
    ∃ F : ℝ → ℝ, ∀ x, HasDerivAt F (f x) x := by
  refine ⟨fun x => ∫ t in a..x, f t, fun x => ?_⟩
  exact integral_hasDerivAt_right (hf.intervalIntegrable a x)
    (hf.stronglyMeasurableAtFilter volume (𝓝 x)) hf.continuousAt

/-- Two antiderivatives of the same 1-form differ by a constant.
    This is the uniqueness part: the kernel of d is {constants}. -/
theorem exact_unique {F G f : ℝ → ℝ}
    (hF : ∀ x, HasDerivAt F (f x) x) (hG : ∀ x, HasDerivAt G (f x) x) :
    ∃ c : ℝ, ∀ x, F x - G x = c := by
  use F 0 - G 0
  intro x
  have h : ∀ y, HasDerivAt (fun z => F z - G z) 0 y := by
    intro y; have := (hF y).sub (hG y); simp at this; exact this
  have hdiff : Differentiable ℝ (fun z => F z - G z) :=
    fun z => (h z).differentiableAt
  have hderiv : ∀ z, deriv (fun z => F z - G z) z = 0 :=
    fun z => (h z).deriv
  have := is_const_of_deriv_eq_zero hdiff hderiv x 0
  linarith

-- ═══════════════════════════════════════════════════════════════
-- PART IV: Differential Forms in 2D
-- ═══════════════════════════════════════════════════════════════

/-
In 2D, the de Rham complex is:

  Ω⁰(ℝ²) --d₀→ Ω¹(ℝ²) --d₁→ Ω²(ℝ²)

where:
  Ω⁰ = {functions f : ℝ² → ℝ}
  Ω¹ = {P(x,y)dx + Q(x,y)dy}
  Ω² = {h(x,y) dx∧dy}

The exterior derivatives are:
  d₀(f) = (∂f/∂x)dx + (∂f/∂y)dy        (gradient)
  d₁(Pdx + Qdy) = (∂Q/∂x - ∂P/∂y)dx∧dy  (curl)

The key identity d₁ ∘ d₀ = 0 (d² = 0) is Clairaut's theorem:
  ∂²f/∂x∂y = ∂²f/∂y∂x for C² functions.
-/

/-- A 1-form in 2D: ω = P(x,y)dx + Q(x,y)dy, represented as the pair (P, Q). -/
structure OneForm2D where
  P : ℝ × ℝ → ℝ  -- coefficient of dx
  Q : ℝ × ℝ → ℝ  -- coefficient of dy

/-- The exterior derivative d₀ : Ω⁰(ℝ²) → Ω¹(ℝ²).
    d(f) = (∂f/∂x)dx + (∂f/∂y)dy -/
noncomputable def extDeriv0_2D (f : ℝ × ℝ → ℝ) : OneForm2D where
  P := fun p => deriv (fun x => f (x, p.2)) p.1
  Q := fun p => deriv (fun y => f (p.1, y)) p.2

/-- The exterior derivative d₁ : Ω¹(ℝ²) → Ω²(ℝ²).
    d(Pdx + Qdy) = (∂Q/∂x - ∂P/∂y) dx∧dy

    This is the **curl** of the vector field (P, Q). -/
noncomputable def extDeriv1_2D (ω : OneForm2D) : ℝ × ℝ → ℝ :=
  fun p => deriv (fun x => ω.Q (x, p.2)) p.1 -
            deriv (fun y => ω.P (p.1, y)) p.2

-- ═══════════════════════════════════════════════════════════════
-- PART V: d² = 0 in 2D (Clairaut's Theorem)
-- ═══════════════════════════════════════════════════════════════

/-- **d² = 0**: The composition d₁ ∘ d₀ vanishes for C² functions.

    Expanding: d₁(d₀(f)) = ∂²f/∂x∂y - ∂²f/∂y∂x = 0

    This is Clairaut's theorem (Schwarz's theorem): the equality of
    mixed partial derivatives for sufficiently smooth functions.

    In the de Rham cohomology framework, d² = 0 is the fundamental
    property that makes the cohomology groups H^k = ker(d_k)/im(d_{k-1})
    well-defined. -/
theorem dd_eq_zero_2D (f : ℝ × ℝ → ℝ) (hf : ContDiff ℝ 2 f) (p : ℝ × ℝ) :
    extDeriv1_2D (extDeriv0_2D f) p = 0 := by
  simp only [extDeriv1_2D, extDeriv0_2D]
  rw [sub_eq_zero]
  -- Differentiability: f is C¹, fderiv ℝ f is C¹ (since f is C²)
  have hDiff : Differentiable ℝ f := hf.differentiable (by norm_num)
  have hFDiff : Differentiable ℝ (fderiv ℝ f) :=
    (hf.fderiv_right (by norm_num)).differentiable (by norm_num)
  -- Express y-partial as fderiv evaluation
  have hDY : ∀ x, deriv (fun y => f (x, y)) p.2 = fderiv ℝ f (x, p.2) (0, 1) := fun x =>
    ((hDiff (x, p.2)).hasFDerivAt.comp_hasDerivAt p.2
      ((hasDerivAt_const p.2 x).prod (hasDerivAt_id p.2)) rfl).deriv
  -- Express x-partial as fderiv evaluation
  have hDX : ∀ y, deriv (fun x => f (x, y)) p.1 = fderiv ℝ f (p.1, y) (1, 0) := fun y =>
    ((hDiff (p.1, y)).hasFDerivAt.comp_hasDerivAt p.1
      ((hasDerivAt_id p.1).prod (hasDerivAt_const p.1 y)) rfl).deriv
  simp_rw [hDY, hDX]
  -- Second partial: d/dx[fderiv ℝ f (x, p.2)] via the embedding x ↦ (x, p.2)
  have hStep1 : HasDerivAt (fun x => fderiv ℝ f (x, p.2))
      (fderiv ℝ (fderiv ℝ f) p (1, 0)) p.1 :=
    (hFDiff p).hasFDerivAt.comp_hasDerivAt p.1
      ((hasDerivAt_id p.1).prod (hasDerivAt_const p.1 p.2)) rfl
  have hStep2 : HasDerivAt (fun y => fderiv ℝ f (p.1, y))
      (fderiv ℝ (fderiv ℝ f) p (0, 1)) p.2 :=
    (hFDiff p).hasFDerivAt.comp_hasDerivAt p.2
      ((hasDerivAt_const p.2 p.1).prod (hasDerivAt_id p.2)) rfl
  -- Apply evaluation at (0, 1) and (1, 0) respectively
  -- HasDerivAt.clm_apply: if c has deriv c' and u has deriv u', then (fun x => c x (u x)) has deriv c'(u x) + c(x)(u')
  have hDer2XY : HasDerivAt (fun x => fderiv ℝ f (x, p.2) (0, 1))
      (fderiv ℝ (fderiv ℝ f) p (1, 0) (0, 1)) p.1 := by
    have h := hStep1.clm_apply (hasDerivAt_const p.1 (0, 1 : ℝ × ℝ))
    simp only [map_zero, add_zero] at h; exact h
  have hDer2YX : HasDerivAt (fun y => fderiv ℝ f (p.1, y) (1, 0))
      (fderiv ℝ (fderiv ℝ f) p (0, 1) (1, 0)) p.2 := by
    have h := hStep2.clm_apply (hasDerivAt_const p.2 (1, 0 : ℝ × ℝ))
    simp only [map_zero, add_zero] at h; exact h
  rw [hDer2XY.deriv, hDer2YX.deriv]
  -- Symmetry of the second Fréchet derivative: Clairaut/Schwarz theorem
  exact hf.contDiffAt.isSymmSndFDerivAt (1, 0) (0, 1)

-- ═══════════════════════════════════════════════════════════════
-- PART VI: Green's Theorem as Stokes in 2D
-- ═══════════════════════════════════════════════════════════════

/-- Integration of a 1-form ω = Pdx + Qdy around the boundary of
    the rectangle [a,b]×[c,d], traversed counterclockwise. -/
noncomputable def lineIntegralRect (ω : OneForm2D) (a b c d : ℝ) : ℝ :=
  (∫ x in a..b, ω.P (x, c)) + (∫ y in c..d, ω.Q (b, y)) -
  (∫ x in a..b, ω.P (x, d)) - (∫ y in c..d, ω.Q (a, y))

/-- Integration of a 2-form h dx∧dy over the rectangle [a,b]×[c,d]. -/
noncomputable def areaIntegralRect (h : ℝ × ℝ → ℝ) (a b c d : ℝ) : ℝ :=
  ∫ y in c..d, ∫ x in a..b, h (x, y)

/-- **Green's theorem** for rectangles, expressed in Stokes form:
    ∫_{∂R} ω = ∫_R dω

    This is the 2D special case of the generalized Stokes theorem.
    The proof strategy is:
    1. Split the double integral: ∫∫ (∂Q/∂x - ∂P/∂y) = ∫∫ ∂Q/∂x - ∫∫ ∂P/∂y
    2. Apply FTC to ∂Q/∂x: ∫_a^b ∂Q/∂x dx = Q(b,y) - Q(a,y)
    3. Apply Fubini + FTC to ∂P/∂y: ∫∫ ∂P/∂y = ∫(P(x,d) - P(x,c))dx
    4. Combine: line integral = double integral

    The full proof is in `GreensTheoremOQ01.lean` (0 sorries, 0 axioms).
    Here we state the result in the Stokes framework. -/
theorem stokes_2d_rectangle (ω : OneForm2D) (a b c d : ℝ)
    (hQ_deriv : ∀ y, ∀ x ∈ uIcc a b,
      HasDerivAt (fun x => ω.Q (x, y)) (deriv (fun x => ω.Q (x, y)) x) x)
    (hQ_int : ∀ y ∈ uIcc c d,
      IntervalIntegrable (fun x => deriv (fun x => ω.Q (x, y)) x) volume a b)
    (hP_deriv : ∀ x, ∀ y ∈ uIcc c d,
      HasDerivAt (fun y => ω.P (x, y)) (deriv (fun y => ω.P (x, y)) y) y)
    (hP_int : ∀ x ∈ uIcc a b,
      IntervalIntegrable (fun y => deriv (fun y => ω.P (x, y)) y) volume c d)
    -- Boundary integrability
    (hQb : IntervalIntegrable (fun y => ω.Q (b, y)) volume c d)
    (hQa : IntervalIntegrable (fun y => ω.Q (a, y)) volume c d)
    (hPc : IntervalIntegrable (fun x => ω.P (x, c)) volume a b)
    (hPd : IntervalIntegrable (fun x => ω.P (x, d)) volume a b)
    -- Inner integrability of ∂P/∂y in x
    (hPdy_x_int : ∀ y ∈ uIcc c d,
      IntervalIntegrable (fun x => deriv (fun y' => ω.P (x, y')) y) volume a b)
    -- Outer integrability of inner integrals
    (hQ_outer_int : IntervalIntegrable
      (fun y => ∫ x in a..b, deriv (fun x => ω.Q (x, y)) x) volume c d)
    (hPdy_outer_int : IntervalIntegrable
      (fun y => ∫ x in a..b, deriv (fun y' => ω.P (x, y')) y) volume c d)
    -- Fubini: swap integration order for ∂P/∂y
    (hFubini : ∫ y in c..d, ∫ x in a..b, deriv (fun y' => ω.P (x, y')) y =
               ∫ x in a..b, ∫ y in c..d, deriv (fun y' => ω.P (x, y')) y) :
    lineIntegralRect ω a b c d =
    areaIntegralRect (extDeriv1_2D ω) a b c d := by
  -- Proved via GreensTheoremOQ01.greens_theorem_concrete
  simp only [lineIntegralRect, areaIntegralRect, extDeriv1_2D]
  have h := GreensTheoremOQ01.greens_theorem_concrete ω.P ω.Q a b c d
    (fun p => deriv (fun x => ω.Q (x, p.2)) p.1)
    (fun p => deriv (fun y => ω.P (p.1, y)) p.2)
    hQ_deriv hQ_int hP_deriv hP_int
    hQb hQa hPc hPd hPdy_x_int hQ_outer_int hPdy_outer_int hFubini
  simp only [GreensTheoremOQ01.rectLineIntegral, GreensTheoremOQ01.rectDoubleIntegral] at h
  exact h

-- ═══════════════════════════════════════════════════════════════
-- PART VII: The Abstract Generalized Stokes Theorem
-- ═══════════════════════════════════════════════════════════════

/-
The fully general Stokes theorem states:

  ∫_M dω = ∫_{∂M} ω

for any compact oriented smooth n-manifold M with boundary ∂M
and any smooth (n-1)-form ω on M.

This requires:
1. Smooth manifolds with boundary (Mathlib: `SmoothManifoldWithCorners`)
2. Differential k-forms as smooth sections of Λᵏ(T*M)
3. The exterior derivative d : Ωᵏ(M) → Ωᵏ⁺¹(M)
4. Integration of n-forms on oriented n-manifolds
5. The induced orientation and inclusion ∂M ↪ M

Mathlib has (1), (2) partially (via `ExteriorAlgebra`), and (3) partially.
Formalizing (4) — integration of differential forms on manifolds — is an
active area of Mathlib development. When available, the concrete
instances proved in this file (1D: `stokes_1d`, 2D: `stokes_2d_rectangle`)
would become special cases of the general statement.

The hierarchy of special cases:
  n=1: FTC          ∫_[a,b] F'dx = F(b) - F(a)
  n=2: Green         ∮ Pdx+Qdy = ∬ (∂Q/∂x - ∂P/∂y) dA
  n=2: Stokes (3D)   ∮ F⃗·dr⃗ = ∬ (∇×F⃗)·dS⃗
  n=3: Gauss         ∬ F⃗·dS⃗ = ∭ (∇·F⃗) dV
  general: Stokes    ∫_M dω = ∫_{∂M} ω
-/

-- ═══════════════════════════════════════════════════════════════
-- PART VIII: The Hierarchy of Integral Theorems
-- ═══════════════════════════════════════════════════════════════

/-- Summary: the 1D Stokes theorem (= FTC) is a special case.
    M = [a,b] (oriented 1-manifold with boundary),
    ω = F (a 0-form), dω = F'dx (a 1-form).
    ∫_M dω = ∫_a^b F'dx and ∫_{∂M} ω = F(b) - F(a). -/
theorem stokes_hierarchy_1d : ∀ (F : ℝ → ℝ) (a b : ℝ),
    a ≤ b →
    Differentiable ℝ F →
    Continuous (deriv F) →
    intForm1D (extDeriv1D F) a b = bdryEval F a b :=
  fun F a b hab hd hc => stokes_1d_differentiable hab hd hc

/-- The Stokes theorem implies the evaluation formula: to compute
    an integral ∫_a^b f(x) dx, find F with F' = f, then F(b) - F(a). -/
theorem evaluation_formula {f : ℝ → ℝ} {a b : ℝ} {F : ℝ → ℝ}
    (hab : a ≤ b)
    (hF : Differentiable ℝ F)
    (hF'_cont : Continuous (deriv F))
    (hF_deriv : ∀ x, deriv F x = f x) :
    ∫ x in a..b, f x = F b - F a := by
  have heq : ∫ x in a..b, f x = ∫ x in a..b, deriv F x :=
    integral_congr (fun x _ => (hF_deriv x).symm)
  rw [heq]
  have hstokes := stokes_1d_differentiable hab hF hF'_cont
  simp only [intForm1D, extDeriv1D, bdryEval] at hstokes
  exact hstokes

/-- **Closed forms are exact in 1D** (Poincaré lemma).

    Combined with d² = 0, this shows H¹_dR(ℝ) = 0:
    every closed 1-form on ℝ is exact (the first de Rham cohomology
    of ℝ is trivial). In contrast, H¹_dR(S¹) = ℝ (the circle has
    a 1-dimensional first cohomology). -/
theorem h1_trivial : ∀ (f : ℝ → ℝ), Continuous f →
    ∃ F : ℝ → ℝ, extDeriv1D F = f := by
  intro f hf
  obtain ⟨F, hF⟩ := poincare_1d hf
  exact ⟨F, funext fun x => (hF x).deriv⟩

/-- The kernel of d in degree 0 consists of constant functions.

    H⁰_dR(ℝ) = ℝ: the zeroth de Rham cohomology is 1-dimensional,
    reflecting the fact that ℝ is connected. -/
theorem h0_eq_constants {F : ℝ → ℝ} (hF : Differentiable ℝ F)
    (hd : extDeriv1D F = 0) :
    ∀ x y : ℝ, F x = F y := by
  have hderiv : ∀ z, deriv F z = 0 := fun z => by
    have := congr_fun hd z
    exact this
  exact is_const_of_deriv_eq_zero hF hderiv

end GeneralizedStokes
